open Syntax
open Support.Error
module Dict = Map.Make (String)
module SSet = Set.Make (String)

(* typing result: T1@[T2,T3,a] *)
type typing = ty * ty * ty * annot

(* type constraint: T1 = T2 *)
type type_constr = ty * ty

(* annotatino constraint *)
type annot_constr =
  (* Equal: a1 == a2 *)
  | AConEQ of annot * annot
  (* Less Equal: a1 <= a2 *)
  | AConLE of annot * annot
  (* Type Infer: T1 != T2 => a = i *)
  | AConTI of ty * ty * annot
  (* Annot Infer: a1 != a2 => a = i *)
  | AConAI of annot * annot * annot

type type_subst = ty Dict.t
type annot_subst = annot Dict.t
type type_var_set = SSet.t
type type_scheme = type_var_set * type_var_set * ty
type type_context = type_scheme Dict.t

let tcon2string (t1, t2) = type2string_with_annot t1 ^ " = " ^ type2string_with_annot t2

let acon2string =
  let spf = Printf.sprintf in
  function
  | AConEQ (a1, a2) -> spf "%s = %s" (annot2string a1) (annot2string a2)
  | AConLE (a1, a2) -> spf "%s <= %s" (annot2string a1) (annot2string a2)
  | AConTI (t1, t2, a) ->
    spf
      "%s != %s => %s = i"
      (type2string_with_annot t1)
      (type2string_with_annot t2)
      (annot2string a)
  | AConAI (a1, a2, a) ->
    spf "%s != %s => %s" (annot2string a1) (annot2string a2) (annot2string a)
;;

let print_tcons tcons =
  List.iter
    (fun x ->
      print_string (tcon2string x);
      print_newline ())
    tcons;
  print_newline ()
;;

let print_acons acons =
  List.iter
    (fun x ->
      print_string (acon2string x);
      print_newline ())
    acons;
  print_newline ()
;;

let print_asubst =
  Dict.iter (fun x an ->
      print_string (x ^ " -> " ^ annot2string an);
      print_newline ())
;;

let ident x = x

let id_of_ty = function
  | TyId x -> x
  | ty -> raise (Invalid_argument (type2string ty))

and id_of_an = function
  | AnId x -> x
  | an -> raise (Invalid_argument (annot2string an))
;;

let annot_map map_id = function
  | AnId x as a -> map_id x a
  | a -> a
;;

let type_map map_an map_id =
  let rec map = function
    | TyId x as ty -> map_id x ty
    | TyFun (t1, t2, t3, t4, a) -> TyFun (map t1, map t2, map t3, map t4, map_an a)
    | TyList ty -> TyList (map ty)
    | ty -> ty
  in
  map
;;

let term_map map_an map_id =
  let rec map (fi, a, t) =
    ( fi
    , map_an a
    , match t with
      | TmVar x -> map_id x t
      | TmFix (a, f, x, _, t1) -> TmFix (map_an a, f, x, None, map t1)
      | TmAbs (a, x, _, t1) -> TmAbs (map_an a, x, None, map t1)
      | TmApp (a, t1, t2) -> TmApp (map_an a, map t1, map t2)
      | TmLet (x, t1, t2) -> TmLet (x, map t1, map t2)
      | TmShift (a, k, t1) -> TmShift (map_an a, k, map t1)
      | TmReset t1 -> TmReset (map t1)
      | TmIf (t1, t2, t3) -> TmIf (map t1, map t2, map t3)
      | TmSucc t1 -> TmSucc (map t1)
      | TmPred t1 -> TmPred (map t1)
      | TmIsZero t1 -> TmIsZero (map t1)
      | TmCons (t1, t2) -> TmCons (map t1, map t2)
      | TmLMatch (t1, t2, hd, tl, t3) -> TmLMatch (map t1, map t2, hd, tl, map t3)
      | _ -> t )
  in
  map
;;

let tcon_map map_ty (t1, t2) = map_ty t1, map_ty t2

let acon_map map_ty map_an = function
  | AConEQ (a1, a2) -> AConEQ (map_an a1, map_an a2)
  | AConLE (a1, a2) -> AConLE (map_an a1, map_an a2)
  | AConTI (t1, t2, a) -> AConTI (map_ty t1, map_ty t2, map_an a)
  | AConAI (a1, a2, a) -> AConAI (map_an a1, map_an a2, map_an a)
;;

let subst1_ty x tyS = type_map ident (fun y tyT -> if x = y then tyS else tyT)

and subst_ty s =
  type_map ident (fun x tyT ->
      match Dict.find_opt x s with
      | Some tyS -> tyS
      | None -> tyT)
;;

let subst1_tcons x tyS = List.map (tcon_map @@ subst1_ty x tyS)
and subst_tcons s = List.map (tcon_map @@ subst_ty s)

let subst1_an x an = annot_map (fun y an' -> if x = y then an else an')

and subst_an s =
  annot_map (fun x an ->
      match Dict.find_opt x s with
      | Some an -> an
      | None -> an)
;;

let subst1_acons x an = List.map (acon_map ident @@ subst1_an x an)
and subst_acons s = List.map (acon_map ident @@ subst_an s)

(* compose s with [x -> v] or s2 *)
let compose1 f s1 x v = Dict.update x (fun _ -> Some (f s1 v)) s1
let compose f s1 s2 = Dict.fold (fun x v s -> Dict.update x (fun _ -> Some (f s1 v)) s) s2

(* unify the type constraints to get the type substitution *)
let unify_tcons : type_constr list -> type_subst * annot_constr list =
  let comp = compose1 subst_ty in
  let rec occur x = function
    | TyId y -> x = y
    | TyFun (t1, t2, t3, t4, _) -> occur x t1 || occur x t2 || occur x t3 || occur x t4
    | TyList ty -> occur x ty
    | _ -> false
  in
  let rec unify constr : type_subst * annot_constr list =
    match constr with
    | [] -> Dict.empty, []
    | con :: rest ->
      (match con with
      | TyNat, TyNat | TyBool, TyBool -> unify rest
      | TyId x, TyId y when x = y -> unify rest
      | TyId x, tyT | tyT, TyId x ->
        if occur x tyT
        then error dummyinfo "recursive typing"
        else (
          let s, ac = unify (subst1_tcons x tyT rest) in
          comp s x tyT, ac)
      | TyFun (t1, t2, t3, t4, a), TyFun (t1', t2', t3', t4', a') ->
        let s, ac = unify ((t1, t1') :: (t2, t2') :: (t3, t3') :: (t4, t4') :: rest) in
        s, AConEQ (a, a') :: ac
      | TyList ty, TyList ty' -> unify ((ty, ty') :: rest)
      | _ -> error dummyinfo "unsolvable type constraints")
  in
  unify
;;

(* reconstruct the type, and annotate the term *)
let recon : term -> term * typing * type_constr list * annot_constr list =
  (* empty type context & empty type variable set *)
  let empty_tyctx = Dict.empty
  and empty_tvset = SSet.empty in
  (* fresh variable *)
  let new_a () = AnId (freshname "?a")
  and new_X () = TyId (freshname "?X") in
  let rec is_val (_, _, t) =
    match t with
    | TmNat _ | TmBool _ | TmVar _ | TmAbs _ | TmFix _ | TmNil -> true
    | TmCons (t1, t2) -> is_val t1 && is_val t2
    | _ -> false
  in
  (* context querying & extending *)
  let query fi x ctx =
    match Dict.find_opt x ctx with
    | Some scm -> scm
    | None -> error fi ("cannot find " ^ x ^ " in current type context")
  and extend x scm ctx = Dict.update x (fun _ -> Some scm) ctx in
  (* type scheme & instantiate & generalize *)
  let free_tyvars ty =
    let rec go ty acc =
      match ty with
      | TyId x -> SSet.add x acc
      | TyFun (t1, t2, t3, t4, _) -> go t1 acc |> go t2 |> go t3 |> go t4
      | TyList ty -> go ty acc
      | _ -> acc
    in
    go ty empty_tvset
  in
  let inst (_, btv, ty) = SSet.fold (fun x ty -> subst1_ty x (new_X ()) ty) btv ty
  and raw_scm ty = free_tyvars ty, empty_tvset, ty
  and make_scm ftv btv ty =
    ( List.fold_left (fun acc ty -> SSet.add (id_of_ty ty) acc) empty_tvset ftv
    , List.fold_left (fun acc ty -> SSet.add (id_of_ty ty) acc) empty_tvset btv
    , ty )
  and gen_scm ctx ty =
    let ftv = free_tyvars ty in
    let btv = Dict.fold (fun x (ftv, _, _) btv -> SSet.diff btv ftv) ctx ftv in
    let ftv = SSet.diff ftv btv in
    ftv, btv, ty
  in
  (* recon *)
  let rec recon ctx t' =
    let fi, _, t = t' in
    match t with
    (* x *)
    | TmVar x ->
      let scm = query fi x ctx in
      let tyI = inst scm in
      let tyX = new_X () in
      (fi, AnPure, t), (tyI, tyX, tyX, AnPure), [], []
    (* natural *)
    | TmNat _ ->
      let tyX = new_X () in
      (fi, AnPure, t), (TyNat, tyX, tyX, AnPure), [], []
    (* boolean *)
    | TmBool _ ->
      let tyX = new_X () in
      (fi, AnPure, t), (TyBool, tyX, tyX, AnPure), [], []
    (* lambda x: T?. t2 *)
    | TmAbs (_, x, maybeT, t1) ->
      let tyX =
        match maybeT with
        | Some tyT -> tyT
        | None -> new_X ()
      in
      let tyY, a2 = new_X (), new_a () in
      let t1, (tyT1, tyR1, tyS1, a1), tc, ac = recon (extend x (raw_scm tyX) ctx) t1 in
      let ac = AConLE (a1, a2) :: AConTI (tyR1, tyS1, a1) :: ac in
      let ty = TyFun (tyX, tyT1, tyR1, tyS1, a2) in
      (fi, AnPure, TmAbs (a2, x, None, t1)), (ty, tyY, tyY, AnPure), tc, ac
    (* t1 @ t2 *)
    | TmApp (_, t1, t2) ->
      let t1, (tyT1, tyR1, tyS1, a1), tc1, ac1 = recon ctx t1 in
      let t2, (tyT2, tyR2, tyS2, a2), tc2, ac2 = recon ctx t2 in
      let tyX, tyY, a3, a = new_X (), new_X (), new_a (), new_a () in
      let tc =
        (tyT1, TyFun (tyT2, tyX, tyY, tyR2, a3)) :: (tyR1, tyS2) :: List.append tc1 tc2
      in
      let ac =
        AConLE (a1, a)
        :: AConLE (a2, a)
        :: AConLE (a3, a)
        :: AConTI (tyR1, tyS1, a1)
        :: AConTI (tyR2, tyS2, a2)
        :: AConTI (tyY, tyR2, a3)
        :: List.append ac1 ac2
      in
      (fi, a, TmApp (a3, t1, t2)), (tyX, tyY, tyS1, a), tc, ac
    (* fix. f. x. t1 *)
    | TmFix (_, f, x, maybeT, t1) ->
      let tyX =
        match maybeT with
        | Some tyT -> tyT
        | None -> new_X ()
      and tyY, tyZ, tyR1', tyS1', a1', a2 =
        new_X (), new_X (), new_X (), new_X (), new_a (), new_a ()
      in
      let tyF = TyFun (tyX, tyY, tyR1', tyS1', a1') in
      let ctx = ctx |> extend f (raw_scm tyF) |> extend x (raw_scm tyX) in
      let t1, (tyT1, tyR1, tyS1, a1), tc, ac = recon ctx t1 in
      let tc = (tyY, tyT1) :: (tyR1', tyR1) :: (tyS1', tyS1) :: tc in
      let ac =
        AConLE (a1, a2)
        :: AConTI (tyR1, tyS1, a1)
        :: AConLE (a1, a1')
        :: AConLE (a1', a1)
        :: ac
      in
      let ty = TyFun (tyX, tyY, tyR1, tyS1, a2) in
      (fi, AnPure, TmFix (a2, f, x, None, t1)), (ty, tyZ, tyZ, AnPure), tc, ac
    (* let x = v1 in t2 *)
    | TmLet (x, v1, t2) when is_val v1 ->
      let v1, (tyT1, _, _, _), tc1, ac1 = recon ctx v1 in
      let s, ac = unify_tcons tc1 in
      let tyT1' = subst_ty s tyT1 in
      let scm = gen_scm ctx tyT1' in
      let t2, (tyT2, tyR2, tyS2, a2), tc2, ac2 = recon (extend x scm ctx) t2 in
      let a = new_a () in
      let tc = List.append tc1 tc2 in
      let ac =
        AConLE (a2, a) :: AConTI (tyR2, tyS2, a2) :: List.concat [ ac1; ac2; ac ]
      in
      (fi, a, TmLet (x, v1, t2)), (tyT2, tyR2, tyS2, a), tc, ac
    (* let x = t1 in t2 *)
    | TmLet (x, t1, t2) ->
      let t1, (tyT1, tyR1, tyS1, a1), tc1, ac1 = recon ctx t1 in
      let t2, (tyT2, tyR2, tyS2, a2), tc2, ac2 = recon (extend x (raw_scm tyT1) ctx) t2 in
      let a = new_a () in
      let tc = (tyR1, tyS1) :: List.append tc1 tc2 in
      let ac =
        AConLE (a1, a)
        :: AConLE (a2, a)
        :: AConTI (tyR1, tyS1, a1)
        :: AConTI (tyR2, tyS2, a2)
        :: List.append ac1 ac2
      in
      (fi, a, TmLet (x, t1, t2)), (tyT2, tyR2, tyS2, a), tc, ac
    (* if t1 then t2 else t3 *)
    | TmIf (t1, t2, t3) ->
      let t1, (tyT1, tyR1, tyS1, a1), tc1, ac1 = recon ctx t1 in
      let t2, (tyT2, tyR2, tyS2, a2), tc2, ac2 = recon ctx t2 in
      let t3, (tyT3, tyR3, tyS3, a3), tc3, ac3 = recon ctx t3 in
      let a = new_a () in
      let tc =
        (tyR1, tyS2)
        :: (tyR1, tyS3)
        :: (tyR2, tyR3)
        :: (tyT2, tyT3)
        :: (tyT1, TyBool)
        :: List.concat [ tc1; tc2; tc3 ]
      in
      let ac =
        List.fold_right
          (fun (a', tyR, tyS) ls -> AConLE (a', a) :: AConTI (tyR, tyS, a') :: ls)
          [ a1, tyR1, tyS1; a2, tyR2, tyS2; a3, tyR3, tyS3 ]
          (List.concat [ ac1; ac2; ac3 ])
      in
      (fi, a, TmIf (t1, t2, t3)), (tyT2, tyR2, tyS1, a), tc, ac
    (* shift k in t1 *)
    | TmShift (_, k, t1) ->
      let tyX, tyY, tau, a2 = new_X (), new_X (), new_X (), new_a () in
      let tyF = TyFun (tyX, tyY, tau, tau, a2) in
      let scm = make_scm [ tyX; tyY ] [ tau ] tyF in
      let t1, (tyT1, tyR1, tyS1, a1), tc, ac = recon (extend k scm ctx) t1 in
      let tc = (tyT1, tyR1) :: tc in
      let ac = AConTI (tyR1, tyS1, a1) :: ac in
      (fi, AnImpure, TmShift (a2, k, t1)), (tyX, tyY, tyS1, AnImpure), tc, ac
    (* reset t1 *)
    | TmReset t1 ->
      let tyX = new_X () in
      let t1, (tyT1, tyR1, tyS1, a1), tc, ac = recon ctx t1 in
      let tc = (tyT1, tyR1) :: tc in
      let ac = AConTI (tyR1, tyS1, a1) :: ac in
      (fi, AnPure, TmReset t1), (tyS1, tyX, tyX, AnPure), tc, ac
    (* succ t1 *)
    | TmSucc t1 ->
      let t1, (tyT1, tyR1, tyS1, a1), tc, ac = recon ctx t1 in
      let a = new_a () in
      let tc = (tyT1, TyNat) :: tc in
      let ac = AConLE (a1, a) :: AConTI (tyR1, tyS1, a1) :: ac in
      (fi, a, TmSucc t1), (TyNat, tyR1, tyS1, a), tc, ac
    (* pred t1 *)
    | TmPred t1 ->
      let t1, (tyT1, tyR1, tyS1, a1), tc, ac = recon ctx t1 in
      let a = new_a () in
      let tc = (tyT1, TyNat) :: tc in
      let ac = AConLE (a1, a) :: AConTI (tyR1, tyS1, a1) :: ac in
      (fi, a, TmPred t1), (TyNat, tyR1, tyS1, a), tc, ac
    (* iszero t1 *)
    | TmIsZero t1 ->
      let t1, (tyT1, tyR1, tyS1, a1), tc, ac = recon ctx t1 in
      let a = new_a () in
      let tc = (tyT1, TyNat) :: tc in
      let ac = AConLE (a1, a) :: AConTI (tyR1, tyS1, a1) :: ac in
      (fi, a, TmIsZero t1), (TyBool, tyR1, tyS1, a), tc, ac
    | TmCons (t1, t2) ->
      let t1, (tyT1, tyR1, tyS1, a1), tc1, ac1 = recon ctx t1 in
      let t2, (tyT2, tyR2, tyS2, a2), tc2, ac2 = recon ctx t2 in
      let a = new_a () in
      let tc = (tyT2, TyList tyT1) :: (tyS2, tyR1) :: List.append tc1 tc2 in
      let ac =
        List.fold_right
          (fun (a', tyR, tyS) ls -> AConLE (a', a) :: AConTI (tyR, tyS, a') :: ls)
          [ a1, tyR1, tyS1; a2, tyR2, tyS2 ]
          (List.concat [ ac1; ac2 ])
      in
      (fi, a, TmCons (t1, t2)), (tyT2, tyR2, tyS1, a), tc, ac
    | TmNil ->
      let tyX, tyY = new_X (), new_X () in
      (fi, AnPure, TmNil), (TyList tyX, tyY, tyY, AnPure), [], []
    | TmLMatch (t1, t2, hd, tl, t3) ->
      let t1, (tyT1, tyR1, tyS1, a1), tc1, ac1 = recon ctx t1 in
      let t2, (tyT2, tyR2, tyS2, a2), tc2, ac2 = recon ctx t2 in
      let tyX, a = new_X (), new_a () in
      let ctx = ctx |> extend hd (raw_scm tyX) |> extend tl (raw_scm (TyList tyX)) in
      let t3, (tyT3, tyR3, tyS3, a3), tc3, ac3 = recon ctx t3 in
      let tc =
        (tyT1, TyList tyX)
        :: (tyS2, tyR1)
        :: (tyS3, tyR1)
        :: (tyR2, tyR3)
        :: (tyT2, tyT3)
        :: List.concat [ tc1; tc2; tc3 ]
      in
      let ac =
        List.fold_right
          (fun (a', tyR, tyS) ls -> AConLE (a', a) :: AConTI (tyR, tyS, a') :: ls)
          [ a1, tyR1, tyS1; a2, tyR2, tyS2; a3, tyR3, tyS3 ]
          (List.concat [ ac1; ac2; ac3 ])
      in
      (fi, a, TmLMatch (t1, t2, hd, tl, t3)), (tyT2, tyR2, tyS1, a), tc, ac
  in
  fun t -> recon empty_tyctx (term2info t, AnNone, TmReset t)
;;

let unify_acons : type_subst -> annot_constr list -> annot_subst =
  (* let print_msg msg s cons =
       print_string msg;
       print_newline ();
       print_acons cons;
       print_asubst s;
       print_newline ()
     in *)
  let comp s x an =
    Dict.update
      x
      (function
        | Some an' when an' = an -> Some an
        | None -> Some an
        | _ -> error dummyinfo "unsolvable annot constraints")
      s
  in
  let pass0 : annot_constr list -> annot_constr list =
    let rec equal ty1 ty2 =
      match ty1, ty2 with
      | TyNat, TyNat | TyBool, TyBool -> true, []
      | TyId x, TyId y when x = y -> true, []
      | TyFun (t1, t2, t3, t4, a), TyFun (t1', t2', t3', t4', a') ->
        List.fold_left
          (fun (ty_eq, an_prs) (t1, t1') ->
            let eq, prs = equal t1 t1' in
            ty_eq && eq, List.append prs an_prs)
          (true, if a = a' then [] else [ a, a' ])
          [ t1, t1'; t2, t2'; t3, t3'; t4, t4' ]
      | TyList ty, TyList ty' -> equal ty ty'
      | _ -> false, []
    and unify = function
      | [] -> []
      | AConTI (t1, t2, a) :: rest ->
        let eq, prs = equal t1 t2 in
        if eq
        then
          List.fold_right (fun (a1, a2) ls -> AConAI (a1, a2, a) :: ls) prs (unify rest)
        else AConEQ (a, AnImpure) :: unify rest
      | con :: rest -> con :: unify rest
    in
    unify
  in
  let pass1 : annot_constr list -> annot_subst * annot_constr list =
    let rec unify reduced s = function
      | [] -> reduced, s, []
      | con :: rest ->
        (match con with
        (* a1 == a2 *)
        | AConEQ (AnPure, AnImpure) | AConEQ (AnImpure, AnPure) ->
          error dummyinfo "error purity constraints"
        | AConEQ (a1, a2) when a1 = a2 -> unify true s rest
        | AConEQ (AnId x, AnPure) | AConEQ (AnPure, AnId x) ->
          unify true (comp s x AnPure) rest
        | AConEQ (AnId x, AnImpure) | AConEQ (AnImpure, AnId x) ->
          unify true (comp s x AnImpure) rest
        (* a1 <= a2 *)
        | AConLE (AnImpure, AnPure) -> error dummyinfo "error purity constraints"
        | AConLE (a1, a2) when a1 = a2 -> unify true s rest
        | AConLE (AnPure, _) | AConLE (_, AnImpure) -> unify true s rest
        | AConLE (AnId x, AnPure) -> unify true (comp s x AnPure) rest
        | AConLE (AnImpure, AnId x) -> unify true (comp s x AnImpure) rest
        (* a1 != a2 => a == i *)
        | AConAI (a1, a2, AnPure) -> unify true s (AConEQ (a1, a2) :: rest)
        | AConAI (_, _, AnImpure) -> unify true s rest
        | AConAI (AnImpure, AnPure, a) | AConAI (AnPure, AnImpure, a) ->
          unify true s (AConEQ (a, AnImpure) :: rest)
        | _ ->
          let r, s, cs = unify reduced s rest in
          r, s, con :: cs)
    and loop s acons =
      let r, s, cs = unify false s acons in
      (* print_msg "pass1" s cs; *)
      if r then loop s (subst_acons s cs) else s, cs
    in
    loop Dict.empty
  in
  let pass2 : annot_subst * annot_constr list -> annot_subst =
    let rec unify reduced s = function
      | [] -> reduced, s, []
      | con :: rest ->
        (match con with
        (* a1 != a2 => a == i *)
        | AConAI (_, _, AnId x) -> unify true (comp s x AnImpure) rest
        (* a1 == a2 *)
        | AConEQ (AnPure, AnImpure) | AConEQ (AnImpure, AnPure) ->
          error dummyinfo "error purity constraints"
        | AConEQ (a1, a2) when a1 = a2 -> unify true s rest
        | AConEQ (AnId x, AnPure) | AConEQ (AnPure, AnId x) ->
          unify true (comp s x AnPure) rest
        | AConEQ (AnId x, AnImpure) | AConEQ (AnImpure, AnId x) ->
          unify true (comp s x AnImpure) rest
        (* a1 <= a2 *)
        | AConLE (AnImpure, AnPure) -> error dummyinfo "error purity constraints"
        | AConLE (a1, a2) when a1 = a2 -> unify true s rest
        | AConLE (AnPure, _) | AConLE (_, AnImpure) -> unify true s rest
        | AConLE (AnId x, AnPure) -> unify true (comp s x AnPure) rest
        | AConLE (AnImpure, AnId x) -> unify true (comp s x AnImpure) rest
        | _ ->
          let r, s, cs = unify reduced s rest in
          r, s, con :: cs)
    and loop s acons =
      let r, s, cs = unify false s acons in
      (* print_msg "pass2" s cs; *)
      if r then loop s (subst_acons s cs) else s
    in
    fun (s, acons) -> loop s acons
  in
  fun s acons ->
    acons |> List.map (acon_map (subst_ty s) ident) |> pass0 |> pass1 |> pass2
;;

let infer : term -> term * ty =
  let subst_an s =
    annot_map (fun x an ->
        match Dict.find_opt x s with
        | Some a -> a
        | None -> AnPure)
  in
  let apply s = term_map (subst_an s) (fun _ t -> t) in
  fun t ->
    let t, (ty, _, _, _), tcons, acons = recon t in
    let tss, ac = unify_tcons tcons in
    let ass = unify_acons tss (List.append ac acons) in
    apply ass t, subst_ty tss ty |> type_map (subst_an ass) (fun _ tyT -> tyT)
;;
