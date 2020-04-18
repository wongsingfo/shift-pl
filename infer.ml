open Syntax
open Support.Error
module Dict = Map.Make (String)

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
type type_scheme = string list * ty
type type_context = type_scheme Dict.t

(* fresh type variable *)
let fresh_tyv () = TyId (freshname "?X")

(* fresh annot variable *)
let fresh_anv () = AnId (freshname "?a")

(* empty type context *)
let empty_tyctx : type_context = Dict.empty

(* add a new binding to type context *)
let tyctx_add x scm ctx : type_context = Dict.update x (fun _ -> Some scm) ctx

(* find the type scheme based on a given variable *)
let tyctx_find fi x ctx : type_scheme =
  match Dict.find_opt x ctx with
  | Some scm -> scm
  | None -> error fi ("cannot find " ^ x ^ " in current type context")
;;

(* substitute the variable in a type *)
let rec subst_ty x tyS tyT : ty =
  match tyT with
  | TyId y when x = y -> tyS
  | TyFun (ty1, ty2, ty3, ty4, a) ->
    TyFun
      (subst_ty x tyS ty1, subst_ty x tyS ty2, subst_ty x tyS ty3, subst_ty x tyS ty4, a)
  | _ -> tyT
;;

(* substitute the variable in the type constraints *)
let subst_tycons x tyS tc : type_constr list =
  List.map (fun (tyT1, tyT2) -> subst_ty x tyS tyT1, subst_ty x tyS tyT2) tc
;;

(* substitute the variable in an annot *)
let rec subst_an x s a : annot =
  match a with
  | AnId y when x = y -> s
  | _ -> a
;;

(* substitute the variable in the annot constraints *)
let subst_ancons x s ac : annot_constr list =
  List.map
    (function
      | AConLE (a1, a2) -> AConLE (subst_an x s a1, subst_an x s a2)
      | AConTI (t1, t2, a) -> AConTI (t1, t2, subst_an x s a)
      | AConAI (a1, a2, a3) -> AConAI (subst_an x s a1, subst_an x s a2, subst_an x s a3)
      | AConEQ (a1, a2) -> AConEQ (subst_an x s a1, subst_an x s a2))
    ac
;;

(* apply the substitution in the type *)
let rec apply_tysubst s tyT : ty =
  match tyT with
  | TyId x ->
    (match Dict.find_opt x s with
    | Some tyS -> tyS
    | None -> tyT)
  | TyFun (ty1, ty2, ty3, ty4, a) ->
    TyFun
      ( apply_tysubst s ty1
      , apply_tysubst s ty2
      , apply_tysubst s ty3
      , apply_tysubst s ty4
      , a )
  | _ -> tyT
;;

(* compose substitution s with [x -> tyT] *)
let compose_tysubst s x tyT : type_subst = Dict.add x (apply_tysubst s tyT) s
let compose_ansubst s x a : annot_subst = Dict.add x a s

let apply_ansubst : annot_subst -> term -> term =
 fun s ->
  let rec app a : annot =
    match a with
    | AnId x ->
      (match Dict.find_opt x s with
      | Some a -> a
      | None -> AnPure)
    | _ -> AnPure
  in
  let rec apply (fi, a, t) =
    ( fi
    , app a
    , match t with
      | TmAbs (a', x, _, t1) -> TmAbs (app a', x, None, apply t1)
      | TmApp (a', t1, t2) -> TmApp (app a', apply t1, apply t2)
      | _ -> t )
  in
  apply
;;

(* instantiate the type scheme *)
let inst (xs, ty) : ty = List.fold_left (fun ty x -> subst_ty x (fresh_tyv ()) ty) ty xs

(* reconstruct the type, and annotate the term *)
let rec recon ctx t' : term * typing * type_constr list * annot_constr list =
  let fi, _, t = t' in
  match t with
  (* x *)
  | TmVar x ->
    let scm = tyctx_find fi x ctx in
    let tyI = inst scm in
    let tyX = fresh_tyv () in
    (fi, AnPure, t), (tyI, tyX, tyX, AnPure), [], []
  (* natural *)
  | TmNat _ ->
    let tyX = fresh_tyv () in
    (fi, AnPure, t), (TyNat, tyX, tyX, AnPure), [], []
  (* boolean *)
  | TmBool _ ->
    let tyX = fresh_tyv () in
    (fi, AnPure, t), (TyBool, tyX, tyX, AnPure), [], []
  (* lambda x: T?. t2 *)
  | TmAbs (_, x, maybeT, t1) ->
    let tyX =
      match maybeT with
      | Some tyT -> tyT
      | None -> fresh_tyv ()
    in
    let tyY, a2 = fresh_tyv (), fresh_anv () in
    let t1, (tyT1, tyR1, tyS1, a1), tc, ac = recon (tyctx_add x ([], tyX) ctx) t1 in
    let ac' = AConLE (a1, a2) :: AConTI (tyR1, tyS1, a1) :: ac in
    let ty = TyFun (tyX, tyT1, tyR1, tyS1, a2) in
    (fi, AnPure, TmAbs (a2, x, None, t1)), (ty, tyY, tyY, AnPure), tc, ac'
  (* t1 @ t2 *)
  | TmApp (_, t1, t2) ->
    let t1, (tyT1, tyR1, tyS1, a1), tc1, ac1 = recon ctx t1 in
    let t2, (tyT2, tyR2, tyS2, a2), tc2, ac2 = recon ctx t2 in
    let tyX, tyY, a3, a = fresh_tyv (), fresh_tyv (), fresh_anv (), fresh_anv () in
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
  | _ -> error fi ("currently not supporting the term: " ^ term2string t')
;;

(* unify the type constraints to get the type substitution *)
let unify_tycons : type_constr list -> type_subst =
  let rec occur x tyT =
    match tyT with
    | TyId y -> x = y
    | TyFun (t1, t2, t3, t4, _) -> occur x t1 || occur x t2 || occur x t3 || occur x t4
    | _ -> false
  in
  let rec unify constr : type_subst =
    match constr with
    | [] -> Dict.empty
    | (ty1, ty2) :: rest when ty1 = ty2 -> unify rest
    | (TyId x, tyT) :: rest ->
      if occur x tyT
      then error dummyinfo "recursive typing"
      else compose_tysubst (unify (subst_tycons x tyT rest)) x tyT
    | (tyT, TyId x) :: rest ->
      if occur x tyT
      then error dummyinfo "recursive typing"
      else compose_tysubst (unify (subst_tycons x tyT rest)) x tyT
    | (TyFun (t1, t2, t3, t4, _), TyFun (t1', t2', t3', t4', _)) :: rest ->
      unify ((t1, t1') :: (t2, t2') :: (t3, t3') :: (t4, t4') :: rest)
    | _ -> error dummyinfo "unsolvable constraints"
  in
  unify
;;

let unify_ancons : type_subst -> annot_constr list -> annot_subst =
  let rec apply_tyc s constr =
    match constr with
    | [] -> []
    | AConTI (t1, t2, a) :: rest ->
      AConTI (apply_tysubst s t1, apply_tysubst s t2, a) :: apply_tyc s rest
    | cons :: rest -> cons :: apply_tyc s rest
  in
  let rec app_ans s a =
    match a with
    | AnId x ->
      (match Dict.find_opt x s with
      | Some a -> a
      | None -> a)
    | _ -> a
  and apply_ans s ancons =
    match ancons with
    | AConLE (a1, a2) -> AConLE (app_ans s a1, app_ans s a2)
    | AConEQ (a1, a2) -> AConEQ (app_ans s a1, app_ans s a2)
    | AConTI (t1, t2, a) -> AConTI (t1, t2, app_ans s a)
    | AConAI (a1, a2, a) -> AConAI (app_ans s a1, app_ans s a2, app_ans s a)
  in
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
    | _ -> false, []
  and unify0 constr : annot_constr list =
    match constr with
    | [] -> []
    | AConTI (t1, t2, a) :: rest ->
      let eq, prs = equal t1 t2 in
      if eq
      then List.fold_right (fun (a1, a2) ls -> AConAI (a1, a2, a) :: ls) prs (unify0 rest)
      else AConEQ (a, AnImpure) :: unify0 rest
    | cons :: rest -> cons :: unify0 rest
  in
  let rec unify1 reduced constr subst : bool * annot_constr list * annot_subst =
    match constr with
    | [] -> reduced, constr, subst
    | AConEQ (AnId x, AnPure) :: rest ->
      unify1 true (subst_ancons x AnPure rest) (compose_ansubst subst x AnPure)
    | AConEQ (AnId x, AnImpure) :: rest ->
      unify1 true (subst_ancons x AnImpure rest) (compose_ansubst subst x AnPure)
    | AConLE (AnPure, _) :: rest -> unify1 true rest subst
    | AConLE (_, AnImpure) :: rest -> unify1 true rest subst
    | AConLE (AnId x, AnPure) :: rest ->
      unify1 true (subst_ancons x AnPure rest) (compose_ansubst subst x AnPure)
    | AConLE (AnImpure, AnId x) :: rest ->
      unify1 true (subst_ancons x AnImpure rest) (compose_ansubst subst x AnImpure)
    | AConAI (a1, a2, AnPure) :: rest ->
      unify1 true (AConLE (a1, a2) :: AConLE (a2, a1) :: rest) subst
    | AConAI (_, _, AnImpure) :: rest -> unify1 true rest subst
    | AConAI (AnPure, AnPure, _) :: rest -> unify1 true rest subst
    | AConAI (AnImpure, AnImpure, _) :: rest -> unify1 true rest subst
    | AConAI (AnImpure, AnPure, AnId x) :: rest ->
      unify1 true (subst_ancons x AnImpure rest) (compose_ansubst subst x AnImpure)
    | AConAI (AnPure, AnImpure, AnId x) :: rest ->
      unify1 true (subst_ancons x AnImpure rest) (compose_ansubst subst x AnImpure)
    | AConAI (AnPure, a2, a) :: rest -> unify1 true (AConAI (a2, AnPure, a) :: rest) subst
    | AConAI (AnImpure, a2, a) :: rest ->
      unify1 true (AConAI (a2, AnImpure, a) :: rest) subst
    | cons :: rest ->
      let r, c, s = unify1 false rest subst in
      r, apply_ans s cons :: c, s
  and loop1 constr subst : annot_constr list * annot_subst =
    let r, c, s = unify1 false constr subst in
    if r then loop1 c s else c, s
  in
  let rec unify2 reduced constr subst : bool * annot_constr list * annot_subst =
    match constr with
    | [] -> reduced, constr, subst
    | AConAI (_, _, AnId x) :: rest ->
      unify2 true (subst_ancons x AnImpure rest) (compose_ansubst subst x AnImpure)
    | cons :: rest ->
      let r, c, s = unify2 false rest subst in
      r, apply_ans s cons :: c, s
  and loop2 constr subst : annot_subst =
    let r, c, s = unify2 false constr subst in
    if r then loop2 c s else s
  in
  fun subst constr ->
    let c, s = loop1 (unify0 (apply_tyc subst constr)) Dict.empty in
    loop2 c s
;;

let infer t =
  let t, (ty, _, _, _), tc, ac = recon empty_tyctx t in
  let tysubst = unify_tycons tc in
  apply_ansubst (unify_ancons tysubst ac) t, apply_tysubst tysubst ty
;;
