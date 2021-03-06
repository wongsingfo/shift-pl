open Support.Error

type annot =
  | AnPure
  | AnImpure
  | AnId of string
  | AnNone

type ty =
  | TyBool
  | TyNat
  (* TyFun(a, b, c, d) = a/c -> b/d = a -> b @cps[c, d] *)
  | TyFun of ty * ty * ty * ty * annot
  | TyId of string
  | TyList of ty

type term = info * annot * term'

and term' =
  | TmVar of string
  | TmFix of annot * string * string * ty option * term
  | TmAbs of annot * string * ty option * term
  | TmApp of annot * term * term
  | TmLet of string * term * term
  | TmShift of annot * string * term
  | TmReset of term
  | TmIf of term * term * term
  | TmCons of term * term
  (* lmatch t1 { case nil => t2 case hd :: tl => t3 } *)
  | TmLMatch of term * term * string * string * term
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmNat of int
  | TmBool of bool
  | TmNil

let term2info (fi, _, _) = fi

let freshname =
  let dict = Hashtbl.create 10 in
  fun prefix ->
    let no =
      try
        let i = Hashtbl.find dict prefix in
        Hashtbl.replace dict prefix (i + 1);
        i
      with
      | Not_found ->
        Hashtbl.add dict prefix 1;
        0
    in
    prefix ^ string_of_int no
;;

let annot2string = function
  | AnId x -> x
  | AnPure -> "p"
  | AnImpure -> "i"
  | AnNone -> ""
;;

let type2string_with_annot =
  let spf = Printf.sprintf in
  let rec go = function
    | TyBool -> "Bool"
    | TyNat -> "Nat"
    | TyId x -> x
    | TyFun (ty1, ty2, ty3, ty4, a) ->
      spf "(%s -> %s)@[%s, %s, %s]" (go ty1) (go ty2) (go ty3) (go ty4) (annot2string a)
    | TyList ty -> spf "List[%s]" (go ty)
  in
  go
;;

let type2string =
  let spf = Printf.sprintf in
  let rec top_type ty = fun_type ty
  and fun_type ty =
    match ty with
    | TyFun (ty1, ty2, ty3, ty4, a) -> spf "%s -> %s" (atom_type ty1) (fun_type ty2)
    | _ -> atom_type ty
  and atom_type ty =
    match ty with
    | TyBool -> "Bool"
    | TyNat -> "Nat"
    | TyId x -> x
    | TyList ty -> spf "List[%s]" (top_type ty)
    | _ -> spf "(%s)" (top_type ty)
  in
  top_type
;;

let term2string_with_annot =
  let spf = Printf.sprintf in
  let rec go (_, a, t) =
    let a = annot2string a in
    match t with
    | TmVar x -> spf "%s[%s]" x a
    | TmNat i -> spf "%s[%s]" (string_of_int i) a
    | TmBool b -> spf "%s[%s]" (string_of_bool b) a
    | TmAbs (a', x, _, t1) -> spf "(lambda[%s] %s. %s)[%s]" (annot2string a') x (go t1) a
    | TmFix (a', f, x, _, t1) ->
      spf "(fix[%s] %s. %s. %s)[%s]" (annot2string a') f x (go t1) a
    | TmApp (a', t1, t2) -> spf "(%s [%s] %s)[%s]" (go t1) (annot2string a') (go t2) a
    | TmLet (x, t1, t2) -> spf "(let %s = %s in %s)[%s]" x (go t1) (go t2) a
    | TmShift (a', k, t1) -> spf "(shift[%s] %s. %s)[%s]" (annot2string a') k (go t1) a
    | TmReset t1 -> spf "(reset %s)[%s]" (go t1) a
    | TmIf (t1, t2, t3) -> spf "(if %s then %s else %s)[%s]" (go t1) (go t2) (go t3) a
    | TmSucc t1 -> spf "(succ %s)[%s]" (go t1) a
    | TmPred t1 -> spf "(pred %s)[%s]" (go t1) a
    | TmIsZero t1 -> spf "(iszero %s)[%s]" (go t1) a
    | TmCons (t1, t2) -> spf "(cons %s %s)[%s]" (go t1) (go t2) a
    | TmLMatch (t1, t2, hd, tl, t3) ->
      spf
        "(lmatch %s { case nil => %s case %s :: %s => %s})[%s]"
        (go t1)
        (go t2)
        hd
        tl
        (go t3)
        a
    | TmNil -> spf "nil[%s]" a
  in
  go
;;

let term2string =
  let spf = Printf.sprintf in
  let rec top_term t' =
    let _, _, t = t' in
    match t with
    | TmLet (x, t1, t2) -> spf "let %s = %s in %s" x (top_term t1) (top_term t2)
    | TmIf (t1, t2, t3) ->
      spf "if %s then %s else %s" (top_term t1) (top_term t2) (top_term t3)
    | TmShift (_, k, t1) -> spf "shift %s in %s" k (top_term t1)
    | TmReset t1 -> spf "reset %s" (top_term t1)
    | TmAbs (_, x, Some ty, t1) -> spf "lambda %s:%s. %s" x (type2string ty) (top_term t1)
    | TmAbs (_, x, None, t1) -> spf "lambda %s. %s" x (top_term t1)
    | TmFix (_, f, x, Some ty, t1) ->
      spf "fix %s. %s:%s. %s" f x (type2string ty) (top_term t1)
    | TmFix (_, f, x, None, t1) -> spf "fix %s. %s. %s" f x (top_term t1)
    | TmLMatch (t1, t2, hd, tl, t3) ->
      spf
        "lmatch %s { case nil => %s case %s :: %s => %s }"
        (top_term t1)
        (top_term t2)
        hd
        tl
        (top_term t3)
    | _ -> app_term t'
  and app_term t' =
    (* if is_list t'
       then cons2string t'
       else ( *)
    let _, _, t = t' in
    match t with
    | TmApp (_, t1, t2) -> spf "%s %s" (app_term t1) (atom_term t2)
    | TmCons (t1, t2) -> spf "cons %s %s" (atom_term t1) (atom_term t2)
    | _ -> atom_term t'
  (* ) *)
  and atom_term t' =
    let _, _, t = t' in
    match t with
    | TmSucc t1 -> spf "succ %s" (atom_term t1)
    | TmPred t1 -> spf "pred %s" (atom_term t1)
    | TmIsZero t1 -> spf "iszero %s" (atom_term t1)
    | TmVar x -> x
    | TmBool b -> string_of_bool b
    | TmNat n -> string_of_int n
    | TmNil -> "[]"
    | _ -> spf "(%s)" (top_term t')
    (* and is_list = function
         | _, _, TmNil -> true
         | _, _, TmCons (_, tl) -> is_list tl
         | _ -> false
       and cons2slist = function
         | _, _, TmNil -> []
         | _, _, TmCons (hd, tl) -> top_term hd :: cons2slist tl
         | _ -> assert false
       and cons2string t = "[" ^ String.concat ", " (cons2slist t) ^ "]" *)
  in
  top_term
;;
