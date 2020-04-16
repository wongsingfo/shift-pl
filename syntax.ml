open Support.Error

type ty =
  | TyBool
  | TyNat
  | TyFun of ty * ty * ty * ty
  | TyId of string

type term = info * term'

and term' =
  | TmVar of string
  | TmFix of string * string * ty option * term
  | TmAbs of string * ty option * term
  | TmApp of term * term
  | TmLet of string * term * term
  | TmShift of string * term
  | TmReset of term
  | TmIf of term * term * term
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmNat of int
  | TmBool of bool

type purity =
  | Pure
  | Impure

type aterm = info * purity * aterm'

and aterm' =
  | ATVar of string
  | ATFix of purity * string * string * aterm
  | ATAbs of purity * string * aterm
  | ATApp of purity * aterm * aterm
  | ATLet of string * aterm * aterm
  | ATShift of purity * string * aterm
  | ATReset of aterm
  | ATIf of aterm * aterm * aterm
  | ATSucc of aterm
  | ATPred of aterm
  | ATIsZero of aterm
  | ATNat of int
  | ATBool of bool

let term2info (fi, _) = fi

let freshname =
  let counter = ref 0 in
  fun () ->
    let x = !counter in
    incr counter;
    "?X" ^ string_of_int x
;;

let type2string =
  let spf = Printf.sprintf in
  let rec top_type ty = fun_type ty
  and fun_type ty =
    match ty with
    | TyFun (ty1, ty2, _, _) -> spf "%s->%s" (atom_type ty1) (fun_type ty2)
    | _ -> atom_type ty
  and atom_type ty =
    match ty with
    | TyBool -> "Bool"
    | TyNat -> "Nat"
    | TyId x -> x
    | _ -> spf "(%s)" (top_type ty)
  in
  top_type
;;

let term2string =
  let spf = Printf.sprintf in
  let rec top_term t' =
    let _, t = t' in
    match t with
    | TmLet (x, t1, t2) -> spf "let %s = %s in %s" x (top_term t1) (top_term t2)
    | TmIf (t1, t2, t3) ->
      spf "if %s then %s else %s" (top_term t1) (top_term t2) (top_term t3)
    | TmShift (k, t1) -> spf "shift %s in %s" k (top_term t1)
    | TmReset t1 -> spf "reset %s" (top_term t1)
    | TmAbs (x, Some ty, t1) -> spf "lambda %s:%s. %s" x (type2string ty) (top_term t1)
    | TmAbs (x, None, t1) -> spf "lambda %s. %s" x (top_term t1)
    | TmFix (f, x, Some ty, t1) ->
      spf "fix %s.%s:%s. %s" f x (type2string ty) (top_term t1)
    | TmFix (f, x, None, t1) -> spf "fix %s.%s. %s" f x (top_term t1)
    | _ -> app_term t'
  and app_term t' =
    let _, t = t' in
    match t with
    | TmSucc t1 -> spf "succ %s" (atom_term t1)
    | TmPred t1 -> spf "pred %s" (atom_term t1)
    | TmIsZero t1 -> spf "iszero %s" (atom_term t1)
    | TmApp (t1, t2) -> spf "%s %s" (app_term t1) (atom_term t2)
    | _ -> atom_term t'
  and atom_term t' =
    let _, t = t' in
    match t with
    | TmVar x -> x
    | TmBool b -> string_of_bool b
    | TmNat n -> string_of_int n
    | _ -> spf "(%s)" (top_term t')
  in
  top_term
;;
