open Support.Error

type annot =
  | AnPure
  | AnImpure
  | AnId of string

type ty =
  | TyBool
  | TyNat
  (* TyFun(a, b, c, d) = a/c -> b/d = a -> b @cps[c, d] *)
  | TyFun of ty * ty * ty * ty * annot
  | TyId of string

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
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmNat of int
  | TmBool of bool

val term2string : term -> string
val type2string : ty -> string
val freshname : string -> string
val term2info : term -> info
