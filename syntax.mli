open Support.Error

type annot =
  | AnPure
  | AnImpure
  (* purity variable, for solving constraints *)
  | AnId of string
  (* after CPS, we don't care about the purity any more *)
  | AnNone

type ty =
  | TyBool
  | TyNat
  (* TyFun(T1, T2, T3, T4, a) = T1 -> T2 @cps[T3, T4, a] *)
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
val term2string_with_annot : term -> string
val type2string : ty -> string
val type2string_with_annot : ty -> string
val annot2string : annot -> string
val freshname : string -> string
val term2info : term -> info
