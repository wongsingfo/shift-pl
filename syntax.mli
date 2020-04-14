open Support.Error

type ty =
  | TyBool
  | TyNat
  | TyFun of
      { tm : ty * ty
      ; cm : ty * ty
      }
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

val term2string : term -> string
val type2string : ty -> string
val freshname : unit -> string
val term2info : term -> info
