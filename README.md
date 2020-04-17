# 冲冲冲？

`make interface`可以将`parser.mly lexer.mll *.mli`编译为`*.cmi *.cmti`，方便merlin的分析

## Syntax

```ocaml
type annot =
  | AnPure
  | AnImpure
  | AnId of string

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
```