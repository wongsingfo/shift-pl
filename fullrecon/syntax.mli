(* module Syntax: syntax trees and associated support functions *)

open Support.Pervasive
open Support.Error

(* Data type definitions *)
type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyId of string

type term =
    TmVar of info * int * int
  | TmLet of info * string * term * term
  | TmTrue of info
  | TmFalse of info
  | TmIf of info * term * term * term
  | TmZero of info
  | TmSucc of info * term
  | TmPred of info * term
  | TmIsZero of info * term
  | TmAbs of info * string * ty option * term
  | TmApp of info * term * term
  | TmFix of info * string * string * ty option * term
  (* List Manipulation *)
  | TmLMatch of info * term * term * string * string * term
  | TmNil of info
  | TmCons of info * term * term

type binding =
    NameBind 
  | VarBind of ty

type command =
  | Eval of info * term
  | Bind of info * string * binding

(* Contexts *)
type context
val emptycontext : context 
val ctxlength : context -> int
val addbinding : context -> string -> binding -> context
val addname: context -> string -> context
val index2name : info -> context -> int -> string
val getbinding : info -> context -> int -> binding
val name2index : info -> context -> string -> int
val isnamebound : context -> string -> bool
val getTypeFromContext : info -> context -> int -> ty

(* Shifting and substitution *)
val termShift: int -> term -> term
val termSubstTop: term -> term -> term

(* Printing *)
val printtm: context -> term -> unit
val printtm_ATerm: bool -> context -> term -> unit
val printty : ty -> unit
val printty_Type : bool -> ty -> unit
val prbinding : context -> binding -> unit

(* Misc *)
val tmInfo: term -> info

