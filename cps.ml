open Syntax
open Support.Error

exception NoRuleApplies

(* for the ease of typing *)
type cps_term = 
  | Var of string
  | Fix of string * string * ty option * cps_term
  | Abs of string * ty option * cps_term
  | App of cps_term * cps_term
  | Let of string * cps_term * cps_term
  | Shift of string * cps_term
  | Reset of cps_term
  | If of cps_term * cps_term * cps_term
  | Succ of cps_term
  | Pred of cps_term
  | IsZero of cps_term
  | Nat of int
  | Bool of bool

let rec cps_term_to_term (t: cps_term) : term = (match t with
    | Var(s) -> dummyinfo, AnNone, 
        TmVar(s)
    | Fix(f, x, ty, t') -> dummyinfo, AnNone, 
        TmFix(AnNone, f, x, ty, cps_term_to_term t')
    | Abs(x, ty, t') -> dummyinfo, AnNone,
        TmAbs(AnNone, x, ty, cps_term_to_term t')
    | App(t1, t2) -> dummyinfo, AnNone,
        TmApp(AnNone, cps_term_to_term t1, cps_term_to_term t2)
    | Let(x, v, t') -> dummyinfo, AnNone,
        TmLet(x, cps_term_to_term v, cps_term_to_term t')
    | Shift(x, t') -> dummyinfo, AnNone,
        TmShift(AnNone, x, cps_term_to_term t')
    | Reset(t') -> dummyinfo, AnNone,
        TmReset(cps_term_to_term t')
    | If(c, v1, v2) -> dummyinfo, AnNone,
        TmIf(cps_term_to_term c, cps_term_to_term v1, cps_term_to_term v2)
    | Succ(t') -> dummyinfo, AnNone,
        TmSucc(cps_term_to_term t')
    | Pred(t') -> dummyinfo, AnNone,
        TmPred(cps_term_to_term t')
    | IsZero(t') -> dummyinfo, AnNone,
        TmIsZero(cps_term_to_term t')
    | Nat(v) -> dummyinfo, AnNone, TmNat(v)
    | Bool(v) -> dummyinfo, AnNone, TmBool(v)
) (* end of match *)

let new_k () : string = freshname "?k"

let cps t = t

let is_pure (t: term) : bool = (match t with
    | (_, AnPure, _) -> true
    | _ -> false)

let rec cps_pure (t: term) : cps_term = (match t with
    | (_, AnImpure, _) -> raise NoRuleApplies
    | (_, AnId(_), _) -> raise NoRuleApplies
    | (_, AnNone, _) -> raise NoRuleApplies
    | (_, _, TmVar v) -> Var v
    | (_, _, TmNat v) -> Nat v
    | (_, _, TmBool v) -> Bool v
    | (_, _, TmAbs(AnPure, _1, _2, e1)) when is_pure e1
    -> Abs(_1, _2, cps_pure e1)
    | (_, _, TmAbs(AnPure, _1, _2, e1)) when is_pure e1
    -> let k : string = new_k () in
        Abs(_1, _2,
            Abs(k, None, 
                App(Var(k), cps_pure e1)))
    | (_, _, TmAbs(AnPure, _1, _2, e1)) when not (is_pure e1)
    -> let k : string = new_k () in
        Abs(_1, _2,
            Abs(k, None, 
                cps_with_k e1 (fun v -> App(Var(k), v))))
    | _ -> raise NoRuleApplies)

and cps_with_k (t: term) (k: cps_term -> cps_term) : cps_term = (match t with 
    | _ -> raise NoRuleApplies)



