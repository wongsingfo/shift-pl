open Syntax

exception NoRuleApplies

type cps_term = 
  | Var of string
  | Fix of string * string * ty option * cps_term
  | Abs of string * ty option * cps_term
  | App of cps_term * cps_term
  | Let of string * cps_term * cps_term
  | Shift of annot * string * cps_term
  | Reset of cps_term
  | If of cps_term * cps_term * cps_term
  | Succ of cps_term
  | Pred of cps_term
  | IsZero of cps_term
  | Nat of int
  | Bool of bool

let new_k () : string = freshname "?k"

let cps t = t

let is_pure (t: term) : bool = (match t with
    | (_, AnPure, _) -> true
    | _ -> false) 

let rec cps_pure (t: term) : cps_term = (match t with
    | (i, AnPure, TmVar v) -> Var v
    | (i, AnPure, TmNat v) -> Nat v
    | (i, AnPure, TmBool v) -> Bool v
    | (i, AnPure, TmAbs(AnPure, _1, _2, e1)) when is_pure e1
    -> Abs(_1, _2, cps_pure e1)
    | (i, AnImpure, TmAbs(AnPure, _1, _2, e1)) when is_pure e1
    -> let k : string = new_k () in
        Abs(_1, _2,
            Abs(k, None, 
                App(Var(k), cps_pure e1)))
    | (i, AnImpure, TmAbs(AnPure, _1, _2, e1)) when not (is_pure e1)
    -> let k : string = new_k () in
        Abs(_1, _2,
            Abs(k, None, 
                cps_with_k e1 (fun v -> App(Var(k), v))))
    | _ -> raise NoRuleApplies)

and cps_with_k (t: term) (k: cps_term -> cps_term) : cps_term = (match t with 
    | _ -> raise NoRuleApplies)



