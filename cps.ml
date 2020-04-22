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
let new_v () : string = freshname "?v"

let is_pure (t: term) : bool = (match t with
    | (_, AnPure, _) -> true
    | _ -> false)

(* see Figure 8. *)
let rec cps_pure (t: term) : cps_term = (match t with
    | (_, AnImpure, _) -> raise NoRuleApplies
    | (_, AnId(_), _) -> raise NoRuleApplies
    | (_, AnNone, _) -> raise NoRuleApplies
    (* constant *)
    | (_, _, TmNat v) -> Nat v
    | (_, _, TmBool v) -> Bool v
    (* variable *)
    | (_, _, TmVar v) -> Var v

    (* abstraction #1 *)
    | (_, _, TmAbs(AnPure, _1, _2, e1)) when is_pure e1
    -> Abs(_1, _2, cps_pure e1)
    (* abstraction #2 *)
    | (_, _, TmAbs(AnImpure, _1, _2, e1)) when is_pure e1
    -> let k : string = new_k () in
        Abs(_1, _2,
            Abs(k, None, 
                App(Var(k), cps_pure e1)))
    (* abstraction #3 *)
    | (_, _, TmAbs(AnImpure, _1, _2, e1)) when not @@ is_pure e1
    -> let k : string = new_k () in
        Abs(_1, _2,
            Abs(k, None, 
                cps_with_k e1 (fun v -> App(Var(k), v))))

    (* Fix #1 *)
    | (_, _, TmFix(AnPure, f, x, ty, e1))
    -> Fix(f, x, ty, cps_pure e1)
    (* Fix #2 *)
    | (_, _, TmFix(AnImpure, f, x, ty, e1)) when is_pure e1
    -> let k : string = new_k () in
        Abs(x, ty, Abs(k, None, App(Var(k), 
          App(Fix(f, x, ty, cps_pure e1), Var(x)))))
    (* Fix #3 *)
    | (_, _, TmFix(AnImpure, f, x, ty, e1)) when not @@ is_pure e1
    -> let k : string = new_k () in
        Fix(f, x, ty, 
          Abs(k, None,
            cps_with_k e1 (fun v -> App(Var(k), v))))

    (* Application *)
    | (_, _, TmApp(AnPure, e1, e2))
    -> App(cps_pure e1, cps_pure e2)

    (* Reset #1 *)
    | (_, _, TmReset(e1)) when is_pure e1
    -> cps_pure e1
    (* Reset #2 *)
    | (_, _, TmReset(e1)) when not @@ is_pure e1
    -> cps_with_k e1 @@ fun v -> v

    (* let *)
    | (_, _, TmLet(x, e1, e2)) when is_pure e1 && is_pure e2
    -> Let(x, cps_pure e1, cps_pure e2)

    (* if *)
    | (_, _, TmIf(e1, e2, e3)) when is_pure e1 && is_pure e2 && is_pure e3
    -> If(cps_pure e1, cps_pure e2, cps_pure e3)

    (* Primitive functions *)
    | (_, _, TmSucc(e1)) -> Succ(cps_pure e1)
    | (_, _, TmPred(e1)) -> Pred(cps_pure e1)
    | (_, _, TmIsZero(e1)) -> IsZero(cps_pure e1)

    | _ -> raise NoRuleApplies)


and cps_with_k (t: term) (k: cps_term -> cps_term) : cps_term = (match t with 
    | (_, AnPure, _) -> k @@ cps_pure t

    (* Application *)
    | (_, _, TmApp(AnPure, e1, e2)) 
    -> cps_with_k e1 @@ fun v1 -> 
        cps_with_k e2 @@ fun v2 ->
          k @@ App(v1, v2)
    | (_, _, TmApp(AnImpure, e1, e2)) 
    -> cps_with_k e1 @@ fun v1 -> 
        cps_with_k e2 @@ fun v2 ->
          let v : string = new_v () in
            App(App(v1, v2), Abs(v, None, k @@ Var v))

    (* Shift *)
    | (_, _, TmShift(AnPure, x, e1))
    -> let v : string = new_v () in
        Let(x, Abs(v, None, k @@ Var v), 
          cps_with_k e1 @@ fun v1 -> v1)
    | (_, _, TmShift(AnImpure, x, e1))
    -> let v : string = new_v () and k' : string = new_k () in
        Let(x, 
            Abs(v, None, 
                Abs(k', None, k @@ Var v)),
            cps_with_k e1 @@ fun v1 -> v1)

    (* let *)
    | (_, _, TmLet(x, v1, e2)) when is_pure v1
    -> Let(x, cps_pure v1, cps_with_k e2 k)
    | (_, _, TmLet(x, v1, e2)) when not @@ is_pure v1
    -> raise NoRuleApplies

    (* if *)
    | (_, _, TmIf(e1, e2, e3)) 
    -> cps_with_k e1 @@ fun v1 ->
      let v' : string = new_v () and k' : string = new_k () in
        Let(k', Abs(v', None, k @@ Var v'),
          If(v1, 
             cps_with_k e2 (fun v -> App(Var k', v)),
             cps_with_k e3 (fun v -> App(Var k', v))))

    | _ -> raise NoRuleApplies)

let cps (t: term) : term = 
  let (t': cps_term) = 
    if is_pure t then cps_pure(t)
    else cps_with_k t (fun x -> x)
  in cps_term_to_term t'

