# shift-pl

## differences from fullrecon:

syntax.ml, syntax.mli (line 25)
```ocaml
type term =
  ...
  (* shift k in t *)
  | TmShift of info * string * term
  (* reset t *)
  | TmReset of info * term
```

parser.mly (line 38)
```ocaml
%token <Support.Error.info> SHIFT
%token <Support.Error.info> RESET
```

parser.mly (line 167)
```ocaml
Term:
  ...
  | SHIFT LCID IN Term
      { fun ctx -> TmShift($1, $2.v, $4 (addname ctx $2.v)) }
  | RESET Term 
      { fun ctx -> TmReset($1, $2 ctx) }
  ...
```

lexer.mll (line 27)
```ocaml
  ("shift", fun i -> Parser.SHIFT i);
  ("reset", fun i -> Parser.RESET i);
```