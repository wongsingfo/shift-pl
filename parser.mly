/*  
 *  Yacc grammar for the parser.  The files parser.mli and parser.ml
 *  are generated automatically from parser.mly.
 */

%{
open Support.Error
open Support.Pervasive
open Syntax
%}

/* ---------------------------------------------------------------------- */
/* Preliminaries */

/* We first list all the tokens mentioned in the parsing rules
   below.  The names of the tokens are common to the parser and the
   generated lexical analyzer.  Each token is annotated with the type
   of data that it carries; normally, this is just file information
   (which is used by the parser to annotate the abstract syntax trees
   that it constructs), but sometimes -- in the case of identifiers and
   constant values -- more information is provided.
 */

/* Keyword tokens */
%token <Support.Error.info> LET
%token <Support.Error.info> IN
%token <Support.Error.info> IF
%token <Support.Error.info> THEN
%token <Support.Error.info> ELSE
%token <Support.Error.info> TRUE
%token <Support.Error.info> FALSE
%token <Support.Error.info> BOOL
%token <Support.Error.info> SUCC
%token <Support.Error.info> PRED
%token <Support.Error.info> ISZERO
%token <Support.Error.info> NAT
%token <Support.Error.info> LAMBDA
%token <Support.Error.info> SHIFT
%token <Support.Error.info> RESET
%token <Support.Error.info> FIX
%token <Support.Error.info> CONS
%token <Support.Error.info> LMATCH
%token <Support.Error.info> CASE
%token <Support.Error.info> NIL
%token <Support.Error.info> LIST

/* Identifier and constant value tokens */
%token <string Support.Error.withinfo> UCID  /* uppercase-initial */
%token <string Support.Error.withinfo> LCID  /* lowercase/symbolic-initial */
%token <int Support.Error.withinfo> INTV
%token <float Support.Error.withinfo> FLOATV
%token <string Support.Error.withinfo> STRINGV

/* Symbolic tokens */
%token <Support.Error.info> APOSTROPHE
%token <Support.Error.info> DQUOTE
%token <Support.Error.info> ARROW
%token <Support.Error.info> BANG
%token <Support.Error.info> BARGT
%token <Support.Error.info> BARRCURLY
%token <Support.Error.info> BARRSQUARE
%token <Support.Error.info> COLON
%token <Support.Error.info> COLONCOLON
%token <Support.Error.info> COLONEQ
%token <Support.Error.info> COLONHASH
%token <Support.Error.info> COMMA
%token <Support.Error.info> DARROW
%token <Support.Error.info> DDARROW
%token <Support.Error.info> DOT
%token <Support.Error.info> EOF
%token <Support.Error.info> EQ
%token <Support.Error.info> EQEQ
%token <Support.Error.info> EXISTS
%token <Support.Error.info> GT
%token <Support.Error.info> HASH
%token <Support.Error.info> LCURLY
%token <Support.Error.info> LCURLYBAR
%token <Support.Error.info> LEFTARROW
%token <Support.Error.info> LPAREN
%token <Support.Error.info> LSQUARE
%token <Support.Error.info> LSQUAREBAR
%token <Support.Error.info> LT
%token <Support.Error.info> RCURLY
%token <Support.Error.info> RPAREN
%token <Support.Error.info> RSQUARE
%token <Support.Error.info> SEMI
%token <Support.Error.info> SLASH
%token <Support.Error.info> STAR
%token <Support.Error.info> TRIANGLE
%token <Support.Error.info> USCORE
%token <Support.Error.info> VBAR

/* ---------------------------------------------------------------------- */
/* The starting production of the generated parser is the syntactic class
   toplevel.  The type that is returned when a toplevel is recognized is
     Syntax.context -> (Syntax.command list * Syntax.context) 
   that is, the parser returns to the user program a function that,
   when given a naming context, returns a fully parsed list of
   Syntax.commands and the new naming context that results when
   all the names bound in these commands are defined.

   All of the syntactic productions in the parser follow the same pattern:
   they take a context as argument and return a fully parsed abstract
   syntax tree (and, if they involve any constructs that bind variables
   in some following phrase, a new context).
   
*/

%start top_level
%type <Syntax.term> top_level
%%

/* ---------------------------------------------------------------------- */
/* Main body of the parser definition */

/* The top level of a file is a sequence of commands, each terminated
   by a semicolon. */
top_level:
  | top_term SEMI { $1 }
;

/* All type expressions */
top_type: 
  | fun_type { $1 }
;

/* Atomic types are those that never need extra parentheses */
atom_type:
  | LPAREN top_type RPAREN { $2 } 
  | BOOL { TyBool }
  | NAT { TyNat }
  | UCID { TyId($1.v) }
  | LIST LSQUARE top_type RSQUARE { TyList $3 }
;

fun_type:
  | atom_type ARROW fun_type 
    { TyFun ($1, $3, TyId (freshname "?X"), TyId (freshname "?X"), AnNone) }
  | atom_type 
    { $1 }
;

id_ty_pair:
  | LCID 
    { $1.v, None }
  | LCID COLON top_type
    { $1.v, Some $3 }
  | USCORE
    { "_", None }
  | USCORE COLON top_type
    { "_", Some $3 }
;

id_ty_pairs_:
  | id_ty_pair id_ty_pairs_
    { $1 :: $2 }
  | 
    { [] }
;

id_ty_pairs:
  | id_ty_pair id_ty_pairs_ 
    { $1 :: $2 }
;

top_term:
  | LET LCID EQ top_term IN top_term
    { $1, AnNone, TmLet($2.v, $4, $6) }
  | LET USCORE EQ top_term IN top_term
    { $1, AnNone, TmLet("_", $4, $6) }
  | IF top_term THEN top_term ELSE top_term
    { $1, AnNone, TmIf($2, $4, $6) }
  | SHIFT LCID IN top_term
    { $1, AnNone, TmShift(AnNone, $2.v, $4) }
  | RESET top_term 
    { $1, AnNone, TmReset($2) }
  | LMATCH top_term LCURLY CASE NIL DARROW top_term CASE LCID COLONCOLON LCID DARROW top_term RCURLY
  /*  1     2         3      4   5    6       7      8     9      10       11   12      13       14 */
    { $1, AnNone, TmLMatch($2, $7, $9.v, $11.v, $13) }
  | LAMBDA id_ty_pairs DOT top_term 
    { List.fold_right (fun (id, ty) t -> $1, AnNone, TmAbs(AnNone, id, ty, t)) $2 $4 }
  | FIX LCID DOT id_ty_pair id_ty_pairs_ DOT top_term
    { let id, ty = $4 in $1, AnNone, TmFix(AnNone, $2.v, id, ty, List.fold_right (fun (id, ty) t -> $1, AnNone, TmAbs(AnNone, id, ty, t)) $5 $7) }
  | app_term 
    { $1 }
;

app_term:
  | SUCC atom_term
    { $1, AnNone, TmSucc($2) }
  | PRED atom_term
    { $1, AnNone, TmPred($2) }
  | ISZERO atom_term
    { $1, AnNone, TmIsZero($2) }
  | CONS atom_term atom_term 
    { $1, AnNone, TmCons($2, $3) }
  | app_term atom_term
    { term2info $1, AnNone, TmApp(AnNone, $1, $2) }
  | atom_term
    { $1 }
;

/* Atomic terms are ones that never require extra parentheses */
atom_term:
  | LCID 
    { $1.i, AnNone, TmVar($1.v) }
  | TRUE
    { $1, AnNone, TmBool(true) }
  | FALSE
    { $1, AnNone, TmBool(false) }
  | NIL 
    { $1, AnNone, TmNil }
  | LSQUARE RSQUARE
    { $1, AnNone, TmNil }
  | LSQUARE top_term term_list RSQUARE
    { $1, AnNone, TmCons ($2, $3) }
  | INTV
    { $1.i, AnNone, TmNat($1.v) }
  | LPAREN top_term RPAREN
    { $2 }
;

term_list:
  | 
    { dummyinfo, AnNone, TmNil }
  | COMMA top_term term_list
    { $1, AnNone, TmCons ($2, $3) }
;
