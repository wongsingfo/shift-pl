/*  
 *  Yacc grammar for the parser.  The files parser.mli and parser.ml
 *  are generated automatically from parser.mly.
 */

%{
open Support.Error
open Support.Pervasive
open Syntax

let annot () = AnId (freshname "?a")
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
;

fun_type:
  | atom_type ARROW fun_type 
    { TyFun ($1, $3, TyId (freshname "?X"), TyId (freshname "?X"), annot ()) }
  | atom_type 
    { $1 }
;

top_term:
  | top_term_
    { let fi, t = $1 in fi, annot (), t }
  | app_term
    { $1 }
;

app_term:
  | app_term_
    { let fi, t = $1 in fi, annot (), t }
  | atom_term
    { $1 }
;

atom_term:
  | atom_term_
    { let fi, t = $1 in fi, annot (), t }
  | LPAREN top_term RPAREN  
    { $2 } 
;

top_term_:
  | LET LCID EQ top_term IN top_term
    { $1, TmLet($2.v, $4, $6) }
  | LET USCORE EQ top_term IN top_term
    { $1, TmLet("_", $4, $6) }
  | IF top_term THEN top_term ELSE top_term
    { $1, TmIf($2, $4, $6) }
  | SHIFT LCID IN top_term
    { $1, TmShift(annot (), $2.v, $4) }
  | RESET top_term 
    { $1, TmReset($2) }
  | LAMBDA LCID DOT top_term 
    { $1, TmAbs(annot (), $2.v, None, $4) }
  | LAMBDA LCID COLON top_type DOT top_term 
    { $1, TmAbs(annot (), $2.v, Some $4, $6) }
  | LAMBDA USCORE COLON top_type DOT top_term 
    { $1, TmAbs(annot (), "_", Some $4, $6) }
  | FIX LCID DOT LCID DOT top_term
    { $1, TmFix(annot (), $2.v, $4.v, None, $6) }
  | FIX LCID DOT LCID COLON top_type DOT top_term
    { $1, TmFix(annot (), $2.v, $4.v, Some $6, $8) }
;

app_term_:
  | SUCC atom_term
    { $1, TmSucc($2) }
  | PRED atom_term
    { $1, TmPred($2) }
  | ISZERO atom_term
    { $1, TmIsZero($2) }
  | app_term atom_term
    { term2info $1, TmApp(annot (), $1, $2) }
;

/* Atomic terms are ones that never require extra parentheses */
atom_term_:
  | LCID 
    { $1.i, TmVar($1.v) }
  | TRUE
    { $1, TmBool(true) }
  | FALSE
    { $1, TmBool(false) }
  | INTV
    { $1.i, TmNat($1.v) }
;