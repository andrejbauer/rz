
%{
  (* header *)
  open Syntax

  let parse_error _ =
    raise (Message.Parse (Message.loc_here 1, "parse error"))

  exception Impossible

  let foldTheoryFunctor bnd bdy = List.fold_right (fun bnd thr -> TheoryFunctor (bnd, thr)) bnd bdy

  let makeTermVar strng fxty = Var(None, N(strng, fxty))
  let makeTermPath mdl strng fxty = Var(Some mdl, N(strng, fxty))

  (** XXX Could we ever have infix sets ? *)
  let makeSetVar stnm  = Set_name (None, stnm)
  let makeSetPath mdl strng = Set_name (Some mdl, strng)

  let rec makeLambda lst st =
    match lst with
	[] -> st
      | bnd :: lst' -> Lambda (bnd, makeLambda lst' st)

  let rec makeSetLambda lst st =
    match lst with
	[] -> st
      | bnd :: lst' -> SetLambda (bnd, makeSetLambda lst' st)
%}

/* Tokens */

%token AND
%token ANDSYMBOL
%token ARROW
%token AXIOM
%token BAR
%token BACKQUOTE
%token BEGIN
%token BOOL
%token COLON
%token COMMA
%token <string> COMMENT 
%token CONSTANT
%token COROLLARY
%token DOUBLEARROW
%token END
%token EOF
%token EQUAL
%token EQUIV
%token EXISTS
%token FALSE
%token FORALL
%token FUN
%token HASH
%token IFF
%token IFFSYMBOL
%token IMPLICIT
%token IN
%token <string> INFIXOP0
%token <string> INFIXOP1
%token <string> INFIXOP2
%token <string> INFIXOP3
%token <string> INFIXOP4
%token <int> PROJECT
%token <string> LABEL
%token LBRACE
%token LBRACK
%token LEMMA
%token LET
%token LPAREN
%token MATCH
%token MODEL
%token <string> NAME
%token <string> TNAME
%token NOT
%token OR
%token ORSYMBOL
%token PERCENT
%token PERIOD
%token PLUS
%token PREDICATE
%token <string> PREFIXOP
%token PROP
%token PROPOSITION
%token RBRACE
%token RBRACK
%token RELATION
%token RPAREN
%token RZ
%token SET
%token SUBIN
%token SUBOUT
%token STABLE
%token STABLEPROP
%token STAR
%token STRUCTURE
%token THE
%token THEOREM
%token THEORY
%token THY
%token TRUE
%token UNIQUE
%token UNIT
%token WITH

/* Precedence and associativity */

%nonassoc AXIOM CONSTANT CORROLARY LEMMA PREDICATE PROPOSITION RELATION SET STABLE THEOREM

/* set forming symbols */

%right BAR
%right ARROW

/* term forming symbols (and also a few set forming) */

%nonassoc LET IN
%nonassoc PERIOD
%nonassoc IFF
%right IMPLY
%left OR
%left AND

%nonassoc EQUAL 
%nonassoc SUBIN SUBOUT
%right    COMMA
%left     INFIXOP0
%right    INFIXOP1
%left     INFIXOP2 PLUS
%left     INFIXOP3 STAR
%right    INFIXOP4
%left     PERCENT
%nonassoc RZ

%nonassoc PREFIXOP NOT 
%right TNAME
%nonassoc HASH

/* Entry points */

%start toplevels
%type <Syntax.toplevel list> toplevels

%%

toplevels:
  | EOF                       { [] }
  | toplevel toplevels      { $1 :: $2 }

toplevel:
  | THEORY TNAME thargs EQUAL theory                  { Theorydef ($2, foldTheoryFunctor $3 $5) }
  | COMMENT                                           { TopComment($1) }
  | MODEL TNAME COLON theory                          { TopModel($2, $4) }

thargs:
  |                                         { [] }
  | LPAREN TNAME COLON theory RPAREN thargs { ($2, $4) :: $6 }

theory:
  | TNAME                               { TheoryName $1 }
  | theory LPAREN model RPAREN          { TheoryApp ($1, $3) }
  | THY theory_elements END             { Theory $2 }

theory_elements:
  |                             	{ [] }
  | theory_element theory_elements	{ $1 :: $2 }

predicate_def:
  | PREDICATE                   { Unstable }
  | STABLE PREDICATE            { Stable }
  | RELATION                    { Unstable }
  | STABLE RELATION             { Stable }
  | EQUIVALENCE                 { Equivalence }

theory_element:
  | SET NAME	                        { Abstract_set ($2, KindSet) }
  | SET NAME COLON kind                  { Abstract_set ($2, $4) }
  | SET NAME args EQUAL set	        { Let_set ($2, None, makeSetLambda $3 $5) }
  | CONSTANT name COLON set	        { Value ($2, $4) }
  | CONSTANT name_typed EQUAL term      { Let_term ($2, $4) }
    /* Wacky syntax! */
  | CONSTANT name_typed args EQUAL term { Let_term ($2, makeLambda $3 $5) }
  | predicate_def name COLON set        { Predicate ($2, $1, $4) }
  | predicate_def name ON set           { Predicate ($2, $1, Exp (None, $4, Prop)) }
  | predicate_def name args EQUAL term  { Let_predicate (($2, None), $1, makeLambda $3 $5) }
  | thm name margs args EQUAL term      { Sentence ($1, $2, $3, $4, $6) }
  | MODEL TNAME COLON theory            { Model ($2, $4) }
  | IMPLICIT name_list COLON set        { Implicit ($2, $4) }
  | COMMENT                             { Comment ($1) }

kind:
  | SET            { KindSet }
  | PROP           { KindProp Unstable }
  | STABLEPROP     { KindProp Stable }
  | STABLE         { KindProp Stable }
  | EQUIVALENCE    { KindProp Equivalence }
  | set IMPLY kind { KindArrow(None, $1, $3) }

thm:
  | AXIOM          { Axiom }
  | THEOREM        { Theorem }
  | LEMMA          { Lemma }
  | PROPOSITION    { Proposition }
  | COROLLARY      { Corollary }

name_list:
  | NAME                        { [$1] }
  | NAME COMMA name_list        { $1 :: $3 }

margs:
  |                                        { [] }
  | LBRACK TNAME COLON theory RBRACK margs { ($2, $4) :: $6 }

args:
  |                                           { [] }
  | name_typed args                           { $1 :: $2 }

name:
    NAME                          { N($1, Word) }
  | LPAREN PREFIXOP RPAREN        { N($2, Prefix) }
  | LPAREN INFIXOP0 RPAREN        { N($2, Infix0) }
  | LPAREN INFIXOP1 RPAREN        { N($2, Infix1) }
  | LPAREN INFIXOP2 RPAREN        { N($2, Infix2) }
  | LPAREN PLUS RPAREN            { N("+", Infix2) }
  | LPAREN INFIXOP3 RPAREN        { N($2, Infix3) }
  | LPAREN STAR RPAREN            { N("*", Infix3) }

model:
    TNAME                        { ModelName $1 }
  | model PERIOD TNAME           { ModelProj ($1, $3) }
  | model LPAREN model RPAREN    { ModelApp ($1, $3) }
	
path:
    model PERIOD                 { $1 }
 
longtermname:
    path NAME                     { makeTermPath $1 $2 Word }
  | LPAREN path PREFIXOP RPAREN   { makeTermPath $2 $3 Prefix }
  | LPAREN path INFIXOP0 RPAREN   { makeTermPath $2 $3 Infix0 }
  | LPAREN path INFIXOP1 RPAREN   { makeTermPath $2 $3 Infix1 }
  | LPAREN path INFIXOP2 RPAREN   { makeTermPath $2 $3 Infix2 }
  | LPAREN path PLUS RPAREN       { makeTermPath $2 "+" Infix2 }
  | LPAREN path INFIXOP3 RPAREN   { makeTermPath $2 $3 Infix3 }
  | LPAREN path STAR RPAREN       { makeTermPath $2 "*" Infix3 }
  | NAME                          { makeTermVar $1 Word }
  | LPAREN PREFIXOP RPAREN        { makeTermVar $2 Prefix }
  | LPAREN INFIXOP0 RPAREN        { makeTermVar $2 Infix0 }
  | LPAREN INFIXOP1 RPAREN        { makeTermVar $2 Infix1 }
  | LPAREN INFIXOP2 RPAREN        { makeTermVar $2 Infix2 }
  | LPAREN PLUS RPAREN            { makeTermVar "+" Infix2 }
  | LPAREN INFIXOP3 RPAREN        { makeTermVar $2 Infix3 }
  | LPAREN STAR RPAREN            { makeTermVar "*" Infix3 } 

longsetname:
    path NAME                     { makeSetPath $1 $2 }
  | NAME                          { makeSetVar $1 }

name_typed:
    name                         { ($1, None) }
  | LPAREN name COLON set RPAREN { ($2, Some $4) }

simple_set:
  | LBRACE RBRACE		{ Empty }
  | UNIT			{ Unit }
  | PROP                        { Prop }
  | STABLEPROP                  { StableProp }
  | longsetname	                { $1 }
  | LPAREN set RPAREN           { $2 }
  | subset                      { $1 }
  | simple_set PERCENT longtermname    { Quotient ($1, $3) }
  | RZ simple_set               { Rz $2 }

apply_set:
    simple_set                  { $1 }
  | apply_set simple_term       { SetApp ($1, $2) }

subset:
    LBRACE name BAR term RBRACE { Subset (($2, None), $4) }
  | LBRACE name COLON set BAR term RBRACE { Subset (($2, Some $4), $6) }
  | LBRACE name WITH term RBRACE { Subset (($2, None), $4) }
  | LBRACE name COLON set WITH term RBRACE { Subset (($2, Some $4), $6) }

subset_or_longsetname:
    subset  { $1 }
  | longsetname { $1 }

product_list:
    apply_set STAR apply_set        { [(None, $1); (None, $3)] }
  | LPAREN name COLON set RPAREN STAR apply_set  { [(Some $2, $4); (None, $7)] }
  | LPAREN name COLON set RPAREN STAR product_list  { (Some $2, $4) :: $7 }
 
product:
    product_list                { Product $1 }
  | apply_set                   { $1 }

sum_list:
    LABEL COLON product               { [($1, Some $3)] }
  | LABEL                             { [($1, None)] }
  | sum_list PLUS LABEL               { $1 @ [($3, None)] }
  | sum_list PLUS LABEL COLON product { $1 @ [($3, Some $5)] }

set:
    product                                  { $1 }
  | sum_list                                 { Sum $1 }
  | LPAREN name COLON set RPAREN ARROW set   { Exp (Some $2, $4, $7) }
  | set ARROW set                            { Exp (None, $1, $3) }

simple_term:
    TRUE                         { True }
  | FALSE                        { False }
  | longtermname                 { $1 }
  | LPAREN term COLON set RPAREN { Constraint ($2, $4) }
  | LPAREN RPAREN                { Star }
  | LPAREN term_seq RPAREN       { Tuple $2 }
  | LPAREN term RPAREN           { $2 }
  | BEGIN term END               { $2 }
  | LBRACK term RBRACK           { RzQuot $2 }
  | simple_term PERIOD INTEGER   { Proj ($3, $1) }
  | PREFIXOP simple_term         { App (makeTermVar $1 Prefix, $2) }
  | path PREFIXOP simple_term    { App (makeTermPath $1 $2 Prefix, $3) }
  | NOT simple_term              { Not $2 }

apply_term:
    simple_term                  { $1 }
  | apply_term simple_term       { App ($1, $2) }

and_term:
    and_term AND term           { $1 @ [$3] }
  | term AND term               { [$1; $3] }

or_term:
    or_term OR term            { $1 @ [$3] }
  | term OR term               { [$1; $3] }

term:
    apply_term                  { $1 }
  | term IMPLY term             { Imply ($1, $3) }
  | term IFF term               { Iff ($1, $3) }
  | LABEL simple_term           { Inj ($1, Some $2) }
  | LABEL                       { Inj ($1, None) }
  | term EQUAL term             { Equal (None, $1, $3) }
  | LPAREN term EQUAL term IN set RPAREN   { Equal (Some $6 , $2, $4) }
  | LET name_typed EQUAL term IN term { Let ($2, $4, $6, None) }
  | LET LBRACK name_typed RBRACK EQUAL term IN term { RzChoose ($3, $6, $8, None) }
  | LET name_typed PERCENT longtermname EQUAL term IN term { Choose ($2, $4, $6, $8, None) }
  | and_term                    { And $1 }
  | or_term                     { Or $1 }
  | term INFIXOP0 term          { App (App (makeTermVar $2 Infix0, $1), $3) }
  | term path INFIXOP0 term  %prec INFIXOP0        { App (App (makeTermPath $2 $3 Infix0, $1), $4) }
  | term INFIXOP1 term          { App (App (makeTermVar $2 Infix1, $1), $3) }
  | term path INFIXOP1 term          { App (App (makeTermPath $2 $3 Infix1, $1), $4) }
  | term INFIXOP2 term          { App (App (makeTermVar $2 Infix2, $1), $3) }
  | term path INFIXOP2 term          { App (App (makeTermPath $2 $3 Infix2, $1), $4) }
  | term PLUS term              { App (App (makeTermVar "+" Infix2, $1), $3) }
  | term path PLUS term              { App (App (makeTermPath $2 "+" Infix2, $1), $4) }
  | term INFIXOP3 term          { App (App (makeTermVar $2 Infix3, $1), $3) }
  | term path INFIXOP3 term          { App (App (makeTermPath $2 $3 Infix3, $1), $4) }
  | term STAR term              { App (App (makeTermVar "*" Infix3, $1), $3) }
  | term path STAR term              { App (App (makeTermPath $2 "*" Infix3, $1), $4) }
  | term INFIXOP4 term          { App (App (makeTermVar $2 Infix4, $1), $3) }
  | term path INFIXOP4 term          { App (App (makeTermPath $2 $3 Infix4, $1), $4) }
  | term PERCENT longtermname       { Quot ($1, $3) }
  | term SUBIN subset_or_longsetname   { Subin ($1, $3) }
  | term SUBOUT subset_or_longsetname  { Subout ($1, $3) }
  | MATCH term WITH cases END   { Case ($2, $4) }
  | LAMBDA name_typed PERIOD term { Lambda ($2, $4) }
  | THE name_typed PERIOD term { The ($2, $4) }
  | FORALL name_typed PERIOD term { Forall ($2, $4) }
  | EXISTS name_typed PERIOD term { Exists ($2, $4) }
  | UNIQUE name_typed PERIOD term { Unique ($2, $4) }

term_seq:
    term COMMA term             { [$1; $3] }
  | term COMMA term_seq         { $1 :: $3 }

cases:
    LABEL name_typed ARROW term            { [$1, Some $2, $4] }
  | LABEL ARROW term                       { [$1, None, $3] }
  | LABEL name_typed ARROW term BAR cases  { ($1, Some $2, $4) :: $6 } 
  | LABEL ARROW term BAR cases             { ($1, None, $3) :: $5 } 
