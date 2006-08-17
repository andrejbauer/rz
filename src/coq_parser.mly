
%{
  (* header *)
  open Syntax

  let parse_error _ =
    raise (Message.Parse (Message.loc_here 1, "parse error"))

  exception Impossible

  let foldTheoryFunctor bnd bdy = List.fold_right (fun bnd thr -> TheoryFunctor (bnd, thr)) bnd bdy

  let makeIdent strng fxty = Ident (N (strng, fxty))
  let makeMProj mdl strng fxty = MProj (mdl, Ident (N (strng, fxty)))

  let rec makeLambda lst st =
    match lst with
	[] -> st
      | bnd :: lst' -> Lambda (bnd, makeLambda lst' st)
%}

/* Tokens */

%token ANDSYMBOL
%token ARROW
%token AXIOM
%token BAR
%token COLON
%token COLONEQUAL
%token COMMA
%token <string> COMMENT 
%token DEFINITION
%token DOUBLEARROW
%token END
%token EOF
%token EQUAL
%token EQUIV
%token EXISTS
%token FALSE
%token FORALL
%token FUN
%token HYPOTHESIS
%token IFFSYMBOL
%token IMPLICIT
%token INCLUDE
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
%token LET
%token LPAREN
%token MATCH
%token MODEL
%token <string> NAME
%token NOT
%token ORSYMBOL
%token PARAMETER
%token PERCENT
%token PERIOD
%token PLUS
%token <string> PREFIXOP
%token PROP
%token RBRACE
%token RBRACK
%token RPAREN
%token RZ
%token SET
%token SUBIN
%token SUBOUT
%token STABLE
%token STAR
%token THE
%token THEORY
%token THY
%token <string> TNAME
%token TRUE
%token TYPE
%token UNIQUE
%token UNIT
%token WITH

/* Precedence and associativity */

%nonassoc MODEL THEORY THY

%nonassoc AXIOM COMMENT DEFINITION EQIUIV HYPOTHESIS IMPLICIT INCLUDE PARAMETER TYPE

%nonassoc COLONEQUAL

%nonassoc IFFSYMBOL
%nonassoc FORALL EXISTS UNIQUE THE NOT
%right ARROW
%left ORSYMBOL
%left ANDSYMBOL

%nonassoc LET IN
%nonassoc PERIOD
%nonassoc EQUAL 
%nonassoc FUN MATCH WITH BAR
%nonassoc SUBIN SUBOUT
%left     INFIXOP0
%right    INFIXOP1
%left     INFIXOP2 PLUS
%left     INFIXOP3 STAR
%right    INFIXOP4
%left     PERCENT
%nonassoc RZ

%nonassoc PREFIXOP

/* Entry points */

%start toplevels
%type <Syntax.toplevel list> toplevels

%%

toplevels:
  | EOF                       { [] }
  | toplevel toplevels      { $1 :: $2 }

toplevel:
  | THEORY NAME thargs EQUAL theory                   { Theorydef ($2, foldTheoryFunctor $3 $5) }
  | COMMENT                                           { TopComment($1) }
  | MODEL NAME COLON theory                           { TopModel($2, $4) }

thargs:
  |                                         { [] }
  | LPAREN NAME COLON theory RPAREN thargs  { ($2, $4) :: $6 }

theory:
  | NAME                                { TheoryName $1 }
  | theory LPAREN expr RPAREN           { TheoryApp ($1, $3) }
  | THY theory_elements END             { Theory $2 }

theory_elements:
  |                            	   { [] }
  | theory_element theory_elements { $1 :: $2 }

parameter_decl:
  | PARAMETER                   { Parameter }
  | AXIOM                       { Axiom }
  | HYPOTHESIS                  { Hypothesis }

definition_decl:
  | DEFINITION      { () }

theory_element:
  | definition_decl ident binder_list decl COLONEQUAL expr PERIOD
                                                      { Definition ($2, $4, makeLambda $3 $6) }
  | parameter_decl ident_list COLON expr PERIOD       { Parameter ($1, [($2, $4)]) }
  | parameter_decl binder_list PERIOD                 { Parameter ($1, $2) }
  | IMPLICIT TYPE ident_list COLON expr PERIOD        { Implicit ($3, $5) }
  | INCLUDE theory PERIOD                             { Include $2 }
  | COMMENT                                           { Comment ($1) }

decl:
  |                              { None }
  | COLON simple_expr            { Some $2 }

ident_list:
  | ident                        { [$1] }
  | ident ident_list             { $1 :: $2 }

arg:
  | ident                              { $1, None }
  | LPAREN ident COLON expr RPAREN     { $2, Some $4 }

arg_noparen:
  | ident                              { $1, None }
  | ident COLON expr                   { $1, Some $3 }

binder_list:
  | binder                       { [$1] }
  | binder binder_list           { $1 :: $2 }

binder:
  | LPAREN ident_list COLON expr RPAREN  { ($2, $4) }

ident:
    NAME                          { N ($1, Word) }
  | LPAREN operator RPAREN        { N $2 }

operator:
  | PREFIXOP         { $1, Prefix }
  | INFIXOP0         { $1, Infix0 }
  | INFIXOP1         { $1, Infix1 }
  | INFIXOP2         { $1, Infix2 }
  | PLUS             { "+", Infix2 }
  | INFIXOP3         { $1, Infix3 }
  | STAR             { "*", Infix3 }


model:
  | TNAME                                     { Ident $1 }
  | model PERIOD TNAME                        { MProj ($1, $3) }
  | model LPAREN model RPAREN                 { App ($1, $3) }

path:
  | model PERIOD                  { $1 }

name:
  | path NAME                     { makeMProj $1 ($2, Word) }
  | path LPAREN operator RPAREN   { makeMProj $1 $3 }
  | NAME                          { makeIdent ($1, Word) }
  | LPAREN operator RPAREN        { makeIdent $2 }

simple_expr:
  | LBRACE RBRACE                             { Empty }
  | UNIT                                      { Unit }
  | SET                                       { Set }
  | PROP                                      { Prop }
  | STABLE                                    { Stable }
  | LPAREN RPAREN                             { EmptyTuple }
  | FALSE                                     { False }
  | TRUE                                      { True }
  | name                                      { $1 }
  | LPAREN expr RPAREN                        { $2 }
  | LPAREN term_list RPAREN                   { Tuple $2 }
  | LABEL                                     { Inj ($1, None) }

apply_expr:
  | simple_expr                               { $1 }
  | apply_expr simple_expr                    { App ($1, $2) }
  | RZ simple_expr                            { Rz $2 }
  | EQUIV simple_expr                         { Equiv $2 }
  | LABEL simple_expr                         { Inj ($1, Some $2) }
  | simple_expr PROJECT                       { Proj ($2, $1) }

term:
  | apply_expr                                { $1 }
  | or_list                                   { Or $1 }
  | and_list                                  { And $1 }
  | NOT term                                  { Not $2 }
  | FORALL binder_list COMMA term             { Forall ($2, $4) }
  | EXISTS binder_list COMMA term             { Exists ($2, $4) }
  | UNIQUE binder_list COMMA term             { Unique ($2, $4) }
  | term IFFSYMBOL term                       { Iff ($1, $3) }
  | term EQUAL term                           { Equal ($1, $3) }
  | THE arg_noparen COMMA term                { The ($2, $4) }
  | MATCH term WITH case_list END             { Case ($2, $4) }
  | LET LBRACK arg_noparen RBRACK EQUAL term IN term
                                              { RzChoose ($3, $6, $8) }
  | LET arg PERCENT term EQUAL term IN term   { Choose ($2, $4, $6, $8) }
  | LET arg_noparen EQUAL term IN term        { Let ($2, $4, $6) }

set:
  | LBRACE binding1 WITH expr RBRACE          { Subset ($2, $4) }
  | LBRACE binding1 BAR expr RBRACE           { Subset ($2, $4) }

expr:
  | term                                      { $1 }
  | set                                       { $1 }
  | FUN binder_list DOUBLEARROW expr          { Lambda ($2, $4) }
  | LPAREN ident COLON expr RPAREN ARROW expr { Arrow ($2, $4, $7) }  
  | expr ARROW expr                           { Arrow ( wildName (), $1, $3) }
  | LPAREN ident COLON expr RPAREN            { Constraint ($2, $4) } 
  | product_list                              { Product $1 }
  | sum_list                                  { Sum $1 }
  | expr PERCENT term                         { Quotient ($1, $3) }
  | term SUBIN expr                           { Subin ($1, $3) }
  | term SUBOUT expr                          { Subout ($1, $3) }
 
term_list:
  | term COMMA term                   { [$1; $3] }
  | term COMMA term_list              { $1 :: $3 }

product_list:
  | product_expr STAR expr            { [$1], $3 }
  | product_expr STAR product_list    { let ps,q = $3 in ($1 :: p, q) }

product_expr:
  | LPAREN ident COLON expr RPAREN    { $2, $4 }
  | expr                              { wildName(), $1 }

sum_list:
  | LABEL COLON apply_expr                { [($1, Some $3)] }
  | LABEL BAR sum_list                    { ($1, None) :: $3 }
  | LABEL COLON apply_expr BAR sum_list   { ($1, Some $3) :: $5 }

binding1:
  | ident              { $1, None }
  | ident COLON expr   { $1, Some $3 }

tuple_list:
  | expr COMMA expr       { [$1; $3] }
  | expr COMMA tuple_list { $1 :: $3 }

case1:
  | LABEL arg DOUBLEARROW expr                   { $1, Some $2, $4 }
  | LABEL DOUBLEARROW expr                       { $1, None, $3 }

case_list:
  | case1                                        { [$1] }
  | case1 BAR case_list                          { $1 :: $3 }

and_list:
  | term ANDSYMBOL term                { [$1; $3] }
  | term ANDSYMBOL and_list            { $1 :: $3 }

or_list:
  | term ORSYMBOL term                 { [$1; $3] }
  | term ORSYMBOL or_list              { $1 :: $3 }
