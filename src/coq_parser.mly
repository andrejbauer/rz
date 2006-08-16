
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
%token TRUE
%token TYPE
%token UNIQUE
%token UNIT
%token WITH

/* Precedence and associativity */

%nonassoc AXIOM DEFINITION EQIUIV HYPOTHESIS SET STABLE WITH

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
  | COLON expr                   { Some $2 }

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
    NAME                          { N($1, Word) }
  | LPAREN PREFIXOP RPAREN        { N($2, Prefix) }
  | LPAREN INFIXOP0 RPAREN        { N($2, Infix0) }
  | LPAREN INFIXOP1 RPAREN        { N($2, Infix1) }
  | LPAREN INFIXOP2 RPAREN        { N($2, Infix2) }
  | LPAREN PLUS RPAREN            { N("+", Infix2) }
  | LPAREN INFIXOP3 RPAREN        { N($2, Infix3) }
  | LPAREN STAR RPAREN            { N("*", Infix3) }

nonapp_expr:
  | ident                        	      { Ident $1 }
  | expr PERIOD ident            	      { MProj ($1, $3) }
  | FUN binder_list DOUBLEARROW expr          { Lambda ($2, $4) }
  | LPAREN ident COLON expr RPAREN ARROW expr { Arrow ($2, $4, $7) }  
  | expr ARROW expr                           { Arrow ( wildName (), $1, $3) }
  | LPAREN ident COLON expr RPAREN            { Constraint ($2, $4) } 
  | LBRACE RBRACE                             { Empty }
  | UNIT                                      { Unit }
  | product_list                              { Product ($1, $2) }
  | sum_list                                  { Sum $1 }
  | LBRACE binding1 WITH expr RBRACE          { Subset ($2, $4) }
  | LBRACE binding1 BAR expr RBRACE           { Subset ($2, $4) }
  | expr PERCENT expr                         { Quotient ($1, $3) }
  | RZ expr                                   { Rz $2 }
  | SET                                       { Set }
  | PROP                                      { Prop }
  | EQUIV expr                                { Equiv $2 }
  | STABLE                                    { Stable }
  | LPAREN RPAREN                             { EmptyTuple }
  | LPAREN expr_list RPAREN                   { Tuple $2 }
  | expr PROJECT                              { Proj ($2, $1) }
  | LABEL                                     { Inj ($1, None) }
  | LABEL expr                                { Inj ($1, Some $2) }
  | MATCH expr WITH case_list END             { Case ($2, $4) }
  | LET LBRACK arg_noparen RBRACK EQUAL expr IN expr
                                              { RzChoose ($3, $6, $8) }
  | LET arg PERCENT expr EQUAL expr IN expr   { Choose ($2, $4, $6, $8) }
  | expr SUBIN expr                           { Subin ($1, $3) }
  | expr SUBOUT expr                          { Subout ($1, $3) }
  | LET arg_noparen EQUAL expr IN expr        { Let ($2, $4, $6) }
  | THE arg_noparen COMMA expr                { The ($2, $4) }
  | FALSE                                     { False }
  | TRUE                                      { True }
  | and_list                                  { And $1 }
  | expr IFFSYMBOL expr                       { Iff ($1, $3) }
  | or_list                                   { Or $1 }
  | NOT expr                                  { Not $2 }
  | expr EQUAL expr                           { Equal ($1, $3) }
  | FORALL binder_list COMMA expr             { Forall ($2, $4) }
  | EXISTS binder_list COMMA expr             { Exists ($2, $4) }
  | UNIQUE binder_list COMMA expr             { Unique ($2, $4) }
 
expr:
  | expr nonapp_expr            { App ($1, $2) }

expr_list:
  | expr COMMA expr             { [$1; $3] }
  | expr COMMA expr_list        { $1 :: $3 }

product_list:
  | product_expr STAR expr            { [$1], $3 }
  | product_expr STAR product_list    { let ps,q = $3 in ($1 :: p, q) }

product_expr:
  | LPAREN ident COLON expr RPAREN    { $2, $4 }
  | expr                              { 

sum_list:
  | LABEL COLON expr                  { [($1, Some $3)] }
  | LABEL                             { [($1, None)] }
  | sum_list PLUS LABEL               { $1 @ [($3, None)] }
  | sum_list PLUS LABEL COLON expr    { $1 @ [($3, Some $5)] }

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
  | expr ANDSYMBOL expr                { [$1; $3] }
  | expr ANDSYMBOL and_list            { $1 :: $3 }

or_list:
  | expr ORSYMBOL expr                 { [$1; $3] }
  | expr ORSYMBOL and_list             { $1 :: $3 }

/* *** OLD STUFF BELOW HERE ***

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
  | MATCH expr WITH cases END    { Case ($2, $4) }


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
*/
