
%{
  (* header *)
  open Name
  open Syntax

  let parse_error _ =
    raise (Message.Parse (Message.loc_here 1, "parse error"))

  exception Impossible

  let makeWord strng = N (strng, Word)
  let makeIdent (strng, fxty) = Ident (N (strng, fxty))
  let makeMProj mdl (strng, fxty) = MProj (mdl, N (strng, fxty))

  let rec makeLambda lst st =
    match lst with
	[] -> st
      | bnd -> Lambda (bnd, st)

(*
  let nameError str1 str2 n = 
    raise (Message.Parse (Message.loc_here n,  
			 "End " ^ str2 ^ " found where End " ^
			   str1 ^ " was expected"))

  let unclosed what n =
    raise (Message.Parse (Message.loc_here n,  
			 "Missing " ^ what))
*)

%}

/* Tokens */

%token ANDSYMBOL
%token ANDSYMBOL2
%token ARROW
%token AXIOM
%token BAR
%token BOOL
%token BFALSE
%token BTRUE
%token COLON
%token COLONEQUAL
%token COMMA
%token <string> COMMENT 
%token DEFINITION
%token DOUBLEARROW
%token EMPTY
%token EMPTYTUPLE
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
%token <string> LABEL
%token LBRACE
%token LBRACK
%token LET
%token LPAREN
%token MATCH
%token <string> MPROJECT
%token <string> MPROJECTP /* Prefix-operator projection */
%token <string> MPROJECT0 /* Level-0 binary operator projection */
%token <string> MPROJECT1 /* Level-1 binary operator projection */
%token <string> MPROJECT2 /* Level-2 binary operator projection */
%token <string> MPROJECT3 /* Level-3 binary operator projection */
%token <string> MPROJECT4 /* Level-4 binary operator projection */
%token <string> NAME
%token NOT
%token ORSYMBOL
%token ORSYMBOL2
%token PARAMETER
%token PERCENT
%token PERIOD
%token PERIOD_LPAREN
%token PLUS
%token <string> PREFIXOP
%token <int> PROJECT
%token PROP
%token RBRACE
%token RBRACK
%token REQUIRE
%token RPAREN
%token RZ
%token SET
%token SUBIN
%token SUBOUT
%token STABLE
%token STAR
%token THE
%token THEOREM
%token THEORY
%token THY
/* %token <string> TNAME */
%token TRUE
%token TYPE
%token UNIQUE
%token UNIT
%token WILDCARD
%token WITH

/* Precedence and associativity */

%nonassoc THEORY THY

%nonassoc AXIOM COMMENT DEFINITION EQIUIV HYPOTHESIS IMPLICIT INCLUDE PARAMETER THEOREM TYPE

%nonassoc COLONEQUAL

%nonassoc COMMA DOUBLEARROW
%left SUBIN SUBOUT COLON
%nonassoc IFFSYMBOL
%right ARROW
%left ORSYMBOL2
%left ORSYMBOL
%left ANDSYMBOL2
%left ANDSYMBOL
%nonassoc NOT

%nonassoc IN 
%nonassoc PERIOD PERIOD_LPAREN MPROJECT
%nonassoc EQUAL 
%nonassoc WITH BAR
%left     INFIXOP0 MPROJECT0
%right    INFIXOP1 MPROJECT1
%left     INFIXOP2 MPROJECT2 PLUS 
%left     INFIXOP3 MPROJECT3 STAR
%right    INFIXOP4 MPROJECT4
%left     PERCENT
%nonassoc RZ
%nonassoc PREFIXOP

/* Entry points */

%start toplevels
%type <string list * Syntax.theory_element list> toplevels

%%

toplevels:
  | theory_elements EOF  { $1 }

theory_elements:
  |                            	   { ([],[]) }
  | theory_element theory_elements { (fst $1 @ fst $2, snd $1 @ snd $2) }

parameter_decl:
  | PARAMETER                   { Parameter }
  | AXIOM                       { Axiom }
  | THEOREM                     { Theorem }
  | HYPOTHESIS                  { Hypothesis }

definition_decl:
  | DEFINITION      { () }

theory_element:
  | REQUIRE NAME PERIOD                               { ([$2],[]) }
  | definition_decl ident binderz decl COLONEQUAL expr PERIOD
                                                      { ([], [Definition ($2, $4, makeLambda $3 $6)]) }
/*
  | definition_decl ident binderz decl COLONEQUAL expr error
                                                      { unclosed "Definition" 7 }
*/
  | parameter_decl ident_list COLON expr PERIOD       { ([], [Value ($1, [($2, $4)])]) }
  | parameter_decl assums PERIOD                      { ([], [Value ($1, $2)]) }
  | IMPLICIT TYPE ident_list COLON expr PERIOD        { ([], [Implicit ($3, $5)] ) }
  | INCLUDE expr PERIOD                               { ([], [Include $2]) }
  | COMMENT                                           { ([], [Comment ($1)]) }
						      
decl:
  |                              { None }
  | COLON expr            { Some $2 }

ident_list:
  | ident                        { [$1] }
  | ident ident_list             { $1 :: $2 }

arg_noparen_required:
  | ident                              { $1, None }
  | ident COLON expr                   { $1, Some $3 }
  | LPAREN ident COLON expr RPAREN     { $2, Some $4 }

assums:
  | assum                        { [$1] }
  | assum assums                 { $1 :: $2 }

assum:
  | LPAREN ident_list COLON expr RPAREN  { ($2, $4) }

/*
binder_list:
  | binder                       { [$1] }
  | binder binder_list           { $1 :: $2 }
*/

binderz:
    /* Empty */              { [] }
  | binder binderz           { $1 :: $2 }

binder:
  | LPAREN ident_list COLON expr RPAREN  { ($2, Some $4) }
  | ident                                { ([$1], None) }

ident:
    NAME                          { N ($1, Word) }
  | LPAREN operator RPAREN        { let nm, fx = $2 in N (nm, fx) }
  | operator                      { let nm, fx = $1 in N (nm, fx) }

operator:
  | PREFIXOP         { $1, Prefix }
  | binop            { $1 }
  
binop: 
  | INFIXOP0         { $1, Infix0 }
  | INFIXOP1         { $1, Infix1 }
  | INFIXOP2         { $1, Infix2 }
  | PLUS             { "+", Infix2 }
  | INFIXOP3         { $1, Infix3 }
  | STAR             { "*", Infix3 }
  | INFIXOP4         { $1, Infix4 }

name:
/*  | name MPROJECT                        { makeMProj $1 ($2, Word) } */
/*  | name PERIOD_LPAREN operator RPAREN   { makeMProj $1 $3 } */
  | NAME                                   { makeIdent ($1, Word) }
  | LPAREN binop RPAREN                    { makeIdent $2 }

simple_expr:
  | EMPTY                                     { Empty }
  | UNIT                                      { Unit }
  | BOOL                                      { Bool }
  | SET                                       { Set }
  | PROP                                      { Prop }
  | STABLE                                    { Stable }
  | LPAREN RPAREN                             { EmptyTuple }
  | EMPTYTUPLE                                { EmptyTuple }
  | FALSE                                     { False }
  | BFALSE                                    { BFalse }
  | TRUE                                      { True }
  | BTRUE                                     { BTrue }
  | name                                      { $1 }
  | LPAREN expr RPAREN                        { $2 }
  | LPAREN expr_list RPAREN                   { Tuple $2 }
  | LABEL                                     { Label $1 }
  | LBRACE binding1 WITH expr RBRACE          { Subset ($2, $4) }
  | LBRACE binding1 BAR expr RBRACE           { Subset ($2, $4) }

  | THY theory_elements END                   { Theory (snd $2) }
  | MATCH expr WITH case_list END             { Case ($2, $4) }
  | simple_expr PROJECT                       { Proj ($2, $1) }
  | simple_expr MPROJECT                       { makeMProj $1 ($2, Word) }
  | simple_expr MPROJECTP                     { makeMProj $1 ($2, Prefix) } 
  | simple_expr MPROJECT0                     { makeMProj $1 ($2, Infix0) }
  | simple_expr MPROJECT1                     { makeMProj $1 ($2, Infix1) }
  | simple_expr MPROJECT2                     { makeMProj $1 ($2, Infix2) }
  | simple_expr MPROJECT3                     { makeMProj $1 ($2, Infix3) }
  | simple_expr MPROJECT4                     { makeMProj $1 ($2, Infix4) }
  | simple_expr PERIOD_LPAREN operator RPAREN  { makeMProj $1 $3 }
  | PREFIXOP                                  { makeIdent($1,Prefix) }

apply_expr:
  | apply_expr simple_expr                    { App ($1, $2) }
  | simple_expr                               { $1 } 
  
unary_expr:
  | apply_expr                                { $1 }
  | NOT unary_expr                            { Not $2 }
  | EQUIV unary_expr                          { Equiv $2 }
  | RZ unary_expr                             { Rz $2 }

bin_expr:
  | unary_expr { $1 }
  | bin_expr INFIXOP0 bin_expr                { App(App(makeIdent($2,Infix0), $1), $3) }
  | bin_expr INFIXOP1 bin_expr                { App(App(makeIdent($2,Infix1), $1), $3) }
  | bin_expr INFIXOP2 bin_expr                { App(App(makeIdent($2,Infix2), $1), $3) }
  | bin_expr PLUS bin_expr                    { App(App(makeIdent("+",Infix2), $1), $3) }
  | bin_expr INFIXOP3 bin_expr                { App(App(makeIdent($2,Infix3), $1), $3) }
  | bin_expr INFIXOP4 bin_expr                { App(App(makeIdent($2,Infix4), $1), $3) }
/*  | bin_expr simple_expr MPROJECT0 bin_expr   {} */
  | bin_expr EQUAL bin_expr                   { Equal ($1, $3) }
  | bin_expr PERCENT bin_expr                 { Quotient ($1, $3) }
  | bin_expr SUBIN bin_expr                   { Subin ($1, $3) }
  | bin_expr SUBOUT bin_expr                  { Subout ($1, $3) }
    
or_expr:
  | bin_expr                                  { $1 }
  | bin_expr ORSYMBOL or_list                 { Or ((None,$1) :: $3) }
  | LBRACK LABEL COLON expr RBRACK ORSYMBOL or_list { Or((Some $2,$4) :: $7) }    

and_expr:
  | or_expr                                  { $1 }
  | or_expr ANDSYMBOL and_list               { And ($1 :: $3) }
  
expr:
  | and_expr                                   { $1 }
  | summand PLUS sum_list                     { Sum ($1 :: $3) }
  | dep_expr ARROW expr                       { let x, y = $1 in Arrow (x, y, $3) }
  | expr ARROW expr                           { Arrow (wildName(), $1, $3) }
  | product_list %prec PLUS /* < STAR */      { Product $1 }
  | expr IFFSYMBOL expr                       { Iff ($1, $3) }
  | FORALL xbinder_list COMMA expr             { Forall ($2, $4) }
  | EXISTS xbinder_list COMMA expr             { Exists ($2, $4) }
  | UNIQUE xbinder_list COMMA expr             { Unique ($2, $4) }
  | THE arg_noparen_required COMMA expr       { The ($2, $4) }
  | LET LBRACK ident RBRACK EQUAL expr IN expr { Choose ($3, $6, $8) }
  | LET RZ ident EQUAL expr IN expr           { RzChoose ($3, $5, $7) }
  | LET arg_noparen_required EQUAL expr IN expr { Let ($2, $4, $6) }
  | FUN xbinder_list DOUBLEARROW expr          { Lambda ($2, $4) }
  | expr COLON expr                            { Constraint ($1, $3) } 

and_list:
  | or_expr                     { [$1] }
  | and_list ANDSYMBOL or_expr  { $1 @ [$3] }

or_list:
  | bin_expr                        { [(None,$1)] }
  | LBRACK LABEL COLON expr RBRACK  { [(Some $2, $4)] }
  | or_list ORSYMBOL bin_expr       { $1 @ [(None,$3)] }
  | or_list ORSYMBOL LBRACK LABEL COLON expr RBRACK %prec ORSYMBOL  { $1 @ [(Some $4, $6)] }
    
expr_list:
  | expr COMMA expr                   { [$1; $3] }
  | expr COMMA expr_list              { $1 :: $3 }

product_list:
  | dep_expr STAR dep_expr             { [$1; $3] }
  | expr STAR expr                     { [(wildName(), $1); (wildName(), $3)] }
  | dep_expr STAR expr                 { [$1; (wildName(), $3)] }
  | expr STAR dep_expr                 { [(wildName(), $1); $3] }
  | product_list STAR dep_expr         { $1 @ [$3] }
  | product_list STAR expr             { $1 @ [(wildName(), $3)] }

summand:
  | LBRACK LABEL RBRACK               { ($2, None) }
  | LBRACK LABEL COLON expr RBRACK    { ($2, Some $4) }
  
sum_list:
  | summand                           { [$1] }
  | sum_list PLUS summand             { $1 @ [$3] }

dep_expr:
  | LBRACK ident COLON expr RBRACK    { $2, $4 }

binding1:
  | ident              { $1, None }
  | ident COLON expr   { $1, Some $3 }

case1:
  | LABEL arg_noparen_required DOUBLEARROW expr  { $1, Some $2, $4 }
  | LABEL DOUBLEARROW expr                       { $1, None, $3 }
  /* Permit an optional bar before the first case */
  | BAR LABEL arg_noparen_required DOUBLEARROW expr  { $2, Some $3, $5 }
  | BAR LABEL DOUBLEARROW expr                       { $2, None, $4 }

case_list:
  | case1                                        { [$1] }
  | case1 BAR case_list                          { $1 :: $3 }

/* Bindings that can include wildcards */

identorwildcard:
    ident                              { $1 }
  | WILDCARD                           { wildName() }

identorwildcards:
    /* Empty */                        { [] }
  | identorwildcard identorwildcards   { $1 :: $2 }

xbinder:
    identorwildcard                   { ([$1], None) }
  | LPAREN identorwildcards COLON expr RPAREN  
                                     { ($2, Some $4)} 
xbinder_list:
    identorwildcards                  { [($1, None)] }
  | identorwildcards COLON expr       { [($1, Some $3)] }
  | xbindersStartingWithParen         { $1 }

xbindersStartingWithParen:
    LPAREN identorwildcards COLON expr RPAREN    
                                     { [($2, Some $4)] }
  | xbindersStartingWithParen xbinder  { $1 @ [$2] }

/*
xbinderz:
                                     { [] }
  | xbinder xbinderz                 { $1 :: $2 }
*/

