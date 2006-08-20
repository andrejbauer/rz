
%{
  (* header *)
  open Name
  open Syntax

  let parse_error _ =
    raise (Message.Parse (Message.loc_here 1, "parse error"))

  exception Impossible

  let foldTheoryFunctor bnd bdy = List.fold_right (fun bnd thr -> TheoryFunctor (bnd, thr)) bnd bdy

  let makeWord strng = N (strng, Word)
  let makeIdent (strng, fxty) = Ident (N (strng, fxty))
  let makeMProj mdl (strng, fxty) = MProj (mdl, N (strng, fxty))

  let wildName =
    let k = ref 0 in
      fun () -> incr k; N ("_" ^ string_of_int !k, Wild)

  let rec makeLambda lst st =
    match lst with
	[] -> st
      | bnd -> Lambda (bnd, st)

  let nameError str1 str2 = 
    raise (Message.Parse (Message.loc_here 1,  
			 "End " ^ str2 ^ " found where End " ^
			   str1 ^ " was expected"))
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
%token <int> PROJECT
%token <string> LABEL
%token LBRACE
%token LBRACK
%token LET
%token LPAREN
%token MATCH
%token MODEL
%token MODULE
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
%token WILDCARD
%token WITH

/* Precedence and associativity */

%nonassoc MODEL THEORY THY

%nonassoc AXIOM COMMENT DEFINITION EQIUIV HYPOTHESIS IMPLICIT INCLUDE PARAMETER TYPE

%nonassoc COLONEQUAL

%nonassoc IFFSYMBOL
%nonassoc COMMA DOUBLEARROW
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
%right    COLON

/* Entry points */

%start toplevels
%type <Syntax.toplevel list> toplevels

%%

toplevels:
  | EOF                       { [] }
  | toplevel toplevels      { $1 :: $2 }

toplevel:
  | THEORY TNAME thargs COLONEQUAL theory { Theorydef (makeWord $2, foldTheoryFunctor $3 $5) }
  | COMMENT                              { TopComment($1) }
  | MODEL NAME COLON theory              { TopModel(makeWord $2, $4) }
  | MODULE TYPE TNAME PERIOD theory_elements END TNAME PERIOD 
      { if $3 = $7 then
	  Theorydef (makeWord $3, Theory $5) 
        else
          nameError $3 $7}

thargs:
  |                                         { [] }
  | LPAREN NAME COLON theory RPAREN thargs  { (makeWord $2, $4) :: $6 }

theory:
  | TNAME                                { TheoryName (makeWord $1) }
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
  | definition_decl ident binderz decl COLONEQUAL expr PERIOD
                                                      { Definition ($2, $4, makeLambda $3 $6) }
  | parameter_decl ident_list COLON expr PERIOD       { Value ($1, [($2, $4)]) }
  | parameter_decl assums PERIOD                      { Value ($1, $2) }
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

arg_noparen_required:
  | ident                              { $1, None }
  | ident COLON expr                   { $1, Some $3 }
  | LPAREN ident COLON expr RPAREN     { $2, Some $4 }

assums:
  | assum                        { [$1] }
  | assum assums                 { $1 :: $2 }

assum:
  | LPAREN ident_list COLON expr RPAREN  { ($2, $4) }

binder_list:
  | binder                       { [$1] }
  | binder binder_list           { $1 :: $2 }

binderz:
    /* Empty */              { [] }
  | binder binderz           { $1 :: $2 }

binder:
  | LPAREN ident_list COLON expr RPAREN  { ($2, Some $4) }
  | LPAREN ident_list RPAREN             { ($2, None) }

ident:
    NAME                          { N ($1, Word) }
  | LPAREN operator RPAREN        { let nm, fx = $2 in N (nm, fx) }

operator:
  | PREFIXOP         { $1, Prefix }
  | INFIXOP0         { $1, Infix0 }
  | INFIXOP1         { $1, Infix1 }
  | INFIXOP2         { $1, Infix2 }
  | PLUS             { "+", Infix2 }
  | INFIXOP3         { $1, Infix3 }
  | STAR             { "*", Infix3 }


model:
  | TNAME                                     { Ident (makeWord $1) }
  | model PERIOD TNAME                        { MProj ($1, makeWord $3) }
  | model LPAREN model RPAREN                 { App ($1, $3) }

name:
  | model PERIOD NAME                     { makeMProj $1 ($3, Word) }
  | model PERIOD LPAREN operator RPAREN   { makeMProj $1 $4 }
  | NAME                                  { makeIdent ($1, Word) }
  | LPAREN operator RPAREN                { makeIdent $2 }

simple_expr:
  | LBRACE RBRACE                             { Empty }
  | EMPTY                                     { Empty }
  | UNIT                                      { Unit }
  | SET                                       { Set }
  | PROP                                      { Prop }
  | STABLE                                    { Stable }
  | LPAREN RPAREN                             { EmptyTuple }
  | EMPTYTUPLE                                { EmptyTuple }
  | FALSE                                     { False }
  | TRUE                                      { True }
  | name                                      { $1 }
  | LPAREN expr RPAREN                        { $2 }
  | LPAREN expr_list RPAREN                   { Tuple $2 }
  | LABEL                                     { Inj ($1, None) }
  | LBRACE binding1 WITH expr RBRACE          { Subset ($2, $4) }
  | LBRACE binding1 BAR expr RBRACE           { Subset ($2, $4) }
  | LBRACK sum_list RBRACK                    { Sum $2 }

apply_expr:
  | apply_expr simple_expr                    { App ($1, $2) }
  | RZ simple_expr                            { Rz $2 }
  | EQUIV simple_expr                         { Equiv $2 }
  | LABEL simple_expr                         { Inj ($1, Some $2) }
  | simple_expr PROJECT                       { Proj ($2, $1) }
  | simple_expr                               { $1 } 

expr:
/*  | simple_expr                               { $1 }  */
  | apply_expr                                { $1 }
  | or_list                                   { Or $1 }
  | and_list                                  { And $1 }
  | expr EQUAL expr                           { Equal ($1, $3) }
  | NOT expr                                  { Not $2 }
  | dep_expr ARROW expr                       { let x, y = $1 in Arrow (x, y, $3) }
  | expr ARROW expr                           { Arrow (wildName(), $1, $3) }
  | product_list                              { Product $1 }
  | expr IFFSYMBOL expr                       { Iff ($1, $3) }
  | FORALL xbinder_list COMMA expr             { Forall ($2, $4) }
  | EXISTS xbinder_list COMMA expr             { Exists ($2, $4) }
  | UNIQUE xbinder_list COMMA expr             { Unique ($2, $4) }
  | THE arg_noparen_required COMMA expr       { The ($2, $4) }
  | MATCH expr WITH case_list END             { Case ($2, $4) }
  | LET RZ arg EQUAL expr IN expr             { RzChoose ($3, $5, $7) }
  | LET arg PERCENT expr EQUAL expr IN expr   { Choose ($2, $4, $6, $8) }
  | LET arg_noparen_required EQUAL expr IN expr { Let ($2, $4, $6) }
  | FUN xbinder_list DOUBLEARROW expr          { Lambda ($2, $4) }
  | expr COLON expr                           { Constraint ($1, $3) } 
  | expr PERCENT expr                         { Quotient ($1, $3) }
  | expr SUBIN expr                           { Subin ($1, $3) }
  | expr SUBOUT expr                          { Subout ($1, $3) }
  | expr INFIXOP0 expr                        
      { App(App(makeIdent($2,Infix0), $1), $3) }
  | expr INFIXOP1 expr                        
      { App(App(makeIdent($2,Infix1), $1), $3) }
  | expr INFIXOP2 expr                        
      { App(App(makeIdent($2,Infix2), $1), $3) }
  | expr INFIXOP3 expr                        
      { App(App(makeIdent($2,Infix3), $1), $3) }
  | expr INFIXOP4 expr                        
      { App(App(makeIdent($2,Infix4), $1), $3) }

  /* Also need cases for binary relations inside modules */

and_list:
  | expr ANDSYMBOL expr                { [$1; $3] }
  | and_list ANDSYMBOL expr            { $1 @ [$3] }

or_list:
  | expr ORSYMBOL expr                 { [$1; $3] }
  | or_list ORSYMBOL expr              { $1 @ [$3] }

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

sum_list:
  | LABEL                                  { [($1, None)] }
  | LABEL COLON apply_expr                 { [($1, Some $3)] }
  | LABEL PLUS sum_list                    { ($1, None) :: $3 }
  | LABEL COLON apply_expr PLUS sum_list   { ($1, Some $3) :: $5 }

dep_expr:
  | LBRACK ident COLON expr RBRACK    { $2, $4 }

binding1:
  | ident              { $1, None }
  | ident COLON expr   { $1, Some $3 }

case1:
  | LABEL arg DOUBLEARROW expr                   { $1, Some $2, $4 }
  | LABEL DOUBLEARROW expr                       { $1, None, $3 }

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
