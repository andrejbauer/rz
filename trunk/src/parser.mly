%{
  (* header *)
  open Syntax

  let parse_error _ =
    raise (Message.Parse (Message.loc_here 1, "parse error"))

%}

/* Tokens */

%token AND
%token ARROW
%token AXIOM
%token BAR
%token BACKQUOTE
%token BEGIN
%token BOOL
%token COLON
%token COMMA
%token CONSTANT
%token COROLLARY
%token END
%token EOF
%token EQUAL
%token EXISTS
%token FALSE
%token FORALL
%token HASH
%token IFF
%token IMPLY
%token IMPLICIT
%token IN
%token <string> INFIXOP0
%token <string> INFIXOP1
%token <string> INFIXOP2
%token <string> INFIXOP3
%token <string> INFIXOP4
%token <int> INTEGER
%token <string> LABEL
%token LAMBDA
%token LBRACE
%token LBRACK
%token LEMMA
%token LET
%token LPAREN
%token MATCH
%token MODEL
%token <string> NAME
%token NOT
%token ONE
%token ON
%token OR
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
%token SLASH
%token SUBIN
%token SUBOUT
%token STABLE
%token STABLEPROP
%token STAR
%token STRUCTURE
%token THEOREM
%token THEORY
%token THY
%token TRUE
%token TWO
%token WITH
%token ZERO

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
%left     INFIXOP3 STAR SLASH
%right    INFIXOP4
%left     PERCENT
%nonassoc RZ

%nonassoc PREFIXOP NOT
%nonassoc HASH

/* Entry points */

%start theoryspecs
%type <Syntax.theoryspec list> theoryspecs

%%

theoryspecs:
  | EOF                         { [] }
  | theoryspec theoryspecs      { $1 :: $2 }



theoryspec:
  | THEORY NAME EQUAL theory    { {t_arg = None; 
                                   t_name = $2; 
                                   t_body = $4} }
  | THEORY NAME LPAREN theory_body RPAREN EQUAL theory 
                                { {t_arg = Some $4;
                                   t_name = $2;
                                   t_body = $7} }


theory:
  | THY theory_body END         { Theory $2 }
  | NAME                        { TheoryID $1 }

theory_body:
  |                             { [] }
  | theory_element theory_body	{ $1 :: $2 }

theory_element:
    SET NAME  			{ Set (($2, Syntax.Word), None) }
  | SET NAME EQUAL set		{ Set (($2, Syntax.Word), Some $4) }
  | CONSTANT name COLON set	{ Value ($2, $4) }
  | CONSTANT name_typed EQUAL term { Let_term ($2, $4) }
  | PREDICATE name COLON set    { Predicate ($2, Unstable, $4) }
  | STABLE PREDICATE name COLON set    { Predicate ($3, Stable, $5) }
  | RELATION name COLON set     { Predicate ($2, Unstable, $4) }
  | STABLE RELATION name COLON set     { Predicate ($3, Stable, $5) }
  | PREDICATE name args EQUAL term { Let_predicate ($2, $3, $5) }
  | RELATION name args EQUAL term { Let_predicate ($2, $3, $5) }
  | AXIOM name args EQUAL term   { Sentence (Axiom, $2, $3, $5) }
  | THEOREM name args EQUAL term { Sentence (Theorem, $2, $3, $5) }
  | LEMMA name args EQUAL term       { Sentence (Lemma, $2, $3, $5) }
  | PROPOSITION name args EQUAL term { Sentence (Proposition, $2, $3, $5) }
  | COROLLARY name args EQUAL term   { Sentence (Corollary, $2, $3, $5) }
  | MODEL NAME COLON theory      { Model($2, $4) }
  | STRUCTURE NAME COLON theory      { Model($2, $4) }
  | IMPLICIT name_list COLON set  { Implicit($2, $4) }

name_list:
  | NAME                        { [$1] }
  | NAME COMMA name_list        { $1 :: $3 }

args:
                                { [] }
  | args_curried		{ $1 }
  | LPAREN arg_list RPAREN	{ $2 }

args_curried:
    name_typed                  { [$1] }
  | name_typed args_curried     { $1 :: $2 }

arg_list:
    name_typed COMMA name_typed	{ [$1; $3] }
  | name_typed COMMA arg_list	{ $1 :: $3 }

name:
    NAME                          { ($1, Word) }
  | LPAREN PREFIXOP RPAREN        { ($2, Prefix) }
  | LPAREN INFIXOP0 RPAREN        { ($2, Infix0) }
  | LPAREN INFIXOP1 RPAREN        { ($2, Infix1) }
  | LPAREN INFIXOP2 RPAREN        { ($2, Infix2) }
  | LPAREN PLUS RPAREN            { ("+", Infix2) }
  | LPAREN INFIXOP3 RPAREN        { ($2, Infix3) }
  | LPAREN STAR RPAREN            { ("*", Infix3) }
  | LPAREN SLASH RPAREN           { ("/", Infix3) }

name_typed:
    name                         { ($1, None) }
  | LPAREN name COLON set RPAREN { ($2, Some $4) }

simple_set:
    ZERO 			{ Empty }
  | LBRACE RBRACE		{ Empty }
  | ONE				{ Unit }
  | TWO                         { Bool }
  | BOOL                        { Bool }
  | PROP                        { Prop }
  | STABLEPROP                  { StableProp }
  | NAME                        { Set_name ($1, Syntax.Word) }
  | LPAREN set RPAREN           { $2 }
  | subset                      { $1 }
  | simple_set SLASH LPAREN name COMMA name COLON term RPAREN { Quotient ($1, $4, $6, $8) }
  | RZ simple_set               { Rz $2 }

subset:
    LBRACE name BAR term RBRACE { Subset (($2, None), $4) }
  | LBRACE name COLON set BAR term RBRACE { Subset (($2, Some $4), $6) }

subset_or_name:
    subset  { $1 }
  | NAME    { Set_name ($1, Syntax.Word) }

product:
    simple_set STAR simple_set        { [$1; $3] }
  | product STAR simple_set           { $1 @ [$3] }

sum:
    LABEL COLON simple_set             { [($1, Some $3)] }
  | LABEL                              { [($1, None)] }
  | sum PLUS LABEL                     { $1 @ [($3, None)] }
  | sum PLUS LABEL COLON simple_set    { $1 @ [($3, Some $5)] }

set:
    simple_set                  { $1 }
  | product                     { Product $1 }
  | sum                         { Sum $1 }
  | set ARROW set               { Exp ($1, $3) }

simple_term:
    TRUE                        { True }
  | FALSE                       { False }
  | name                        { Var $1 }
  | ZERO                        { Var ("0", Word) }
  | ONE                         { Var ("1", Word) }
  | LPAREN term COLON set RPAREN { Constraint ($2, $4) }
  | LPAREN RPAREN               { Star }
  | LPAREN term_seq RPAREN      { Tuple $2 }
  | LPAREN term RPAREN          { $2 }
  | BEGIN term END              { $2 }
  | simple_term PERIOD INTEGER    { Proj ($3, $1) }
  | simple_term PERIOD ZERO       { Proj (0, $1) }
  | simple_term PERIOD ONE        { Proj (1, $1) }
  | simple_term PERIOD TWO        { Proj (2, $1) }
  | PREFIXOP simple_term        { App (Var ($1, Prefix), $2) }
  | NOT simple_term             { Not $2 }

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
  | LET name_typed EQUAL term IN term { Let ($2, $4, $6) }
  | LET LBRACK name_typed RBRACK EQUAL term IN term { RzChoose ($3, $6, $8) }
  | and_term                    { And $1 }
  | or_term                     { Or $1 }
  | term INFIXOP0 term          { App (App (Var ($2, Infix0), $1), $3) }
  | term INFIXOP1 term          { App (App (Var ($2, Infix1), $1), $3) }
  | term INFIXOP2 term          { App (App (Var ($2, Infix2), $1), $3) }
  | term PLUS term              { App (App (Var ("+", Infix2), $1), $3) }
  | term INFIXOP3 term          { App (App (Var ($2, Infix3), $1), $3) }
  | term STAR term              { App (App (Var ("*", Infix3), $1), $3) }
  | term SLASH term             { App (App (Var ("/", Infix3), $1), $3) }
  | term INFIXOP4 term          { App (App (Var ($2, Infix4), $1), $3) }
  | term PERCENT term           { Quot ($1, $3) }
  | LBRACK term RBRACK          { RzQuot $2 }
  | term SUBIN subset_or_name   { Subin ($1, $3) }
  | term SUBOUT subset_or_name  { Subout ($1, $3) }
  | MATCH term WITH cases END   { Case ($2, $4) }
  | LAMBDA name_typed PERIOD term { Lambda ($2, $4) }
  | FORALL name_typed PERIOD term { Forall ($2, $4) }
  | EXISTS name_typed PERIOD term { Exists ($2, $4) }

term_seq:
    term COMMA term             { [$1; $3] }
  | term COMMA term_seq         { $1 :: $3 }

cases:
    LABEL name_typed ARROW term            { [$1, Some $2, $4] }
  | LABEL ARROW term                       { [$1, None, $3] }
  | LABEL name_typed ARROW term BAR cases  { ($1, Some $2, $4) :: $6 } 
  | LABEL ARROW term BAR cases             { ($1, None, $3) :: $5 } 
