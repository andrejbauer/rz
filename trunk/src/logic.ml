type label = string

type variable = string

type name = string

type atomic = name * set list

and proposition =
    False
  | True
  | Atomic of name * term list
  | And of proposition list
  | Imply of proposition * proposition
  | Iff of proposition * proposition
  | Or of proposition list
  | Forall of variable * set option * proposition
  | Exists of variable * set option * proposition
  | Not of proposition
  | Equal of set option * term * term

and set =
    Empty
  | Unit
  | InvisibleUnit (* used with labels *)
  | Bool
  | Basic of string
  | Product of set list
  | Exp of set * set
  | Sum of (label * set) list
  | Subset of variable * set option * proposition
  | Quotient of set * variable * variable * proposition
  | RZ of set

and term =
    Var of variable
  | Star
  | Tuple of term list
  | Proj of int * term
  | App of term * term
  | Lambda of variable * set option * term
  | Inj of label * term
  | Case of term * (label * variable * term) list
  | Quot of term
  | Choose of variable * term * term
  | Let of variable * term * term

type context = (variable * set) list

type sort =
    TEmpty
  | TUnit
  | TBool
  | TBasic of string
  | TProduct of sort list
  | TExp of sort * sort
  | TSum of (label * sort) list


(********************************************************************)

type sentence_type = Axiom | Lemma | Theorem | Proposition | Corollary

type theory_element =
    Set of name
  | Let_set of name * set
  | Predicate of name * set
  | Let_predicate of name * variable list * proposition
  | Let_term of name * term
  | Value of name * set
  | Variable of name * set
  | Define of name * term
  | Sentence of sentence_type * name * proposition
      
type theory = {
  t_name : string ;
  t_body : theory_element list
}
