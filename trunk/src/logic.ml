type label = string

type variable = string

type name = string

type binding = 

type atomic = name * set list

and proposition =
    False
  | True
  | Atomic of name * term
  | And of proposition list
  | Imply of proposition * proposition
  | Iff of proposition * proposition
  | Or of proposition list
  | Forall of variable * set * proposition
  | Exists of variable * set * proposition
  | Not of proposition
  | Equal of set * term * term

and set =
    Empty
  | Unit
  | InvisibleUnit (* used with labels *)
  | Bool
  | Basic of string
  | Product of set list
  | Exp of set * set
  | Sum of (label * set) list
  | Subset of variable * set * proposition
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
  | Predicate of name * stability * set
  | Let_predicate of name * variable list * proposition
  | Let_term of name * set * term
  | Value of name * set
  | Variable of name * set
  | Define of name * term
  | Sentence of sentence_type * name * binding * proposition
      
type theory = {
  t_name : string ;
  t_body : theory_element list
}

module S = Syntax

(********************************************************************)

let rec make_theory = function
    S.Set (n, None)-> Basic n
  | S.Set (n, Some t) -> Let_set (n, make_set t)
  | S.Predicate (n, stab, t) -> Predicate (phi, stab, make_set t)
  | S.Let_predicate (n, stab, b, p) -> Let_predicate (n, stab, make_binding, make_proposition p)
  | S.Let_term ((n, Some s), t) -> Let_term (n, s, make_term t)
  | S.Sentence (st, n, b, t) -> Sentence (st, n, b, make_proposition t)

and make_set = function
    S.Empty -> Empty
  | S.Unit -> Unit
  | S.Bool -> Bool
  | S.Set_name n -> Baic n
  | S.Product lst -> Product (List.map make_set lst)
  | S.Sum lst -> Sum (List.map
			(function (lb, None) -> (lb, InvisibleUnit) | (lb, Some s) -> (lb, make_set s)) lst)
  | S.Exp (s, t) -> Exp (make_set s, make_set t)
  | S.Subset (n, Some s, phi) -> Subset (n, make_set s, make_proposition phi)

and make_proposition = function
    S.False -> False
  | S.True -> True
  | S.App (Var n, t) -> Atomic (n, make_term t)
  | S.And (phi, psi) -> And (make_proposition phi, make_proposition psi)
  | S.Imply (phi, psi) -> Imply (make_proposition phi, make_proposition psi)
  | S.Or (phi, psi) -> Or (make_proposition phi, make_proposition psi)
  | S.Not phi -> Not (make_proposition phi)
  | S.Equal (Some s, u, v) -> Equal (make_set s, make_term u, make_term v)
  | S.Forall ((n, Some s), phi) -> Forall (n, make_set s, make_proposition phi)
  | S.Exists ((n, Some s), phi) -> Exists (n, make_set s, make_proposition phi)

and make_term = failwith "not implemented"
