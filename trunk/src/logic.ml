type label = string

type name = Syntax.name

type set_name = Syntax.set_name

type binding = name * set

and atomic = name * set list

and proposition =
    False
  | True
  | Atomic of name * term
  | And of proposition list
  | Imply of proposition * proposition
  | Iff of proposition * proposition
  | Or of proposition list
  | Forall of binding * proposition
  | Exists of binding * proposition
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
  | Subset of binding * proposition
  | RZ of set

and term =
    Var of name
  | Star
  | Tuple of term list
  | Proj of int * term
  | App of term * term
  | Lambda of binding  * term
  | Inj of label * term
  | Case of term * (label * binding * term) list
  | Let of name * term * term

(********************************************************************)

type sentence_type = Syntax.sentence_type

type theory_element =
    Set of set_name
  | Let_set of set_name * set
  | Predicate of name * Syntax.stability * set
  | Let_predicate of name * binding list * proposition
  | Let_term of name * set * term
  | Value of name * set
  | Variable of name * set
  | Define of name * term
  | Sentence of sentence_type * name * binding list * proposition
      
type theory = {
  t_name : string ;
  t_body : theory_element list
}

module S = Syntax

(********************************************************************)

let rec make_theory = function
    S.Set (n, None)-> Set n
  | S.Set (n, Some t) -> Let_set (n, make_set t)
  | S.Predicate (n, stab, t) -> Predicate (n, stab, make_set t)
  | S.Let_predicate (n, b, p) -> Let_predicate (n, make_binding b, make_proposition p)
  | S.Let_term ((n, Some s), t) -> Let_term (n, make_set s, make_term t)
  | S.Sentence (st, n, b, t) -> Sentence (st, n, make_binding b, make_proposition t)

and make_set = function
    S.Empty -> Empty
  | S.Unit -> Unit
  | S.Bool -> Bool
  | S.Set_name n -> Basic n
  | S.Product lst -> Product (List.map make_set lst)
  | S.Sum lst -> Sum (List.map
			(function (lb, None) -> (lb, InvisibleUnit) | (lb, Some s) -> (lb, make_set s)) lst)
  | S.Exp (s, t) -> Exp (make_set s, make_set t)
  | S.Subset ((n, Some s), phi) -> Subset ((n, make_set s), make_proposition phi)


and make_binding b = List.map (fun (n, Some s) -> (n, make_set s)) b

and make_proposition = function
    S.False -> False
  | S.True -> True
  | S.App (S.Var n, t) -> Atomic (n, make_term t)
  | S.And lst -> And (List.map make_proposition lst)
  | S.Imply (phi, psi) -> Imply (make_proposition phi, make_proposition psi)
  | S.Or lst -> Or (List.map make_proposition lst)
  | S.Not phi -> Not (make_proposition phi)
  | S.Equal (Some s, u, v) -> Equal (make_set s, make_term u, make_term v)
  | S.Forall ((n, Some s), phi) -> Forall ((n, make_set s), make_proposition phi)
  | S.Exists ((n, Some s), phi) -> Exists ((n, make_set s), make_proposition phi)

and make_term = function
    S.Var n -> Var n
  | S.Constraint (t, _) -> make_term t
  | S.Star -> Star
  | S.Tuple lst -> Tuple (List.map make_term lst)
  | S.Proj (k, t) -> Proj (k, make_term t)
  | S.App (t, u) -> App (make_term t, make_term u)
  | S.Inj (lb, t) -> Inj (lb, make_term t)
  | S.Case (t, lst) -> Case (make_term t, List.map
			       (function
				    (lb, Some (n, Some s), u) -> (lb, (n, make_set s), make_term u)
				  | (lb, None, u) -> (lb, (Syntax.underscore, InvisibleUnit), make_term u)
			       ) lst)
  | S.Lambda ((n, Some s), t) -> Lambda ((n, make_set s), make_term t)

