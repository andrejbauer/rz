(******************************************************)
(* logic.ml                                           *)
(*                                                    *)
(* Internal (and non-HOL) representation of theories  *)
(* plus related helper functions.                     *)
(*                                                    *)
(* We retain infixness information, but all variables *)
(* must be explicitly annotated.                      *)
(******************************************************)

(**************)
(* Exceptions *)
(**************)

exception Unimplemented

exception HOL             (* If the input is trying to do HOL *)

(*******************)
(* Abstract Syntax *)
(*******************)

(** labels in sums *)
type label = string

(** names of identifiers *)
type name = Syntax.name

(** names of sets *)
type set_name = Syntax.set_name

(** a binding in a quantifier or lambda *)
type binding = name * set

(** first-order proposition, without accompanying context  *)
and proposition =
    False
  | True
  | Atomic of string * term (** atomic proposition *)
  | And    of proposition list
  | Imply  of proposition * proposition
  | Iff    of proposition * proposition
  | Or     of proposition list
  | Forall of binding * proposition
  | Exists of binding * proposition
  | Not    of proposition
  | Equal  of set * term * term

and set =
    Empty
  | Unit
  | Bool (** Bool is isomorphic to Unit+Unit *)
  | Basic   of string
  | Product of set list
  | Exp     of set * set
  | Sum     of (label * set option) list
  | Subset  of binding * proposition
  | RZ      of set (** the set of realizers *)
(** missing quotient types *)

and term =
    Star
(** missing terms for type Bool *)
  | Var    of name
  | Tuple  of term list
  | Proj   of int * term
  | App    of term * term
  | Lambda of binding  * term
  | Inj    of label * term
  | Case   of term * (label * binding option * term) list
  | Let    of binding * term * term
(** missing terms for subsets *)
(** missing terms for realizers *)

type sentence_type = Syntax.sentence_type

type theory_element =
    Set of set_name
  | Let_set of set_name * set
  | Predicate of name * Syntax.stability * set
  | Let_predicate of name * binding list * proposition
  | Let_term of name * set * term (** abbreviation *)
  | Value of name * set
  | Define of name * term (** part of theory *)
  | Sentence of sentence_type * name * binding list * proposition

type context = (string * theory_element) list

type theory = {
  t_name : string;
  t_arg : theory_element list option;
  t_body : theory_element list
}

(****************************************)
(* Substitution functions for Logic.xxx *)
(****************************************)

(*
     substProp:  name -> term -> proposition -> proposition
     substSet :  name -> term -> set -> set
     subst    :  name -> term -> term -> term

     WARNING:  Not capture-avoiding, so either use this
     only for closed terms or terms with free variables that
     are "fresh".
*)

let rec substProp x t =
  (let rec sub = function
      And ps           -> And  (List.map sub ps)
    | Imply (p1,p2)    -> Imply (sub p1, sub p2)
    | Iff (p1,p2)      -> Iff  (sub p1, sub p2)
    | Or  ps           -> Or   (List.map sub ps)
    | Forall((y,s),p1) -> Forall ((y,substSet x t s), 
				    if (x=y) then p1 else sub p1)
    | Exists((y,s),p1) -> Exists ((y,substSet x t s), 
				    if (x=y) then p1 else sub p1)
    | Not p1           -> Not (sub p1)
    | Equal (s,t1,t2)  -> Equal (substSet x t s, subst x t t1, subst x t t2)
    | t                -> t (* False, True, Atomic n *)
  in sub)

and substSet x t =
     (let rec sub = function
           Product ss       -> Product (List.map sub ss)
         | Exp (s1,s2)      -> Exp (sub s1, sub s2)
         | Sum lss          -> Sum (List.map 
                                      (function (l,sopt) -> (l, subOpt sopt)) 
                                    lss)
         | Subset ((y,s),p) -> Subset ((y,sub s),
				       if (x=y) then p else substProp x t p )
         | RZ s             -> RZ(sub s)
(*         | Quotient(s,u)   -> Quotient(sub s, subst x t u) *)
         | s                    -> s  (* Empty, Unit, Bool, and Basic *)
     and subOpt = function
           None -> None
         | Some s -> Some (sub s)
     in sub)

and subst x t = 
    (let rec sub = function
          Var y             -> if (x=y) then t else Var y
        | Tuple ts          -> Tuple (List.map sub ts)
        | Proj (n,t1)       -> Proj (n, sub t1)
        | App (t1,t2)       -> App (sub t1, sub t2)
        | Inj (l,t1)        -> Inj (l, sub t1)
        | Case (t1,arms)    -> Case (t1, subarms arms)
        | Let ((y,s),t1,t2) -> Let((y,substSet x t s),
			   sub t1, 
				   if (x=y) then t2 else sub t2)
(*
        | Choose((y,s),t1,t2) ->
            Choose((y,substSet x t s),
                     sub t1, 
                     if (x=y) then t2 else sub t2)
*)
        | Star          -> Star

     and subarms = function
          [] -> []
        | (l,Some (y,s),u)::rest ->
              (l, Some (y,substSet x t s),
               if (x=y) then u else sub u ) :: (subarms rest)
        | (l,None,u)::rest ->
              (l, None, sub u) :: (subarms rest)
     in sub)



(************************************)
(* Translation from Syntax to Logic *)
(************************************)

(* make_set           : Syntax.set -> Logic.set
   make_bindings      : Syntax.binding list -> Logic.binding list
   make_proposition   : Syntax.term -> Logic.proposition
   make_term          : Syntax.term -> Logic.term
   make_theoryelement : Syntax.theory_element -> Logic.theory_element
   make_theoryspec    : Syntax.theoryspec -> Logic.theory
   make_theory        : Syntax.theory -> Logic.theory_element list
*)

module S = Syntax

let rec make_set = function
    S.Empty -> Empty
  | S.Unit -> Unit
  | S.Bool -> Bool
  | S.Set_name n -> Basic n
  | S.Product lst -> Product (List.map make_set lst)
  | S.Sum lst -> Sum (List.map
			(function (lb, None) -> (lb, None) 
                                | (lb, Some s) -> (lb, Some (make_set s)))
                      lst)
  | S.Exp (s, t) -> Exp (make_set s, make_set t)
  | S.Subset ((n, Some s), phi) -> Subset ((n, make_set s), make_proposition phi)
  | S.Quotient (_,_) -> raise Unimplemented

(* Assumes that we have already done Type Inference
   or that the user has specified sets for all variables
 *)
and make_bindings b = List.map (fun (n, Some s) -> (n, make_set s)) b

and make_proposition = function
    S.False -> False
  | S.True -> True
  | S.App (S.Var (n, S.Word), t) -> Atomic (n, make_term t)
  | S.App (_, _) -> (print_string "Application of non-variable\n";
                     raise Unimplemented)
  | S.And lst -> And (List.map make_proposition lst)
  | S.Imply (phi, psi) -> Imply (make_proposition phi, make_proposition psi)
  | S.Or lst -> Or (List.map make_proposition lst)
  | S.Not phi -> Not (make_proposition phi)
  | S.Equal (Some s, u, v) -> Equal (make_set s, make_term u, make_term v)
  | S.Equal (None, _, v) -> (print_string "Equality missing type annotation\n";
                             raise Unimplemented)
  | S.Forall ((n, Some s), phi) -> Forall ((n, make_set s), make_proposition phi)
  | S.Forall ((_, None), _) -> 
                            (print_string "Forall missing type annotation\n";
                            raise Unimplemented)
  | S.Exists ((n, Some s), phi) -> 
                            Exists ((n, make_set s), make_proposition phi)
  | S.Exists ((_, None), _) -> 
                            (print_string "Exists missing type annotation\n";
                            raise Unimplemented)
  | _ -> raise HOL

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
				    (lb, Some (n, Some s), u) -> (lb, Some (n, make_set s), make_term u)
				  | (lb, None, u) -> (lb, None, make_term u))
			       lst)
  | S.Lambda ((n, Some s), t) -> Lambda ((n, make_set s), make_term t)
  | S.Choose (_,_,_) -> raise Unimplemented
  | _ -> raise HOL

and make_theory_element = function
    S.Set (n, None)-> Set n
  | S.Set (n, Some t) -> Let_set (n, make_set t)
  | S.Predicate (n, stab, t) -> Predicate (n, stab, make_set t)
  | S.Let_predicate (n, b, p) -> Let_predicate (n, make_bindings b, make_proposition p)
  | S.Let_term ((n, Some s), t) -> Let_term (n, make_set s, make_term t)
  | S.Let_term ((_, None), t) -> (print_string "Let_term without ty ann.\n";
                                  raise Unimplemented)
  | S.Sentence (st, n, b, t) -> Sentence (st, n, make_bindings b, make_proposition t)
  | S.Value (n,s) ->  Value (n, make_set s)

and make_theoryspec {S.t_arg=args; S.t_name=name; S.t_body=body} =
  { t_name = name;
    t_arg = (match args with None -> None | Some args -> Some (List.map make_theory_element args));
    t_body = make_theory body
  }
   
and make_theory = function
    S.Theory elts -> List.map make_theory_element elts
  | S.TheoryID id -> raise Unimplemented
