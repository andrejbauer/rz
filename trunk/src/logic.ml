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

module S = Syntax

(*******************)
(* Abstract Syntax *)
(*******************)

(** labels in sums and model components *)
type label = S.label

(** names of identifiers *)
type name = S.name

(** names of components inside models *)
type longname = LN of string * string list * S.name_type

(** names of sets *)
type set_name = S.set_name

(** names of sets *)
type set_longname = longname

(** names of models; must be capitalized *)
type model_name = S.model_name

(** names of theories *)
type theory_name = S.theory_name

(** sorts of sentences *)
type sentence_type = S.sentence_type

(** a binding in a quantifier or lambda *)
type binding = name * set

(** a binding in a parameterized theory *)
and model_binding = model_name * theory

(** first-order proposition, without accompanying context  *)
and proposition =
    False
  | True
  | Atomic of longname * term list (** atomic proposition *)
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
  | Basic   of set_longname
  | Product of set list
  | Exp     of set * set
  | Sum     of (label * set option) list
  | Subset  of binding * proposition
  | Rz      of set (** the set of realizers *)
  | Quotient of set * longname
  | PROP (** we pretend propositions form a set *)
  | STABLE (** we pretend not-not stable propositions form a set *)
  | EQUIV (** we even pretend not-not stable equivalences form a set *)
  | SET  (** we pretend sets form a set! *)

and term =
    Star
(** missing terms for type Bool *)
  | Var    of longname
  | Tuple  of term list
  | Proj   of int * term
  | App    of term * term
  | Lambda of binding  * term
  | Inj    of label * term option
  | Case   of term * (label * binding option * term) list
  | RzQuot of term
  | RzChoose of binding * term * term
  | Quot   of term * longname
  | Choose of binding * set_longname * term * term
  | Let    of binding * term * term
  | Subin  of term * set
  | Subout of term * set

and theory_element =
    Set of set_name
  | Let_set of set_name * set
  | Predicate of name * S.propKind * set
  | Let_predicate of name * S.propKind * binding list * proposition
  | Let_term of name * set * term
  | Value of name * set
  | Sentence of sentence_type * name * model_binding list * binding list * proposition
  | Model of string * theory

and theory = 
    Theory of theory_element list
  | TheoryID of string

and theorydef =
    Theorydef of string * model_binding list * theory

type context = (string * theory_element) list



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

(* AB: These seem not to be used anywhere?
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
         | Rz s             -> Rz (sub s)
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
*)

let ln_of_name (S.N(str,sort)) = LN(str,[],sort)
let ln_of_string str = LN (str, [], S.Word)

let rec string_of_ln (LN (nm, nms, _)) = String.concat "." (nm :: nms)

let ln_of_modelproj mdl nm =
  let rec lom acc = function
      S.ModelName m -> LN (m, acc, S.Word)
    | S.ModelProj (mdl, lbl) -> lom (lbl :: acc) mdl
  in
    lom [nm] mdl

let rec string_of_set = function
    Empty -> "empty"
  | Unit -> "unit"
  | Bool -> "bool"
  | Basic lname -> string_of_ln lname
  | Product lst ->
      "(" ^ (String.concat " * " (List.map string_of_set lst)) ^ ")"
  | Exp (s, t) -> "(" ^ (string_of_set s) ^ " -> " ^ (string_of_set t) ^ ")"
  | Sum lst ->
      "[" ^ (
	String.concat " + " (
	  List.map (function
			lb, None -> lb
		      | lb, Some s -> lb ^ " of " ^ (string_of_set s)
	  ) lst)
      ) ^ "]"

  | Subset _ -> "{...}"
  | Rz s -> "rz " ^ (string_of_set s)
  | Quotient (s, n) -> (string_of_set s) ^ " % " ^ (string_of_ln n)
  | PROP -> "PROP"
  | STABLE -> "STABLE"
  | EQUIV -> "EQUIV"
  | SET -> "SET"


(** *** *)

(************************************)
(* Translation from Syntax to Logic *)
(************************************)

(* make_set           : S.set -> Logic.set
   make_bindings      : S.binding list -> Logic.binding list
   make_proposition   : S.term -> Logic.proposition
   make_term          : S.term -> Logic.term
   make_theoryelement : S.theory_element -> Logic.theory_element
   make_theoryspec    : S.theoryspec -> Logic.theory
   make_theory        : S.theory -> Logic.theory_element list
*)

let rec make_set = function
    S.Empty -> Empty
  | S.Unit -> Unit
  | S.Bool -> Bool
  | S.Set_name nm -> Basic (ln_of_string nm)
  | S.Set_mproj (mdl, lbl) -> Basic (ln_of_modelproj mdl lbl)
  | S.Product lst -> Product (List.map make_set lst)
  | S.Sum lst -> Sum (List.map
			(function (lb, None) -> (lb, None) 
                                | (lb, Some s) -> (lb, Some (make_set s)))
                      lst)
  | S.Exp (s, t) -> Exp (make_set s, make_set t)
  | S.Subset ((n, Some s), phi) -> Subset ((n, make_set s), make_proposition phi)
  | S.Quotient (s, r) -> Quotient (make_set s, r)
  | S.Rz s -> Rz (make_set s)
  | S.Prop -> PROP
  | S.EquivProp -> EQUIV
  | S.StableProp -> STABLE

(* Assumes that we have already done Type Inference
   or that the user has specified sets for all variables
 *)
and make_bindings b = List.map (fun (n, Some s) -> (n, make_set s)) b

and make_proposition = function
    S.False -> False
  | S.True -> True
  | S.App (S.Var n, t) -> Atomic (n, make_term t)
  | S.App (S.App (S.Var n, u), v) -> Atomic (n, Tuple [make_term u; make_term v])
  | S.App (_, _) -> (print_string "Application of non-variable\n";
                     raise Unimplemented)
  | S.And lst -> And (List.map make_proposition lst)
  | S.Imply (phi, psi) -> Imply (make_proposition phi, make_proposition psi)
  | S.Iff (phi, psi) -> Iff (make_proposition phi, make_proposition psi)
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
  | _ -> (print_string "unrecognized proposition\n";
	  raise HOL)

and make_term = function
    S.Var n -> Var n
  | S.Constraint (t, _) -> make_term t
  | S.Star -> Star
  | S.Tuple lst -> Tuple (List.map make_term lst)
  | S.Proj (k, t) -> Proj (k, make_term t)
  | S.App (t, u) -> App (make_term t, make_term u)
  | S.Inj (lb, Some t) -> Inj (lb, Some (make_term t))
  | S.Inj (lb, None) -> Inj (lb, None)
  | S.Case (t, lst) -> Case (make_term t, List.map
			       (function
				    (lb, Some (n, Some s), u) -> (lb, Some (n, make_set s), make_term u)
				  | (lb, None, u) -> (lb, None, make_term u))
			       lst)
  | S.Lambda ((n, Some s), t) -> Lambda ((n, make_set s), make_term t)
  | S.Subin (t, s) -> Subin (make_term t, make_set s)
  | S.Subout (t, s) -> Subout (make_term t, make_set s)
  | S.Quot (t, r) -> Quot (make_term t, r)
  | S.RzQuot t -> RzQuot (make_term t)
  | S.RzChoose ((n, Some s), t, u) -> RzChoose ((n, make_set s), make_term t, make_term u)
  | S.Choose ((n, Some s), r, t, u) -> Choose ((n, make_set s), r, make_term t, make_term u)
  | S.Let (n, t, u) -> failwith "Let not impliemented"
  | _ -> (print_string "unrecognized term\n";
	  raise HOL)

and make_theory_element = function
    S.Set (n, None)-> Set n
  | S.Set (n, Some t) -> Let_set (n, make_set t)
  | S.Predicate (n, stab, t) -> Predicate (n, stab, make_set t)
  | S.Let_predicate (n, stab, b, p) ->
      Let_predicate (n, stab, make_bindings b, make_proposition p)
  | S.Let_term ((n, Some s), t) -> Let_term (n, make_set s, make_term t)
  | S.Let_term ((_, None), t) -> (print_string "Let_term without ty ann.\n";
                                  raise Unimplemented)
  | S.Sentence (st, n, mb, b, t) ->
      Sentence (st, n, make_model_bindings mb, make_bindings b, make_proposition t)
  | S.Value (n, s) -> Value (n, make_set s)
  | S.Model (str, thr) -> Model(str, make_theory thr)

and make_theory = function
    S.Theory elems -> Theory (List.map make_theory_element elems)
  | S.TheoryID id -> TheoryID id

and make_theorydef = function
    S.Theorydef(str, args, thr) ->
      Theorydef (str, make_model_bindings args, make_theory thr)

and make_model_bindings bnd = List.map (fun (m,th) -> (m, make_theory th)) bnd
