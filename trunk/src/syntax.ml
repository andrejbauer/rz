(* Abstract syntax *)

(* Labels are used to denote variants in sum types. We follow ocaml's
   syntax for polymorphic variants. *)

type label = string

(* We follow ocaml's notions of infix and prefix operations *)

type name_type = Word | Prefix | Infix0 | Infix1 | Infix2 | Infix3 | Infix4

type name = string * name_type

type set_name = string

type binding = name * set option

and set =
    Empty (** empty set *)
  | Unit (** unit set *)
  | Bool (** booleans *)
  | Set_name of set_name (** atomic set *)
  | Product of set list (** finite product *)
  | Sum of (label * set option) list (** finite coproduct *)
  | Exp of set * set (** function space *)
  | Subset of binding * term (** subset *)
  | Quotient of set * term (** quotent set *)
  | RZ of set (** the set of realizers *)

and term =
    Var of name
  | Constraint of term * set
  | Star (** the member of Unit *)
  | False
  | True
  | Tuple of term list
  | Proj of int * term (** projection from a tuple *)
  | App of term * term
  | Inj of label * term (** injection into a sum type *)
  | Case of term * (label * binding option * term) list
  | Quot of term * term (** quotient under equivalence relation *)
  | Choose of binding * term * term (** elimination of equivalence class *)
  | And of term list
  | Imply of term * term
  | Iff of term * term
  | Or of term list
  | Not of term
  | Equal of set option * term * term
  | Let of binding * term * term
  | Lambda of binding * term
  | Forall of binding * term
  | Exists of binding * term

(********************************************************************)

(** We do not actually distinguish between different types of sentences,
  but we let the user name them as he likes. *)

type sentence_type = Axiom | Lemma | Theorem | Proposition | Corollary

(* Unstable here really means that we're not guaranteed the relation
   is stable, not that it is definitely not stable.  Perhaps
   "Nonstable" would be less pejorative?
*)
type stability = Stable | Unstable

type theory_element =
    Set of set_name * set option
  | Predicate of name * stability * set
  | Let_predicate of name * stability * binding list * term
  | Let_term of binding * term
  | Value of name * set
  | Variable of name * set
  | Define of name * term       (* CS: what's the semantic difference
                                   between Let_term and Define? *)
  | Sentence of sentence_type * name * binding list * term
  | Model of string * theory
  | Subtheory of theoryspec (* AB: Do we want subtheories? *)
      
and theoryspec = {t_arg  : theory_element list option;
                  t_name : string ;
                  t_body : theory}

and theory = 
     Theory of theory_element list
  |  TheoryID of string
