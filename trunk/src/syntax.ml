(* Abstract syntax *)

(* Labels are used to denote variants in sum types. We follow ocaml's
   syntax for polymorphic variants. *)

type label = string

(* We follow ocaml's notions of infix and prefix operations *)

type name_type = Word | Prefix | Infix0 | Infix1 | Infix2 | Infix3 | Infix4

type name = string * name_type

let underscore = ("_", Word)

type set_name = name

(** names of sets must be valid type names *)

type binding = name * set option

and set =
    Empty                            (** empty set, a.k.a, void *)
  | Unit                             (** unit set *)
  | Bool                             (** booleans *)
  | Set_name of set_name             (** atomic set *)
  | Product  of set list             (** finite product *)
  | Sum      of (label * set option) list (** finite coproduct *)
  | Exp      of set * set            (** function space *)
  | Subset   of binding * term       (** subset *)
  | Quotient of set * name * name * term  (** quotent set *)
  | RZ of set                        (** the set of realizers *)
  | Prop                             (** Only for typechecker internals! *)
  | StableProp                       (** Only for typechecker internals! *)

and term =
    Var        of name
  | Constraint of term * set
  | Star (** the member of Unit *)
  | False
  | True
  | Tuple  of term list
  | Proj   of int   * term (** projection from a tuple *)
  | App    of term  * term
  | Inj    of label * term option (** injection into a sum type *)
  | Case   of term  * (label * binding option * term) list
  | Quot   of term  * term (** quotient under equivalence relation *)
  | Choose of binding * term * term (** elimination of equivalence class *)
  | Subin  of term * set
  | Subout of term * set
  | And    of term list
  | Imply  of term  * term
  | Iff    of term  * term
  | Or     of term list
  | Not    of term
  | Equal  of set option * term * term
  | Let    of binding * term * term
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
    Set           of set_name * set option
  | Predicate     of name * stability * set
  | Let_predicate of name * binding list * term
  | Let_term      of binding * term
  | Value         of name * set
  | Variable      of name * set
  | Define        of name * term   (* CS: what's the semantic difference
                                      between Let_term and Define? *)
  | Sentence      of sentence_type * name * binding list * term
  | Model         of string * theory
  | Subtheory     of theoryspec (* AB: Do we want subtheories? *)
  | Implicit      of string list * set
      
and theoryspec = {t_arg  : theory_element list option;
                  t_name : string ;
                  t_body : theory}

and theory = 
     Theory of theory_element list
  |  TheoryID of string


(* Substitution functions.

     WARNING:  Not capture-avoiding, so either use this
     only for closed terms or terms with free variables that
     are "fresh".
*)

(** AB: As far as I can tell all this stuff is not used anywhere.
        So I commented it out. *)
(*

exception Unimplemented

let rec subst x t = 
     let rec sub = function
          Var y           -> if (x=y) then t else Var y
        | Constraint(u,s) -> Constraint(sub u, substSet x t s)
        | Tuple ts      -> Tuple(List.map sub ts)
        | Proj(n,t1)    -> Proj(n, sub t1)
        | App(t1,t2)    -> App(sub t1, sub t2)
        | Inj(l,t1)     -> Inj(l, sub t1)
        | Case(t1,arms) -> Case(t1,subarms arms)
        | Quot(t1,t2)   -> Quot(sub t1, sub t2)
        | Choose((y,sopt),t1,t2) ->
            Choose((y,substSetOption x t sopt),
                     sub t1, 
                     if (x=y) then t2 else sub t2)
        | And ts        -> And(List.map sub ts)
        | Imply(t1,t2)  -> Imply(sub t1, sub t2)
        | Iff(t1,t2)    -> Iff(sub t1, sub t2)
        | Or ts         -> Or(List.map sub ts)
        | Not t         -> Not(sub t)
        | Equal(sopt,t1,t2) -> Equal(substSetOption x t sopt,
                                         sub t1, sub t2)
        | Let((y,sopt),t1,t2) ->
            Let((y,substSetOption x t sopt),
                  sub t1, 
                  if (x=y) then t2 else sub t2)
        | Forall((y,sopt),t1) -> 
            Forall((y,substSetOption x t sopt),
                     if (x=y) then t1 else sub t1)
        | Exists((y,sopt),t1) -> 
            Exists((y,substSetOption x t sopt),
                     if (x=y) then t1 else sub t1)
        | t               -> t
     and subarms = function
          [] -> []
        | (l,None,t)::rest -> (l,None, sub t)::(subarms rest)
        | (l,Some(y,sopt),u)::rest ->
              (l,Some(y,substSetOption x t sopt),
               if (x=y) then u else sub u        )::(subarms rest)
     in sub

and substSet x t =
     let rec sub = function
           Product ss         -> Product(List.map sub ss)
         | Exp(s1,s2)         -> Exp(sub s1, sub s2)
         | Subset((y,sopt),u) ->
              Subset((y,substSetOption x t sopt),
                       if (x=y) then u else subst x t u )
         | Quotient(s,y,y',u)    -> Quotient(sub s, y, y',
					     (if x = y or x = y' then u else subst x t u))
         | s                    -> s
     in sub

and substSetOption x t = function
      None   -> None
    | Some s -> Some (substSet x t s)

*)

module NameOrder = struct
                     type t = name
                     let compare = Pervasives.compare
                   end

module NameMap = Map.Make(NameOrder)

module NameSet = Set.Make(NameOrder)
