(* Abstract syntax *)

(* Labels are used to denote variants in sum types. We follow ocaml's
   syntax for polymorphic variants. *)

type label = string

(* We follow ocaml's notions of infix and prefix operations *)

type name_type = Word | Prefix | Infix0 | Infix1 | Infix2 | Infix3 | Infix4

type name = N of string * name_type

type longname = LN of string * string list * name_type
          
type set_name = name

type set_longname = longname

let toLN (N(str,fixity)) = LN(str,[],fixity)

(** names of sets must be valid type names *)

type binding = name * set option

and mbinding = string * theory

and set =
    Empty                            (** empty set, a.k.a, void *)
  | Unit                             (** unit set *)
  | Bool                             (** booleans *)
  | Set_name of set_longname         (** atomic set *)
  | Product  of set list             (** finite product *)
  | Sum      of (label * set option) list (** finite coproduct *)
  | Exp      of set * set            (** function space *)
  | Subset   of binding * term       (** subset *)
  | Quotient of set * set_longname   (** quotient set *)
  | Rz of set                        (** the set of realizers *)

  | Prop                             (** Only for typechecker internals! *)
  | EquivProp                        (** Only for typechecker internals! *)
  | StableProp                       (** Only for typechecker internals! *)

and term =
    Var        of longname
  | Constraint of term * set
  | Star (** the member of Unit *)
  | False
  | True
  | Tuple  of term list
  | Proj   of int   * term (** projection from a tuple *)
  | App    of term  * term
  | Inj    of label * term option (** injection into a sum type *)
  | Case   of term  * (label * binding option * term) list
  | Quot   of term  * set_longname (** quotient under equivalence relation *)
  | Choose of binding * set_longname * term * term (** elimination of equivalence class *)
  | RzQuot of term
  | RzChoose of binding * term * term (** elimination of rz *)
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

and sentence_type = Axiom | Lemma | Theorem | Proposition | Corollary

(* Unstable here really means that we're not guaranteed the relation
   is stable, not that it is definitely not stable.  Perhaps
   "Nonstable" would be less pejorative?
*)
and propKind = Stable | Unstable | Equivalence

and theory_element =
    Set           of set_name * set option
  | Predicate     of name * propKind * set
  | Let_predicate of name * propKind * binding list * term
  | Let_term      of binding * term
  | Value         of name * set
  | Variable      of name * set
  | Sentence      of sentence_type * name * mbinding list * binding list * term
  | Model         of string * theory
  | Subtheory     of string * (string * theory) list * theory
  | Implicit      of string list * set

and theory = 
    Theory of theory_element list
  | TheoryID of string

and theorydef = 
    Theorydef of string * (string * theory) list * theory

module NameOrder = struct
                     type t = name
                     let compare = Pervasives.compare
                   end

module StringOrder = struct
                     type t = string
                     let compare = Pervasives.compare
                   end

module NameMap = Map.Make(NameOrder)

module StringMap = Map.Make(StringOrder)

module NameSet = Set.Make(NameOrder)

let rec string_of_name = function 
    N(str,Word) -> str
  | N(str,_) -> "(" ^ str ^ ")"

let rec string_of_longname = function 
    LN(str,strs,Word) -> String.concat "." (str :: strs)
  | LN(str,strs,_) -> "(" ^ (String.concat "." (str :: strs)) ^ ")"

let rec string_of_set set = 
  (let rec toStr = function 
      Empty -> "0"
    | Unit  -> "1"
    | Bool  -> "2"
    | Set_name lname -> string_of_longname lname
    | Product sets -> "(" ^ String.concat " * " (List.map toStr sets) ^ ")"
    | Sum sumarms -> "(" ^ String.concat " + " (List.map sumarmToStr sumarms) ^ ")"
    | Exp (set1, set2) -> "(" ^ toStr set1 ^ " -> " ^ toStr set2 ^ ")"
    | Prop -> "Prop"
    | StableProp -> "StableProp"
    | EquivProp -> "EquivProp"
    | Rz set -> "rz (" ^ toStr set ^ ")"
    | Subset (bnd,term) -> "{ " ^ string_of_bnd bnd ^ " | " ^ 
	                     string_of_term term ^ " }"
    | Quotient (s, r) ->
	(match s with
	     Product _ | Sum _ | Exp _ | Rz _ ->
	       "(" ^ (toStr s) ^ ") % " ^ (string_of_longname r)
	   | _ -> (toStr s) ^ " % " ^ (string_of_longname r))


   and sumarmToStr = function
        (lbl, None) -> lbl
     |  (lbl, Some set) -> lbl ^ ":" ^ toStr set

  in
    toStr set)
    
and string_of_term trm =
  (let rec toStr = function
      Var lname  -> string_of_longname lname
    | Constraint(trm, set) -> "(" ^ toStr trm ^ " : " ^ string_of_set set ^ ")"
    | Star -> "()"
    | False -> "false"
    | True -> "true"
    | Tuple trms -> "(" ^ String.concat ", " (List.map toStr trms) ^ ")"
    | Proj (n, trm) -> toStr trm ^ "." ^ string_of_int n
    | App (trm1, trm2) -> "(" ^ toStr trm1 ^ " " ^ toStr trm2 ^ ")"
    | Inj (lbl, Some trm) -> "(" ^ lbl ^ " " ^ toStr trm ^ ")"
    | Inj (lbl, None) -> lbl 
    | Case (_,_) -> "..."
    | Quot (_,_) -> "..."
    | RzQuot t -> "[" ^ (toStr t) ^ "]"
    | RzChoose _ -> "..."
    | Choose _ -> "..."
    | Subin(trm, set) -> "(" ^ toStr trm ^ " :> " ^ string_of_set set ^ ")"
    | Subout(trm, set) -> "(" ^ toStr trm ^ " :< " ^ string_of_set set ^ ")"
    | And trms -> "(" ^ String.concat " && " (List.map toStr trms) ^ ")"
    | Imply (trm1, trm2) -> "(" ^ toStr trm1 ^ " => " ^ toStr trm2 ^ ")"
    | Iff (trm1, trm2) -> "(" ^ toStr trm1 ^ " <=> " ^ toStr trm2 ^ ")"
    | Or trms -> "(" ^ String.concat " || " (List.map toStr trms) ^ ")"
    | Not trm -> "(not " ^ toStr trm ^ ")"
    | Equal(None,trm1,trm2) -> "(" ^ toStr trm1 ^ " = " ^ toStr trm2 ^ ")"
    | Equal(Some set, trm1, trm2) -> 
          "(" ^ toStr trm1 ^ " = " ^ toStr trm2 ^ 
	  " in " ^ string_of_set set ^ ")"
    | Let(bnd,trm1,trm2) ->
	"(let " ^ string_of_bnd bnd ^ " = " ^ toStr trm1 ^
	" in " ^ toStr trm2 ^ ")"
    | Lambda(bnd,trm) ->
	"(lam " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | Forall(bnd,trm) ->
	"(all " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | Exists(bnd,trm) ->
	"(some " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
  in
    toStr trm)


and string_of_bnd = function
        (name, None    ) -> string_of_name name
     |  (name, Some set) -> string_of_name name  ^  ":"  ^  string_of_set set





(* Substitution functions.

     WARNING:  Not capture-avoiding, so either use this
     only for closed terms or terms with free variables that
     are "fresh", or rare other cases where this is sufficient.
*)

exception Unimplemented

type renamingsubst = (name * longname) list

let rec substLN (substitution : renamingsubst) = function
      LN(str, labels, sort) as ln ->
           (try 
              (match (List.assoc (N(str,Word)) substitution)  with
               LN(str',labels',sort') ->
                    LN(str',labels' @ labels, sort'))
            with Not_found -> ln)

let rec subst (substitution : renamingsubst) =
     let rec sub = function
          Var ln -> Var(substLN substitution ln)
        | Constraint(u,s) -> Constraint(sub u, substSet substitution s)
        | Tuple ts      -> Tuple(List.map sub ts)
        | Proj(n,t1)    -> Proj(n, sub t1)
        | App(t1,t2)    -> App(sub t1, sub t2)
        | Inj(l,termopt)     -> Inj(l, substTermOption substitution termopt)
        | Case(t1,arms) -> Case(t1,subarms arms)
        | Quot(t1,ln)   -> Quot(sub t1, substLN substitution ln)
        | Choose((y,sopt),ln,t1,t2) ->
            Choose((y,substSetOption substitution sopt),
                   substLN substitution ln,
                     sub t1, 
                     subst ((y, toLN y)::substitution) t2)
        | And ts        -> And(List.map sub ts)
        | Imply(t1,t2)  -> Imply(sub t1, sub t2)
        | Iff(t1,t2)    -> Iff(sub t1, sub t2)
        | Or ts         -> Or(List.map sub ts)
        | Not t         -> Not(sub t)
        | Equal(sopt,t1,t2) -> Equal(substSetOption substitution sopt,
                                         sub t1, sub t2)
        | Let((y,sopt),t1,t2) ->
            Let((y,substSetOption substitution sopt),
                  sub t1, 
                  subst ((y, toLN y)::substitution) t2)
        | Forall((y,sopt),t1) -> 
            Forall((y,substSetOption substitution sopt),
                   subst ((y, toLN y)::substitution) t1)
        | Exists((y,sopt),t1) -> 
            Exists((y,substSetOption substitution sopt),
                   subst ((y, toLN y)::substitution) t1)
        | t               -> t
     and subarms = function
          [] -> []
        | (l,None,t)::rest -> (l,None, sub t)::(subarms rest)
        | (l,Some(y,sopt),u)::rest ->
              (l,Some(y,substSetOption substitution sopt),
               subst ((y, toLN y)::substitution) u)::(subarms rest)
     in sub

and substSet substitution =
     let rec sub = function
           Set_name ln -> Set_name(substLN substitution ln)
         | Product ss         -> Product(List.map sub ss)
         | Exp(s1,s2)         -> Exp(sub s1, sub s2)
         | Subset((y,sopt),u) ->
              Subset((y,substSetOption substitution sopt),
                     subst ((y, toLN y)::substitution) u)
         | Quotient(s,ln)   -> 
              Quotient(sub s, substLN substitution ln)
         | s                    -> s
     in sub

and substSetOption substitution = function
      None   -> None
    | Some s -> Some (substSet substitution s)

and substTermOption substitution = function
      None   -> None
    | Some term -> Some (subst substitution term)



