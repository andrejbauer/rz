(* Abstract syntax *)

(* Labels are used to denote variants in sum types. We follow ocaml's
   syntax for polymorphic variants. *)

type label = string

(* We follow ocaml's notions of infix and prefix operations *)

type name_type = Word | Prefix | Infix0 | Infix1 | Infix2 | Infix3 | Infix4

type name = N of string * name_type

type set_name = string

type model_name = string

type theory_name = string

(** names of sets must be valid type names *)

type binding = name * set option

and mbinding = model_name * theory

and set =
    Empty                            (** empty set, a.k.a, void *)
  | Unit                             (** unit set *)
  | Bool                             (** booleans *)
  | Set_name of set_name             (** atomic set *)
  | Set_mproj of model * label
  | Product  of set list             (** finite product *)
  | Sum      of (label * set option) list (** finite coproduct *)
  | Exp      of set * set            (** function space *)
  | Subset   of binding * term       (** subset *)
  | Quotient of set * term           (** quotient set *)
  | Rz of set                        (** the set of realizers *)

  | Prop                             (** Only for typechecker internals! *)
  | EquivProp                        (** Only for typechecker internals! *)
  | StableProp                       (** Only for typechecker internals! *)

and model = 
  | ModelName of model_name
  | ModelProj of model * label

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
  | Choose of binding * term * term * term (** elimination of equivalence class *)
  | RzQuot of term
  | RzChoose of binding * term * term (** elimination of rz *)
  | MProj  of model * label * name_type
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
  | Implicit      of string list * set

and theory = 
    Theory of theory_element list
  | TheoryID of theory_name

and theorydef = 
    Theorydef of theory_name * (model_name * theory) list * theory

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

module StringSet = Set.Make(StringOrder)

let rec string_of_name = function 
    N(str,Word) -> str
  | N(str,_) -> "(" ^ str ^ ")"

let rec string_of_set set = 
  (let rec toStr = function 
      Empty -> "0"
    | Unit  -> "1"
    | Bool  -> "2"
    | Set_name stnm -> stnm
    | Product sets -> "(" ^ String.concat " * " (List.map toStr sets) ^ ")"
    | Sum sumarms -> "(" ^ String.concat " + " (List.map sumarmToStr sumarms) ^ ")"
    | Exp (set1, set2) -> "(" ^ toStr set1 ^ " -> " ^ toStr set2 ^ ")"
    | Prop -> "Prop"
    | StableProp -> "StableProp"
    | EquivProp -> "EquivProp"
    | Rz set -> "rz (" ^ toStr set ^ ")"
    | Set_mproj (mdl, lbl) -> string_of_model mdl ^ "::" ^ lbl
    | Subset (bnd,term) -> "{ " ^ string_of_bnd bnd ^ " | " ^ 
	                     string_of_term term ^ " }"
    | Quotient (st, trm) ->
	(match st with
	     Product _ | Sum _ | Exp _ | Rz _ ->
	       "(" ^ (toStr st) ^ ") % " ^ (string_of_term trm)
	   | _ -> (toStr st) ^ " % " ^ (string_of_term trm))


   and sumarmToStr = function
        (lbl, None) -> lbl
     |  (lbl, Some set) -> lbl ^ ":" ^ toStr set

  in
    toStr set)
    
and string_of_term trm =
  (let rec toStr = function
      Var nm  -> string_of_name nm
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
    | MProj(mdl, lbl, Word) -> string_of_model mdl ^ "::" ^ lbl
    | MProj(mdl, lbl, _) -> "(" ^ string_of_model mdl ^ "::" ^ lbl ^ ")"
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


and string_of_model = function
    ModelName strng -> strng
  | ModelProj (mdl, lbl) -> string_of_model mdl ^ "::" ^ lbl


(* Substitution functions.

     WARNING:  Not capture-avoiding, so either use this
     only for closed terms or terms with free variables that
     are "fresh", or rare other cases where this is sufficient.
*)

exception Unimplemented

type subst = {terms: term NameMap.t;
              sets: set StringMap.t;
              models: model StringMap.t}

let emptysubst = {terms = NameMap.empty;
		  sets = StringMap.empty;
		  models = StringMap.empty}

let insertTermvar sbst nm trm =
  {sbst with terms = NameMap.add nm trm sbst.terms}
let insertSetvar sbst nm st =
  {sbst with sets = StringMap.add nm st sbst.sets}
let insertModelvar sbst strng mdl =
  {sbst with models = StringMap.add strng mdl sbst.models}

let getTermvar sbst nm =
   try (NameMap.find nm sbst.terms) with Not_found -> Var nm
let getSetvar sbst stnm =
   try (StringMap.find stnm sbst.sets) with Not_found -> Set_name stnm
let getModelvar sbst mdlnm =
   try (StringMap.find mdlnm sbst.models) with Not_found -> ModelName mdlnm


let rec subst (substitution : subst) =
     let rec sub = function
          Var nm -> getTermvar substitution nm
        | Constraint(u,s) -> Constraint(sub u, substSet substitution s)
        | Tuple ts      -> Tuple(List.map sub ts)
        | Proj(n,t1)    -> Proj(n, sub t1)
        | App(t1,t2)    -> App(sub t1, sub t2)
        | Inj(l,termopt)     -> Inj(l, substTermOption substitution termopt)
        | Case(t1,arms) -> Case(t1,subarms arms)
        | Quot(trm1,trm2)   -> Quot(sub trm1, sub trm2)
        | Choose((y,sopt),trm_equiv,t1,t2) ->
            Choose((y,substSetOption substitution sopt),
                   sub trm_equiv,
                   sub t1, 
                   subst (insertTermvar substitution y (Var y)) t2)
        | MProj(mdl, lbl, fix) -> MProj(substModel substitution mdl, lbl, fix)
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
		  subst (insertTermvar substitution y (Var y)) t2)
        | Forall((y,sopt),t1) -> 
            Forall((y,substSetOption substitution sopt),
		  subst (insertTermvar substitution y (Var y)) t1)
        | Exists((y,sopt),t1) -> 
            Exists((y,substSetOption substitution sopt),
		  subst (insertTermvar substitution y (Var y)) t1)
        | t               -> t
     and subarms = function
          [] -> []
        | (l,None,t)::rest -> (l,None, sub t)::(subarms rest)
        | (l,Some(y,sopt),u)::rest ->
              (l,Some(y,substSetOption substitution sopt),
  	         subst (insertTermvar substitution y (Var y)) u) ::
	      (subarms rest)
     in sub

and substSet substitution =
     let rec sub = function
           Set_name stnm -> getSetvar substitution stnm
         | Set_mproj (mdl, lbl) -> Set_mproj(substModel substitution mdl, lbl) 
         | Product ss         -> Product(List.map sub ss)
         | Exp(s1,s2)         -> Exp(sub s1, sub s2)
         | Subset((y,sopt),u) ->
              Subset((y,substSetOption substitution sopt),
  	         subst (insertTermvar substitution y (Var y)) u)
         | Quotient(st,trm)   -> 
              Quotient(sub st, subst substitution trm)
         | s                    -> s
     in sub

and substSetOption substitution = function
      None    -> None
    | Some st -> Some (substSet substitution st)

and substTermOption substitution = function
      None     -> None
    | Some trm -> Some (subst substitution trm)

and substModel substitution = function
    ModelName strng -> getModelvar substitution strng
  | ModelProj (mdl, lbl) -> ModelProj(substModel substitution mdl, lbl)
