(* Abstract syntax *)

(* Labels are used to denote things that don't vary.  This includes
   names of components of models, and variants in sum types. 
   For the latter, we follow ocaml's syntax for polymorphic variants. *)

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
  | Set_name of model option * set_name  (** atomic set *)
  | Product  of set list             (** finite product *)
  | Sum      of (label * set option) list (** finite coproduct *)
  | Exp      of set * set            (** function space *)
  | Subset   of binding * term       (** subset *)
  | Quotient of set * term           (** quotient set *)
  | Rz of set                        (** the set of realizers *)

  | Prop                             (** Only for typechecker internals! *)
  | EquivProp                        (** Only for typechecker internals! *)
  | StableProp                       (** Only for typechecker internals! *)

and term =
    Var        of model option * name
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
  | Choose of binding * term * term * term * set option (** elimination of equivalence class *)
  | RzQuot of term
  | RzChoose of binding * term * term * set option (** elimination of rz *)
  | Subin  of term * set
  | Subout of term * set
  | And    of term list
  | Imply  of term  * term
  | Iff    of term  * term
  | Or     of term list
  | Not    of term
  | Equal  of set option * term * term
  | Let    of binding * term * term * set option
  | Lambda of binding * term
  | The    of binding * term
  | Forall of binding * term
  | Exists of binding * term
  | Unique of binding * term

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
  | Comment       of string

and model_binding = model_name * theory

and theory = 
    Theory of theory_element list
  | TheoryName of theory_name
  | TheoryFunctor of model_binding * theory
  | TheoryApp of theory * model

and model = 
  | ModelName of model_name
  | ModelProj of model * label
  | ModelApp of model * model

and toplevel = 
    Theorydef of theory_name * theory
  | TopComment of string
  | TopModel  of string * theory

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

let stringSubscript s =
  try
    let k = String.rindex s '_' in
      String.sub s 0 k, Some (String.sub s (k+1) (String.length s - k - 1))
  with Not_found -> s, None

let stringPrime s =
  try
    let k = String.index s '\'' in
      String.sub s 0 k, Some (String.sub s k (String.length s - k))
  with Not_found -> s, None

let splitString n =
  let m, p = stringPrime n in
  let r, s = stringSubscript m in
    r, s, p

let nextString n =
  let r, s, p = splitString n in
    r ^ (match s, p with
	     None, None -> "'"
	   | None, Some "'" -> "''"
	   | None, Some p -> "_1"
	   | Some s, _ ->
	       "_" ^ (
		 try
		   string_of_int (1 + int_of_string s)
		 with
		     Failure "int_of_string" -> "1"
	       )
	)

let freshString good bad occurs =
  let rec find g =
    try
      List.find (fun x -> not (List.mem x bad) && not (occurs x)) g
    with Not_found -> find (List.map nextString g)
  in
    find good

let nextName = function
    N(nm, Word) -> N(nextString nm, Word)
  | _ -> N(nextString "op", Word)

let freshName good bad occurs =
  let rec find g =
    try
      List.find (fun ((N(x,_)) as nm) -> not (List.mem nm bad) && not (occurs x)) g
    with Not_found -> find (List.map nextName g)
  in
    find good

let rec string_of_name = function 
    N(str,Word) -> str
  | N("*",_) -> "( * )"
  | N(str,_) -> "(" ^ str ^ ")"

let rec string_of_set set = 
  (let rec toStr = function 
      Empty -> "0"
    | Unit  -> "1"
    | Bool  -> "2"
    | Set_name (None, stnm) -> stnm
    | Set_name (Some mdl, stnm) -> string_of_model mdl ^ "." ^ stnm
    | Product sets -> "(" ^ String.concat " * " (List.map toStr sets) ^ ")"
    | Sum sumarms -> "(" ^ String.concat " + " (List.map sumarmToStr sumarms) ^ ")"
    | Exp (set1, set2) -> "(" ^ toStr set1 ^ " -> " ^ toStr set2 ^ ")"
    | Prop -> "Prop"
    | StableProp -> "StableProp"
    | EquivProp -> "EquivProp"
    | Rz set -> "rz (" ^ toStr set ^ ")"
    | Subset (bnd,term) -> "{ " ^ string_of_bnd bnd ^ " with " ^ 
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
      Var(None, nm)  -> string_of_name nm
    | Var(Some mdl, N(lbl, Word)) -> string_of_model mdl ^ "." ^ lbl
    | Var(Some mdl, N(lbl, _)) -> "(" ^ string_of_model mdl ^ "." ^ lbl ^ ")"
    | Constraint(trm, set) -> "(" ^ toStr trm ^ " : " ^ string_of_set set ^ ")"
    | Star -> "()"
    | False -> "false"
    | True -> "true"
    | Tuple trms -> "(" ^ String.concat ", " (List.map toStr trms) ^ ")"
    | Proj (n, trm) -> toStr trm ^ "." ^ string_of_int n
    | App (trm1, trm2) -> "(" ^ toStr trm1 ^ " " ^ toStr trm2 ^ ")"
    | Inj (lbl, Some trm) -> "(`" ^ lbl ^ " " ^ toStr trm ^ ")"
    | Inj (lbl, None) -> "`" ^ lbl 
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
    | Let(bnd,trm1,trm2,None) ->
	"(let " ^ string_of_bnd bnd ^ " = " ^ toStr trm1 ^
	" in " ^ toStr trm2 ^ ")"
    | Let(bnd,trm1,trm2,Some st) ->
	"(let " ^ string_of_bnd bnd ^ " = " ^ toStr trm1 ^
	" in " ^ toStr trm2 ^ " : " ^ string_of_set st ^ ")"
    | Lambda(bnd,trm) ->
	"(lam " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | The(bnd,trm) ->
	"(the " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | Forall(bnd,trm) ->
	"(all " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | Exists(bnd,trm) ->
	"(some " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | Unique(bnd,trm) ->
	"(some1 " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
  in
    toStr trm)


and string_of_bnd = function
        (name, None    ) -> string_of_name name
     |  (name, Some set) -> string_of_name name  ^  ":"  ^  string_of_set set

and string_of_mbnd = function
        (mdlnm, thry) -> mdlnm ^ " : " ^ string_of_theory thry

and string_of_theory = function
    Theory _ -> "thy ... end"
  | TheoryName thrynm -> thrynm
  | TheoryApp (thry, mdl) -> 
      string_of_theory thry ^ "(" ^ string_of_model mdl ^ ")"
  | TheoryFunctor (mbnd, thry) ->
      "TFunctor " ^ string_of_mbnd mbnd ^ " . " ^ string_of_theory thry

and string_of_model = function
    ModelName strng -> strng
  | ModelApp (mdl1, mdl2) ->
      string_of_model mdl1 ^ "(" ^ string_of_model mdl2 ^ ")"
  | ModelProj (mdl, lbl) -> string_of_model mdl ^ "." ^ lbl


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
   try (NameMap.find nm sbst.terms) with Not_found -> Var (None, nm)
let getSetvar sbst stnm =
   try (StringMap.find stnm sbst.sets) with Not_found -> Set_name (None, stnm)
let getModelvar sbst mdlnm =
   try (StringMap.find mdlnm sbst.models) with Not_found -> ModelName mdlnm

let display_subst sbst =
  let do_term nm trm = print_string ("[" ^ string_of_name nm ^ "~>" ^ 
					  string_of_term trm ^ "]")
  in let do_set stnm st = print_string ("[" ^ stnm ^ "~>" ^ 
					string_of_set st ^ "]")
  in let do_model mdlnm mdl = print_string ("[" ^ mdlnm ^ "~>" ^ 
					    string_of_model mdl ^ "]")
  in  (print_string "Terms: ";
       NameMap.iter do_term sbst.terms;
       print_string "\nSets: ";
       StringMap.iter do_set sbst.sets;
       print_string "\nSets: ";
       StringMap.iter do_model sbst.models)
   

let rec subst (substitution : subst) =
     let rec sub = function
          Var (None, nm) -> getTermvar substitution nm
        | Var (Some mdl, nm) -> Var(Some (substModel substitution mdl), nm)
        | Constraint(u,s) -> Constraint(sub u, substSet substitution s)
        | Tuple ts      -> Tuple(List.map sub ts)
        | Proj(n,t1)    -> Proj(n, sub t1)
        | App(t1,t2)    -> App(sub t1, sub t2)
	| Lambda _      -> failwith "Syntax.subst: Kaboooom!"
        | Inj(l,termopt)     -> Inj(l, substTermOption substitution termopt)
        | Case(t1,arms) -> Case(t1,subarms arms)
	| RzQuot t -> RzQuot (sub t)
	| RzChoose ((y,sopt),t1,t2,stopt2) ->
	    RzChoose ((y, substSetOption substitution sopt),
		      sub t1,
		      subst (insertTermvar substitution y (Var (None, y))) t2,
		      substSetOption substitution stopt2)
        | Quot(trm1,trm2)   -> Quot(sub trm1, sub trm2)
        | Choose((y,sopt),trm_equiv,t1,t2,stopt2) ->
            Choose((y,substSetOption substitution sopt),
                   sub trm_equiv,
                   sub t1, 
                   subst (insertTermvar substitution y (Var (None, y))) t2,
		   substSetOption substitution stopt2)
        | And ts        -> And(List.map sub ts)
        | Imply(t1,t2)  -> Imply(sub t1, sub t2)
        | Iff(t1,t2)    -> Iff(sub t1, sub t2)
        | Or ts         -> Or(List.map sub ts)
        | Not t         -> Not(sub t)
        | Equal(sopt,t1,t2) -> Equal(substSetOption substitution sopt,
                                         sub t1, sub t2)
        | Let((y,stopt),t1,t2,stopt2) ->
            Let((y,substSetOption substitution stopt),
                  sub t1, 
		  subst (insertTermvar substitution y (Var (None,y))) t2,
	        substSetOption substitution stopt2)
        | Forall((y,sopt),t1) -> 
            Forall((y,substSetOption substitution sopt),
		  subst (insertTermvar substitution y (Var(None,y))) t1)
        | Exists((y,sopt),t1) -> 
            Exists((y,substSetOption substitution sopt),
		  subst (insertTermvar substitution y (Var(None,y))) t1)
        | Unique((y,sopt),t1) -> 
            Unique((y,substSetOption substitution sopt),
		   subst (insertTermvar substitution y (Var(None,y))) t1)
     and subarms = function
          [] -> []
        | (l,None,t)::rest -> (l,None, sub t)::(subarms rest)
        | (l,Some(y,sopt),u)::rest ->
              (l,Some(y,substSetOption substitution sopt),
  	         subst (insertTermvar substitution y (Var(None,y))) u) ::
	      (subarms rest)
     in sub

and substSet substitution =
     let rec sub = function
           Set_name (None, stnm) -> getSetvar substitution stnm
         | Set_name (Some mdl, stnm) -> Set_name(Some(substModel substitution mdl), stnm)
         | Product ss         -> Product(List.map sub ss)
         | Exp(s1,s2)         -> Exp(sub s1, sub s2)
         | Subset((y,sopt),u) ->
              Subset((y,substSetOption substitution sopt),
  	         subst (insertTermvar substitution y (Var(None,y))) u)
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

let rec substTheory sub = 
  let rec dosub = function
      Theory elts       -> Theory (substTheoryElts sub elts)
	  
    | TheoryName thrynm -> TheoryName thrynm
	  
    | TheoryFunctor ( (mdlnm, thry1), thry2 ) ->
	TheoryFunctor( ( mdlnm, dosub thry1 ),
                       let sub' = insertModelvar sub mdlnm ( ModelName mdlnm )
                       in substTheory sub' thry2 )
	  
    | TheoryApp ( thry, mdl ) ->
	TheoryApp ( dosub thry,  substModel sub mdl )
  in dosub

and substTheoryElts sub = function
    [] -> []
  | Set ( stnm, stopt ) :: rest -> 
       let this' = Set ( stnm, substSetOption sub stopt )
       in let sub' = insertSetvar sub stnm ( Set_name ( None, stnm ))
       in let rest' = substTheoryElts sub' rest
       in this' :: rest'
  | Predicate ( nm, pk, st) :: rest -> 
       let this' = Predicate ( nm, pk, substSet sub st )
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Let_predicate ( nm, pk, bnds, trm ) :: rest -> 
       let (bnds', sub_b) = substBnds sub bnds
       in let this' = Let_predicate ( nm, pk, bnds', subst sub_b trm )
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Let_term ( bnd, trm ) :: rest ->
       let ( ( nm, _) as bnd', sub_b) = substBnd sub bnd
       in let this' = Let_term ( bnd' , subst sub_b trm )
       in let sub'  = insertTermvar sub nm ( Var ( None, nm ) )
       in let rest' = substTheoryElts sub' rest
       in this' :: rest'
  | Value ( nm, st ) :: rest ->
       let this'    = Value ( nm, substSet sub st )
       in let sub'  = insertTermvar sub nm ( Var ( None, nm ) )
       in let rest' = substTheoryElts sub' rest
       in this' :: rest'
  | Sentence ( sentsort, nm, mbnds, bnds, trm ) :: rest ->
       let    ( mbnds', sub_m ) = substMBnds sub mbnds
       in let ( bnds',  sub_b ) = substBnds sub_m bnds
       in let trm' = subst sub_b trm
       in let this' = Sentence ( sentsort, nm, mbnds', bnds', trm' )
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Model ( mdlnm, thry ) :: rest ->
       let    thry' = substTheory sub thry 
       in let this' = Model ( mdlnm, thry' )
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Implicit ( strs, set ) :: rest ->
       let    set'  = substSet sub set
       in let this' = Implicit ( strs, set' )
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | ( ( Comment c ) as this') :: rest ->
       let rest' = substTheoryElts sub rest
       in this' :: rest'

and substBnd sub (nm, stopt) = 
    ( ( nm, substSetOption sub stopt ), 
      insertTermvar sub nm ( Var ( None, nm) ) )

and substBnds sub = function
     [] -> ([], sub)
    | bnd :: rest -> 
       let ( bnd',  sub'  ) = substBnd sub bnd
       in let ( rest', sub'' ) = substBnds sub' rest 
       in ( bnd' :: rest' , sub'' )

and substMBnds sub = function
     [] -> ([], sub)
    | (mdlnm, thry) :: rest -> 
       let sub' = insertModelvar sub mdlnm ( ModelName mdlnm  ) in
       let ( rest', sub'' ) = substMBnds sub' rest in
         ( ( mdlnm, substTheory sub thry ) :: rest' , sub'' )

let freshNameString = 
  let counter = ref 0
  in
     function () -> (incr counter;
	             "]" ^ string_of_int (!counter) ^ "[")


