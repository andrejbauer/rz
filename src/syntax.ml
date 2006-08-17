(* Abstract syntax *)

(* Labels are used to denote things that don't vary.  This includes
   names of components of models, and variants in sum types. 
   For the latter, we follow ocaml's syntax for polymorphic variants. *)

type label = string

(* We follow ocaml's notions of infix and prefix operations *)

type fixity = Word | Prefix | Infix0 | Infix1 | Infix2 | Infix3 | Infix4 | Wild

type name = N of string * fixity

type model_name = name (* capitalized *)

type theory_name = name (* capitalized *)

type binding1 = name * expr option

and binding = (name list * expr option) list

and set = expr

and term = expr

and prop = expr

and setkind = expr

and proptype = expr

and model = expr

and expr =
  (*** general expressions ***)
  | Ident  of name                    	 (* variable *)
  | MProj  of model * name             	 (* projection from a model *)
  | App    of expr * expr             	 (* application *)
  | Lambda of binding * expr          	 (* abstraction *)
  | Arrow  of name * expr * expr         (* various arrows and pies *)
  | Constraint of expr * expr            (* typing constraint *)

  (*** sets ***)
  | Empty                                  (* empty set, a.k.a, void *)
  | Unit                                   (* unit set *)
  | Product  of (name * expr) list * expr  (* finite (dependent) product *)
  | Sum      of (label * set option) list  (* finite coproduct *)
  | Subset   of binding1 * prop            (* subset *)
  | Quotient of set * prop                 (* quotient of a set or a term *)
  | Rz       of expr                       (* the set of realizers, or realized term *)

  (*** set kind and proposition types ***)
  | Set
  | Prop
  | Equiv of expr
  | Stable

  (*** terms ***)
  | EmptyTuple                             (* the member of Unit *)
  | Tuple  of term list
  | Proj   of int   * term                 (* projection from a tuple *)
  | Inj    of label * term option          (* injection into a sum type *)
  | Case   of term  * (label * binding1 option * term) list
  | Choose of binding * term * term * term (* elimination of equivalence class *)
  | RzChoose of binding1 * term * term     (* elimination of rz *)
  | Subin  of term * set                   (* Injection into a subset;
					      incurs an obligation *)
  | Subout of term * set                   (* Projection from a subset; 
                                              always possible *)
  | Let    of binding1 * term * term
  | The    of binding1 * term

  (*** propositions ***)
  | False
  | True
  | And    of prop list
  | Iff    of prop  * prop
  | Or     of prop list
  | Not    of prop
  | Equal  of set option * term * term
  | Forall of binding * prop
  | Exists of binding * prop
  | Unique of binding * prop

and sentence_type =
    Axiom
  | Parameter
  | Hypothesis
  | Lemma
  | Theorem
  | Corollary

and theory_element =
  | Definition of name * expr option * expr
  | Parameter  of sentence_type * (name list * expr) list
  | Implicit   of name list * expr
  | Include    of theory
  | Comment    of string

and model_binding = model_name * theory

and theory = 
    Theory of theory_element list
  | TheoryName of theory_name
  | TheoryFunctor of model_binding * theory
  | TheoryApp of theory * model

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

let unionNameSetList = List.fold_left NameSet.union NameSet.empty

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

let string_of_label l = l

let rec string_of_set set = 
  (let rec toStr = function 
      Empty -> "0"
    | Unit  -> "1"
    | Set_name (None, stnm) -> stnm
    | Set_name (Some mdl, stnm) -> string_of_model mdl ^ "." ^ stnm
    | Product noss -> "(" ^ String.concat " * " (List.map string_of_product_part noss) ^ ")"
    | Sum sumarms -> "(" ^ String.concat " + " (List.map sumarmToStr sumarms) ^ ")"
    | Exp (None, set1, set2) -> "(" ^ toStr set1 ^ " -> " ^ toStr set2 ^ ")"
    | Exp (Some nm, set1, set2) -> 
        "((" ^ string_of_name nm ^ ":" ^ toStr set1 ^ ") -> " ^ toStr set2 ^ ")"
    | Set -> "Set"
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
    | SetLambda (bnd,st) -> "(lambda " ^ string_of_bnd bnd ^ " -> " ^ 
	                     toStr st ^ ")"
    | SetApp (st, trm) -> (toStr st) ^ "( " ^ string_of_term trm ^ " )"


   and sumarmToStr = function
        (lbl, None) -> lbl
     |  (lbl, Some set) -> lbl ^ ":" ^ toStr set

  in
    toStr set)

and string_of_product_part = function
	  (None, st) -> string_of_set st
	| (Some nm, st) -> (string_of_name nm) ^ ":" ^ (string_of_set st)
	
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
    | Quot (trm1,trm2) -> "(" ^ string_of_term trm1 ^ " % " ^ string_of_term trm2 ^ ")"
    | RzQuot t -> "[" ^ (toStr t) ^ "]"
    | RzChoose (bnd, trm1, trm2, st_opt) -> 
	"let [" ^ string_of_bnd bnd ^ "] = " ^
	string_of_term trm1 ^ " in " ^ string_of_term trm2 ^ " end" ^
	(match st_opt with None -> "" | Some st -> ": " ^ string_of_set st)

    | Choose (bnd, trm1, trm2, trm3, st_opt) -> 
	"let " ^ string_of_bnd bnd ^ " % " ^ string_of_term trm1 ^ " = " ^
	string_of_term trm2 ^ " in " ^ string_of_term trm3 ^ " end" ^
	(match st_opt with None -> "" | Some st -> ": " ^ string_of_set st) 
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
     |  (name, Some set) -> "(" ^ string_of_name name  ^  ":"  ^  string_of_set set ^ ")"

and string_of_bnds = function
    [] -> ""
  | [bnd] -> string_of_bnd bnd
  | bnd :: bnds -> string_of_bnd bnd ^ " " ^ string_of_bnds bnds

and string_of_mbnd = function
        (mdlnm, thry) -> mdlnm ^ " : " ^ string_of_theory thry

and string_of_mbnds = function
    [] -> ""
  | [mbnd] -> string_of_mbnd mbnd
  | mbnd :: mbnds -> string_of_mbnd mbnd ^ " " ^ string_of_mbnds mbnds

and string_of_kind = function
    KindSet -> "KindSet"
  | KindProp pk -> "KindProp(" ^ string_of_pk pk ^ ")"
  | KindArrow (None, st, knd) -> 
      "(" ^ (string_of_set st) ^ ") => " ^ string_of_kind knd
  | KindArrow (Some nm, st, knd) -> 
      "(" ^ (string_of_name nm) ^ " : " ^ (string_of_set st) ^ ") => " ^
	string_of_kind knd


and string_of_theory = function
    Theory elts -> "thy\n" ^ string_of_theory_elements elts ^ "end"
  | TheoryName thrynm -> thrynm
  | TheoryApp (thry, mdl) -> 
      string_of_theory thry ^ "(" ^ string_of_model mdl ^ ")"
  | TheoryFunctor (mbnd, thry) ->
      "TFunctor " ^ string_of_mbnd mbnd ^ " . " ^ string_of_theory thry

and string_of_theory_element = function
    Abstract_set (stnm, knd) -> "set " ^ stnm ^ " : " ^ (string_of_kind knd)
  | Let_set (stnm, None, st) -> 
	  "set " ^ stnm ^ " = " ^ string_of_set st
  | Let_set (stnm, Some knd, st) -> 
	  "set " ^ stnm ^ " : " ^ string_of_kind knd ^ " = " ^ string_of_set st
  | Predicate (nm, pk, st) -> 
      string_of_pk pk ^ " " ^ string_of_name nm ^ " : " ^ string_of_set st
  | Let_predicate ((nm, None), pk, trm) ->
      string_of_pk pk ^ " " ^ string_of_name nm ^ " = " ^ string_of_term trm
  | Let_predicate ((nm, Some st), pk, trm) ->
      string_of_pk pk ^ " " ^ string_of_name nm ^ " : " ^ string_of_set st ^ " = " ^
	string_of_term trm
  | Let_term (bnd, trm) -> 
      "let " ^ string_of_bnd bnd ^ " = " ^ string_of_term trm
  | Value (nm, st) ->
      "const " ^ string_of_name nm ^ " : " ^ string_of_set st
  | Sentence (ssort, nm, mbnds, bnds, trm) ->
      "axiom  " ^ string_of_name nm ^ " " ^ 
      string_of_mbnds mbnds ^ " " ^ string_of_bnds bnds ^ " =\n " ^
      string_of_term trm
  | Model (mdlnm, thry) -> 
      "model " ^ mdlnm ^ " : " ^ string_of_theory thry
  | Implicit (strs, st) -> 
      "implicit " ^ (String.concat "," strs) ^ " : " ^ string_of_set st
  | Comment strng -> 
      "(* " ^ strng ^ " *)"
  | Variable (nm, st) -> (print_string  
			     "We don't have external syntax for Variable!\n";
			  raise Unimplemented)

and string_of_theory_elements = function
    [] -> ""
  | elt :: elts -> string_of_theory_element elt ^ "\n" ^ 
                   string_of_theory_elements elts
 
and string_of_pk = function
    Stable -> "stable relation"
  | Unstable -> "relation"
  | Equivalence -> "equivalence " 

and string_of_model = function
    ModelName strng -> strng
  | ModelApp (mdl1, mdl2) ->
      string_of_model mdl1 ^ "(" ^ string_of_model mdl2 ^ ")"
  | ModelProj (mdl, lbl) -> string_of_model mdl ^ "." ^ lbl

and string_of_toplevel = function
    Theorydef (thrynm, thry) -> 
      "theory " ^ thrynm ^ " = " ^ string_of_theory thry
  | TopComment strng ->
      "(* " ^ strng ^ " *)"
  | TopModel (mdlnm, thry) ->
      "model " ^ mdlnm ^ " = " ^ string_of_theory thry


(************************)
(** Free name functions *)
(************************)

(* Does not include free set  names model names or theory names; just values of type "name" *)

let rec fnSet = function
    Empty | Unit | Set | Prop
  | EquivProp | StableProp | Set_name (None, _) -> NameSet.empty
  | Set_name (Some mdl, _) -> fnModel mdl
  | Product noss -> fnProduct noss
  | Sum lsos -> fnSum lsos
  | Exp (None, st1, st2) -> NameSet.union (fnSet st1) (fnSet st2)
  | Exp (Some nm, st1, st2) ->
      NameSet.union (fnSet st1) (NameSet.remove nm (fnSet st2))
  | SetLambda ((nm, stopt), st) -> 
      NameSet.union (fnSetOpt stopt) (NameSet.remove nm (fnSet st))
  | Subset((nm, stopt), trm) -> 
      NameSet.union (fnSetOpt stopt) (NameSet.remove nm (fnTerm trm))
  | Quotient(st, trm) 
  | SetApp(st, trm) -> NameSet.union (fnSet st) (fnTerm trm)
  | Rz st -> fnSet st	
      
and fnSetOpt = function
	  None -> NameSet.empty
	| Some st -> fnSet st
	
and fnProduct = function
	  [] -> NameSet.empty
   	| (None, st)::rest -> NameSet.union (fnSet st) (fnProduct rest)
    | (Some n, st)::rest -> NameSet.union (fnSet st) (NameSet.remove n (fnProduct rest))
	
and fnSum = function	 
    [] -> NameSet.empty
  | (_, stopt)::rest -> NameSet.union (fnSetOpt stopt) (fnSum rest)

and fnKind = function
    KindSet | KindProp _ -> NameSet.empty
  | KindArrow(None, st, knd) -> NameSet.union (fnSet st) (fnKind knd)
  | KindArrow(Some nm, st, knd) -> NameSet.union (fnSet st) (NameSet.remove nm (fnKind knd))
      
and fnTerm = function
    Star | False | True | Inj(_, None)-> NameSet.empty
  | Var(None, nm) -> NameSet.singleton nm
  | Var(Some mdl, nm) -> NameSet.add nm (fnModel mdl)
  | Constraint(trm, st) 
  | Subin(trm, st) 
  | Subout(trm, st) -> NameSet.union (fnTerm trm) (fnSet st) 
  | Tuple trms 
  | And trms
  | Or trms -> unionNameSetList (List.map fnTerm trms)
  | Proj(_, trm) 
  | Inj(_, Some trm)
  | RzQuot trm 
  | Not trm -> fnTerm trm
  | App(trm1, trm2) 
  | Quot(trm1, trm2)
  | Imply(trm1, trm2)
  | Iff(trm1, trm2) -> NameSet.union (fnTerm trm1) (fnTerm trm2)
  | Equal(stopt, trm1, trm2) -> 
      unionNameSetList [fnSetOpt stopt; fnTerm trm1; fnTerm trm2]
  | Choose((nm, stopt1), trm1, trm2, trm3, stopt2) ->
      unionNameSetList [fnSetOpt stopt1; fnTerm trm1; fnTerm trm2;
		        NameSet.remove nm (fnTerm trm3); fnSetOpt stopt2]
  | RzChoose ((nm, stopt1), trm1, trm2, stopt2) 
  | Let ((nm, stopt1), trm1, trm2, stopt2) -> 
      unionNameSetList [fnSetOpt stopt1; fnTerm trm1; 
		        NameSet.remove nm (fnTerm trm2); fnSetOpt stopt2]
  | Lambda((nm, stopt), trm)
  | The((nm, stopt), trm)
  | Forall((nm, stopt), trm)
  | Exists((nm, stopt), trm)
  | Unique((nm, stopt), trm) -> 
      NameSet.union (fnSetOpt stopt) (NameSet.remove nm (fnTerm trm))
  | Case (trm, arms) ->
      NameSet.union (fnTerm trm) (unionNameSetList (List.map fnCaseArm arms))

and fnCaseArm = function
    (_, None, trm) -> fnTerm trm
  | (_, Some (nm, stopt), trm) -> 
      NameSet.union (fnSetOpt stopt) (NameSet.remove nm (fnTerm trm))
   
	
and fnModel _ = NameSet.empty


(* Substitution functions. *)

type subst = {terms: term NameMap.t;
              sets: set StringMap.t;
              models: model StringMap.t;
              capturablenames: NameSet.t}

let emptysubst = {terms = NameMap.empty;
		  sets = StringMap.empty;
		  models = StringMap.empty;
		  capturablenames = NameSet.empty}

let insertTermvar sbst nm trm =
  {sbst with terms = NameMap.add nm trm sbst.terms;
     capturablenames = NameSet.union sbst.capturablenames (fnTerm trm)}

let insertSetvar sbst nm st =
  {sbst with sets = StringMap.add nm st sbst.sets;
	 capturablenames = NameSet.union sbst.capturablenames (fnSet st)}
	
let insertModelvar sbst strng mdl =
  {sbst with models = StringMap.add strng mdl sbst.models;
	 capturablenames = NameSet.union sbst.capturablenames (fnModel mdl)}

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
   
(** updateboundName: subst -> name -> subst * name 
	
	Renames the given bound variable so that it can't capture anything being
	substituted in by the substitution.  Returns a substitution updated
	to rename the bound variable, and the new name.
		
	Attempts to avoid renaming if possible. *)
let updateBoundName sbst nm =
	if (NameSet.mem nm sbst.capturablenames) then
	  let rec search nm' =
		   if (NameSet.mem nm' sbst.capturablenames) then
		      search (nextName nm')
		   else 
		      (insertTermvar sbst nm (Var(None,nm')), nm')
	  in search (nextName nm)
	else 
	  (sbst, nm)

let rec subst (substitution : subst) =
	 
     let rec sub = function
          Var (None, nm) -> getTermvar substitution nm
        | Var (Some mdl, nm) -> Var(Some (substModel substitution mdl), nm)
        | Constraint(u,s) -> Constraint(sub u, substSet substitution s)
        | Tuple ts      -> Tuple(List.map sub ts)
        | Proj(n,t1)    -> Proj(n, sub t1)
        | App(t1,t2)    -> App(sub t1, sub t2)
        | Inj(l,termopt)     -> Inj(l, substTermOption substitution termopt)
        | Case(t1,arms) -> Case(t1,subarms arms)
  	| RzQuot t -> RzQuot (sub t)
	| RzChoose ((y,sopt),t1,t2,stopt2) ->
	    let (sbst', y') = updateBoundName substitution y in
	      RzChoose ((y', substSetOption substitution sopt),
		       sub t1,
		       subst sbst' t2,
		       substSetOption substitution stopt2)
        | Quot(trm1,trm2)   -> Quot(sub trm1, sub trm2)
        | Choose((y,sopt),trm_equiv,t1,t2,stopt2) ->
	    let (sbst', y') = updateBoundName substitution y in
              Choose((y',substSetOption substitution sopt),
                    sub trm_equiv,
                    sub t1, 
                    subst sbst' t2,
		    substSetOption substitution stopt2)
        | And ts        -> And(List.map sub ts)
        | Imply(t1,t2)  -> Imply(sub t1, sub t2)
        | Iff(t1,t2)    -> Iff(sub t1, sub t2)
        | Or ts         -> Or(List.map sub ts)
        | Not t         -> Not(sub t)
        | Equal(sopt,t1,t2) -> Equal(substSetOption substitution sopt,
                                         sub t1, sub t2)
        | Subin(trm,st) -> Subin(sub trm, substSet substitution st)
        | Subout(trm,st) -> Subout(sub trm, substSet substitution st)
        | Let((y,stopt),t1,t2,stopt2) ->
			let (sbst', y') = updateBoundName substitution y in
            Let((y',substSetOption substitution stopt),
                sub t1, 
		        subst sbst' t2,
	            substSetOption substitution stopt2)
	
        | Forall((y,sopt),t1) ->
	    let (sbst', y') = updateBoundName substitution y in 
              Forall((y',substSetOption substitution sopt),
		    subst sbst' t1)
	| Exists((y,sopt),t1) ->
	    let (sbst', y') = updateBoundName substitution y in 
	      Exists((y',substSetOption substitution sopt),
		    subst sbst' t1)
	| Unique((y,sopt),t1) ->
	    let (sbst', y') = updateBoundName substitution y in 
	      Unique((y',substSetOption substitution sopt),
		    subst sbst' t1)
	| Lambda((y,sopt),t1) ->
	    let (sbst', y') = updateBoundName substitution y in 
	      Lambda((y',substSetOption substitution sopt),
		    subst sbst' t1)
	| The((y,sopt),t1) ->
	    let (sbst', y') = updateBoundName substitution y in 
	      The((y',substSetOption substitution sopt),
		    subst sbst' t1)
        | (Star | False | True) as trm -> trm
        

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
         | Product ss         -> Product (substProd substitution ss)
         | Exp(None,s1,s2)     -> Exp(None,sub s1, sub s2)
         | Exp(Some y, s1, s2) ->
	    let (sbst', y') = updateBoundName substitution y in 
              Exp(Some y', sub s1, substSet sbst' s2)
         | Subset((y,sopt),u) ->
	     let (sbst', y') = updateBoundName substitution y in 
               Subset((y',substSetOption substitution sopt),
  	         subst sbst' u)
         | Quotient(st,trm)   -> 
              Quotient(sub st, subst substitution trm)
         | s                    -> s
     and substProd sbst = function
	 [] -> []
       | (None,st)::rest ->  (None, substSet sbst st) :: (substProd sbst rest)
       | (Some y,st)::rest -> 
	   let (sbst', y') = updateBoundName sbst y in 
	   (Some y', substSet sbst st) :: (substProd sbst' rest)


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
  | ModelApp (mdl1, mdl2) -> ModelApp(substModel substitution mdl1,
				      substModel substitution mdl2)

and substKind substitution = function
  | KindArrow(None, st, k) ->
      KindArrow(None, substSet substitution st, substKind substitution k)
  | KindArrow(Some y, st, k) -> 
      let (sbst', y') = updateBoundName substitution y in
	KindArrow(Some y', substSet substitution st, substKind sbst' k)
  | (KindProp _ | KindSet) as knd -> knd


let rec substTheory sub = 
  let rec dosub = function
      Theory elts       -> Theory (substTheoryElts sub elts)
	  
    | TheoryName thrynm -> TheoryName thrynm
	  
    | TheoryFunctor ((mdlnm, thry1), thry2) ->
	TheoryFunctor((mdlnm, dosub thry1),
                       let sub' = insertModelvar sub mdlnm (ModelName mdlnm)
                       in substTheory sub' thry2)
	  
    | TheoryApp (thry, mdl) ->
	TheoryApp (dosub thry,  substModel sub mdl)
  in dosub

and substTheoryElts sub = function
    [] -> []
  | Abstract_set (stnm, knd) :: rest ->
      (Abstract_set (stnm, substKind sub knd)) :: (substTheoryElts sub rest)
  | Let_set (setnm, None, st) :: rest ->
      (Let_set (setnm, None, substSet sub st)) :: (substTheoryElts sub rest)
  | Let_set (setnm, Some knd, st) :: rest ->
      (Let_set (setnm, Some (substKind sub knd), substSet sub st)) :: 
	(substTheoryElts sub rest)
  | Predicate (nm, pk, st) :: rest -> 
       let this' = Predicate (nm, pk, substSet sub st)
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Let_predicate (nm, pk, trm) :: rest -> 
       let this' = Let_predicate (nm, pk, subst sub trm)
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Let_term (bnd, trm) :: rest ->
       let ((nm, _) as bnd', sub_b) = substBnd sub bnd
       in let this' = Let_term (bnd', subst sub_b trm)
       in let sub'  = insertTermvar sub nm (Var (None, nm))
       in let rest' = substTheoryElts sub' rest
       in this' :: rest'
  | Value (nm, st) :: rest ->
       let this'    = Value (nm, substSet sub st)
       in let sub'  = insertTermvar sub nm (Var (None, nm))
       in let rest' = substTheoryElts sub' rest
       in this' :: rest'
  | Sentence (sentsort, nm, mbnds, bnds, trm) :: rest ->
       let    (mbnds', sub_m) = substMBnds sub mbnds
       in let (bnds',  sub_b) = substBnds sub_m bnds
       in let trm' = subst sub_b trm
       in let this' = Sentence (sentsort, nm, mbnds', bnds', trm')
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Model (mdlnm, thry) :: rest ->
       let    thry' = substTheory sub thry 
       in let this' = Model (mdlnm, thry')
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Implicit (strs, set) :: rest ->
       let    set'  = substSet sub set
       in let this' = Implicit (strs, set')
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | ((Comment c) as this') :: rest ->
       let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Variable _ :: _ -> raise Unimplemented

and substBnd sub (nm, stopt) = 
    ((nm, substSetOption sub stopt), 
      insertTermvar sub nm (Var (None, nm)))

and substBnds sub = function
     [] -> ([], sub)
    | bnd :: rest -> 
       let (bnd',  sub' ) = substBnd sub bnd
       in let (rest', sub'') = substBnds sub' rest 
       in (bnd' :: rest', sub'')

and substMBnds sub = function
     [] -> ([], sub)
    | (mdlnm, thry) :: rest -> 
       let sub' = insertModelvar sub mdlnm (ModelName mdlnm ) in
       let (rest', sub'') = substMBnds sub' rest in
         ((mdlnm, substTheory sub thry) :: rest', sub'')

let freshNameString = 
  let counter = ref 0
  in
     function () -> (incr counter;
	             "]" ^ string_of_int (!counter) ^ "[")

(** etaequivTheories : theory -> theory -> bool

    Eta-equivalence (extensionality) test for theories
 *)
let rec etaEquivTheories thry1 thry2 = 
(*
    let _ = print_endline "First theory" in 
    let _ = print_endline (string_of_theory thry1) in
    let _ = print_endline "Second theory" in
    let _ = print_endline (string_of_theory thry2) in
*)
  (match (thry1, thry2) with
  | (TheoryFunctor ((mdlnm1, thry11), thry12), 
     TheoryFunctor ((mdlnm2, thry21), thry22)) ->
       (etaEquivTheories thry11 thry21) 
	 && let mdlnm3 = freshNameString() 
	 in let sub1 = insertModelvar emptysubst mdlnm1 (ModelName mdlnm3)
	 in let sub2 = insertModelvar emptysubst mdlnm2 (ModelName mdlnm3)
	 in let thry12' = substTheory sub1 thry12 
	 in let thry22' = substTheory sub2 thry22 
	 in etaEquivTheories thry12' thry22'
  | (TheoryFunctor ((_, thry11), _), _) ->
      let mdlnm3 = freshNameString ()
      in let thry2' = TheoryFunctor((mdlnm3, thry11), 
				     TheoryApp (thry2, ModelName mdlnm3))
      in etaEquivTheories thry1 thry2'

  | (_, TheoryFunctor ((_, thry21), _)) ->
      let mdlnm3 = freshNameString ()
      in let thry1' = TheoryFunctor((mdlnm3, thry21), 
				     TheoryApp (thry1, ModelName mdlnm3))
      in etaEquivTheories thry1' thry2 
  | _ -> thry1 = thry2
)
