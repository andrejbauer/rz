(******************************************************)
(* logic.ml                                           *)
(*                                                    *)
(* Internal representation of theories plus related   *)
(* helper functions.                                  *)
(*                                                    *)
(* We retain infixness information, but all variables *)
(* must be explicitly annotated.                      *)
(******************************************************)

(**************)
(* Exceptions *)
(**************)

exception Unimplemented
exception Impossible

exception HOL             (* If the input is trying to do HOL *)

(*******************)
(* Abstract Syntax *)
(*******************)

open Name

module S = Syntax

(** names of models; must be capitalized *)
type model_name = name

type model = 
    ModelName of model_name
  | ModelProj of model * model_name
  | ModelApp of model * model

(** names of components inside models *)
type longname = LN of model option * name

(** short names of sets *)
type set_name = name

(** long names of sets *)
type set_longname = SLN of model option * set_name

(** names of theories *)
type theory_name = S.theory_name

(** sorts of sentences *)
type sentence_type = S.sentence_type

(** a binding in a quantifier or lambda *)
type binding = name * set

(** a binding in a parameterized theory *)
and model_binding = model_name * theory

(** first-order proposition *)
and proposition =
    False
  | True
  | Atomic  of longname
  | And     of proposition list
  | Imply   of proposition * proposition
  | Iff     of proposition * proposition
  | Or      of proposition list
  | Forall  of binding * proposition
  | Exists  of binding * proposition
  | Unique  of binding * proposition
  | Not     of proposition
  | Equal   of set * term * term
  | PApp    of proposition * term
  | PLambda of binding * proposition

and set =
    Empty
  | Unit  (* Unit is the singleton containing EmptyTuple *)
  | Basic    of set_longname
  | Product  of binding list
  | Exp      of name * set * set
  | Sum      of (label * set option) list
  | Subset   of binding * proposition
  | Rz       of set (** the set of realizers *)
  | Quotient of set * proposition
  | SApp     of set * term
  | SLambda  of binding * set

and proptype =
    Prop
  | StableProp
  | EquivProp of set
  | PropArrow of name * set * proptype

and setkind =
    KindSet
  | KindArrow of name * set * setkind

and term =
    EmptyTuple
  | Var      of longname
  | Tuple    of term list
  | Proj     of int * term
  | App      of term * term
  | Lambda   of binding  * term
  | The      of binding  * proposition (* description operator *)
  | Inj      of label * term option
  | Case     of term * (label * binding option * term) list
  | RzQuot   of term
  | RzChoose of binding * term * term * set
  | Quot     of term * proposition
  | Choose   of binding * term * term * term * set
  | Let      of binding * term * term * set  (* set is type of the whole let *)
  | Subin    of term * set
  | Subout   of term * set

and theory_element =
    Set of set_name * setkind
  | Let_set of set_name * setkind * set
  | Predicate of name * proptype
  | Let_predicate of name * proptype * proposition
  | Let_term of name * set * term
  | Value of name * set
  | Sentence of sentence_type * name * model_binding list * binding list * proposition
  | Model of model_name * theory
  | Comment of string

and theory = 
    Theory of theory_element list
  | TheoryName of theory_name
  | TheoryFunctor of model_binding * theory
  | TheoryApp of theory * model
    
and toplevel =
    Theorydef of theory_name * theory
  | TopComment of string
  | TopModel  of model_name * theory


(***************************************************)
(* Constructors-with-bindings as curried functions *)
(***************************************************)

let fForall x y = Forall(x,y)
let fExists x y = Exists(x,y)
let fUnique x y = Unique(x,y)
let fPLambda x y = PLambda(x,y)
let fSubset x y = Subset(x,y)
let fSLambda x y = SLambda(x,y)
let fLambda x y = Lambda(x,y)
let fThe x y = The(x,y)

  (* Hack because Exp, PropArrow and KindArrow take a binding semantically,
     but not syntactically *)
let fExp       (x,y) z = Exp(x,y,z)
let fPropArrow (x,y) z = PropArrow(x,y,z)
let fKindArrow (x,y) z = KindArrow(x,y,z)

(****************************************)
(* Substitution functions for Logic.xxx *)
(****************************************)

(** The function [substMXXX m mdl] substitutes mode name (string) [m]
    for model [mdl] *)

let rec substMModel m mdl = function
    (ModelName m') as mdl' -> if m = m' then mdl else mdl'
  | ModelProj (mdl', n) -> ModelProj (substMModel m mdl mdl', n)
  | ModelApp (mdl1, mdl2) -> ModelApp (substMModel m mdl mdl1, substMModel m mdl mdl2)
      
and substMLN m mdl = function
    (LN (None, _)) as ln -> ln
  | LN (Some mdl', nm) -> LN (Some (substMModel m mdl mdl'), nm)
      
and substMSLN m mdl = function
    (SLN (None, _)) as ln -> ln
  | SLN (Some mdl', nm) -> SLN (Some (substMModel m mdl mdl'), nm)
      
and substMProp m mdl p =
  let rec subst = function
      False -> False
    | True -> True
    | Atomic lnm -> Atomic (substMLN m mdl lnm)
    | PApp (p,t) -> PApp (subst p, substMTerm m mdl t)
    | PLambda ((n,s),p) -> PLambda ((n, substMSet m mdl s), subst p)
    | And lst -> And (List.map subst lst)
    | Imply (p, q) -> Imply (subst p, subst q)
    | Iff (p, q) -> Iff (subst p, subst q)
    | Or lst -> Or (List.map subst lst)
    | Forall ((n,s),p) -> Forall ((n, substMSet m mdl s), subst p)
    | Exists ((n,s),p) -> Exists ((n, substMSet m mdl s), subst p)
    | Unique ((n,s),p) -> Unique ((n, substMSet m mdl s), subst p)
    | Not p -> Not (subst p)
    | Equal (s, t, u) -> Equal (substMSet m mdl s, substMTerm m mdl t, substMTerm m mdl u)
  in
    subst p

and substMTerm m mdl t =
  let rec subst = function
      EmptyTuple -> EmptyTuple
    | Var ln -> Var (substMLN m mdl ln)
    | Tuple lst -> Tuple (List.map subst lst)
    | Proj (i,t) -> Proj (i, subst t)
    | App (t, u) -> App (subst t, subst u)
    | Lambda ((n,s), t) -> Lambda ((n, substMSet m mdl s), subst t)
    | The ((n,s), p) -> The ((n, substMSet m mdl s), substMProp m mdl p)
    | Inj (_, None) as t -> t
    | Inj (lbl, Some t) -> Inj (lbl, Some (subst t))
    | Case (t, lst) -> Case (subst t,
			     List.map (function
					   lbl, None, t -> lbl, None, subst t
					 | lbl, Some (n,s), t -> lbl, Some (n, substMSet m mdl s), subst t)
			       lst)
    | RzQuot t -> RzQuot (subst t)
    | RzChoose ((n,s), t, u, s') ->
	RzChoose ((n, substMSet m mdl s), subst t, subst u, substMSet m mdl s')
    | Quot (t, p) -> Quot (subst t, substMProp m mdl p)
    | Choose ((n,s),v,t,u,s') ->
	Choose ((n, substMSet m mdl s), subst v, subst t, subst u, substMSet m mdl s')
    | Let ((n,s), t, u, s') -> Let ((n, substMSet m mdl s), subst t, subst u, substMSet m mdl s')
    | Subin (t, s) -> Subin (subst t, substMSet m mdl s)
    | Subout (t, s) -> Subout (subst t, substMSet m mdl s)
  in
    subst t

and substMSet m mdl s =
  let rec subst = function
      Empty -> Empty
    | Unit -> Unit
    | Basic ln -> Basic (substMSLN m mdl ln)
    | Product lst -> Product (List.map (fun (n,s) -> (n, subst s)) lst)
    | Exp (n, s, t) -> Exp (n, subst s, subst t)
    | Sum lst -> Sum (List.map
			(function lbl, None -> lbl, None | lbl, Some s -> lbl, Some (subst s))
			lst)
    | Subset ((n,s),p) -> Subset((n, subst s), substMProp m mdl p)
    | Rz s -> Rz (subst s)
    | Quotient (s, p) -> Quotient (subst s, substMProp m mdl p)
    | SApp (s, t) -> SApp (subst s, substMTerm m mdl t)
    | SLambda ((n,s), t) -> SLambda ((n, subst s), subst t)
  in
    subst s

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
        | Let ((y,s),t1,t2,s2) -> Let((y,substSet x t s),
                                      sub t1, 
				      if (x=y) then t2 else sub t2,
                                      substSet x t s2)
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

let rec string_of_model = function
    ModelName nm -> string_of_name nm
  | ModelApp (mdl1, mdl2) ->
      string_of_model mdl1 ^ "(" ^ string_of_model mdl2 ^ ")"
  | ModelProj (mdl, lbl) -> string_of_model mdl ^ "." ^ string_of_name lbl

let rec string_of_ln = function
    LN (None, nm) -> string_of_name nm
  | LN (Some mdl, nm) -> (string_of_model mdl) ^ "."  ^ (string_of_name nm)

let rec string_of_sln = function
    SLN (None, nm) -> string_of_name nm
  | SLN (Some mdl, nm) -> (string_of_model mdl) ^ "."  ^ string_of_name nm

let rec string_of_set = function
    Empty -> "empty"
  | Unit -> "unit"
  | Basic lname -> string_of_sln lname
  | Product lst ->
      "(" ^ (String.concat " * "
	       (List.map (
		  function
		      (N(_, Wild), s) -> string_of_set s
		    | (nm, s) -> string_of_name nm ^ " : " ^ string_of_set s) lst)) ^ ")"
  | Exp (nm, s, t) ->
      if isWild nm then
	"(" ^ string_of_set s ^ " -> " ^ string_of_set t ^ ")"
      else
      "((" ^ string_of_name nm ^ " : " ^ (string_of_set s) ^ ") -> " ^ (string_of_set t) ^ ")"
  | Sum lst ->
      "[" ^ (
	String.concat " + " (
	  List.map (function
			lb, None -> lb
		      | lb, Some s -> lb ^ " of " ^ (string_of_set s)
	  ) lst)
      ) ^ "]"

  | Subset _ -> "{... with ...}"
  | Rz s -> "rz " ^ (string_of_set s)
  | Quotient (s, p) -> (string_of_set s) ^ " % (...)"
  | SApp (s, t) -> (string_of_set s) ^ " " ^ (string_of_term t)
  | SLambda ((n,s), t) -> "lam " ^ string_of_name n ^ " : " ^ string_of_set s ^ " . " ^ string_of_set t

and string_of_term trm =
  (let rec toStr = function
      Var(LN(None, nm))  -> string_of_name nm
    | Var(LN(Some mdl, nm)) -> string_of_model mdl ^ "." ^ string_of_name nm
    | EmptyTuple -> "()"
    | Tuple trms -> "(" ^ String.concat ", " (List.map toStr trms) ^ ")"
    | Proj (n, trm) -> toStr trm ^ "." ^ string_of_int n
    | App (trm1, trm2) -> "(" ^ toStr trm1 ^ " " ^ toStr trm2 ^ ")"
    | Inj (lbl, Some trm) -> "(`" ^ lbl ^ " " ^ toStr trm ^ ")"
    | Inj (lbl, None) -> "`" ^ lbl 
    | Case (trm,arms) -> 
	let rec doArm = function
	    (lbl, None, trm) -> lbl ^ " => " ^ toStr trm
	  | (lbl, Some (n,ty), trm) -> 
	      lbl ^ "(" ^ string_of_name n ^ " : " ^ string_of_set ty ^
		") => " ^ toStr trm
	in 
	  "case " ^ toStr trm ^ " of " ^
	    (String.concat "\n| " (List.map doArm arms)) ^ " end"


    | Quot (trm1,prp2) -> "(" ^ toStr trm1 ^ " % " ^ string_of_prop prp2 ^ ")"
    | RzQuot t -> "[" ^ (toStr t) ^ "]"
    | RzChoose (bnd, trm1, trm2, st) -> 
	"let [" ^ string_of_bnd bnd ^ "] = " ^
	string_of_term trm1 ^ " in " ^ string_of_term trm2 ^ " end" ^
	 ": " ^ string_of_set st

    | Choose (bnd, trm1, trm2, trm3, st) -> 
	"let " ^ string_of_bnd bnd ^ " % " ^ string_of_term trm1 ^ " = " ^
	string_of_term trm2 ^ " in " ^ string_of_term trm3 ^ " end" ^
	 ": " ^ string_of_set st
    | Subin(trm, set) -> "(" ^ toStr trm ^ " :> " ^ string_of_set set ^ ")"
    | Subout(trm, set) -> "(" ^ toStr trm ^ " :< " ^ string_of_set set ^ ")"
    | Let(bnd,trm1,trm2,st) ->
	"(let " ^ string_of_bnd bnd ^ " = " ^ toStr trm1 ^
	" in " ^ toStr trm2 ^ " : " ^ string_of_set st  ^ ")"
    | Lambda(bnd,trm) ->
	"(lam " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | The(bnd,prp) ->
	"(the " ^ string_of_bnd bnd ^ " . " ^ string_of_prop prp ^ ")"
  in
    toStr trm)

and string_of_prop prp =
  (let rec toStr = function
      Atomic(LN(None, nm))  -> string_of_name nm
    | Atomic(LN(Some mdl, nm)) -> string_of_model mdl ^ "." ^ string_of_name nm
    | False -> "False"
    | True -> "True"
    | PApp (prp1, trm2) -> "(" ^ toStr prp1 ^ " " ^ string_of_term trm2 ^ ")"
    | And trms -> "(" ^ String.concat " && " (List.map toStr trms) ^ ")"
    | Imply (trm1, trm2) -> "(" ^ toStr trm1 ^ " => " ^ toStr trm2 ^ ")"
    | Iff (trm1, trm2) -> "(" ^ toStr trm1 ^ " <=> " ^ toStr trm2 ^ ")"
    | Or trms -> "(" ^ String.concat " || " (List.map toStr trms) ^ ")"
    | Not trm -> "(not " ^ toStr trm ^ ")"
    | Equal(st,trm1,trm2) -> "(" ^ string_of_term trm1 ^ " = " ^ string_of_term trm2 ^ " : " ^ string_of_set st ^ ")"
    | Forall(bnd,trm) ->
	"(all " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | Exists(bnd,trm) ->
	"(some " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | Unique(bnd,trm) ->
	"(some1 " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | PLambda(bnd,prp) ->
	"(plambda " ^ string_of_bnd bnd ^ " . " ^ toStr prp ^ ")"
  in
    toStr prp)

and string_of_proptype = function
    Prop -> "Prop"
  | StableProp -> "StableProp"
  | EquivProp st -> "EquivProp(" ^ string_of_set st ^ ")"
  | PropArrow(nm, st, pt) -> 
      if isWild nm then
	string_of_set st ^ " -> " ^ string_of_proptype pt
      else 
	"(" ^ string_of_name nm ^ " : " ^ string_of_set st ^ ") -> " ^
	  string_of_proptype pt


and string_of_kind = function
    KindSet -> "KindSet"
  | KindArrow (nm, st, knd) -> 
      if isWild nm then
	string_of_set st ^ " => " ^ string_of_kind knd
      else 
	"(" ^ string_of_name nm ^ " : " ^ string_of_set st ^ ") => " ^
	  string_of_kind knd



and string_of_theory = function
    Theory elts -> "thy\n" ^ string_of_theory_elements elts ^ "end"
  | TheoryName thrynm -> string_of_name thrynm
  | TheoryApp (thry, mdl) -> 
      string_of_theory thry ^ "(" ^ string_of_model mdl ^ ")"
  | TheoryFunctor (mbnd, thry) ->
      "TFunctor " ^ string_of_mbnd mbnd ^ " . " ^ string_of_theory thry

and string_of_theory_element = function
    Set (stnm, knd) -> "set " ^ string_of_name stnm ^ " : " ^ (string_of_kind knd)
  | Let_set (stnm, knd, st) -> 
	  "set " ^ string_of_name stnm ^ " : " ^ string_of_kind knd ^ " = " ^ string_of_set st
  | Predicate (nm, pt) -> 
      "predicate " ^ string_of_name nm ^ " : " ^ string_of_proptype pt
  | Let_predicate (nm, pt, prp) ->
      "predicate " ^ string_of_name nm ^ " : " ^ string_of_proptype pt ^ "  = " ^ string_of_prop prp
  | Value (nm, st) ->
      "const " ^ string_of_name nm ^ " : " ^ string_of_set st
  | Let_term (nm, st, trm) -> 
      "let " ^ string_of_name nm ^ " : " ^ string_of_set st ^ " = " ^ string_of_term trm
  | Sentence (ssort, nm, mbnds, bnds, prp) ->
      "axiom  " ^ string_of_name nm ^ " " ^ 
      string_of_mbnds mbnds ^ " " ^ string_of_bnds bnds ^ " =\n " ^
      string_of_prop prp
  | Model (mdlnm, thry) -> 
      "model " ^ string_of_name mdlnm ^ " : " ^ string_of_theory thry
  | Comment strng -> 
      "(* " ^ strng ^ " *)"

and string_of_theory_elements = function
    [] -> ""
  | elt :: elts -> string_of_theory_element elt ^ "\n" ^ 
                   string_of_theory_elements elts

and string_of_mbnd = function
        (mdlnm, thry) -> string_of_name mdlnm ^ " : " ^ string_of_theory thry

and string_of_mbnds = function
    [] -> ""
  | [mbnd] -> string_of_mbnd mbnd
  | mbnd :: mbnds -> string_of_mbnd mbnd ^ " " ^ string_of_mbnds mbnds

and string_of_bnd = function
     (name, set) -> "(" ^ string_of_name name  ^  ":"  ^  string_of_set set ^ ")"

and string_of_bnds = function
    [] -> ""
  | [bnd] -> string_of_bnd bnd
  | bnd :: bnds -> string_of_bnd bnd ^ " " ^ string_of_bnds bnds

let string_of_toplevel = function
    Theorydef (thrynm, thry) -> 
      "theory " ^ string_of_name thrynm ^ " = " ^ string_of_theory thry
  | TopComment strng ->
      "(* " ^ strng ^ " *)"
  | TopModel (mdlnm, thry) ->
      "model " ^ string_of_name mdlnm ^ " = " ^ string_of_theory thry


(** *** *)

let rename = function
  | "<" -> "_less"
  | ">" -> "_greater"
  | "<=" -> "_leq"
  | ">=" -> "_geq"
  | "=" -> "_equal"
  | "<>" -> "_neq"
  | str -> begin
      let names =
	[('!',"_bang"); ('$',"_dollar"); ('%',"_percent");
	 ('&',"_and"); ('*',"_star"); ('+',"_plus");
	 ('-',"_minus"); ('.',"_dot"); ('/',"_slash");
	 (':',"_colon"); ('<',"_less"); ('=',"_equal");
	 ('>',"_greater"); ('?',"_question"); ('@',"_at");
	 ('^',"_carat"); ('|',"_vert"); ('~',"_tilde")] in
      let n = String.length str in
      let rec map i =
	if i < n then (List.assoc str.[i] names) ^ (map (i+1)) else ""
      in
	try map 0 with Not_found -> failwith "Logic.rename: unexpected character"
    end

let typename_of_name = function
    N(_, Word) as nm -> nm
  | N(str, _) -> N(rename str, Word)

let typename_of_ln = function
    LN (_, N(_, Word)) as n -> n
  | LN (mdl, N(p, _)) -> LN (mdl, N(rename p, Word))

let sln_of_ln (LN (mdl, nm)) = SLN (mdl, typename_of_name nm)

let longname_of_name nm = LN(None, nm)
let set_longname_of_name nm = SLN(None, nm)
let model_name_of_name = function
    N(strng, Word) as nm -> nm
  | nm -> (print_string "Cannot treat the name ";
	   print_string (string_of_name nm);
	   print_string " as a model name.";
	   raise Impossible)



let joinProperPropType p1 p2 = 
  begin
    match (p1,p2) with
	(StableProp, StableProp) -> StableProp
      | ((Prop | StableProp), (Prop | StableProp)) -> Prop
      | _ -> failwith "joinProperPropType only allows Prop and StableProp!"
  end

let joinProperPropTypes lst = List.fold_left joinProperPropType StableProp lst


let rec fnSet = function
    Empty | Unit  -> NameSet.empty
  | Basic (SLN(None, nm)) -> NameSet.singleton nm
  | Basic (SLN(Some mdl, _)) -> fnModel mdl
  | Product noss -> fnProduct noss
  | Sum lsos     -> fnSum lsos
  | Exp (nm, st1, st2) ->
      NameSet.union (fnSet st1) (NameSet.remove nm (fnSet st2))
  | SLambda ((nm, st1), st2) -> 
      NameSet.union (fnSet st1) (NameSet.remove nm (fnSet st2))
  | Subset((nm, st), prp) -> 
      NameSet.union (fnSet st) (NameSet.remove nm (fnProp prp))
  | Quotient(st, prp) ->
      NameSet.union (fnSet st) (fnProp prp)
  | SApp(st, trm) -> NameSet.union (fnSet st) (fnTerm trm)
  | Rz st -> fnSet st	
      
and fnSetOpt = function
	  None -> NameSet.empty
	| Some st -> fnSet st
	
and fnProduct = function
    [] -> NameSet.empty
  | (nm, st)::rest -> NameSet.union (fnSet st) (NameSet.remove nm (fnProduct rest))
	
and fnSum = function	 
    [] -> NameSet.empty
  | (_, stOpt)::rest -> NameSet.union (fnSetOpt stOpt) (fnSum rest)

and fnKind = function
    KindSet -> NameSet.empty
  | KindArrow(nm, st, knd) -> NameSet.union (fnSet st) (NameSet.remove nm (fnKind knd))
      
and fnTerm = function
    EmptyTuple | Inj(_, None)-> NameSet.empty
  | Var(LN(None, nm)) -> NameSet.singleton nm
  | Var(LN(Some mdl, nm)) -> NameSet.add nm (fnModel mdl)
  | Subin(trm, st) 
  | Subout(trm, st) -> NameSet.union (fnTerm trm) (fnSet st) 
  | Tuple trms -> unionNameSetList (List.map fnTerm trms)
  | Proj(_, trm) 
  | Inj(_, Some trm)
  | RzQuot trm -> fnTerm trm
  | App(trm1, trm2) -> NameSet.union (fnTerm trm1) (fnTerm trm2)
  | Quot(trm1, prp2) -> NameSet.union (fnTerm trm1) (fnProp prp2)
  | Choose((nm, st1), trm1, trm2, trm3, st2) ->
      unionNameSetList [fnSet st1; fnTerm trm1; fnTerm trm2;
		        NameSet.remove nm (fnTerm trm3); fnSet st2]
  | RzChoose ((nm, st1), trm1, trm2, st2) 
  | Let ((nm, st1), trm1, trm2, st2) -> 
      unionNameSetList [fnSet st1; fnTerm trm1; 
		        NameSet.remove nm (fnTerm trm2); fnSet st2]
  | Lambda((nm, st), trm) ->
      NameSet.union (fnSet st) (NameSet.remove nm (fnTerm trm))
  | The((nm, st), prp) ->
      NameSet.union (fnSet st) (NameSet.remove nm (fnProp prp))
  | Case (trm, arms) ->
      NameSet.union (fnTerm trm) (unionNameSetList (List.map fnCaseArm arms))

and fnProp = function
    False | True -> NameSet.empty
  | Atomic(LN(None, nm)) -> NameSet.singleton nm
  | Atomic(LN(Some mdl, nm)) -> fnModel mdl
  | And prps
  | Or prps -> unionNameSetList (List.map fnProp prps)
  | Not prp -> fnProp prp
  | Imply(prp1, prp2)
  | Iff(prp1, prp2) -> NameSet.union (fnProp prp1) (fnProp prp2)
  | Equal(st, trm1, trm2) -> 
      unionNameSetList [fnSet st; fnTerm trm1; fnTerm trm2]
  | PApp(prp, trm) -> NameSet.union (fnProp prp) (fnTerm trm)
  | PLambda((nm, st), prp)
  | Forall((nm, st), prp)
  | Exists((nm, st), prp)
  | Unique((nm, st), prp) -> 
      NameSet.union (fnSet st) (NameSet.remove nm (fnProp prp))

and fnCaseArm = function
    (_, None, trm) -> fnTerm trm
  | (_, Some (nm, st), trm) -> 
      NameSet.union (fnSet st) (NameSet.remove nm (fnTerm trm))
   
	
and fnModel = function
    ModelName nm -> NameSet.singleton nm
  | ModelProj (mdl, _) -> fnModel mdl
  | ModelApp (mdl1, mdl2) -> NameSet.union (fnModel mdl1) (fnModel mdl2)

(* Substitution functions. *)

type subst = {terms: term NameMap.t;
              sets: set NameMap.t;
	      props : proposition NameMap.t;
              models: model NameMap.t;
              capturablenames: NameSet.t}

let emptysubst = {terms = NameMap.empty;
		  props = NameMap.empty;
		  sets = NameMap.empty;
		  models = NameMap.empty;
		  capturablenames = NameSet.empty}

let insertTermvar sbst nm trm =
  {sbst with terms = NameMap.add nm trm sbst.terms;
     capturablenames = NameSet.union sbst.capturablenames (fnTerm trm)}

let insertPropvar sbst nm prp =
  {sbst with props = NameMap.add nm prp sbst.props;
     capturablenames = NameSet.union sbst.capturablenames (fnProp prp)}

let insertSetvar sbst nm st =
  {sbst with sets = NameMap.add nm st sbst.sets;
	 capturablenames = NameSet.union sbst.capturablenames (fnSet st)}
	
let insertModelvar sbst strng mdl =
  {sbst with models = NameMap.add strng mdl sbst.models;
	 capturablenames = NameSet.union sbst.capturablenames (fnModel mdl)}

let getTermvar sbst nm =
   try (NameMap.find nm sbst.terms) with
       Not_found -> Var (LN (None, nm))

let getPropvar sbst nm =
   try (NameMap.find nm sbst.props) with
       Not_found -> Atomic (LN (None, nm))

let getSetvar sbst stnm =
   try (NameMap.find stnm sbst.sets) with 
       Not_found -> Basic (SLN(None, stnm))

let getModelvar sbst mdlnm =
   try (NameMap.find mdlnm sbst.models) with 
       Not_found -> ModelName mdlnm

let display_subst sbst =
  let do_term nm trm = print_string ("[" ^ string_of_name nm ^ "~>" ^ 
					string_of_term trm ^ "]")
  in let do_set stnm st = print_string ("[" ^ string_of_name stnm ^ "~>" ^ 
					   string_of_set st ^ "]")
  in let do_model mdlnm mdl = print_string ("[" ^ string_of_name mdlnm ^ "~>" ^ 
					       string_of_model mdl ^ "]")
  in  (print_string "Terms: ";
       NameMap.iter do_term sbst.terms;
       print_string "\nSets: ";
       NameMap.iter do_set sbst.sets;
       print_string "\nSets: ";
       NameMap.iter do_model sbst.models)
   
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
		      (insertTermvar sbst nm (Var (LN (None,nm'))), nm')
	  in search (nextName nm)
	else 
	  (sbst, nm)

let rec subst (substitution : subst) =
	 
     let rec sub = function
         EmptyTuple -> EmptyTuple
       | Var (LN (None, nm)) -> getTermvar substitution nm
       | Var (LN (Some mdl, nm)) -> 
	   Var( LN(Some(substModel substitution mdl), nm) )
       | Tuple ts      -> Tuple(List.map sub ts)
       | Proj(n,t1)    -> Proj(n, sub t1)
       | App(t1,t2)    -> App(sub t1, sub t2)
       | Inj(l,termopt) -> Inj(l, substTermOption substitution termopt)
       | Case(t1,arms) -> Case(t1,subarms arms)
       | RzQuot t -> RzQuot (sub t)
       | RzChoose ((y,sopt),t1,t2,ty) ->
	   let (sbst', y') = updateBoundName substitution y in
	     RzChoose ((y', substSet substitution sopt),
		      sub t1,
		      subst sbst' t2,
		      substSet substitution ty)
        | Quot(trm1,prp2) -> Quot(sub trm1, substProp substitution prp2)
        | Choose((y,sopt),trm_equiv,t1,t2,stopt2) ->
	    let (sbst', y') = updateBoundName substitution y in
              Choose((y',substSet substitution sopt),
                    sub trm_equiv,
                    sub t1, 
                    subst sbst' t2,
		    substSet substitution stopt2)
        | Subin(trm,st) -> Subin(sub trm, substSet substitution st)
        | Subout(trm,st) -> Subout(sub trm, substSet substitution st)
        | Let((y,stopt),t1,t2,stopt2) ->
	    let (sbst', y') = updateBoundName substitution y in
            Let((y',substSet substitution stopt),
               sub t1, 
	       subst sbst' t2,
	       substSet substitution stopt2)
	

	| Lambda((y,sopt),t1) ->
	    let (sbst', y') = updateBoundName substitution y in 
	      Lambda((y',substSet substitution sopt),
		    subst sbst' t1)
	| The((y,sopt), prp) ->
	    let (sbst', y') = updateBoundName substitution y in 
	      The((y',substSet substitution sopt),
		    substProp sbst' prp)
        

     and subarms = function
          [] -> []
        | (l,None,t)::rest -> (l,None, sub t)::(subarms rest)
        | (l,Some(y,sopt),u)::rest ->
	    let (sbst',y') = updateBoundName substitution y in
              (l, Some(y', substSet substitution sopt), subst sbst' u) ::
	      (subarms rest)
     in sub

and substProp substitution = 
  let rec sub = function
      True -> True
    | False -> False
    | Atomic (LN (None, nm)) -> getPropvar substitution nm
    | Atomic (LN (Some mdl, nm)) -> 
	Atomic( LN(Some(substModel substitution mdl), nm) )
    | And ts        -> And(List.map sub ts)
    | Imply(t1,t2)  -> Imply(sub t1, sub t2)
    | Iff(t1,t2)    -> Iff(sub t1, sub t2)
    | Or ts         -> Or(List.map sub ts)
    | Not t         -> Not(sub t)
    | Equal(ty,t1,t2) -> Equal(substSet substitution ty,
                               subst substitution t1,
			       subst substitution t2)
    | Forall((y,sopt),t1) ->
	let (sbst', y') = updateBoundName substitution y in 
          Forall((y',substSet substitution sopt),
		substProp sbst' t1)
    | Exists((y,sopt),t1) ->
	let (sbst', y') = updateBoundName substitution y in 
	  Exists((y',substSet substitution sopt),
		substProp sbst' t1)
    | Unique((y,sopt),t1) ->
	let (sbst', y') = updateBoundName substitution y in 
	  Unique((y',substSet substitution sopt),
		substProp sbst' t1)
    | PLambda((y,sopt),t1) ->
	let (sbst', y') = updateBoundName substitution y in 
	  PLambda((y',substSet substitution sopt),
		 substProp sbst' t1)
    | PApp(prp1,trm2) -> PApp(sub prp1, subst substitution trm2)
  in sub
      

and substSet substitution =
     let rec sub = function
	   Unit -> Unit
	 | Empty -> Empty
         | Basic (SLN (None, stnm)) -> 
	     getSetvar substitution stnm
         | Basic (SLN (Some mdl, stnm)) -> 
	     Basic (SLN (Some (substModel substitution mdl), stnm))
         | Product ss -> Product (substProd substitution ss)
         | Exp(y, s1, s2) ->
	    let (sbst', y') = updateBoundName substitution y in 
              Exp(y', sub s1, substSet sbst' s2)
         | Subset((y,sopt),u) ->
	     let (sbst', y') = updateBoundName substitution y in 
               Subset((y',substSet substitution sopt),
  	         substProp sbst' u)
         | Quotient(st,prp)   -> 
              Quotient(sub st, substProp substitution prp)
	 | Rz st -> Rz (sub st)
	 | SApp(st1,trm2) -> SApp(sub st1, subst substitution trm2)
	 | Sum lsos ->
	     let f (l, so) = (l, substSetOption substitution so)
	     in Sum (List.map f lsos)
         | SLambda((y,st),u) ->
	     let (sbst', y') = updateBoundName substitution y in 
               SLambda((y',substSet substitution st),
  	              substSet sbst' u)

     and substProd sbst = function
	 [] -> []
       | (y,st)::rest -> 
	   let (sbst', y') = updateBoundName sbst y in 
	   (y', substSet sbst st) :: (substProd sbst' rest)


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
    KindArrow(y, st, k) -> 
      let (sbst', y') = updateBoundName substitution y in
	KindArrow(y', substSet substitution st, substKind sbst' k)
  | KindSet -> KindSet

and substProptype substitution = function
    Prop -> Prop
  | StableProp -> StableProp
  | EquivProp ty -> EquivProp (substSet substitution ty)
  | PropArrow(y,st,prpty) ->
      let (sbst', y') = updateBoundName substitution y in
	PropArrow(y', substSet substitution st, substProptype sbst' prpty)
      
let rec substTheory substitution = function 
      Theory elts       -> Theory (substTheoryElts substitution elts)
    | TheoryName thrynm -> TheoryName thrynm
    | TheoryFunctor ((y, thry1), thry2) ->
	let (sbst',y') = updateBoundName substitution y in
	  TheoryFunctor((y, substTheory substitution thry1),
		        substTheory sbst' thry2)
    | TheoryApp (thry, mdl) ->
	TheoryApp (substTheory substitution thry,  
		   substModel substitution mdl)

and substTheoryElts _ = raise Unimplemented

(* Can't implement this correctly without an outer label / inner variable
   distinction. :( *)


(*
    sub = function ->
    [] -> []
  | Set (stnm, knd) :: rest ->
      (Set (stnm, substKind sub knd)) :: (substTheoryElts sub rest)
  | Let_set (setnm, knd, st) :: rest ->
      (Let_set (setnm, substKind sub knd, substSet sub st)) :: 
	(substTheoryElts sub rest)
  | Predicate (nm, pt) :: rest -> 
       let this' = Predicate (nm, substProptype sub pt, substSet sub st)
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Let_predicate (nm, prpty, prp) :: rest -> 
       let this' = Let_predicate (nm, substProptype sub pt, substProp sub prp)
       in let rest' = substTheoryElts sub rest
       in this' :: rest'
  | Let_term (nm, st, trm) :: rest ->
       let ((nm, st'), sub_b) = substBnd sub (nm, st)
       in let this' = Let_term (nm, st', subst sub_b trm)
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
*)

