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
    | ModelName of model_name
    | ModelProj of model * model_name
    | ModelApp of model * model

(** names of components inside models *)
and longname = LN of model option * name

(** short names of sets *)
and set_name = name

(** long names of sets *)
and set_longname = SLN of model option * set_name

(** names of theories *)
and theory_name = S.theory_name

(** sorts of sentences *)
and sentence_type = S.sentence_type

(** a binding in a quantifier or lambda *)
and binding = name * set

(** a binding in a parameterized theory *)
and model_binding = model_name * theory
    
(** first-order proposition *)
and proposition =
    | False
    | True
    | Atomic  of longname * proptype
    | And     of proposition list
    | Imply   of proposition * proposition
    | Iff     of proposition * proposition
    | Or      of (label * proposition) list
    | Forall  of binding * proposition
    | Exists  of binding * proposition
    | Unique  of binding * proposition
    | Not     of proposition
    | Equal   of set * term * term
    | PApp    of proposition * term
    | PLambda of binding * proposition
    | IsEquiv of proposition * set                (* [IsEquiv(p,s)] means [p] is an equivalence relation on [s] *)
    | PCase   of term * set * (label * binding option * proposition) list
    | PLet    of binding * term * proposition (* Propositional let-term *)
    | PBool   of term   (* Embedding of boolean terms *)
    | PIdentityCoerce of proposition * proptype * proptype * proposition list 
  
and set =
    | Empty
    | Unit  (* Unit is the singleton containing EmptyTuple *)
    | Bool  (* Decidable propositions *)
    | Basic    of set_longname * setkind
    | Product  of binding list
    | Exp      of name * set * set
    | Sum      of (label * set option) list
    | Subset   of binding * proposition
    | Rz       of set (* the set of realizers *)
    | Quotient of set * proposition
    | SApp     of set * term
    | SLambda  of binding * set

and proptype =
    | Prop
    | StableProp
    | EquivProp of set
    | PropArrow of name * set * proptype

and setkind =
    | KindSet
    | KindArrow of name * set * setkind

and term =
    | EmptyTuple
    | BConst   of bool
    | BNot     of term
    | BOp      of bop * term list
    | Var      of longname
    | Tuple    of term list
    | Proj     of int * term
    | App      of term * term
    | Lambda   of binding  * term
    | The      of binding  * proposition (* description operator *)
    | Inj      of label * term option * set  (* Annotated with the sum type *)
    | Case     of term * set * (label * binding option * term) list * set
    | RzQuot   of term
    | RzChoose of binding * term * term * set
    | Quot     of term * proposition
    | Choose   of binding * proposition * term * term * set
    | Let      of binding * term * term * set  (* set is type of the whole let *)
    | Subin    of term * binding * proposition (* [Subin(a,(x,t),p)] coerces [a] to [{x:t|p}] *)
    | Subout   of term * set
    | IdentityCoerce of term * set * set * proposition list (* from first set to second set, which are supposed to be equal except we can't check it. *)

and bop = AndOp | OrOp | ImplyOp | IffOp

and declaration =
    DeclProp     of proposition option * proptype
  | DeclSet      of set option         * setkind
  | DeclTerm     of term option        * set
  | DeclModel    of                      theory
  | DeclTheory   of theory             * theorykind
  | DeclSentence of model_binding list * proposition

and theory_element =
    | Declaration of name * declaration
    | Comment of string

and theory = 
    | Theory of theory_element list
    | TheoryName of theory_name
    | TheoryLambda of model_binding * theory   (* Family of theories *)
    | TheoryArrow of model_binding * theory    (* Theory of a family of models *)
    | TheoryApp of theory * model
    | TheoryProj of model * name
  
and theorykind =
    | ModelTheoryKind    (* Kind of theories that classify models,
              including classifiersfor families of models. *)
    | TheoryKindArrow of model_binding * theorykind (* Classifies TheoryLambdas *)

and toplevel =
    Theorydef of theory_name * theory
  | TopComment of string
  | TopModel  of model_name * theory


(** Helper function to determined stability of a proptype. *)
let rec is_stable = function
    Prop -> false
  | StableProp -> true
  | EquivProp _ -> true
  | PropArrow (_, _, pt) -> is_stable pt

let rec is_equiv = function
    Prop -> false
  | StableProp -> false
  | EquivProp _ -> true
  | PropArrow (_, _, pt) -> is_equiv pt

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
let fImply x y = Imply(x,y)
let fPBool x = PBool(x)

  (* Hack because Exp, PropArrow and KindArrow take a binding semantically,
     but not syntactically *)
let fExp       (x,y) z = Exp(x,y,z)
let fPropArrow (x,y) z = PropArrow(x,y,z)
let fKindArrow (x,y) z = KindArrow(x,y,z)
let fEquivProp x = EquivProp x

(************************)
(* Random useful things *)
(************************)

let foldTheoryArrow bnds bdy = 
  List.fold_right (fun mbnd thry -> TheoryArrow (mbnd, thry)) bnds bdy

let foldTheoryLambda bnds bdy = 
  List.fold_right (fun mbnd thry -> TheoryLambda (mbnd, thry)) bnds bdy

let foldTheoryKindArrow bnds bdy = 
  List.fold_right (fun mbnd thry -> TheoryKindArrow (mbnd, thry)) bnds bdy

let doOpt funct = function
    None -> None
  | Some v -> Some (funct v)


(* Oops...this optimization isn't meaning preserving unless we can
   guarantee that ty is inhabited.  Too bad.

let foldForall =
  let maybeForall  (nm,ty) prp = 
    if isWild nm then prp else Forall((nm,ty), prp)
  in List.fold_right maybeForall
*)

let foldForall = 
  List.fold_right fForall

let foldImply = 
  List.fold_right fImply

let maybeIdentityCoerce trm ty1 ty2 reqs = 
  match reqs with
      [] -> trm
    | reqs -> IdentityCoerce(trm, ty1, ty2, reqs)

let maybePIdentityCoerce prp pt1 pt2 reqs = 
  match reqs with
      [] -> prp
    | reqs -> PIdentityCoerce(prp, pt1, pt2, reqs)

let set_of_name nm knd = Basic(SLN(None, nm), knd)
let term_of_name nm = Var(LN(None, nm))
let prop_of_name nm pt = Atomic(LN(None, nm), pt)
let model_of_name nm = ModelName nm
let theory_of_name nm = TheoryName nm

(****************************************)
(** (Not-Very)-Pretty-Printing Routines *)
(****************************************)

let string_of_label = S.string_of_label

let rec string_of_model = function
    ModelName nm -> string_of_name nm
  | ModelApp (mdl1, mdl2) ->
      string_of_model mdl1 ^ "(" ^ string_of_model mdl2 ^ ")"
  | ModelProj (mdl, nm) -> string_of_model mdl ^ "." ^ string_of_name nm

and string_of_ln = function
    LN (None, nm) -> string_of_name nm
  | LN (Some mdl, nm) -> (string_of_model mdl) ^ "."  ^ (string_of_name nm)

and string_of_sln = function
    SLN (None, nm) -> string_of_name nm
  | SLN (Some mdl, nm) -> (string_of_model mdl) ^ "."  ^ string_of_name nm

and string_of_set = function
    Empty -> "empty"
  | Unit -> "unit"
  | Bool -> "bool"
  | Basic (lname, _) -> string_of_sln lname
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

  | Subset ((n,s), p) -> 
      "{" ^ string_of_name n ^ " : " ^ string_of_set s ^ " with " ^ 
  string_of_prop p ^ "}"
  | Rz s -> "rz " ^ (string_of_set s)
  | Quotient (s, p) -> (string_of_set s) ^ " % " ^ string_of_prop p
  | SApp (s, t) -> (string_of_set s) ^ " " ^ (string_of_term t)
  | SLambda ((n,s), t) -> "lam " ^ string_of_name n ^ " : " ^ string_of_set s ^ " . " ^ string_of_set t

and string_of_bop = function
      AndOp -> " && "
    | OrOp -> " || "
    | ImplyOp -> " -> "
    | IffOp -> " <-> "

and string_of_term trm =
  (let rec toStr = function
      Var(LN(None, nm))  -> string_of_name nm
    | Var(LN(Some mdl, nm)) -> string_of_model mdl ^ "." ^ string_of_name nm
    | EmptyTuple -> "()"
    | BConst true -> "true"
    | BConst false -> "false"
    | BNot trm -> "not " ^ toStr trm
    | BOp (bop, trms) -> 
          "(" ^ String.concat (string_of_bop bop) (List.map toStr trms) ^ ")"
    | Tuple trms -> "(" ^ String.concat ", " (List.map toStr trms) ^ ")"
    | Proj (n, trm) -> toStr trm ^ "." ^ string_of_int n
    | App (trm1, trm2) -> "(" ^ toStr trm1 ^ " " ^ toStr trm2 ^ ")"
    | Inj (lbl, Some trm, ty) -> "(`" ^ lbl ^ " " ^ toStr trm ^ " : " ^ 
	string_of_set ty ^ ")"
    | Inj (lbl, None, ty) -> "(" ^ "`" ^ lbl ^ " : " ^ string_of_set ty ^ ")"
    | Case (trm,ty',arms,ty'') -> 
	let rec doArm = function
	    (lbl, None, trm) -> lbl ^ " => " ^ toStr trm
	  | (lbl, Some (n,ty), trm) -> 
              lbl ^ "(" ^ string_of_name n ^ " : " ^ string_of_set ty ^
		") => " ^ toStr trm
	in 
	  "case " ^ toStr trm ^ " : " ^ string_of_set ty' ^ " of " ^
	    (String.concat "\n| " (List.map doArm arms)) ^ " end" ^
	    ": " ^ string_of_set ty''

    | Quot (trm1,prp2) -> "(" ^ toStr trm1 ^ " % " ^ string_of_prop prp2 ^ ")"
    | RzQuot t -> "[" ^ (toStr t) ^ "]"
    | RzChoose (bnd, trm1, trm2, st) -> 
	"let rz " ^ string_of_bnd bnd ^ " = " ^
	  string_of_term trm1 ^ " in " ^ string_of_term trm2 ^ 
	  ": " ^ string_of_set st ^ " end"
	  
    | Choose (bnd, prp1, trm2, trm3, st) -> 
	"let [" ^ string_of_bnd bnd ^ "] % " ^ string_of_prop prp1 ^ " = " ^
	  string_of_term trm2 ^ " in " ^ string_of_term trm3 ^ 
	  ": " ^ string_of_set st ^ " end" 
    | Subin(trm, bnd, prp) -> "(" ^ toStr trm ^ " :> {" ^ string_of_bnd bnd ^ " | " ^ string_of_prop prp ^ "})"
    | Subout(trm, set) -> "(" ^ toStr trm ^ " :< " ^ string_of_set set ^ ")"
    | Let(bnd,trm1,trm2,st) ->
	"(let " ^ string_of_bnd bnd ^ " = " ^ toStr trm1 ^
	  " in " ^ toStr trm2 ^ " : " ^ string_of_set st  ^ ")"
    | Lambda(bnd,trm) ->
	"(lam " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | The(bnd,prp) ->
	"(the " ^ string_of_bnd bnd ^ " . " ^ string_of_prop prp ^ ")"
    | IdentityCoerce(trm, ty1, ty2, _) ->
	"(" ^ toStr trm ^ " : " ^ string_of_set ty1 ^ " ~> " ^
	  string_of_set ty2 ^ ")"
  in
    toStr trm)

and string_of_prop prp =
  (let rec toStr = function
      Atomic(LN(None, nm), _)  -> string_of_name nm
    | Atomic(LN(Some mdl, nm), _) -> string_of_model mdl ^ "." ^ string_of_name nm
    | False -> "False"
    | True -> "True"
    | PApp (prp1, trm2) -> "(" ^ toStr prp1 ^ " " ^ string_of_term trm2 ^ ")"
    | And prps -> "(" ^ String.concat " && " (List.map toStr prps) ^ ")"
    | Imply (prp1, prp2) -> "(" ^ toStr prp1 ^ " => " ^ toStr prp2 ^ ")"
    | Iff (prp1, prp2) -> "(" ^ toStr prp1 ^ " <=> " ^ toStr prp2 ^ ")"
    | Or trms ->
  "(" ^ String.concat " \\/ " (List.map (fun (lbl, trm) -> lbl ^ ":" ^ toStr trm) trms) ^ ")"
    | Not trm -> "(not " ^ toStr trm ^ ")"
    | Equal(st,trm1,trm2) -> "(" ^ string_of_term trm1 ^ " =" ^ string_of_set st ^ "= " ^ string_of_term trm2 ^ ")"
    | Forall(bnd,trm) ->
	"(all " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | Exists(bnd,trm) ->
	"(some " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | Unique(bnd,trm) ->
	"(some1 " ^ string_of_bnd bnd ^ " . " ^ toStr trm ^ ")"
    | PLambda(bnd,prp) ->
	"(plambda " ^ string_of_bnd bnd ^ " . " ^ toStr prp ^ ")"
    | IsEquiv (prp, st) ->
	"IsEquiv(" ^ toStr prp ^ " on " ^ string_of_set st ^ ")"
    | PCase (trm, ty', arms) -> 
	let rec doArm = function
	    (lbl, None, prp) -> lbl ^ " => " ^ toStr prp
	  | (lbl, Some (n,ty), prp) -> 
              lbl ^ "(" ^ string_of_name n ^ " : " ^ string_of_set ty ^
		") => " ^ toStr prp
	in 
	  "case " ^ string_of_term trm ^ " : " ^ string_of_set ty' ^ " of " ^
	    (String.concat "\n| " (List.map doArm arms)) ^ " end"
    | PLet ((n,s), t, p) ->
	"let " ^ string_of_name n ^ ":" ^ string_of_set s ^ " = " ^ 
	  string_of_term t ^ " in " ^ toStr p ^ " end"
    | PBool trm -> "PBOOL(" ^ string_of_term trm ^ ")" 
    | PIdentityCoerce(prp, pt1, pt2, _) ->
	"(" ^ toStr prp ^ " : " ^ string_of_proptype pt1 ^ " :> " ^
	  string_of_proptype pt2 ^ ")"

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
  | TheoryLambda (mbnd, thry) ->
      "TLambda " ^ string_of_mbnd mbnd ^ " . " ^ string_of_theory thry
  | TheoryArrow (mbnd, thry) ->
      "TArrow " ^ string_of_mbnd mbnd ^ " . " ^ string_of_theory thry
  | TheoryProj (mdl, nm) ->
      string_of_model mdl ^ "." ^ string_of_name nm

and string_of_theory_element = function
    Declaration(stnm, DeclSet(None, knd)) ->
      "set " ^ string_of_name stnm ^ " : " ^ (string_of_kind knd)
  | Declaration(stnm, DeclSet(Some st, knd)) -> 
    "set " ^ string_of_name stnm ^ " : " ^ string_of_kind knd ^ " = " ^ string_of_set st
  | Declaration(nm, DeclProp(None, pt)) ->
      "predicate " ^ string_of_name nm ^ " : " ^ string_of_proptype pt
  | Declaration(nm, DeclProp(Some prp, pt)) ->
      "predicate " ^ string_of_name nm ^ " : " ^ string_of_proptype pt ^ "  = " ^ string_of_prop prp
  | Declaration(nm, DeclTerm(None, st)) ->
      "const " ^ string_of_name nm ^ " : " ^ string_of_set st
  | Declaration(nm, DeclTerm(Some trm, st)) ->
      "let " ^ string_of_name nm ^ " : " ^ string_of_set st ^ " = " ^ string_of_term trm
  | Declaration(nm, DeclSentence (mbnds, prp)) ->
      "axiom  " ^ string_of_name nm ^ " " ^ string_of_mbnds mbnds ^ " =\n " ^ string_of_prop prp
  | Declaration(nm, DeclModel(thry)) -> 
      "model " ^ string_of_name nm ^ " : " ^ string_of_theory thry
  | Declaration(nm, DeclTheory(thry, theorykind)) -> 
      "theory " ^ string_of_name nm ^ " = " ^ string_of_theory thry
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


let typename_of_name = function
    N (_, Word) as nm -> nm
  | N (str, _) -> N (makeTypename str, Word)
  | G (k, lst) -> 
      Name.gensym (List.map
        (function
      (_, Word) as nm -> nm
          | (str, _) -> (makeTypename str, Word))
        lst)

let prop_typename_of_name = function
    N (p, Word) -> N ("ty_" ^ p, Word)
  | N (str, _) -> N (makeTypename str, Word)
  | G (k, lst) -> 
      Name.gensym (List.map
        (function
      (p, Word) -> ("ty_" ^ p, Word)
          | (str, _) -> (makeTypename str, Word))
        lst)

let typename_of_ln (LN (mdl, nm)) = LN (mdl, typename_of_name nm)

let sln_of_ln (LN (mdl, nm)) = SLN (mdl, typename_of_name nm)

let longname_of_name nm = LN(None, nm)
let set_longname_of_name nm = SLN(None, nm)

let model_name_of_name nm =
  if validModelName nm then
    nm
  else 
    (print_string "Cannot treat the name ";
     print_string (string_of_name nm);
     print_string " as a model name.";
     raise Impossible)


let theory_name_of_name = model_name_of_name


(***********************************)
(** Free-variable (name) functions *)
(***********************************)

let fnOpt fnFun = function
    None -> NameSet.empty
  | Some x -> fnFun x

let rec fnSet = function
  | Empty | Unit | Bool -> NameSet.empty
  | Basic (SLN(None, nm), knd) -> NameSet.union (NameSet.singleton nm) (fnSetkind knd)
  | Basic (SLN(Some mdl, _), knd) -> NameSet.union (fnModel mdl) (fnSetkind knd)
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

and fnSetkind = function
    KindSet -> NameSet.empty
  | KindArrow(nm, st, knd) -> NameSet.union (fnSet st) (NameSet.remove nm (fnSetkind knd))
      
and fnTerm = function
  | EmptyTuple | BConst _ -> NameSet.empty
  | BNot trm -> fnTerm trm
  | Var(LN(None, nm)) -> NameSet.singleton nm
  | Var(LN(Some mdl, nm)) -> NameSet.add nm (fnModel mdl)
  | Subin(trm, (nm,st), prp) ->
      NameSet.union (fnTerm trm) 
         (NameSet.union (fnSet st) (NameSet.remove nm (fnProp prp)))
  | Subout(trm, st) -> NameSet.union (fnTerm trm) (fnSet st) 
  | Inj(_, None, st) -> fnSet st
  | BOp(_,trms)
  | Tuple trms -> unionNameSetList (List.map fnTerm trms)
  | Proj(_, trm) 
  | RzQuot trm -> fnTerm trm
  | Inj(_, Some trm, st) -> NameSet.union (fnTerm trm) (fnSet st)
  | App(trm1, trm2) -> NameSet.union (fnTerm trm1) (fnTerm trm2)
  | Quot(trm1, prp2) -> NameSet.union (fnTerm trm1) (fnProp prp2)
  | Choose((nm, st1), prp1, trm2, trm3, st2) ->
      unionNameSetList [fnSet st1; fnProp prp1; fnTerm trm2;
            NameSet.remove nm (fnTerm trm3); fnSet st2]
  | RzChoose ((nm, st1), trm1, trm2, st2) 
  | Let ((nm, st1), trm1, trm2, st2) -> 
      unionNameSetList [fnSet st1; fnTerm trm1; 
            NameSet.remove nm (fnTerm trm2); fnSet st2]
  | Lambda((nm, st), trm) ->
      NameSet.union (fnSet st) (NameSet.remove nm (fnTerm trm))
  | The((nm, st), prp) ->
      NameSet.union (fnSet st) (NameSet.remove nm (fnProp prp))
  | Case (trm, ty, arms, ty') ->
      unionNameSetList ( fnTerm trm :: fnSet ty :: fnSet ty' ::
         List.map fnCaseArm arms )
  | IdentityCoerce(trm, ty1, ty2, prps) ->
      unionNameSetList 
	(fnTerm trm :: fnSet ty1 :: fnSet ty2 :: List.map fnProp prps)

and fnProp = function
    False | True -> NameSet.empty
  | Atomic(LN(None, nm), pt) -> NameSet.union (NameSet.singleton nm) (fnProptype pt)
  | Atomic(LN(Some mdl, nm), pt) -> NameSet.union (fnModel mdl) (fnProptype pt)
  | And prps -> unionNameSetList (List.map fnProp prps)
  | Or prps -> unionNameSetList (List.map (fun (_, p) -> fnProp p) prps)
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
  | IsEquiv (prp, st) -> NameSet.union (fnProp prp) (fnSet st) 
  | PCase (trm, ty, arms) ->
      NameSet.union (fnTerm trm) 
  (NameSet.union (fnSet ty)
      (unionNameSetList (List.map fnPCaseArm arms)))
  | PLet((nm,st),trm,prp) ->
      NameSet.union (fnSet st)
  (NameSet.union (fnTerm trm)
      (NameSet.remove nm (fnProp prp)))
  | PBool trm -> fnTerm trm
  | PIdentityCoerce(prp, pt1, pt2, prps) ->
      unionNameSetList 
	(fnProp prp :: fnProptype pt1 :: fnProptype pt2 :: List.map fnProp prps)

and fnCaseArm = function
    (_, None, trm) -> fnTerm trm
  | (_, Some (nm, st), trm) -> 
      NameSet.union (fnSet st) (NameSet.remove nm (fnTerm trm))

and fnProptype = function
    Prop | StableProp -> NameSet.empty
  | EquivProp s -> fnSet s
  | PropArrow (nm, st, pt) -> NameSet.union (fnSet st) (NameSet.remove nm (fnProptype pt))

and fnPCaseArm = function
    (_, None, trm) -> fnProp trm
  | (_, Some (nm, st), trm) -> 
      NameSet.union (fnSet st) (NameSet.remove nm (fnProp trm))
  
and fnModel = function
    ModelName nm -> NameSet.singleton nm
  | ModelProj (mdl, _) -> fnModel mdl
  | ModelApp (mdl1, mdl2) -> NameSet.union (fnModel mdl1) (fnModel mdl2)

and fnTheory = function
    TheoryName nm -> NameSet.singleton nm
  | TheoryApp(thry,mdl) ->
      NameSet.union (fnTheory thry) (fnModel mdl)
  | TheoryLambda((nm,thry1),thry2) 
  | TheoryArrow((nm,thry1),thry2) ->
      NameSet.union (NameSet.remove nm (fnTheory thry1)) (fnTheory thry2)
  | Theory elems -> fnElems elems
  | TheoryProj(mdl,nm) -> fnModel mdl

and fnElems = function
    [] -> NameSet.empty
  | Comment _ :: rest -> fnElems rest
  | Declaration(nm, decl) :: rest ->
      NameSet.union (fnDecl decl) (NameSet.remove nm (fnElems rest))

and fnDecl = function
    DeclProp(popt, pt) -> NameSet.union (fnOpt fnProp popt) (fnProptype pt)
  | DeclSet(sopt, knd) -> NameSet.union (fnOpt fnSet sopt) (fnKind knd)
  | DeclTerm(topt, ty) -> NameSet.union (fnOpt fnTerm topt) (fnSet ty)
  | DeclModel thry     -> fnTheory thry
  | DeclTheory(thry,tknd) -> NameSet.union (fnTheory thry) (fnTheoryKind tknd)
  | DeclSentence([], prp) -> fnProp prp
  | DeclSentence((nm,thy)::mbnds, prp) ->
      NameSet.union (fnTheory thy) 
  (NameSet.remove nm (fnDecl(DeclSentence(mbnds,prp))))

and fnTheoryKind = function
    ModelTheoryKind -> NameSet.empty
  | TheoryKindArrow((nm,thry),tknd) ->
      NameSet.union (fnTheory thry) (NameSet.remove nm (fnTheoryKind tknd))

and fnKind = function
    KindSet -> NameSet.empty
  | KindArrow(nm,ty,knd) ->
      NameSet.union (fnSet ty) (NameSet.remove nm (fnKind knd))


(** Is a set suitable for ||...|| abreviation? *)
let rec isSimple s =
  let isFree x s = not (NameSet.mem x (fnSet s)) in
    match s with
      | Empty | Unit | Bool -> true
      | Basic (_, KindSet) -> true
      | Basic (_, _) -> false
      | Product [] -> true
      | Product [(_, s)] -> isSimple s
      | Product ((x,s)::lst) ->
    isSimple s && isFree x (Product lst) && isSimple (Product lst)
      | Exp (x, s1, s2) -> isFree x s2 && isSimple s1 && isSimple s2
      | Sum _ | Subset _ | Rz _ | Quotient _ | SApp _ | SLambda _ -> false
      

(***************************)
(** Substitution functions *)
(***************************)

type subst = {terms: term NameMap.t;
              sets: set NameMap.t;
        props : proposition NameMap.t;
              models: model NameMap.t;
        theories : theory NameMap.t;
              capturablenames: NameSet.t}

let emptysubst = {terms = NameMap.empty;
      props = NameMap.empty;
      sets = NameMap.empty;
      models = NameMap.empty;
      theories = NameMap.empty;
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

let insertTheoryvar sbst strng mdl =
  {sbst with theories = NameMap.add strng mdl sbst.theories;
   capturablenames = NameSet.union sbst.capturablenames (fnTheory mdl)}

let removeName sbst nm =
  {terms  = NameMap.remove nm sbst.terms;
   props  = NameMap.remove nm sbst.props;
   sets   = NameMap.remove nm sbst.sets;
   models = NameMap.remove nm sbst.models;
   theories = NameMap.remove nm sbst.theories;
   capturablenames = sbst.capturablenames}  (* XXX Overly conservative? *)


let getTermvar sbst nm =
   try (NameMap.find nm sbst.terms) with
       Not_found -> Var (LN (None, nm))

let getPropvar sbst nm pt =
   try (NameMap.find nm sbst.props) with
       Not_found -> Atomic (LN (None, nm), pt)

let getSetvar sbst stnm knd =
   try (NameMap.find stnm sbst.sets) with 
       Not_found -> Basic (SLN(None, stnm), knd)

let getModelvar sbst mdlnm =
   try (NameMap.find mdlnm sbst.models) with 
       Not_found -> ModelName mdlnm

let getTheoryvar sbst thrynm =
   try (NameMap.find thrynm sbst.theories) with 
       Not_found -> TheoryName thrynm

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

(* Verify that the given name will not incur variable capture.  (I.e.,
   that we'd have to alpha-vary it if we wanted to push the
   substitution inside the scope of this bound variable. *)
let checkNoCapture sbst nm =
  if (NameSet.mem nm sbst.capturablenames) then
    (* XXX:  Because removing names from a substitution does not update
       capturablenames, we could do a double-check here to make sure that
       the name really is going to be captured at this particular moment. *)
    failwith ("Cannot remove shadowing of " ^ string_of_name nm)
  else
    ()

let rec subst sbst =
  
  let rec sub = function
    | EmptyTuple -> EmptyTuple
    | BConst b -> BConst b
    | BNot trm -> sub trm
    | BOp (bop, trms) -> BOp(bop, List.map sub trms)
    | Var (LN (None, nm)) -> getTermvar sbst nm
    | Var (LN (Some mdl, nm)) -> 
  Var( LN(Some(substModel sbst mdl), nm) )
    | Tuple ts      -> Tuple(List.map sub ts)
    | Proj(n,t1)    -> Proj(n, sub t1)
    | App(t1,t2)    -> App(sub t1, sub t2)
    | Inj(l,termopt,st) -> Inj(l, doOpt (subst sbst) termopt, substSet sbst st)
    | Case(t1,ty,arms,ty2) -> Case(sub t1, substSet sbst ty, 
           subarms arms, substSet sbst ty2)
    | RzQuot t -> RzQuot (sub t)
    | RzChoose ((y,sopt),t1,t2,ty) ->
  let (sbst', y') = updateBoundName sbst y in
    RzChoose ((y', substSet sbst sopt),
       sub t1,
       subst sbst' t2,
       substSet sbst ty)
    | Quot(trm1,prp2) -> Quot(sub trm1, substProp sbst prp2)
    | Choose((y,sopt),p,t1,t2,stopt2) ->
	let (sbst', y') = updateBoundName sbst y in
          Choose((y',substSet sbst sopt),
                 substProp sbst p,
                 sub t1, 
                 subst sbst' t2,
		 substSet sbst stopt2)
    | Subin(trm,(y,st),prp) -> 
	let (sbst', y') = updateBoundName sbst y in 
	  Subin(sub trm,
		(y',substSet sbst st),
		substProp sbst' prp)
    | Subout(trm,st) -> Subout(sub trm, substSet sbst st)
    | Let((y,st1),t1,t2,st2) ->
	let (sbst', y') = updateBoundName sbst y in
          Let((y',substSet sbst st1),
              sub t1, 
	      subst sbst' t2,
	      substSet sbst st2)
	    
    | Lambda((y,st),t1) ->
	let (sbst', y') = updateBoundName sbst y in 
	  Lambda((y',substSet sbst st),
		 subst sbst' t1)
	    
    | The((y,st), prp) ->
	let (sbst', y') = updateBoundName sbst y in 
	  The((y',substSet sbst st),
	      substProp sbst' prp)

    | IdentityCoerce(trm, ty1, ty2, prps) ->
	IdentityCoerce(sub trm,
		       substSet sbst ty1,
		       substSet sbst ty2,
		       List.map (substProp sbst) prps)
	    
  and subarms = function
      [] -> []
    | (l,None,t)::rest -> (l,None, sub t)::(subarms rest)
    | (l,Some(y,sopt),u)::rest ->
  let (sbst',y') = updateBoundName sbst y in
          (l, Some(y', substSet sbst sopt), subst sbst' u) ::
      (subarms rest)
  in sub

and substProp sbst = 
  let rec sub = function
      True -> True
    | False -> False
    | Atomic (LN (None, nm), pt) -> getPropvar sbst nm (substProptype sbst pt)
    | Atomic (LN (Some mdl, nm), pt) -> 
	Atomic( LN(Some(substModel sbst mdl), nm), substProptype sbst pt)
    | And ts         -> And(List.map sub ts)
    | Imply (t1,t2)  -> Imply (sub t1, sub t2)
    | Iff (t1,t2)    -> Iff (sub t1, sub t2)
    | Or ts          -> Or (List.map (fun (lbl, p) -> (lbl, sub p)) ts)
    | Not t          -> Not (sub t)
    | Equal (ty,t1,t2) -> Equal (substSet sbst ty,
         subst sbst t1,
         subst sbst t2)
    | Forall((y,sopt),t1) ->
	let (sbst', y') = updateBoundName sbst y in 
          Forall((y',substSet sbst sopt),
		 substProp sbst' t1)
    | Exists((y,sopt),t1) ->
	let (sbst', y') = updateBoundName sbst y in 
    Exists((y',substSet sbst sopt),
	   substProp sbst' t1)
    | Unique((y,sopt),t1) ->
	let (sbst', y') = updateBoundName sbst y in 
	  Unique((y',substSet sbst sopt),
		 substProp sbst' t1)
    | PLambda((y,sopt),t1) ->
	let (sbst', y') = updateBoundName sbst y in 
	  PLambda((y',substSet sbst sopt),
		  substProp sbst' t1)
    | PApp(prp1,trm2) -> PApp(sub prp1, subst sbst trm2)
    | IsEquiv (prp, st) -> IsEquiv(sub prp, substSet sbst st)
    | PCase(t1,ty,arms) -> PCase(t1, substSet sbst ty, psubarms arms)
    | PLet((y,st), trm, prp) ->
	let (sbst', y') = updateBoundName sbst y in
	  PLet((y',substSet sbst st), 
               subst sbst trm, substProp sbst' prp)
    | PBool trm -> PBool(subst sbst trm)
    | PIdentityCoerce(prp, pt1, pt2, prps) ->
	PIdentityCoerce(sub prp,
			substProptype sbst pt1,
			substProptype sbst pt2,
			List.map sub prps)
	    

	
  and psubarms = function
      [] -> []
    | (l,None,p)::rest -> (l,None, sub p)::(psubarms rest)
    | (l,Some(y,sopt),p)::rest ->
  let (sbst',y') = updateBoundName sbst y in
          (l, Some(y', substSet sbst sopt), substProp sbst' p) ::
      (psubarms rest)
  in sub

and substSet sbst =
  let rec sub = function
      Unit -> Unit
    | Empty -> Empty
    | Bool -> Bool
    | Basic (SLN (None, stnm), knd) ->
  getSetvar sbst stnm (substSetkind sbst knd)
    | Basic (SLN (Some mdl, stnm), knd) -> 
  Basic (SLN (Some (substModel sbst mdl), stnm), substSetkind sbst knd)
    | Product ss -> Product (substProd sbst ss)
    | Exp(y, s1, s2) ->
  let (sbst', y') = updateBoundName sbst y in 
          Exp(y', sub s1, substSet sbst' s2)
    | Subset((y,sopt),u) ->
  let (sbst', y') = updateBoundName sbst y in 
          Subset((y',substSet sbst sopt),
            substProp sbst' u)
    | Quotient(st,prp)   -> 
        Quotient(sub st, substProp sbst prp)
    | Rz st -> Rz (sub st)
    | SApp(st1,trm2) -> SApp(sub st1, subst sbst trm2)
    | Sum lsos ->
  let f (l, so) = (l, doOpt (substSet sbst) so)
  in Sum (List.map f lsos)
    | SLambda((y,st),u) ->
  let (sbst', y') = updateBoundName sbst y in 
          SLambda((y',substSet sbst st),
             substSet sbst' u)

  and substProd sbst = function
      [] -> []
    | (y,st)::rest -> 
  let (sbst', y') = updateBoundName sbst y in 
    (y', substSet sbst st) :: (substProd sbst' rest)


  in sub

and substModel sbst = function
    ModelName strng -> getModelvar sbst strng
  | ModelProj (mdl, lbl) -> ModelProj(substModel sbst mdl, lbl)
  | ModelApp (mdl1, mdl2) -> ModelApp(substModel sbst mdl1,
             substModel sbst mdl2)

and substSetkind sbst = function
    KindArrow(y, st, k) -> 
      let (sbst', y') = updateBoundName sbst y in
  KindArrow(y', substSet sbst st, substSetkind sbst' k)
  | KindSet -> KindSet

and substProptype sbst = function
    Prop -> Prop
  | StableProp -> StableProp
  | EquivProp ty -> EquivProp (substSet sbst ty)
  | PropArrow(y,st,prpty) ->
      let (sbst', y') = updateBoundName sbst y in
  PropArrow(y', substSet sbst st, substProptype sbst' prpty)
    
and substTheory sbst = function 
    Theory elts       -> Theory (substTheoryElts sbst elts)
  | TheoryName thrynm -> getTheoryvar sbst thrynm
  | TheoryArrow ((y, thry1), thry2) ->
      let (sbst',y') = updateBoundName sbst y in
  TheoryArrow((y, substTheory sbst thry1),
       substTheory sbst' thry2)
  | TheoryLambda ((y, thry1), thry2) ->
      let (sbst',y') = updateBoundName sbst y in
  TheoryLambda((y, substTheory sbst thry1),
        substTheory sbst' thry2)
  | TheoryApp (thry, mdl) ->
      TheoryApp (substTheory sbst thry,  
    substModel sbst mdl)
  | TheoryProj(mdl,nm) ->
      TheoryProj(substModel sbst mdl, nm)

and substTheoryKind sub = function
    ModelTheoryKind               -> ModelTheoryKind
  | TheoryKindArrow((y,thry), tk) ->
      let(sub', y') = updateBoundName sub y in
  TheoryKindArrow((y', substTheory sub thry), 
            substTheoryKind sub' tk)
  

(* Can't implement this fully without an outer label / inner variable
   distinction. !
*)
and substTheoryElts sub = function
    [] -> []
  | Declaration(nm, DeclSet(stopt, knd)) :: rest ->
      let _ = checkNoCapture sub nm
      in let sub' = removeName sub nm
      in 
     Declaration(nm, DeclSet(doOpt (substSet sub) stopt, 
          substSetkind sub knd)) ::
       (substTheoryElts sub' rest)
  | Declaration(nm, DeclProp(prpopt, pt)) :: rest ->
      let _ = checkNoCapture sub nm
      in let this' = Declaration(nm, DeclProp(doOpt (substProp sub) prpopt,
               substProptype sub pt))
      in let sub'  = removeName sub nm
      in let rest' = substTheoryElts sub' rest
      in this' :: rest'
  | Declaration(nm, DeclTerm(trmopt, ty)) :: rest ->
      let _ = checkNoCapture sub nm
      in let this' = Declaration(nm, DeclTerm(doOpt (subst sub) trmopt,
                 substSet sub ty))
      in let sub'  = removeName sub nm
      in let rest' = substTheoryElts sub' rest
      in this' :: rest'
  | Declaration(nm, DeclSentence(mbnds, prp)) :: rest ->
      (* Even though you can't refer to an axiom, it's really confusing
         to have an axiom a and a term a in the same scope.  Worse, 
   both would generate a module value "a" in the final output code.
         So, we pretend that names of axioms are just like names of 
         propositions. *)
      let _ = checkNoCapture sub nm 
      in let (mbnds', sub_m) = substMBnds sub mbnds
      in let prp' = substProp sub prp
      in let this' = Declaration(nm, DeclSentence(mbnds', prp'))
      in let sub'  = removeName sub nm
      in let rest' = substTheoryElts sub' rest
      in this' :: rest'
  | Declaration(nm, DeclModel (thry)) :: rest ->
      let _ = checkNoCapture sub nm
      in let thry' = substTheory sub thry 
      in let this' = Declaration(nm, DeclModel (thry'))
      in let sub' = removeName sub nm
      in let rest' = substTheoryElts sub' rest
      in this' :: rest'
  | Declaration(nm, DeclTheory (thry, thryknd)) :: rest ->
      let _ = checkNoCapture sub nm
      in let thry' = substTheory sub thry
      in let thrykind' = substTheoryKind sub thryknd
      in let this' = Declaration(nm, DeclTheory(thry', thrykind'))
      in let sub' = removeName sub nm
      in let rest' = substTheoryElts sub' rest
      in this' :: rest'
  | ((Comment c) as this') :: rest ->
       let rest' = substTheoryElts sub rest
       in this' :: rest'

and substTheoryElt sub elem =
  match substTheoryElts sub [elem] with
      [elem'] -> elem'
    | _ -> raise Impossible

and substTheoryDecl sub decl =
  match substTheoryElt sub (Declaration(wildName(), decl)) with
  | Declaration(_, decl') -> decl'
  | _ -> raise Impossible

and substTheoryDeclOpt sub = function
  | None -> None
  | Some decl -> Some (substTheoryDecl sub decl)

and substMBnds sub = function
     [] -> ([], sub)
    | (mdlnm, thry) :: rest -> 
       let sub' = insertModelvar sub mdlnm (ModelName mdlnm ) in
       let (rest', sub'') = substMBnds sub' rest in
         ((mdlnm, substTheory sub thry) :: rest', sub'')

(* Specialized functions just for inserting a model *)
    
let modelSubst nm mdl = insertModelvar emptysubst nm mdl

let substMModel nm mdl = substModel (modelSubst nm mdl)
let substMSet nm mdl = substSet (modelSubst nm mdl)
let substMSetOption nm mdl = doOpt (substSet (modelSubst nm mdl))
let substMSetkind nm mdl = substSetkind (modelSubst nm mdl)
let substMTerm nm mdl = subst (modelSubst nm mdl)


