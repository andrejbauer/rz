(* Abstract Syntax for the Output Code *)

open Name

module L = Logic

(*******************************************)
(** {2: Definition of the Abstract Syntax} *)
(*******************************************)

type modul_name = L.model_name

type modul =
    ModulName of modul_name
  | ModulProj of modul * modul_name
  | ModulApp  of modul * modul
  | ModulStruct of moduldef list

and moduldef =
    DefType of name * ty
  | DefTerm of name * ty * term
  | DefModul of name * signat * modul
  | DefSignat of name * signat

and longname = LN of modul option * name

and ty_name = L.set_name

and signat_name = L.theory_name

and ty =
    NamedTy of longname                    (* 0 *)
  | UnitTy                                 (* 0 *)
  | VoidTy                                 (* 0 *)
  | TopTy                                  (* 0 *)
  | SumTy of (label * ty option) list      (* 1 *)
  | TupleTy of ty list                     (* 2 *)
  | ArrowTy of ty * ty                     (* 3 *)
  | PolyTy of name list * ty

(** Simple types may appear in totality predicates *)
and simple_ty =
  | SNamedTy of longname
  | SUnitTy
  | SVoidTy
  | STopTy
  | STupleTy of simple_ty list
  | SArrowTy of simple_ty * simple_ty
(* Note: hoistProp will break if simple_ty may contain terms. *)
(* Note: simple types must be closed under thinning. *)

(** Modest set, or a uniform family of modest sets. *)
and modest = {
  ty : ty;
  tot : proposition; (* with proptype (indexing ->)ty->Prop *)
  per : proposition; (* with proptype (indexing ->)ty->ty->Prop *)
}

and binding = name * ty

and pattern =
  | WildPat 
  | VarPat of name                        (* Don't use Varpat in Case/PCase *)
  | TuplePat of pattern list
  | ConstrPat of label * binding option   (* Don't use ConstrPat in Let/PLet *)

and term =
  | EmptyTuple
  | Dagger
  | Id         of longname
  | App        of term * term
  | Lambda     of binding * term
  | Tuple      of term list
  | Proj       of int * term
  | Inj        of label * term option
  | Case       of term * (pattern * term) list
  | Let        of pattern * term * term   
  | Obligation of binding list * proposition * term
  | PolyInst   of term * ty list  (* Not fully implemented yet *)

(** Propositional function *)
and proposition =
  | True                                      (* truth *)
  | False                                     (* falsehood *)
  | SimpleSupport of simple_ty                (* support of a simple set *)
  | SimplePer of simple_ty                    (* per of a simple set *)
  | BasicProp  of longname                    (* basic prop with a realizer *)
  | Equal      of term * term                 (* (obs?) equality of terms *)
  | And        of proposition list            (* conjunction *)
  | Imply      of proposition * proposition   (* implication *)
  | Iff        of proposition * proposition   (* equivalence *)
  | Not        of proposition                 (* negation *)
  | Forall     of binding * proposition       (* universal quantifier *)
  | ForallSupport of (name * simple_ty) * proposition (* universal over total elements *)
  | PApp       of proposition * term          (* application of propositional function *)
  | PLambda    of binding * proposition       (* abstraction of a proposition over a type *)
  | PObligation of binding list * proposition * proposition   (* obligation *)
  | PCase       of term * (pattern * proposition) list (* propositional case *)
  | PLet        of pattern * term * proposition        (* Local term-binding *)

and proptype = 
    | Prop
    | PropArrow of ty * proptype

and assertionAnnot =
    Annot_NoOpt             (* Do not optimize the proposition *)
  | Annot_Declare of name

and assertion = 
  {alabel : string;                     (* Name of the assertion *)
   atyvars: name list;                  (* Quantified over types *)
   apbnds : (name * proptype) list;     (* Quantified over predicates *)
   aannots: assertionAnnot list;        (* Assertion options *)
   aprop  : proposition}                (* The actual assertion *)

and signat_element =
    Spec      of name * spec * assertion list
  | Assertion of assertion
  | Comment   of string

and spec =
    ValSpec    of name list * ty
  | ModulSpec  of signat
  | TySpec     of ty option
  | SignatSpec of signat
  | PropSpec   of proptype

and signat =
    SignatName of signat_name
  | SignatProj of modul * signat_name
  | Signat of signat_element list
  | SignatFunctor of modul_binding * signat
  | SignatApp of signat * modul

and signatkind =
    | ModulSignatKind    (* Kind of theories that classify modules,
		            including classifiers for functors *)
    | SignatKindArrow of modul_binding * signatkind (* Classifies SignatFunctors *)

and modul_binding = modul_name * signat

and toplevel = signat_element list
    
(****************************************)
(* {3: Helper functions for the syntax} *)
(****************************************)

(* ln_of_name : nm -> longname *)
let ln_of_name nm = LN (None, nm)

(* id: name -> term *)
let id nm = Id (ln_of_name nm)

(* Is a proposition a per? *)
let rec isPerProp = function
  | BasicProp (LN (_, N(_, Per))) -> true
  | SimplePer _ -> true
  | PApp (p, _) -> isPerProp p
  | _ -> false

(* Is a proposition a support? *)
let rec isSupportProp = function
  | BasicProp (LN (_, N(_, Support))) -> true
  | SimpleSupport _ -> true
  | PApp (p, _) -> isSupportProp p
  | _ -> false

let rec support_of_per = function
  | BasicProp (LN (m, N(s, Per))) -> BasicProp (LN (m, N(s, Support)))
  | SimplePer sty -> SimpleSupport sty
  | PApp (p, t) -> PApp (support_of_per p, t)
  | _ -> failwith "outsyn.ml: invalid call to support_of_per"

(* namedty: name -> ty *)
let namedty nm = NamedTy (ln_of_name nm)

let rec ty_of_simple_ty = function
  | SNamedTy nm -> NamedTy nm
  | SUnitTy -> UnitTy
  | SVoidTy -> VoidTy
  | STopTy -> TopTy
  | STupleTy lst -> TupleTy (List.map ty_of_simple_ty lst)
  | SArrowTy (sty1, sty2) -> ArrowTy (ty_of_simple_ty sty1, ty_of_simple_ty sty2)

let rec simple_ty_of_ty = function
  | NamedTy nm -> SNamedTy nm
  | UnitTy -> SUnitTy
  | VoidTy -> SVoidTy
  | TopTy -> STopTy
  | TupleTy lst -> STupleTy (List.map simple_ty_of_ty lst)
  | ArrowTy (ty1, ty2) -> SArrowTy (simple_ty_of_ty ty1, simple_ty_of_ty ty2)
  | _ -> failwith "simple_ty_of_ty: invalid type"

let tupleOrTopTy = function
    [] -> TopTy
  | ts -> TupleTy ts

let curried_app head args =
  List.fold_left (fun ap x -> App (ap, x)) head args

let nested_lambda args trm =
  List.fold_right (fun b t -> Lambda (b, t)) args trm

let nested_arrowty args ty =
  List.fold_right (fun b t -> ArrowTy (b, t)) args ty

let nested_let names defns trm =
  List.fold_right2 (fun n t1 t2 -> Let (VarPat n, t1, t2)) names defns trm

let nested_plet names defns prp =
  List.fold_right2 (fun n t1 p2 -> PLet (VarPat n, t1, p2)) names defns prp

let nested_let' pats defns trm =
  List.fold_right2 (fun pat t1 t2 -> Let (pat, t1, t2)) pats defns trm

let nested_plet' pats defns prp =
  List.fold_right2 (fun pat t1 p2 -> PLet (pat, t1, p2)) pats defns prp

let nested_imply args prp =
  List.fold_right (fun b t -> Imply (b, t)) args prp

let nested_forall args prp =
  List.fold_right (fun b t -> Forall (b, t)) args prp

let rec dagger_of_ty = function
    NamedTy _ -> Dagger (* XXX: suspicous, should unfold definition? *)
  | UnitTy -> failwith "Cannot make a dagger from UnitTy"
  | VoidTy -> failwith "Cannot make a dagger from VoidTy"
  | TopTy -> Dagger
  | SumTy _ -> failwith "Cannot make a dagger from SumTy"
  | TupleTy lst -> Tuple (List.map dagger_of_ty lst)
  | ArrowTy (t1, t2) -> Lambda ((wildName(), t1), Dagger)
  | PolyTy _ -> failwith "Cannot make a dagger from PolyTy"

let fLet(a,b,c) = Let(a,b,c)
let fPLet(a,b,c) = PLet(a,b,c)

(*
   mapWithAccum:  
     ('a -> 'b -> 'a * 'b) -> 'a -> 'b list -> 'a * 'b list

   e.g., a is a typing context or a substitution, and the b's are
   variables to rename; we want back the accumlated substitution
   *and* all the renamed variables.
*)
let rec mapWithAccum f a = function
   [] -> (a, [])
 | b::bs -> 
   let (a',b') = f a b
   in let (a'', bs') = mapWithAccum f a' bs
   in (a'', b'::bs') 

(* takeList : 'a list -> int -> 'a list

   Returns a prefix of length n
*)
let rec takeList lst n =
    if n <= 0 then
      []
    else
      List.hd lst :: takeList (List.tl lst) (n-1)

(** ======== FREE VARIABLES ======= *)

(* In the following code, the primed functions take two extra
arguments: flt is the list of bound variables whose scope we are
inside; acc is the accumulated list of free variables discovered so
far. *)

let fvList' fvFn' flt acc lst =
  List.fold_left (fvFn' flt) acc lst

let rec fvTerm' flt acc = function
  | Id (LN(None,nm)) -> 
      if List.mem nm flt then acc else nm :: acc
  | Id (LN(Some _, _)) -> acc
  | EmptyTuple -> acc
  | Dagger -> acc
  | App (u, v) -> fvTerm' flt (fvTerm' flt acc u) v
  | Lambda ((n, s), t) -> fvTerm' (n::flt) (fvTy' flt acc s) t
  | Tuple lst -> List.fold_left (fun a t -> fvTerm' flt a t) acc lst
  | Proj (_, t) -> fvTerm' flt acc t
  | Inj (_, Some t) -> fvTerm' flt acc t
  | Inj (_, None) -> acc
  | Case (t, lst) ->
      fvCaseArms' flt (fvTerm' flt acc t) lst
  | Let (pat, t1, t2) -> 
      fvPat' flt (fvTerm' flt (fvTerm' (bvPat pat@flt) acc t2) t1) pat
  | Obligation (bnds, p, t) -> 
      let flt' = (List.map fst bnds) @ flt
      in fvTerm' flt' (fvProp' flt' acc p) t
  | PolyInst(trm, tys) ->
      fvTyList' flt (fvTerm' flt acc trm) tys

and fvPat' flt acc = function
    WildPat -> acc
  | VarPat nm -> if List.mem nm acc then acc else nm :: acc
  | TuplePat lst -> fvPatList' flt acc lst
  | ConstrPat (_,None) -> acc
  | ConstrPat (_,Some(nm,ty)) -> fvTy' (nm::flt) acc ty

and bvPat = function
    WildPat -> []
  | VarPat nm -> [nm]
  | TuplePat lst -> List.concat (List.map bvPat lst)
  | ConstrPat (_,None) -> []
  | ConstrPat (_,Some(nm,_)) -> [nm]

and fvPatList' flt acc lst = fvList' fvPat' flt acc lst

and fvCaseArm' flt acc (pat, trm) =
  fvTerm' ((bvPat pat)@flt) (fvPat' flt acc pat) trm


and fvCaseArms' flt acc arms = fvList' fvCaseArm' flt acc arms


and fvProp' flt acc = function
    True  -> acc
  | False -> acc
  | SimpleSupport sty -> fvSimpleTy' flt acc sty
  | SimplePer sty -> fvSimpleTy' flt acc sty
  | BasicProp (LN(Some _, _)) -> acc
  | BasicProp (LN(None,nm)) -> if List.mem nm flt then acc else nm :: acc
  | Not p -> fvProp' flt acc p
  | And lst -> fvPropList' flt acc lst
  | Equal (u, v) -> fvTerm' flt (fvTerm' flt acc u) v
  | Imply (p, q) 
  | Iff   (p, q) -> fvProp' flt (fvProp' flt acc p) q
  | Forall      ((n, s), p)
  | PLambda     ((n, s), p) -> fvProp' (n::flt) (fvTy' flt acc s) p
  | ForallSupport ((n, sty), p) -> fvProp' (n::flt) (fvSimpleTy' flt acc sty) p
  | PApp  (p, t) -> fvProp' flt (fvTerm' flt acc t) p
  | PObligation (bnds, p, q) -> 
      let flt' = (List.map fst bnds) @ flt
      in fvProp' flt' (fvProp' flt' acc p) q
  | PCase (t, lst) ->
      fvPCaseArms' flt (fvTerm' flt acc t) lst
  | PLet (pat, t, p) -> 
      fvPat' flt (fvProp' ((bvPat pat)@flt) (fvTerm' flt acc t) p) pat

and fvPCaseArm' flt acc (pat,prp) = 
  fvProp' ((bvPat pat)@flt) (fvPat' flt acc pat) prp  

and fvPCaseArms' flt acc arms = fvList' fvPCaseArm' flt acc arms

and fvPropList' flt acc lst = fvList' fvProp' flt acc lst

and fvTermList' flt acc lst = fvList' fvTerm' flt acc lst

and fvModestList' flt acc = List.fold_left (fun a t -> fvModest' flt a (snd t)) acc

and fvTyList' flt acc lst = fvList' fvTy' flt acc lst

and fvSimpleTyList' flt acc lst = fvList' fvSimpleTy' flt acc lst

and fvModest' flt acc {tot=p; per=q} = fvProp' flt (fvProp' flt acc p) q

and fvTy' flt acc = function
    NamedTy(LN(None,nm)) ->
      if List.mem nm flt then acc else nm :: acc
  | NamedTy(LN(Some _, _)) -> acc
  | (UnitTy | VoidTy | TopTy) -> acc
  | SumTy(sumarms) -> List.fold_left (fvSum' flt) acc sumarms
  | TupleTy tys -> List.fold_left (fvTy' flt) acc tys
  | ArrowTy(ty1,ty2) ->
      fvTy' flt (fvTy' flt acc ty1) ty2
  | PolyTy(nms,ty) ->
      fvTy' (nms @ flt) acc ty

and fvSimpleTy' flt acc = function
  | SNamedTy _
  | SUnitTy
  | SVoidTy
  | STopTy -> acc
  | STupleTy lst -> fvSimpleTyList' flt acc lst
  | SArrowTy (sty1, sty2) ->
      fvSimpleTy' flt (fvSimpleTy' flt acc sty1) sty2

and fvSum' flt acc (_,tyopt) = fvTyOpt' flt acc tyopt

and fvTyOpt' flt acc = function
    None -> acc
  | Some ty -> fvTy' flt acc ty

(*********************************************************)
(* Substitution:                                         *)
(*   Wrapper functions that take only the term/type/etc. *)
(*********************************************************)

let fvTerm      = fvTerm'      [] []
let fvProp      = fvProp'      [] []
let fvModest    = fvModest'    [] []
let fvPCaseArm  = fvPCaseArm'  [] []
let fvPCaseArms = fvPCaseArms' [] []
let fvCaseArm   = fvCaseArm'   [] []
let fvCaseArms  = fvCaseArms'  [] []
let fvTy        = fvTy'        [] []

(***************************************************************)
(** {2: Count occurrences of subterms satisfying a predicate.} *)
(***************************************************************)

(**
Actually, we have three predicates; one for terms, one for types,
and one for propositions.  We return the total number of times any
predicate is satisfied.  

As currently written, the code does not search *inside* terms (or
types, or predicates) that is discovered match a predicate.
*)

type countPred = {termPred: term -> bool;
                  tyPred  : ty -> bool;
		  styPred : simple_ty -> bool;
		  propPred: proposition -> bool}

(* occurrencesOfTermName : nm -> countPred

   For counting the occurrences of a given term name.

   N.B.  Ignores possibility of shadowing; code computes all
   occurrences, not just the free ones.

   (But if there's no shadowing, an invariant that both thinning and
   optimization maintain, then any occurrence is a free occurrence.
*)
let occurrencesOfTermName nm =
  let isMatchingTermName = function
      Id(LN(None,nm')) -> nm = nm'
    | _ -> false
  in let isFalse _ = false
  in
  {termPred = isMatchingTermName;
   tyPred   = isFalse;
   styPred  = isFalse;
   propPred = isFalse}

(* occurrencesOfTermName : nm -> countPred

   For counting the tuple projections from the given term name. 
   (E.g., counting occurrences of nm.0, nm.1, etc.)  

   NB: Ignores the possibility of shadowing.
*)
let occurrencesOfNameInProj nm =
  let isMatchingProj = function
      Proj(_,Id(LN(None,nm'))) -> nm = nm'
    | _ -> false
  in let isFalse _ = false
  in
  {termPred = isMatchingProj;
   tyPred   = isFalse;
   styPred  = isFalse;
   propPred = isFalse}

let countList countFn cpred lst = 
  List.fold_left (fun a p -> a + countFn cpred p) 0 lst

let rec countTerm (cp: countPred) trm = 
  if (cp.termPred trm) then
    1
  else
    match trm with
    | Id (LN(None,nm)) -> 0
    | Id (LN(Some mdl, _)) -> countModul cp mdl
    | EmptyTuple -> 0
    | Dagger -> 0
    | App (u, v) -> countTerm cp u + countTerm cp v
    | Lambda ((n, s), t) -> countTerm cp t
    | Tuple lst -> countTermList cp lst
    | Proj (_, t) -> countTerm cp t
    | Inj (_, Some t) -> countTerm cp t
    | Inj (_, None) -> 0
    | Case (t, lst) -> List.fold_left (fun a arm -> a + countCaseArm cp arm) (countTerm cp t) lst
    | Let (_, t1, t2) -> 
	(* XXX : Ignores types in patterns *)
	countTerm cp t1 + countTerm cp t2
    | Obligation (bnds, p, t) ->
	countProp cp p + countTerm cp t
    | PolyInst (trm, tys) ->
	List.fold_left (fun a ty -> a + countTy cp ty) (countTerm cp trm) tys

and countTermList cp lst = countList countTerm cp lst

and countCaseArm cp = function
    (_, t) -> countTerm cp t   (*** XXX: Ignores types in patterns *)

and countProp cp prp =
    if cp.propPred prp then
	1
    else
      match prp with
	True -> 0
      | False -> 0
      | BasicProp _ -> 0
      | SimpleSupport sty -> countSimpleTy cp sty
      | SimplePer sty -> countSimpleTy cp sty
      | Equal (u, v) -> countTerm cp u + countTerm cp v
      | And lst -> countPropList cp lst
      | Imply (u, v) -> countProp cp u + countProp cp v
      | Forall ((n, _), p) -> countProp cp p
      | ForallSupport ((n, sty), p) -> countSimpleTy cp sty + countProp cp p
      | Not p -> countProp cp p
      | Iff (p, q) -> countProp cp p + countProp cp q
      | PApp (p, t) -> countProp cp p + countTerm cp t
      | PLambda ((n, _), p) -> countProp cp p
      | PObligation (bnds, p, q) -> 
	  countProp cp p + countProp cp q

  | PCase (t, lst) ->
      (countTerm cp t) + (countList countPCaseArm cp lst)

  | PLet (_, t, p) ->
      (* XXX: Ignores types in patterns *)
      countTerm cp t + countProp cp p

and countPCaseArm cp (_, p) = countProp cp p

and countModest cp {tot=p; per=q} = countProp cp p + countProp cp q

and countPropList cp lst = countList countProp cp lst

and countModestList cp lst = countList countModest cp lst

and countTy cp ty = 
  if (cp.tyPred ty) then
    1
  else
    match ty with
      NamedTy(LN(None,_)) -> 0
    | NamedTy(LN(Some mdl, _)) ->
	countModul cp mdl
    | UnitTy
    | VoidTy
    | TopTy -> 0
    | SumTy lst -> countSumArms cp lst
    | TupleTy lst -> countTys cp lst
    | ArrowTy (ty1,ty2) -> countTy cp ty1 + countTy cp ty2
    | PolyTy (_,ty) -> countTy cp ty

and countSimpleTy cp sty = 
  if (cp.styPred sty) then
    1
  else
    match sty with
      | SNamedTy(LN(None,_)) | SUnitTy | SVoidTy | STopTy -> 0
      | SNamedTy(LN(Some mdl, _)) -> countModul cp mdl
      | STupleTy lst -> countSimpleTys cp lst
      | SArrowTy (sty1,sty2) -> countSimpleTy cp sty1 + countSimpleTy cp sty2

and countTyOpt cp = function
    None -> 0
  | Some ty -> countTy cp ty

and countSumArms cp lst = 
  countList (fun cp (_,tyopt) -> countTyOpt cp tyopt) cp lst

and countTys cp lst = countList countTy cp lst

and countSimpleTys cp lst = countList countSimpleTy cp lst

and countModul cp = function
  | ModulName _
  | ModulProj _
  | ModulApp  _ -> 0
  | ModulStruct _ -> failwith "countModule: ModulStruct not implemented"



(** ====== SUBSTITUTION FUNCTIONS ========= *)

module LNOrder =
struct
  type t = longname
  let compare = Pervasives.compare
end

module ModulOrder =
struct
  type t = modul
  let compare = Pervasives.compare
end

module LNMap  = Map.Make(LNOrder)
module ModulMap = Map.Make(ModulOrder)


(** A substitution is a simultaneous map from terms to terms,
    types to types, and moduls to moduls.

    Note that substitutions do *not* check for alpha-equivalence;
    exact matches are required.

    Fortunately, the primary uses of these functions are replacing
    variables, and occasionally replacing paths, and neither of these
    contain bound variables.
*)

type subst = {terms : term     LNMap.t;
              tys   : ty       LNMap.t;
	      props : longname LNMap.t;
              moduls: modul ModulMap.t}

let emptysubst = {terms  = LNMap.empty;
		  tys    = LNMap.empty;
		  props  = LNMap.empty;
		  moduls = ModulMap.empty}

(** see also display_subst below *)

let fvSubst subst = 
  let acc = LNMap.fold (fun _ x a -> fvTerm' [] a x) subst.terms []
  in let acc = LNMap.fold (fun _ x a -> fvTy' [] a x) subst.tys acc
(*  in let acc = ModulMap.fold (fun _ x a -> fvModul' [] a x) subst.tys acc *)
  in acc


let insertTermLN sbst ln trm' =
  {sbst with terms = LNMap.add ln trm' sbst.terms}

let insertTermvar sbst nm trm' =
  insertTermLN sbst (LN(None,nm)) trm'

let insertTyLN sbst ln ty' =
  {sbst with tys = LNMap.add ln ty' sbst.tys}

let insertTyvar sbst nm ty' =
  insertTyLN sbst (LN(None,nm)) ty'

let insertPropLN sbst ln ln' =
  {sbst with props = LNMap.add ln ln' sbst.props}

let insertModulvar sbst nm mdl =
  {sbst with moduls = ModulMap.add (ModulName nm) mdl sbst.moduls}

let termsSubst lst =
  List.fold_left (fun sbst (nm,trm) -> insertTermvar sbst nm trm) emptysubst lst

let termSubst nm trm = insertTermvar emptysubst nm trm

let getTermLN sbst trm =
   try Some (LNMap.find trm sbst.terms) with 
       Not_found -> None

let getTyLN sbst ln =
   try Some (LNMap.find ln sbst.tys) with 
       Not_found -> None

let getPropLN sbst ln =
   try Some (LNMap.find ln sbst.props) with 
       Not_found -> None

let getModul sbst mdl =
   try Some (ModulMap.find mdl sbst.moduls) with 
       Not_found -> None

(*****************************************)
(* Useful special cases of substitutions *)
(*****************************************)

(* renaming    : Substitution to replace one name by another
   renamingList: Substitution to replace one set (list) of names by another
 *)

(* The primed functions renaming' and renamingList' extend a 
   given substitution; the unprimed functions create a new
   substitution 
 *)

let renaming' subst n n' = insertTermvar subst n (id n')
let renaming n n'        = renaming' emptysubst n n'

let renamingList' subst ns ns' =
  List.fold_left2 renaming' subst ns ns'
let renamingList ns ns' = renamingList' emptysubst ns ns'

let tyrenaming' subst n n' = insertTyvar subst n (namedty n')
let tyrenaming n n'        = tyrenaming' emptysubst n n'

let tyrenamingList' subst ns ns' =
  List.fold_left2 tyrenaming' subst ns ns'
let tyrenamingList ns ns' = tyrenamingList' emptysubst ns ns'


(** The substitution functions accept an optional occ argument which
    is used for extra occur checks (for example in a context). The occ
    function accepts a name and returns a bool. No fresh variable
    generated by a substitution will satisfy the occ check. *)

let rec substLN ?occ sbst = function
    (LN (None, _)) as ln -> ln
  | LN (Some mdl, nm) -> LN (Some (substModul ?occ sbst mdl), nm)

and substModul ?occ sbst orig_mdl =
  match (getModul sbst orig_mdl) with
      Some mdl' -> mdl'
    | None -> 
	match orig_mdl with
	    ModulName nm -> ModulName nm
	  | ModulProj (mdl, nm)   -> ModulProj (substModul ?occ sbst mdl, nm)
	  | ModulApp (mdl1, mdl2) -> ModulApp (substModul ?occ sbst mdl1, 
					       substModul ?occ sbst mdl2)
	  | ModulStruct mdldfs -> ModulStruct (substDefs ?occ sbst mdldfs)

(* XXX: Actually, the first two "failwiths" are too pessimistic.  It's
   actually OK in ML to have a term and a type with the same name. *)
and substDefs ?occ sbst = function
    [] -> []
  | DefType(nm, ty) :: rest ->
      if (List.mem nm (fvSubst sbst)) then
	failwith "Outsyn.substDefs:  Can't avoid shadowing a type name"
      else
	DefType(nm, substTy ?occ sbst ty) ::
	  substDefs ?occ (insertTyvar sbst nm (namedty nm)) rest
  | DefTerm(nm, ty, trm) :: rest ->
      if (List.mem nm (fvSubst sbst)) then
	failwith "Outsyn.substDefs:  Can't avoid shadowing a term name"
      else
	DefTerm(nm, substTy ?occ sbst ty, substTerm ?occ sbst trm) ::
	  substDefs ?occ (insertTermvar sbst nm (id nm)) rest
  | DefModul(nm, signat, mdl) :: rest ->
      if (List.mem nm (fvSubst sbst)) then
	failwith "Outsyn.substDefs:  Can't avoid shadowing a modul name"
      else
	DefModul(nm, substSignat ?occ sbst signat, substModul ?occ sbst mdl) ::
	  substDefs ?occ (insertModulvar sbst nm (ModulName nm)) rest
  | DefSignat(nm, signat) :: rest ->
      if (List.mem nm (fvSubst sbst)) then
	failwith "Outsyn.substDefs:  Can't avoid shadowing a signature name"
      else
(* No signature renaming, as signatures always have fixed labels
	DefSignat(nm, substSignat ?occ sbst signat) ::
	  substDefs ?occ (insertSignatvar sbst nm (SignatName nm)) rest
*)
	DefSignat(nm, substSignat ?occ sbst signat) ::
	  substDefs ?occ sbst rest

	  

and substProp ?occ sbst = function
    True -> True
  | False -> False
  | SimpleSupport sty -> SimpleSupport (substSimpleTy ?occ sbst sty)
  | SimplePer sty -> SimplePer (substSimpleTy ?occ sbst sty)
  | BasicProp ln ->
      BasicProp (match getPropLN sbst ln with
		   | None -> substLN ?occ sbst ln
		   | Some ln -> ln)
  | Equal (u, v) -> Equal (substTerm ?occ sbst u, substTerm ?occ sbst v)
  | And lst -> And (substPropList ?occ sbst lst)
  | Imply (p, q) -> Imply (substProp ?occ sbst p, substProp ?occ sbst q)
  | Iff (p, q) -> Iff (substProp ?occ sbst p, substProp ?occ sbst q)
  | Not p -> Not (substProp ?occ sbst p)
  | Forall ((n, ty), q) ->
      let n' = refresh n in
	Forall ((n', substTy ?occ sbst ty), substProp ?occ (insertTermvar sbst n (id n')) q)
  | ForallSupport ((n, sty), q) ->
      let n' = refresh n in
	ForallSupport ((n', substSimpleTy ?occ sbst sty),
		       substProp ?occ (insertTermvar sbst n (id n')) q)
  | PApp (p, t) -> PApp (substProp ?occ sbst p, substTerm ?occ sbst t)
  | PLambda ((n, s), p) ->
      let n' = refresh n in
	PLambda ((n', s), substProp ?occ (insertTermvar sbst n (id n')) p)
  | PObligation (bnds, p, q) ->
      let (sbst', bnds') = renameBnds ?occ sbst bnds
      in 
	PObligation (bnds', substProp ?occ sbst' p, substProp ?occ sbst' q)

  | PCase (trm, lst) -> 
	PCase (substTerm ?occ sbst trm,
	       substPCaseArms ?occ sbst lst)
  | PLet (pat, t, p) ->
      let (pat', sbst') = substPat ?occ sbst pat
      in
	PLet (pat', substTerm ?occ sbst t, 
	     substProp ?occ sbst' p)

and substPat' ?occ (sbst : subst) (pat:pattern) : pattern * (name*name) list = 
  match pat with
    WildPat -> (pat, [])
  | VarPat n ->
      let n' = refresh n in
      (VarPat n', [(n,n')])
  | TuplePat pats -> 
      let (pats', pairs) = substPats' ?occ sbst pats
      in (TuplePat pats', pairs)
  | ConstrPat(_,None) -> (pat, [])
  | ConstrPat(lbl, Some(n,ty)) -> 
      let n' =  refresh n in
      (ConstrPat(lbl, Some (n', substTy ?occ sbst ty)),
       [(n,n')])

and substPats' ?occ (sbst : subst) pats = 
  let (pats', pairlists) = List.split (List.map (substPat' ?occ sbst) pats)
  in (pats', List.concat pairlists)

and substPat ?occ (sbst : subst) (pat : pattern) : pattern * subst =
  (* Substitute into all the whole pattern first *)
  let (pat', pairs) = substPat' ?occ sbst pat
  (* ...and then add the renamed variables to the substitution,
     in parallel. *)
  in let (ns,ns') = List.split pairs
  in let sbst' = renamingList' sbst ns ns'
  in (pat', sbst')
	  

and substPCaseArm ?occ sbst (pat, p) =
  let (pat', sbst') = substPat ?occ sbst pat
  in (pat', substProp ?occ sbst' p)
    
and substPCaseArms ?occ sbst arms =
  List.map (substPCaseArm ?occ sbst) arms

and renameBnds ?occ ?bad sbst = function
    [] -> (sbst, [])
  | (n,ty)::bnds -> 
      let bad' = match bad with None -> fvSubst sbst | Some b -> b
      in let n' = refresh n
      in let bnd' = (n', substTy ?occ sbst ty)
      in let sbst' = insertTermvar sbst n (id n')
      in let (sbst'', bnds') = renameBnds ?occ ~bad:(n'::bad') sbst' bnds
      in (sbst'', bnd'::bnds')

and substTerm ?occ sbst orig_term = 
	match orig_term with
	    Id ln ->
	      begin
		match getTermLN sbst (substLN ?occ sbst ln) with
		  None -> Id(substLN ?occ sbst ln)
		| Some trm' -> trm'
	      end 
	  | EmptyTuple -> EmptyTuple
	  | Dagger     -> Dagger
	  | App (t,u) -> App (substTerm ?occ sbst t, substTerm ?occ sbst u)
	  | Lambda ((n, ty), t) ->
	      let n' = refresh n in
		Lambda ((n', substTy ?occ sbst ty), 
		        substTerm ?occ (insertTermvar sbst n (id n')) t)
	  | Let (pat, t, u) ->
	      let (pat', sbst') = substPat ?occ sbst pat
	      in
	      Let (pat', substTerm ?occ sbst t, 
		   substTerm ?occ sbst' u)
	  | Tuple lst -> Tuple (List.map (substTerm ?occ sbst) lst)
	  | Proj (k, t) -> Proj (k, substTerm ?occ sbst t)
	  | Inj (k, None) -> Inj (k, None)
	  | Inj (k, Some t) -> Inj (k, Some (substTerm ?occ sbst t))
	  | Case (t, lst) -> 
	      Case (substTerm ?occ sbst t,
		   substCaseArms ?occ sbst lst)
	  | Obligation (bnds, p, trm) ->
	      let (sbst', bnds') = renameBnds ?occ sbst bnds
	      in
		Obligation (bnds', substProp ?occ sbst' p, substTerm ?occ sbst' trm)
	  | PolyInst(trm, tys) ->
	      PolyInst(substTerm ?occ sbst trm,
		      List.map (substTy ?occ sbst) tys)
		
and substCaseArm ?occ sbst (pat, t) =
  let (pat', sbst') = substPat ?occ sbst pat
  in  (pat', substTerm ?occ sbst' t)
	  
and substCaseArms ?occ sbst arms = 
   List.map (substCaseArm ?occ sbst) arms

and substTermList ?occ sbst = 
  List.map (substTerm ?occ sbst)

and substPropList ?occ sbst = 
  List.map (substProp ?occ sbst)

and substModestList ?occ sbst = 
  List.map (substModest ?occ sbst)

and substTy ?occ sbst = function
  | NamedTy ln ->
      begin
	match getTyLN sbst (substLN ?occ sbst ln) with
	  None -> NamedTy (substLN ?occ sbst ln)
	| Some ty' -> ty'
      end 
  | UnitTy -> UnitTy
  | VoidTy -> VoidTy
  | TopTy  -> TopTy
  | SumTy lst -> 
      SumTy (List.map (fun (lbl, tyopt) -> 
	                 (lbl, substTyOption ?occ sbst tyopt)) 
	       lst)
  | TupleTy lst -> 
      TupleTy (List.map (substTy ?occ sbst) lst)
  | ArrowTy (ty1, ty2) -> 
      ArrowTy (substTy ?occ sbst ty1, substTy ?occ sbst ty2)
  | PolyTy (nms,ty) ->
      PolyTy (nms, substTy ?occ (addTyvarsToSubst sbst nms) ty)  
	
and substTyOption ?occ sbst = function
    None    -> None
  | Some ty -> Some ( substTy ?occ sbst ty )

and substSimpleTy ?occ sbst = function
  | SNamedTy ln -> 
	begin
		match getTyLN sbst ln with
	  	  None -> SNamedTy (substLN ?occ sbst ln)
        | Some ty' -> simple_ty_of_ty ty'
    end	
  | (SUnitTy | SVoidTy | STopTy) as sty -> sty
  | STupleTy lst -> STupleTy (List.map (substSimpleTy ?occ sbst) lst)
  | SArrowTy (sty1, sty2) ->
      SArrowTy (substSimpleTy ?occ sbst sty1, substSimpleTy ?occ sbst sty2)

and substModest ?occ sbst {ty=ty; tot=p; per=q} =
  { ty = substTy ?occ sbst ty;
    tot = substProp ?occ sbst p;
    per = substProp ?occ sbst q
  }
    
and substSignat ?occ sbst = function
    SignatName nm  -> SignatName nm
  | Signat     lst -> Signat (substSignatElements ?occ sbst lst)
  | SignatFunctor ((m,sgnt1), sgnt2) ->
      let sbst' = insertModulvar sbst m (ModulName m) in
	SignatFunctor ((m, substSignat ?occ sbst sgnt1), 
		       substSignat ?occ sbst' sgnt2)
  | SignatApp (sgnt1, mdl) ->
      SignatApp (substSignat ?occ sbst sgnt1,
		substModul ?occ sbst mdl)
  | SignatProj (mdl, nm) ->
      SignatProj(substModul ?occ sbst mdl, nm)

and addTyvarsToSubst sbst = function
    [] -> sbst
  | tv::tvs -> 
      (* XXX: Does not detect shadowing  *)
      insertTyvar (addTyvarsToSubst sbst tvs) tv (NamedTy (LN (None,tv)))

and substSpec ?occ sbst = function
    ValSpec (tyvars, ty)        -> 
      ValSpec (tyvars, substTy ?occ (addTyvarsToSubst sbst tyvars) ty)
  | ModulSpec signat  -> ModulSpec (substSignat ?occ sbst signat)
  | TySpec tyopt      -> TySpec (substTyOption ?occ sbst tyopt)
  | SignatSpec signat -> SignatSpec (substSignat ?occ sbst signat)
  | PropSpec pt       -> PropSpec (substProptype ?occ sbst pt)

and substSignatElements ?occ sbst =
  let rec subst sbst = function
      [] -> []
    | Spec(nm, spec, lst) :: rest ->
	Spec (nm, substSpec ?occ sbst spec, 
	     List.map (substAssertion ?occ sbst) lst) ::
	  (subst (insertTermvar sbst nm (id nm)) rest)
    | Assertion assr :: rest ->
	Assertion (substAssertion ?occ sbst assr) ::
	  (subst sbst rest)
    | (Comment _ as cmnt) :: rest ->
	cmnt :: (subst sbst rest)
  in
    subst sbst

and substSignatElement ?occ sbst elem =
  List.hd (substSignatElements ?occ sbst [elem])

and substAssertion ?occ sbst asn =
  let atyvars' = refreshList asn.atyvars
  in let sbst' = renamingList' sbst asn.atyvars atyvars'
  in let (apbnds', sbst'')  = substPBnds sbst' asn.apbnds
  in let aprop' = substProp ?occ sbst'' asn.aprop
  in
  {alabel  = asn.alabel;
   atyvars = atyvars';
   apbnds  = apbnds';
   aannots  = asn.aannots;
   aprop   = aprop'}

and substPBnds ?occ sbst = function
    [] -> ([], sbst)
  | pb::pbs ->
      let (pb', sbst') = substPBnd ?occ sbst pb
      in let (pbs', sbst'') = substPBnds ?occ sbst' pbs
      in (pb'::pbs', sbst'')

and substPBnd ?occ sbst (nm, pt) =
  let nm' = refresh nm
  in let sbst' = renaming' sbst nm nm'
  in let pt' = substProptype sbst pt
  in
  ((nm',pt'), sbst')

and substProptype ?occ sbst = function
    Prop -> Prop
  | PropArrow(ty, pt) ->
      PropArrow(substTy ?occ sbst ty, substProptype ?occ sbst pt)
   

and substBinding ?occ sbst (nm, ty) = 
  let nm' = refresh nm
  in let sbst' = renaming' sbst nm nm'
  in let ty' = substTy ?occ sbst' ty
  in (sbst', (nm', ty'))






(**** SOMEWHAT OLD CODE OLD CODE OLD CODE OLD CODE IS STILL USED IS STILL USED *)

let rec collectSignatApps = function
    SignatApp (s, m) ->
      let hd, args = collectSignatApps s in
	hd, args @ [m]
  | s -> s, []

let rec string_of_modul = function
    ModulName nm -> string_of_name nm
  | ModulProj (mdl, nm) -> (string_of_modul mdl) ^ "." ^ string_of_name nm
  | ModulApp (mdl1, mdl2) -> (string_of_modul mdl1) ^ "(" ^ (string_of_modul mdl2) ^ ")"
  | ModulStruct mdldfs -> "struct\n" ^ string_of_defs mdldfs ^ "\nend"

and string_of_defs defs = 
  String.concat "\n" (List.map string_of_def defs)

and string_of_def = function
    DefType(nm,ty) -> "type " ^ string_of_name nm ^ " = " ^ string_of_ty ty
  | DefTerm(nm,ty,trm) -> "let " ^ string_of_name nm ^ " : " ^ 
      string_of_ty ty ^ " = " ^ string_of_term trm
  | DefModul(nm,signat,mdl) ->
      "module " ^ string_of_name nm ^ " = " ^
	string_of_modul mdl ^ " : " ^ string_of_signat signat
  | DefSignat(nm,signat) ->
      "module type " ^ string_of_name nm ^ " = " ^ string_of_signat signat

and string_of_ln = function
    LN (None, nm) -> string_of_name nm
  | LN (Some mdl, nm) -> (string_of_modul mdl) ^ "."  ^ (string_of_name nm)

and string_of_ty' level t =
  let rec makeTupleTy = function
      []    -> "top"
    | [t]   -> string_of_ty' 1 t
    | t::ts -> (string_of_ty' 1 t) ^ " * " ^ (makeTupleTy ts)

  in let rec makeSumTy = function
      [] -> "void"
    | ts -> 
	"[" ^ (String.concat " | "
		 (List.map (function
				(lb, None) -> "`" ^ lb
			      | (lb, Some t) ->
				  "`" ^ lb ^ " of " ^ (string_of_ty' 1 t))
			   ts)) ^ "]"
		
  in let (level', str ) = 
       (match t with
            NamedTy lname  -> (0, string_of_ln lname)
	  | UnitTy         -> (0, "unit")
	  | TopTy          -> (0, "top")
	  | VoidTy         -> (0, "void")
	  | SumTy ts       -> (1, makeSumTy ts)
          | TupleTy ts     -> (2, makeTupleTy ts)
          | ArrowTy(t1,t2) -> (3, (string_of_ty' 2 t1) ^ " -> " ^ (string_of_ty' 3 t2))
	  | PolyTy(t1,t2) -> (0, "POLYTY")
       )
  in
    if (level' > level) then 
       "(" ^ str ^ ")"
    else
       str

and string_of_ty t = string_of_ty' 999 t

and string_of_sty sty = string_of_ty (ty_of_simple_ty sty)

and string_of_infix t op u =
  match op with
      LN(None, N(str,_)) -> t ^ " " ^ str ^ " " ^ u
    | ln -> (string_of_ln ln) ^ " " ^ t ^ " " ^ u

and string_of_term' level t =
  let (level', str) = match t with
      Id ln -> (0, string_of_ln ln)
    | EmptyTuple -> (0, "()")
    | Dagger -> (0, "DAGGER")
    | App (App (Id (LN(_,N(_, Infix0)) as ln), t), u) -> 
	(9, string_of_infix (string_of_term' 9 t) ln (string_of_term' 8 u))
    | App (App (Id (LN(_,N(_, Infix1)) as ln), t), u) -> 
	(8, string_of_infix (string_of_term' 8 t) ln (string_of_term' 7 u))
    | App (App (Id (LN(_,N(_, Infix2)) as ln), t), u) -> 
	(7, string_of_infix (string_of_term' 7 t) ln (string_of_term' 6 u))
    | App (App (Id (LN(_,N(_, Infix3)) as ln), t), u) -> 
	(6, string_of_infix (string_of_term' 6 t) ln (string_of_term' 5 u))
    | App (App (Id (LN(_,N(_, Infix4)) as  ln), t), u) -> 
	(5, string_of_infix (string_of_term' 5 t) ln (string_of_term' 4 u))
    | App (t, u) -> 
	(4, (string_of_term' 4 t) ^ " " ^ (string_of_term' 3 u))
    | Lambda ((n, ty), t) ->
	(12, "fun (" ^ (string_of_name n) ^ " : " ^ (string_of_ty ty) ^ ") -> " ^
	   (string_of_term' 12 t))
    | Tuple [] -> (0, "()")
    | Tuple [t] -> (0, "Tuple " ^ string_of_term' 0 t)
    | Tuple lst -> (0, "(" ^ (String.concat ", " (List.map (string_of_term' 11) lst)) ^ ")")
    | Proj (k, t) -> (4, ("pi" ^ (string_of_int k) ^ " " ^ (string_of_term' 3 t)))
    | Inj (lb, None) -> (4, ("`" ^ lb))
    | Inj (lb, Some t) -> (4, ("`" ^ lb ^ " " ^ (string_of_term' 3 t)))
    | Case (t, lst) ->
	(13, "match " ^ (string_of_term' 13 t) ^ " with " ^
	   (String.concat " | "
	      (List.map (fun (pat, u) -> (string_of_pat pat) ^ " -> " ^
		           (string_of_term' 11 u))
		 lst)))
    | Let (pat, t, u) ->
	(13, "let " ^ (string_of_pat pat) ^ " = " ^
	   (string_of_term' 13 t) ^ " in " ^ (string_of_term' 13 u) ^ " end")
    | Obligation (bnds, p, trm) ->
	(12,
	 "assure " ^ (string_of_bnds bnds) ^ " . " ^
	 (string_of_proposition p) ^ " in " ^ (string_of_term trm) ^ " end")
    | PolyInst(trm,tys) ->
	(4,
	 string_of_term trm ^ 
	 "(*[" ^
	 (String.concat "," (List.map string_of_ty tys)) ^
	 "]*)")
  in
    if level' > level then "(" ^ str ^ ")" else str

and string_of_term t = string_of_term' 999 t

and string_of_modest m = "<string_of_modest>"

and string_of_term_list delim level lst = String.concat delim (List.map (string_of_term' level) lst)

and string_of_prop_list delim level lst = String.concat delim (List.map (string_of_prop level) lst)

and string_of_name_app str = function
    [] -> str
  | lst-> str ^ " " ^ string_of_term_list " " 8 lst

and string_of_prop level p =
  let (level', str) = match p with
      True -> (0, "true")
    | False -> (0, "false")
    | SimpleSupport sty -> (0, "||" ^ string_of_sty sty ^ "||")
    | SimplePer sty -> (0, "=(" ^ string_of_sty sty ^ ")=")
    | BasicProp n -> (0, string_of_ln n)
    | Equal (t, u) -> (9, (string_of_term' 9 t) ^ " = " ^ (string_of_term' 9 u))
    | And [] -> (0, "true")
    | And lst -> (10, string_of_prop_list " and " 10 lst)
    | Imply (p, q) -> (13, (string_of_prop 12 p) ^ " ==> " ^ (string_of_prop 13 q))
    | Iff (p, q) -> (13, (string_of_prop 12 p) ^ " <=> " ^ (string_of_prop 12 q))
    | Not p -> (9, "not " ^ (string_of_prop 9 p))
    | Forall ((n, ty), p) -> (14, "all (" ^ (string_of_name n) ^ " : " ^
			      (string_of_ty ty) ^ ") . " ^ (string_of_prop 14 p))
    | ForallSupport ((n, sty), p) -> (14, "all (" ^ (string_of_name n) ^ " : ||" ^
			      (string_of_sty sty) ^ "||) . " ^ (string_of_prop 14 p))
    | PLambda ((n, ty), p) ->
	(14, "Pfun " ^ string_of_name n ^ " : " ^ string_of_ty ty ^ " => " ^ string_of_prop 14 p)
    | PApp (SimpleSupport sty, t) -> (0, (string_of_term t) ^ " : ||" ^ string_of_sty sty ^ "||")
    | PApp (PApp (SimplePer sty, t), u) -> (0, (string_of_term t) ^ "=(" ^ string_of_sty sty ^ ")=" ^ string_of_term u)
    | PApp (PApp (BasicProp (LN(_,N(_,(Per|Infix0|Infix1|Infix2|Infix3|Infix4))) as op), t), u) ->
	(8, (string_of_infix (string_of_term u) op (string_of_term t)))
    | PApp (BasicProp (LN(_,N(_,Support)) as op), u) ->
	(9, string_of_term u ^ " : " ^ (string_of_ln op))
    | PApp (p, t) -> (0, string_of_prop 9 p ^ " " ^ string_of_term' 9 t)
    | PObligation (bnds, p, q) ->
	(14,
	 "assure " ^ (string_of_bnds bnds) ^ " . " ^
	 (string_of_proposition p) ^ " in " ^ (string_of_proposition q) ^ " end")
(*
    | PObligation ((_, TopTy), p, q) -> (14, "assure " ^ string_of_prop 14 p ^ " in " ^ string_of_prop 14 q)
    | PObligation ((n, ty), p, q) ->
	(14,
	"assure " ^ (string_of_name n) ^ " : " ^ (string_of_ty ty) ^ " . " ^
	  (string_of_prop 14 p) ^ " in " ^ string_of_prop 14 q ^ " end")
*)

    | PCase (t, lst) ->
	(14, "match " ^ (string_of_term' 13 t) ^ " with " ^
	    (String.concat " | "
	      (List.map (fun (pat, p) ->
		string_of_pat pat  ^ " => " ^ (string_of_prop 14 p)) lst)))
    | PLet (pat, t, p) ->
	(14, "let " ^ (string_of_pat pat) ^ " = " ^
	   (string_of_term' 13 t) ^ " in " ^ (string_of_prop 14 p) ^ " end")

  in
    if level' > level then "(" ^ str ^ ")" else str

and string_of_proposition p = string_of_prop 999 p

and string_of_pat = function
    WildPat -> "_"
  | VarPat nm -> string_of_name nm
  | TuplePat pats -> 
      "(" ^ (String.concat "," (List.map string_of_pat pats)) ^ ")"
  | ConstrPat(lb, None) ->
      "`" ^ lb
  | ConstrPat(lb, Some (n,ty)) ->
      "`" ^ lb ^ " (" ^ string_of_name n ^ ":" ^ string_of_ty ty ^ ")"

and string_of_proptype' level pt = 
  let (level', str) = match pt with
      Prop -> (0, "Prop")
    | PropArrow(t, pt) ->
	(12, string_of_ty t ^ " -> " ^ string_of_proptype' 12 pt)
  in
    if level' > level then "(" ^ str ^ ")" else str

and string_of_proptype pt = string_of_proptype' 999 pt

and string_of_bnd (n,t) = 
  string_of_name n ^ " : " ^ string_of_ty t

and string_of_bnds bnds =
    String.concat ", " (List.map string_of_bnd bnds)

and string_of_mbnd (n,mset) = 
  string_of_name n ^ ":" ^ string_of_modest mset

and string_of_mbnds mbnds =
    String.concat ", " (List.map string_of_mbnd mbnds)

and string_of_pbnd (n,pt) = 
  string_of_name n ^ ":" ^ string_of_proptype pt

and string_of_pbnds pbnds =
    String.concat ", " (List.map string_of_pbnd pbnds)

and string_of_annots = function
    [] -> ""
  | Annot_NoOpt::rest -> "[Definitional] " ^ (string_of_annots rest)
  | Annot_Declare _::rest -> string_of_annots rest

and string_of_assertion asn =
  "(** Assertion " ^ string_of_tyvars asn.atyvars ^ 
    string_of_pbnds asn.apbnds ^ " " ^ asn.alabel ^ " " ^ 
    string_of_annots asn.aannots ^ ":\n" ^ 
    (string_of_proposition asn.aprop) ^ "\n*)"

and string_of_assertions assertions = 
  (String.concat "\n" (List.map string_of_assertion assertions))

and string_of_tyvars = function
    [] -> ""
  | [nm] -> string_of_name nm ^ " " 
  | nms -> "(" ^ (String.concat "," (List.map string_of_name nms)) ^ ") "

and string_of_spec = function
    Spec(nm, ValSpec (tyvars, ty), assertions) ->
      "val " ^ string_of_tyvars tyvars ^ 
      (string_of_name nm) ^ " : " ^ (string_of_ty ty) ^ "\n"
      ^ string_of_assertions assertions
  | Spec(nm, TySpec None, assertions) ->
      "type " ^ string_of_name nm ^ "\n" ^ string_of_assertions assertions
  | Spec(nm, TySpec (Some ty), assertions) -> 
      "type " ^ string_of_name nm ^ " = " ^ (string_of_ty ty) ^ "\n" ^ 
	string_of_assertions assertions
  | Spec(nm, ModulSpec sgntr, assertions) ->
      "module " ^ string_of_name nm ^ " : " ^ (string_of_signat sgntr) ^
	string_of_assertions assertions
  | Spec(nm, SignatSpec signat, assertions) ->
      "signature " ^ string_of_name nm ^ " = " ^ (string_of_signat signat) ^
	string_of_assertions assertions
  | Spec(nm, PropSpec pt, assertions) ->
      "(* proposition " ^ string_of_name nm ^ " : " ^ (string_of_proptype pt) ^
      " *)" ^ string_of_assertions assertions
  | Assertion assertion ->
      string_of_assertion assertion
  | Comment cmmnt -> "(*" ^ cmmnt ^ "*)\n"

and string_of_signat = function
    SignatName nm -> string_of_name nm
  | Signat body  -> "sig\n" ^ (String.concat "\n\n" (List.map string_of_spec body)) ^ "\nend\n"
  | SignatFunctor ((n,t), body) -> 
      "functor (" ^ string_of_name n ^ " : " ^ (string_of_signat t) ^ ") ->\n" ^
      (string_of_signat body) ^ "\n"
  | (SignatApp _) as s ->
      let hd, args = collectSignatApps s in
	"(** " ^ (string_of_signat hd) ^
	(String.concat " " (List.map (fun m -> "(" ^ (string_of_modul m) ^ ")") args)) ^
	" *) " ^
	"XXX: SHOULD COMPUTE SIGNATURE APPLICATION HERE"
  | SignatProj(mdl,nm) -> 
      string_of_modul mdl ^ "." ^ string_of_name nm

let string_of_toplevel body = 
      String.concat "\n\n" (List.map string_of_spec body)

let display_subst sbst =
  let doOne stringizeFn ln x =
    print_string ("[" ^ string_of_ln ln ^ "~>" ^ stringizeFn x ^ "]")
  in let do_modul mdl mdl' = print_string ("[" ^ string_of_modul mdl ^ "~>" ^ 
					    string_of_modul mdl' ^ "]")
  in  (print_string "Terms: ";
       LNMap.iter (doOne string_of_term) sbst.terms;
       print_string "\nTypes: ";
       LNMap.iter (doOne string_of_ty) sbst.tys;
       print_string "\nPropositions: ";
       LNMap.iter (doOne string_of_ln) sbst.props;
       print_string "\nModuls: ";
       ModulMap.iter do_modul sbst.moduls)





(* If we ever let obligations appear in *types*, this will have
   to be modified! *)

(*****************)
(** {2 Hoisting} *)
(*****************)

(* The hoist functions are intended to be run on optimized code *)

let rec listminus lst1 lst2 =
  match lst1 with
      [] -> []
    | x::xs ->
	if (List.mem x lst2) || (List.mem x xs) then 
	  listminus xs lst2
	else 
	  x :: (listminus xs lst2)

(* The next two functions are used in reduce, but we need to pull them
   out of the (very large) mutually-recursive nest so that they can be
   used polymorphically.
*)
type 'a pattern_match =
    Yes of 'a | Maybe | No

let rec pmatch (fLet : pattern * term * 'a -> 'a) matchee pat (trm:'a) = 
  match matchee, pat with 
    (_, WildPat) ->
      Yes (fLet(WildPat, matchee, trm))
  | (_, VarPat nm) ->
      Yes (fLet(VarPat nm, matchee, trm))
  | (Tuple matchees, TuplePat pats ) -> 
      pmatches fLet matchees pats trm
  | (Inj(lbl1,None), ConstrPat(lbl2,None)) when lbl1 = lbl2 ->
      Yes trm
  | (Inj(lbl1,Some trm1), ConstrPat(lbl2, Some(nm2,_))) when lbl1 = lbl2 ->
      Yes (fLet(VarPat nm2,trm1, trm))
  | (Inj _, ConstrPat _) -> No
  | _                    -> Maybe

and pmatches fLet matchees pats trm =
  match matchees, pats with
    [], [] -> Yes trm
  | m::ms, p::ps ->
      begin
	match pmatches fLet ms ps trm with
	  No       -> No
	| Maybe    -> Maybe
	| Yes trm' -> pmatch fLet m p trm' 
      end
  | _, _ -> failwith "Outsyn.pmatches"

(*
   Subtleties in hosting obligations.
   ----------------------------------

   Suppose we have the proposition "prp1 /\ prp2" where
   
      (obs1, prp1') = hoistProp prp1
      (obs2, prp2') = hoistProp prp2

   That is, obs1 contains all the obligations in prp1, and prp1' contains
   whatever's left over, and then similarly for obs2 and prp2'.
   
   The "naive" result would then be
      (obs1 @ obs2,  prp1' /\ prp2')

   But this doesn't quite work:
   (1) hoisting obs1 above prp2' might capture free variables
       in obs2 and in prp2'
   (2) hoisting obs2 above prp1' might capture free variables 
       in prp1', including those bound in obs1.

  Now, if the original code contained no shadowing, then some of
  these possibilities might be impossible.  But, hoisting naturally
  creates shadowing:

  (3) bound variables in prp2' might shadow bound variables in obs1
  (4) bound variables in prp1' might shadow bound variables in obs2

  This isn't an issue of correctness; it just breaks any obvious
  no-shadowing invariant we might hope to maintain.  

  In general, there's no easy way to avoid creating shadowing, at
  least if hoisting is a one-pass algorithm; you don't know where to
  alpha-vary prp2' (or obs1) until both have been computed, and
  similarly you don't know where to alpha-vary prp1' (or obs2) until
  both of these have been computed.

  [Well, you could alpha-vary everything as you go along, trying to
  make every bound variable in the entire program distinct, or
  maintain this as an invariant, but that's bad for readability,
  and such an invariant would be very difficult to maintain correctly.]

  [Actually it's possible that this shadowing, where the other variable
  is always an obligation, might not be an issue.  But since it's not
  100% sure that translate doesn't generate shadowing, we might as
  well make the code work even if there is shadowing in the input.]


  So, we need to rename bound variables in obs1 so that they are
  different from the free variables of obs2 and of prp2', and to
  rename prp1' appropriately.

  And, we need to rename bound variables in obs2 so that they are
  different from the free variables of the (renamed!) obs1' and
  of the (renamed) prp1', and then to rename prp2' appropriately.


  In general, if you have obs_1 ... obs_n and prp_1 ... prp_n, for k
  in 1..n you need to rename the bound variables in obs_k so that they
  are different from the free variables in obs_(k+1), ..., obs_n and
  in all the propositions *except* prp_k, and to rename these bound
  variables in prp_k appropriately. [But see below.]

  --------------
  
  A useful refinement is to merge duplicates hoisted out of different
  subexpressions of the same expression, since these frequently occur
  at the moment.  For now, we only merge *syntactically identical*
  obligations.  A further refinement would be to merge
  alpha-equivalent obligations, e.g.

  assure x:nat. x<>0 in assure y:nat. y<>0 in ...

  but I'll wait until this case actually occurs in practice.

  The rule above won't give quite the right result, though, since
  if we're merging
      assure x:nat ... in trm1
  with  
      assure x:nat ... in trm2
  then we *don't* want to rename the first x, even though it's
  free in trm2.  So, we only want to look for free variables in 
  trm2 that do not correspond to an eliminated-duplicate assurance.


  Eliminating duplicates also gets a little tricky if a single list 
  contains multiple bindings for the same name.  E.g., if we have :
     assure x:nat...  
  in the first list and
     assure x:bool ... in assure x:nat ...
  we cannot eliminate the x:nat because then the x:bool will
  shadow the x:nat in the merged list, which may capture
  uses of x (from the first expression) expecting x to be a nat.

  THEREFORE, we maintain the following invariant:
     No list of obligations may bind the same variable more than once.

  Then the general renaming strategy changes to: 

  If you have obs_1 ... obs_n and prp_1 ... prp_n, for k in 1..n you
  need to rename the bound variables in obs_k so that they are
  different from the free variables in obs_(k+1), ..., obs_n, and
  different from the free variables in every proposition prp_i *except*
  prp_k (once you've removed those free variables from each corresponding to
  eliminated obligations in obs_i), and different from the bound
  variables in obs_(k+1), ..., obs_n;  then to rename these bound
  variables in prp_k appropriately.
*)


(* Compute the free variables in a list of obligations.
   Resulting list might have duplicates. *)
let rec fvObs = function
    [] -> []
  | (bnds,prp) :: rest ->
      (fvProp prp) @ (listminus (fvObs rest) (List.map fst bnds))

let bvObs obs =
  List.flatten (List.map (fun (bnds,_) -> List.map fst bnds) obs)


(* Rename a list of obligations, given bound variable names to avoid
   using, and an initial (renaming) substitution.

   Returns the list of renamed obligations, and a (renaming)
   substitution mapping from old obligation names to new ones. *)
let rec renameObs bad subst = function
    []                    -> ([], subst)
  | (bnds,prp) :: rest ->
      let (subst', bnds') = renameBnds ~bad:bad subst bnds
      in let prp' = substProp subst' prp
      in let (rest', subst'') = renameObs bad subst' rest
      in ( (bnds',prp') :: rest', subst'')
	
let rec printObs = function
    [] -> ()
  | (bnd,p)::rest -> print_endline (string_of_term (Obligation(bnd,p,EmptyTuple))); printObs rest

  
(* Returns set difference, but also returns the names of the 
   bound variables that were removed *)

(* 
   Precondition: obs1 doesn't contain 2 obligations with the same name;
     same for obs2.
*)
let rec obsListminus obs1 obs2 =
  match obs1 with
      [] -> ([], [])
    | ((bnds,_) as ob)::obs ->
	let (ns, obs') = obsListminus obs obs2
	in if (List.mem ob obs2) then
	    ((List.map fst bnds) @ ns, obs')
	  else 
	    (ns, ob::obs')


let merge2Obs' ?bad fvFun1 fvFun2 substFn1 substFn2 obs1 obs2 x1 x2 = 
(*  let _ = print_endline "Obs1"; printObs obs1
  in let _ = print_endline "Obs2"; printObs obs2 in *)

  let bad' = match bad with None -> [] | Some nms -> nms

  (* Delete exact duplicates.
     Correctness relies on the invariant that obs1 and obs2 never
     bind the same variable twice. *)
  in let (deletedNames2, obs2) = obsListminus obs2 obs1

(*  in let _ = print_endline "Obs2'"; printObs obs2  *)

  (* Get the bound variables in an obligation list *)
  in let nms2 = bvObs obs2

  in let (obs1', subst1) = 
    renameObs ((listminus (fvFun2 x2) deletedNames2) @ 
		  (fvObs obs2) @ nms2 @ bad') 
      emptysubst obs1
  in let x1' = substFn1 subst1 x1
  
  in let (obs2', subst2) = 
    renameObs (fvFun1 x1') emptysubst obs2
  in let x2' = substFn2 subst2 x2

(*  in let _ = print_endline "Obs'"; printObs obs' *)

  in (obs1', obs2', x1', x2')

let merge2Obs ?bad fvFun1 fvFun2 substFn1 substFn2 obs1 obs2 x1 x2 = 
  let (obs1', obs2', x1', x2') = 
    merge2Obs' ?bad fvFun1 fvFun2 substFn1 substFn2 obs1 obs2 x1 x2 
  in let obs' = obs1' @ obs2'
  in 
    (obs', x1', x2')

let merge3Obs fvFun1 fvFun2 fvFun3 substFn1 substFn2 substFn3 
              obs1 obs2 obs3 x1 x2 x3 = 
  let (obs12, x1', x2') = 
    merge2Obs fvFun1 fvFun2 substFn1 substFn2 obs1 obs2 x1 x2
  in let fvFun12(a,b) = fvFun1 a @ fvFun1 b
  in let substFn12 sbst (a,b) = (substFn1 sbst a, substFn2 sbst b)
  in let (obs', (x1'',x2''), x3') = 
    merge2Obs fvFun12 fvFun3 substFn12 substFn3 obs12 obs3 (x1',x2') x3
  in 
       (obs', x1'', x2'', x3')


let merge2ObsTerm ?bad obs1 obs2 trm1 trm2 = 
  merge2Obs ?bad fvTerm fvTerm substTerm substTerm obs1 obs2 trm1 trm2

let merge2ObsTermTerms obs1 obs2 trm trms =
  match (merge2ObsTerm obs1 obs2 trm (Tuple trms)) with
      (obs', trm', Tuple trms') -> (obs', trm', trms')
    | _ -> failwith "Obj.merge2ObsTermTerms: impossible"

let merge2ObsProp = merge2Obs fvProp fvProp substProp substProp

let merge2ObsPropProps obs1 obs2 prp prps =
  match (merge2ObsProp obs1 obs2 prp (And prps)) with
      (obs', prp', And prps') -> (obs', prp', prps')
    | _ -> failwith "Obj.merge2ObsPropProps: impossible"

let merge2ObsTermProp ?bad obs1 obs2 trm prp =
  merge2Obs ?bad fvTerm fvProp substTerm substProp obs1 obs2 trm prp


let merge2ObsPropModest =  merge2Obs fvProp fvModest substProp substModest

let hoistList hoistFn fvFn substFn =
   let rec nodups = function
       [] -> []
     | x::xs -> 
	 let z = nodups xs
         in if (List.mem x z) then z else x::z
   in let fvsFn xs = nodups (List.flatten (List.map fvFn xs))
   in let substsFn sbst xs = List.map (substFn sbst) xs
   in let rec loop = function
      [] -> ([], [])
    | x::xs -> 
       let (obs1, x') = hoistFn x
       in let (obs2, xs') = loop xs
       in let (obs', x'', xs'') = 
         merge2Obs fvFn fvsFn substFn substsFn obs1 obs2 x' xs'
       in (obs', x''::xs'')
    in loop

let rec hoistArm trm (lbl, bndopt, x) =
  match bndopt with
      None -> 
	let addPremise (bnds, p) = 
	  (* Alpha-vary so that bnds don't capture any variables in trm *)
	  let (subst', bnds') = renameBnds ~bad:(fvTerm trm) emptysubst bnds
	  in let p' = substProp subst' p
	  in (bnds', Imply(Equal(trm,Inj(lbl,None)), p'))
	in let (obs, x') = hoist x
	in let obs' = List.map addPremise obs
	in (obs', (lbl, None, x'))

    | Some (nm,ty) ->
	(* BEFORE:

	     match trm with
	       ...
	       | lbl(nm:ty) => assure n:t.p(n) in x

           AFTER:

             assure n':t . (forall nm:ty, trm = lbl(nm) -> p(n'))
           &
	     match trm with
               ...
               | lbl(nm) => x
        *)
	let addPremise (bnds, p) = 
	  (* Alpha-vary so that n doesn't capture any variables in trm
             or get shadowed by nm *)
	  (* Alpha-vary so that bnds don't capture any variables in trm *)
	  let (subst', bnds') = renameBnds ~bad:(fvTerm trm) emptysubst bnds
	  in let p' = substProp subst' p
	  in ( bnds',
	       Forall( (nm,ty), 
		     Imply( Equal(trm, Inj(lbl,Some(Id(LN(None,nm))))), p' ) ) )
	in let (obs, x') = hoist x
	in let obs' = List.map addPremise obs
	in (obs', (lbl, Some(nm,ty), x'))

and hoistPropArm trm1 trm2 (lbl, bndopt1, bndopt2, prp) =
  let fvtrms = fvTerm trm1 @ fvTerm trm2
  in
  match (bndopt1, bndopt2) with
      (None, None) -> 
	let addPremise (bnds, p) = 
	  (* Alpha-vary so that bnds don't capture any variables in trm1/trm2 *)
	  let (subst', bnds') = renameBnds ~bad:fvtrms emptysubst bnds
	  in let p' = substProp subst' p
	  in (bnds', Imply(And[Equal(trm1,Inj(lbl,None));
				 Equal(trm2,Inj(lbl,None))], p'))
	in let (obs, prp') = hoistProp prp
	in let obs' = List.map addPremise obs
	in (obs', (lbl, bndopt1, bndopt2, prp'))

    | (Some (nm1,ty1), None) ->
	let addPremise (bnds, p) = 
	  (* Alpha-vary so that bnds don't capture any variables in trm1/trm2
             or get shadowed by nm1 *)
	  let (subst', bnds') = renameBnds ~bad:(nm1 :: fvtrms) emptysubst bnds
	  in let p' = substProp subst' p
	  in ( bnds',
	       Forall( (nm1,ty1), 
		     Imply( And[Equal(trm1, Inj(lbl,Some(Id(LN(None,nm1)))));
			        Equal(trm2, Inj(lbl,None))], p' ) ) )
	in let (obs, prp') = hoistProp prp
	in let obs' = List.map addPremise obs
	in (obs', (lbl, bndopt1, bndopt2, prp'))

    | (None, Some (nm2,ty2)) ->
	let addPremise (bnds, p) = 
	  (* Alpha-vary so that bnds don't capture any variables in trm1/trm2
             or get shadowed by nm2 *)
	  let (subst', bnds') = renameBnds ~bad:(nm2 :: fvtrms) emptysubst bnds
	  in let p' = substProp subst' p
	  in ( bnds', 
	       Forall( (nm2,ty2), 
		     Imply( And[Equal(trm1, Inj(lbl,None));
			        Equal(trm2, Inj(lbl,Some(Id(LN(None,nm2)))))], 
			    p' ) ) )
	in let (obs, prp') = hoistProp prp
	in let obs' = List.map addPremise obs
	in (obs', (lbl, bndopt1, bndopt2, prp'))

    | (Some(nm1,ty1), Some(nm2,ty2)) ->
	let addPremise (bnds, p) = 
	  (* Alpha-vary so that bnds don't capture any variables in trm1/trm2
             or get shadowed by nm1 or nm2 *)
	  let (subst', bnds') = 
	    renameBnds ~bad:(nm1 :: nm2 :: fvtrms) emptysubst bnds
	  in let p' = substProp subst' p
	  in ( bnds',
	       Forall( (nm1,ty1), 
		 Forall( (nm2,ty2), 
		     Imply( And[Equal(trm1, Inj(lbl,Some(Id(LN(None,nm1)))));
			        Equal(trm2, Inj(lbl,Some(Id(LN(None,nm2)))))], 
			    p' ) ) ))
	in let (obs, prp') = hoistProp prp
	in let obs' = List.map addPremise obs
	in (obs', (lbl, bndopt1, bndopt2, prp'))


and hoist trm =
  match trm with
      Id _ 
    | EmptyTuple 
    | Dagger 
    | Inj(_, None) -> ([], trm)

    | App(trm1, trm2) ->
	let    (obs1,trm1') = hoist trm1
	in let (obs2, trm2') = hoist trm2
	in let (obs', trm1'', trm2'') = merge2ObsTerm obs1 obs2 trm1' trm2'
	in (obs', reduce (App(trm1'',trm2'')) )

    | Lambda((nm,ty),trm) ->
	let (obs1, trm1') = hoist trm
	in let obs1' = List.map (quantifyOb nm ty) obs1
	in (obs1', Lambda((nm,ty), trm1'))

    | Tuple trms ->
	let (obs, trms') = hoistTerms trms
	in (obs, Tuple trms')

    | Proj(n, trm) ->
	let (obs, trm') = hoist trm
	in (obs, reduce (Proj(n,trm')))

    | Inj(lbl, Some trm) ->
	let (obs, trm') = hoist trm
	in (obs, Inj(lbl, Some trm'))

    | PolyInst(trm, tys) ->
	let (obs, trm') = hoist trm
	in (obs, PolyInst(trm', tys))

    | Case(trm,arms) ->
	let (obs1, trm') = hoist trm
	in let (obs2, arms') = hoistCaseArms arms
        in let (obs', trm'', arms'') = 
           merge2Obs fvTerm fvCaseArms substTerm substCaseArms
             obs1 obs2 trm' arms'
        in (obs', Case(trm'', arms''))

    | Let(pat, trm1, trm2) ->
	(* See comments for PLet *)

	let (obs1, trm1') = hoist trm1
	in let (preobs2, trm2') = hoist trm2

	in let (obs1', preobs2', trm1'', trm2'') = 
	  merge2Obs' ~bad:(bvPat pat) fvTerm fvTerm substTerm substTerm
             obs1 preobs2 trm1' trm2'

	in let addPremise (bnds,prp) =
	  (bnds, reduceProp (PLet(pat, trm1'', prp)))
	in let obs2' = List.map addPremise preobs2'

	in let obs' = obs1' @ obs2'

	in (obs', reduce (Let(pat, trm1'', trm2'')))

(*

  Turned off for now; pulling obligations out of prp extends their scope,
  which leads to more renaming without any obviously-big gains

    | Obligation([], prp, trm) ->
	let (obs1a, prp') = hoistProp prp
	in let obs1b = [([], prp')] 
	in let obs1 = obs1a @ obs1b
	in let (obs2, trm') = hoist trm
	in let (obs', _, trm'') = 
	  (* We need to merge the obligations, and rename obs1 propositions
	     so that they don't capture any free variables of trm' *)
	  (* EmptyTuple stands for anything without free variables *)
	  merge2ObsTerm obs1 obs2 EmptyTuple trm'
	in (obs', trm'')
*)

    | Obligation(bnds, prp, trm) ->
        (** What should be the result of hoisting
               assure x:s . (assure y:t. phi(x,y) in psi(x,y)) in trm ?
            It's not entirely clear; perhaps
               assure z:s*t. (phi(z.0,z.1) /\ psi(z.0,z.1)) in trm
            But for our purposes it doesn't really matter; we can just
            pull off
               ((x,s), assure y:t.phi(x,y) in psi(x,y)) 
            as a single assurance; the really important invariant is that
            the residue trm' of trm contains no assurances, *not* that
            all assurances are at top level.
         *)
        (* But, to get a little closer to the assurances-at-top-level
           idea, and in case we can do some duplicate-assurance elimination,
           we'll at least move assurances to the top of prp.
         *)
	let (obsp, prp') = hoistProp prp
	in let obs1 = [(bnds, foldPObligation obsp prp')]
	in let (obs2, trm') = hoist trm
        (* It's ok to use @ rather than a merge function here;
        obs2 was already in the scope of obs1, and trm' was
        already in the scope of both. *)
	in (obs1 @ obs2, trm') 

and hoistTerms trms = hoistList hoist fvTerm substTerm trms

and hoistProps prps = hoistList hoistProp fvProp substProp prps

and hoistPCaseArms arms = hoistList hoistPCaseArm fvPCaseArm substPCaseArm arms

and hoistCaseArms arms = hoistList hoistCaseArm fvCaseArm substCaseArm arms

and hoistPCaseArm (pat, prp) =
  let (obs,prp') = hoistProp prp
  in let obs' = List.map (quantifyObPat pat) obs
  in (obs', (pat, prp'))

and hoistCaseArm (pat, trm) =
  let (obs,trm') = hoist trm
  in let obs' = List.map (quantifyObPat pat) obs
  in (obs', (pat, trm'))

(* Fortunately, terms cannot appear in types, so we only have
   to universally quantify the proposition parts of the
   obligations *)
and quantifyOb nm ty (bnd, prp) = (bnd, Forall((nm,ty), prp))

and quantifyObTotal nm sty (bnd, prp) = (bnd, ForallSupport((nm,sty), prp))

and quantifyObPat pat (ob : binding list * proposition) =
  match pat with
    WildPat -> ob
  | VarPat _ -> failwith "quantifyObPat: can't infer variable's type"
  | TuplePat pats -> quantifyObPats pats ob
  | ConstrPat(_,None) -> ob
  | ConstrPat(_,Some(nm,ty)) -> quantifyOb nm ty ob
  
and premiseOb hyp (bnd, prp) = (bnd, Imply(hyp, prp))
  
and quantifyObPats pats ob = 
  List.fold_right quantifyObPat pats ob

and hoistProp orig_prp =
  let ans = 
    match orig_prp with
	True
      | False -> ([], orig_prp)
	  
      | SimpleSupport _ | SimplePer _ -> ([], orig_prp)
	  (* XXX this ain't gonna work if simple types contain variables. *)

      | BasicProp _ -> ([], orig_prp)
	    
      | Equal(trm1, trm2) ->
	  let (obs1, trm1') = hoist trm1
	  in let (obs2, trm2') = hoist trm2
	  in let (obs', trm1'', trm2'') = merge2ObsTerm obs1 obs2 trm1' trm2'
	  in (obs', Equal(trm1'', trm2''))
	    
      | And prps ->
	  let (obs, prps') = hoistProps prps
	  in (obs, And prps')
	    
      | Imply(prp1, prp2) ->
	  let (obs1, prp1') = hoistProp prp1
	  in let (obs2, prp2') = hoistProp prp2
      in let obs2' = List.map (premiseOb prp1') obs2
	  in let (obs', prp1'', prp2'') = merge2ObsProp obs1 obs2' prp1' prp2'
	  in (obs', Imply(prp1'', prp2''))
	    
      | Iff(prp1, prp2) ->
	  let (obs1, prp1') = hoistProp prp1
	  in let (obs2, prp2') = hoistProp prp2
	  in let (obs', prp1'', prp2'') = merge2ObsProp obs1 obs2 prp1' prp2'
	  in (obs', Iff(prp1'', prp2''))
	    
      | Not prp ->
	  let (obs, prp') = hoistProp prp
	  in (obs, Not prp')
	    
      | Forall((nm,ty),prp) ->
	  let (obs, prp') = hoistProp prp
	  in let obs' = List.map (quantifyOb nm ty) obs
	  in (obs', Forall((nm,ty), prp') )
	    
      | ForallSupport((nm,sty),prp) ->
	  let (obs, prp') = hoistProp prp
	  in let obs' = List.map (quantifyObTotal nm sty) obs
	  in (obs', ForallSupport((nm,sty), prp') )
	    
      | PLambda((nm,ty), prp) ->
	  let (obs, prp') = hoistProp prp
	  in let obs' = List.map (quantifyOb nm ty) obs
	  in (obs', PLambda((nm,ty), prp') )
	    
      | PApp(prp, trm) ->
	  let (obs1, prp') = hoistProp prp
	  in let (obs2, trm') = hoist trm
	  in let (obs', prp'', trm'') = 
	    merge2Obs fvProp fvTerm substProp substTerm obs1 obs2 prp' trm'
	  in (obs', PApp(prp'', trm''))
	    
      | PCase(trm, arms) -> 
	  let (obs1, trm') = hoist trm
	  in let (obs2, arms') = hoistPCaseArms arms
	  in let (obs', trm'', arms'') =
	    merge2Obs fvTerm fvPCaseArms substTerm substPCaseArms
              obs1 obs2 trm' arms'
	  in (obs', PCase(trm'', arms''))
	    
      | PObligation(bnd, prp1, prp2) ->
          (* For justification of this code, see the comments for 
             the Obligation case of the hoist function. *)
	  let (obsp, prp1') = hoistProp prp1
	  in let obs1 = [(bnd, foldPObligation obsp prp1')]
	in let (obs2, prp2') = hoistProp prp2
	in (obs1 @ obs2, prp2') 
	  
    | PLet(pat, trm, prp) ->
	(* BEFORE (assuming only assure is in body):
	   let nm = (assure m:t.q(m) in trm(m)) 
                in (assure n:t.p(n,nm) in prp(n,nm))
	   
           AFTER:
           assure m':t. q(m')
           assure n':t. let nm = trm'(m'[!]) in p(n',nm)
           &
           let nm = trm'(m') in prp(n',nm)
	   
        *)
	
	let (obs1, trm') = hoist trm
	in let (preobs2, prp') = hoistProp prp
	  
	in let (obs1', preobs2', trm'', prp'') = 
	  merge2Obs' ~bad:(bvPat pat) fvTerm fvProp substTerm substProp
             obs1 preobs2 trm' prp'

	(* Normally we'd call addPremise before merging the
	   obligations, but there's a glitch.  
	    (1) We'd rather wrap the obligations in preobs2 with
                  the definition nm = trm' instead of nm = trm
                  (i.e., not duplicate the obligations in trm)

            (2) But trm' refers to variables bound in obs1.
 
                If we wrap the definition nm = trm' around preobs2
                  to get obs2, then the bound variables in obs1 that 
                  are free in trm' would be free in obs2, and then the
                  merge function would alpha-vary the bound variables
                  in obs1 to avoid capture.  At the very least this
                  is unnecessary renaming, and it's actually going to
                  be wrong --- the occurrences of trm' in the
                  wrappers won't be renamed to match.

            (3) So, we first merge the bindings, get trm''
                  (which reflects any renamings in obs1) and 
                  only then wrap preobs2.
	*)
	in let addPremise (bnds,p) =
	  (bnds, reduceProp (PLet(pat, trm'', p)))
	in let obs2' = List.map addPremise preobs2'

	in let obs' = obs1' @ obs2'

	in (obs', reduceProp (PLet(pat, trm'', prp'')))

  in
    (
      (*  print_endline "hoistProp";
	  print_endline (string_of_proposition prp);
	  print_endline ((string_of_proposition (snd ans)));	 *)
   ans)

and hoistModest {ty=ty; tot=tot; per=per} =
  let (obs1, tot') = hoistProp tot
  in let (obs2, per') = hoistProp per
  in let (obs', tot'', per'') = merge2ObsProp obs1 obs2 tot' per'
  in (obs', {ty=ty; tot=tot''; per=per''})


and foldPObligation args body = 
  List.fold_right (fun (bnd,prp) x -> PObligation(bnd,prp,x)) args body

and foldObligation args body = 
  List.fold_right (fun (bnd,prp) x -> Obligation(bnd,prp,x)) args body


(************************)
(** {2 Head-reductions} *)
(************************)

and simpleTerm = function
    Id _ -> true
  | EmptyTuple -> true
  | Dagger -> true
  | Inj(_, None) -> true
  | Inj(_, Some t) -> simpleTerm t
  | Proj(_,t) -> simpleTerm t
(*  | App(Id _, t) -> simpleTerm t
  | Tuple ts -> List.for_all simpleTerm ts
*)
  | _ -> false

and reduce trm =
  match trm with 
    App(Lambda ((nm, _), trm1), trm2) ->
      reduce (Let(VarPat nm, trm2, trm1))

  | App(Obligation(bnds,prp,trm1), trm2) ->
      (* Complicated but short method of renaming bnds to
	 avoid the free variables of trm2 *)
      let nm = wildName() 
      in let trm' = Obligation(bnds,prp,App(trm1,id nm))
      in let trm'' = substTerm (termSubst nm trm2) trm'
      in reduce trm'' 

  | App(Let(pat,trm1,trm2),trm3) ->
      let (pat',sbst) = substPat emptysubst pat (* Side-effect of refreshing *)
      in let trm2' = substTerm sbst trm2
      in let body' = reduce (App(trm2',trm3))
      in reduce (Let(pat',trm1,body'))

  | Obligation(bnds,prp,trm) ->
      Obligation(bnds, prp, reduce trm)

  | Proj(n, Obligation(bnd,prp,trm1)) ->
      Obligation(bnd, prp, reduce (Proj(n,trm1)))

  | Lambda((nm1,_), App(trm1, Id(LN(None,nm2)))) when nm1 = nm2 ->
      (** Eta-reduction ! *)
      if (List.mem nm1 (fvTerm trm1)) then
	trm
      else
	reduce trm1

  | Let (pat1, Let (pat2, trm2a, trm2b), trm3) ->
      (* Side-effect of refreshing *)
      let (pat2',sbst) = substPat emptysubst pat2
      in let trm2b' = substTerm sbst trm2b
      in reduce (Let(pat2', trm2a, Let(pat1, trm2b', trm3)))

  | Let (VarPat nm1, trm2, trm3) ->
      (* XXX May lose obligations *)
      if (simpleTerm trm2) ||
         (countTerm (occurrencesOfTermName nm1) trm3 < 2) then 
	reduce (substTerm (insertTermvar emptysubst nm1 trm2) trm3)
      else
	trm

  | Let (WildPat, trm2, trm3) ->
      (* XXX May lose obligations *)
      trm3

  | Proj(n, trm) ->
      begin
	match reduce trm with
	    Tuple trms -> 
(*	      let (obs, trms') = hoistTerms trms
	      in foldObligation obs (reduce (List.nth trms' n)) *)
	      List.nth trms n
	  | Let (pat1, trm2, trm3) -> 
	      Let (pat1, trm2, reduce (Proj (n, trm3)))
	  | Obligation (bnd1, prp2, trm3) ->
	      Obligation (bnd1, prp2, reduce (Proj (n, trm3)))
          | trm' -> Proj(n, trm')
      end

  | Case(trm1, arms) as orig_term ->
      let trm1' = reduce trm1
      in let rec armLoop = function
	  [] -> failwith "Outsyn.reduce Case: ran out of arms"
	| (pat,trm)::rest ->
	    match pmatch fLet trm1' pat trm with
	      Yes trm' -> reduce trm'
	    | No       -> armLoop rest
	    | Maybe    -> orig_term
      in armLoop arms

  | trm -> trm

and reduceProp prp = 
  match prp with
      PApp(PLambda ((nm, _), prp1), trm2) ->
	reduceProp (PLet(VarPat nm, trm2, prp1))

    | PApp(PLet(pat,trm1,prp2),trm3) ->
	let (pat',sbst) = 
	  substPat emptysubst pat (* Side-effect of refreshing *)
	in let prp2' = substProp sbst prp2
	in let body' = reduceProp (PApp(prp2',trm3))
	in reduceProp (PLet(pat',trm1,body'))

    | PLet (pat1, Let (pat2, trm2a, trm2b), prp3) ->
	let (pat2',sbst) = 
	  substPat emptysubst pat2 (* Side-effect of refreshing *)
	in let trm2b' = substTerm sbst trm2b
	in reduceProp (PLet(pat2', trm2a, PLet(pat1, trm2b', prp3)))
	  
    | PLet(VarPat nm, trm1, prp2) ->
	(* XXX: May lose obligations *)
	if (simpleTerm trm1) || 
	(countProp (occurrencesOfTermName nm) prp2 < 2) then
          reduceProp (substProp (termSubst nm trm1) prp2)
	else
          prp

    | PLet(WildPat, trm1, prp2) -> 
	(* XXX: May lose obligations *)
          prp2

    | PApp(PObligation(bnds,prp1,prp2), trm3) ->
      (* Complicated but short method of renaming bnds to
	 avoid the free variables of trm3 *)
      let nm = wildName() 
      in let prp' = PObligation(bnds,prp1,PApp(prp2,id nm))
      in let prp'' = substProp (termSubst nm trm3) prp'
      in reduceProp prp''
  |  PObligation(bnds, prp1, prp2) -> 
       PObligation(bnds, prp1, reduceProp prp2)

  | PLambda((nm1,_), PApp(prp1, Id(LN(None,nm2))))  ->
      (** Eta-reduction ! *)
      ((* print_endline (Name.string_of_name nm1);
       print_endline (Name.string_of_name nm2); *)
       if (List.mem nm1 (fvProp prp1)) then
	 prp
       else
	 reduceProp prp1)
	
(* We don't eta-reduce NamedProp's because
   they are supposed to be fully-applied.

  | PMLambda((nm1,_), NamedProp(n, Dagger, lst))
  | PLambda((nm1,_), NamedProp(n, Dagger, lst)) ->
      begin
	match List.rev lst with
	    (Id(LN(None,nm2))::es) -> 
	      let p' = NamedProp(n, Dagger, List.rev es)
	      in if (nm1 = nm2) && not (List.mem nm1 (fvProp p')) then
		  reduceProp p'
		else
		  prp
	  | _ -> prp
      end
*)

  | PCase(trm1, arms) as orig_prop ->
      let trm1' = reduce trm1
      in let rec armLoop = function
	  [] -> False (* Ran out of possible arms *)
	| (pat,trm)::rest ->
	    match pmatch fPLet trm1' pat trm with
	      Yes trm' -> reduceProp trm'
	    | No       -> armLoop rest
	    | Maybe    -> orig_prop
      in armLoop arms

  | prp -> prp
