(* Abstract Syntax for the Output Code *)

open Name

module L = Logic

(*******************************************)
(** {2: Definition of the Abstract Syntax} *)
(*******************************************)

type modul_name = L.model_name

type modul =
  | ModulName of modul_name
  | ModulProj of modul * modul_name
  | ModulApp  of modul * modul
  | ModulStruct of moduldef list

and moduldef =
  | DefType of name * ty
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
  | BoolTy                                 (* 0 *)
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
  | SBoolTy
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
  | BConst of bool
  | BOp of bop * term list
  | BNot of term
  | Dagger
  | Id         of longname
  | App        of term * term
  | Lambda     of binding * term
  | Tuple      of term list
  | Proj       of int * term
  | Inj        of label * term option * ty
  | Case       of term * (pattern * term) list
  | Let        of pattern * term * term   
  | Obligation of binding list * proposition * term
  | PolyInst   of term * ty list  (* Not fully implemented yet *)

and bop = AndOp | OrOp | ImplyOp | IffOp

(** Propositional function *)
and proposition =
  | True                                      (* truth *)
  | False                                     (* falsehood *)
  | SimpleSupport of simple_ty                (* support of a simple set *)
  | SimplePer of simple_ty                    (* per of a simple set *)
  | BasicProp  of longname                    (* basic prop with a realizer *)
  | Equal      of term * term                 (* equality of terms *)
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
  | PBool       of term                       (* coercion of a boolean to a prop *)

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
  | SBoolTy -> BoolTy
  | STupleTy lst -> TupleTy (List.map ty_of_simple_ty lst)
  | SArrowTy (sty1, sty2) -> ArrowTy (ty_of_simple_ty sty1, ty_of_simple_ty sty2)

let rec simple_ty_of_ty = function
  | NamedTy nm -> SNamedTy nm
  | UnitTy -> SUnitTy
  | VoidTy -> SVoidTy
  | TopTy -> STopTy
  | BoolTy -> SBoolTy
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
  | BoolTy -> failwith "Cannot make a dagger from BoolTy"
  | SumTy _ -> failwith "Cannot make a dagger from SumTy"
  | TupleTy lst -> Tuple (List.map dagger_of_ty lst)
  | ArrowTy (t1, t2) -> Lambda ((wildName(), t1), Dagger)
  | PolyTy _ -> failwith "Cannot make a dagger from PolyTy"

let fLet(a,b,c) = Let(a,b,c)
let fPLet(a,b,c) = PLet(a,b,c)
let fPBool a = PBool a

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
  | BConst _ -> acc
  | BNot t -> fvTerm' flt acc t
  | BOp (_, lst) -> fvList' fvTerm' flt acc lst
  | Dagger -> acc
  | App (u, v) -> fvTerm' flt (fvTerm' flt acc u) v
  | Lambda ((n, s), t) -> fvTerm' (n::flt) (fvTy' flt acc s) t
  | Tuple lst -> List.fold_left (fun a t -> fvTerm' flt a t) acc lst
  | Proj (_, t) -> fvTerm' flt acc t
  | Inj (_, Some t, ty) -> fvTerm' flt (fvTy' flt acc ty) t
  | Inj (_, None, ty) -> fvTy' flt acc ty
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
  | PCase (t, lst) -> fvPCaseArms' flt (fvTerm' flt acc t) lst
  | PLet (pat, t, p) -> fvPat' flt (fvProp' ((bvPat pat)@flt) (fvTerm' flt acc t) p) pat
  | PBool t -> fvTerm' flt acc t

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
  | UnitTy | VoidTy | TopTy | BoolTy -> acc
  | NamedTy(LN(None,nm))    -> if List.mem nm flt then acc else nm :: acc
  | NamedTy(LN(Some _, _))  -> acc
  | SumTy(sumarms)          -> List.fold_left (fvSum' flt) acc sumarms
  | TupleTy tys             -> List.fold_left (fvTy' flt) acc tys
  | ArrowTy(ty1,ty2)        -> fvTy' flt (fvTy' flt acc ty1) ty2
  | PolyTy(nms,ty)          -> fvTy' (nms @ flt) acc ty

and fvSimpleTy' flt acc = function
  | SNamedTy _
  | SUnitTy
  | SVoidTy
  | STopTy
  | SBoolTy -> acc
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
let fvPat       = fvPat'       [] []

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
    | BConst _ -> 0
    | BNot t -> countTerm cp t
    | BOp (_, lst) -> countTermList cp lst
    | Dagger -> 0
    | App (u, v) -> countTerm cp u + countTerm cp v
    | Lambda ((n, s), t) -> countTerm cp t
    | Tuple lst -> countTermList cp lst
    | Proj (_, t) -> countTerm cp t
    | Inj (_, Some t, ty) -> countTerm cp t + countTy cp ty
    | Inj (_, None,ty) -> countTy cp ty
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
      | PObligation (bnds, p, q) -> countProp cp p + countProp cp q
      | PBool t -> countTerm cp t

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
    | TopTy
    | BoolTy -> 0
    | SumTy lst -> countSumArms cp lst
    | TupleTy lst -> countTys cp lst
    | ArrowTy (ty1,ty2) -> countTy cp ty1 + countTy cp ty2
    | PolyTy (_,ty) -> countTy cp ty

and countSimpleTy cp sty = 
  if (cp.styPred sty) then
    1
  else
    match sty with
      | SNamedTy(LN(None,_)) | SUnitTy | SVoidTy | STopTy | SBoolTy -> 0
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
  | PBool t -> PBool (substTerm ?occ sbst t)

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
          | BConst b   -> BConst b
	  | BNot t     -> BNot (substTerm ?occ sbst t)
	  | BOp (bop, lst) -> BOp (bop, List.map (substTerm ?occ sbst) lst)
          | Dagger     -> Dagger
          | App (t,u)  -> App (substTerm ?occ sbst t, substTerm ?occ sbst u)
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
          | Inj (k, None, ty) -> Inj (k, None, substTy ?occ sbst ty)
          | Inj (k, Some t, ty) -> Inj (k, Some (substTerm ?occ sbst t),
				       substTy ?occ sbst ty)
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
  | BoolTy -> BoolTy
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
  | (SUnitTy | SVoidTy | STopTy | SBoolTy) as sty -> sty
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
          | BoolTy         -> (0, "bool")
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
    | BConst true -> (0, "true")
    | BNot t -> (4, "not " ^ string_of_term' 4 t)
    | BOp (AndOp, lst) -> (9, string_of_term_list " && " 9 lst)
    | BOp (OrOp, lst) -> (9, string_of_term_list " || " 9 lst)
    | BOp (ImplyOp, lst) -> (9, string_of_term_list " <= " 9 lst)
    | BOp (IffOp, lst) -> (9, string_of_term_list " = " 9 lst)
    | BConst false -> (0, "false")
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
    | Inj (lb, None, _) -> (4, ("`" ^ lb))
    | Inj (lb, Some t, _) -> (4, ("`" ^ lb ^ " " ^ (string_of_term' 3 t)))
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
    | PBool t -> (0, string_of_term t)
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





