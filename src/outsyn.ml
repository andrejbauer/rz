(* Abstract Syntax for the Output Code *)

open Name

module L = Logic

type modul_name = L.model_name

type modul =
    ModulName of modul_name
  | ModulProj of modul * modul_name
  | ModulApp  of modul * modul

type longname = LN of modul option * name

type ty_name = L.set_name
type ty_longname = TLN of modul option * ty_name

type signat_name = L.theory_name

type ty =
    NamedTy of ty_longname                 (* 0 *)
  | UnitTy                                 (* 0 *)
  | VoidTy                                 (* 0 *)
  | TopTy                                  (* 0 *)
  | SumTy of (label * ty option) list      (* 1 *)
  | TupleTy of ty list                     (* 2 *)
  | ArrowTy of ty * ty                     (* 3 *)

(** Modest set, or a uniform family of modest sets. *)
and modest = {
  ty : ty;
  tot : proposition; (* propositional abstraction (indexing ->) ty -> Prop *)
  per : proposition; (* propositional abstraction (indexing ->) ty -> ty -> Prop *)
}

and binding = name * ty

and mbinding = name * modest

and term =
    Id of longname
  | EmptyTuple
  | Dagger
  | App of term * term
  | Lambda of binding * term
  | Tuple of term list
  | Proj of int * term
  | Inj of label * term option
  | Case of term * (label * binding option * term) list
  | Let of name * term * term
  | Obligation of binding list * proposition * term

(** Propositional function *)
and proposition =
  | True                                       (* truth *)
  | False                                      (* falsehood *)
  | IsPer of ty_name * term list               (* the fact that a type is equipped with a per *)
  | IsPredicate of name * ty option * (name * modest) list
                                               (* [name] is a (parametrized) predicate  *)
  | IsEquiv of proposition * modest            (* is a stable equivalence relation *)
  | NamedTotal of ty_longname * term list      (* totality of a term *)
  | NamedPer of ty_longname * term list        (* extensional equality of terms *)
  | NamedProp of longname * term * term list   (* basic proposition with a realizer *)
  | Equal of term * term                       (* (observational?) equality of terms *)
  | And of proposition list                    (* conjunction *)
  | Cor of proposition list                    (* classical disjunction *)
  | Imply of proposition * proposition         (* implication *)
  | Iff of proposition * proposition           (* equivalence *)
  | Not of proposition                         (* negation *)
  | Forall of binding * proposition            (* universal quantifier *)
  | ForallTotal of binding * proposition       (* universal ranging over total elements *)
  | Cexists of binding * proposition           (* classical existential *)
  | PApp of proposition * term                 (* application of propositional function *)
  | PMApp of proposition * term                (* application of propositional function to a total element *)
  | PLambda of binding * proposition           (* abstraction of a proposition over a type *)
  | PMLambda of mbinding * proposition         (* abstraction over a modest set *)
  | PObligation of binding list * proposition * proposition   (* obligation *)
  | PCase of term * term * (label * binding option * binding option * proposition) list (* propositional case *)

type proptype = 
    | Prop
    | PropArrow of binding * proptype
    | PropMArrow of mbinding * proptype 

type assertion = string * proposition

type signat_element =
    ValSpec of name * ty * assertion list
  | ModulSpec of modul_name * signat
  | AssertionSpec of assertion
  | TySpec of ty_name * ty option * assertion list
  | Comment of string

and signat =
    SignatName of signat_name
  | Signat of signat_element list
  | SignatFunctor of modul_binding * signat
  | SignatApp of signat * modul * signat (** SignatApp(f,m,n): n is the result of f(m) *)

and signatkind =
    | ModulSignatKind    (* Kind of theories that classify modules,
		            including classifiers for functors *)
    | SignatKindArrow of modul_binding * signatkind (* Classifies SignatFunctors *)

and modul_binding = modul_name * signat

and toplevel = 
    Signatdef  of signat_name * signat
  | TopComment of string
  | TopModul   of modul_name  * signat
    
let tln_of_tyname nm = TLN (None, nm)
let ln_of_name nm = LN (None, nm)

let id nm = Id (ln_of_name nm)
let namedty nm = NamedTy (tln_of_tyname nm)

let mk_word str = N(str, Word)
let mk_id str = Id (LN(None, N(str,Word)))
let tuplify = function [] -> Dagger | [t] -> t | ts -> Tuple ts

let tupleOrDagger = function
    [] -> Dagger
  | xs -> Tuple xs

let tupleOrTopTy = function
    [] -> TopTy
  | ts -> TupleTy ts

let curried_app head args =
  List.fold_left (fun ap x -> App (ap, x)) head args

let nested_lambda args trm =
  List.fold_right (fun b t -> Lambda (b, t)) args trm

let rec dagger_of_ty = function
    NamedTy _ -> Dagger (* XXX: suspicous, should unfold definition? *)
  | UnitTy -> failwith "Cannot make a dagger from UnitTy"
  | VoidTy -> failwith "Cannot make a dagger from VoidTy"
  | TopTy -> Dagger
  | SumTy _ -> failwith "Cannot make a dagger from SumTy"
  | TupleTy lst -> Tuple (List.map dagger_of_ty lst)
  | ArrowTy (t1, t2) -> Lambda ((wildName(), t1), Dagger)


(** ======== FREE VARIABLES ======= *)

let rec fvTerm' flt acc = function
  | Id (LN(None,nm)) -> 
      if List.mem nm flt then acc else nm :: acc
  | Id (LN(Some _, _)) -> acc
  | EmptyTuple -> acc
  | Dagger -> acc
  | App (u, v) -> fvTerm' flt (fvTerm' flt acc u) v
  | Lambda ((n, s), t) -> fvTerm' (n::flt) acc t
  | Tuple lst -> List.fold_left (fun a t -> fvTerm' flt a t) acc lst
  | Proj (_, t) -> fvTerm' flt acc t
  | Inj (_, Some t) -> fvTerm' flt acc t
  | Inj (_, None) -> acc
  | Case (t, lst) ->
      fvCaseArms' flt (fvTerm' flt acc t) lst
  | Let (n, t1, t2) -> fvTerm' flt (fvTerm' (n::flt) acc t2) t1
  | Obligation (bnds, p, t) -> 
      let flt' = (List.map fst bnds) @ flt
      in fvTerm' flt' (fvProp' flt' acc p) t

and fvCaseArm' flt acc (_, bnd, t) =
    fvTerm' (match bnd with None -> flt | Some (n, _) -> n::flt) acc t

and fvCaseArms' flt acc arms =
    List.fold_left (fvCaseArm' flt) acc arms

and fvProp' flt acc = function
    True -> acc
  | False -> acc
  | IsPer (_, lst) -> fvTermList' flt acc lst
  | IsPredicate (_, _, lst) -> fvModestList' flt acc lst
  | IsEquiv (r, {tot=p; per=q}) -> fvProp' flt (fvProp' flt (fvProp' flt acc p) q) r
  | NamedTotal (_, lst) -> fvTermList' flt acc lst
  | NamedPer (_, lst) -> fvTermList' flt acc lst
  | Equal (u, v) -> fvTerm' flt (fvTerm' flt acc u) v
  | And lst -> fvPropList' flt acc lst
  | Cor lst -> fvPropList' flt acc lst
  | Imply (u, v) -> fvProp' flt (fvProp' flt acc v) u
  | Forall ((n, _), p) -> fvProp' (n::flt) acc p
  | ForallTotal ((n, _), p) -> fvProp' (n::flt) acc p
  | Cexists ((n, _), p) -> fvProp' (n::flt) acc p
  | Not p -> fvProp' flt acc p
  | Iff (p, q) -> fvProp' flt (fvProp' flt acc p) q
  | NamedProp (LN(None,nm), t, lst) ->
      let acc' = fvTerm' flt (fvTermList' flt acc lst) t in
	if List.mem nm flt then acc' else nm :: acc'
  | NamedProp (LN(Some _, _), t, lst) -> fvTerm' flt (fvTermList' flt acc lst) t
  | PApp (p, t) -> fvProp' flt (fvTerm' flt acc t) p
  | PMApp (p, t) -> fvProp' flt (fvTerm' flt acc t) p
  | PLambda ((n, _), p) -> fvProp' (n::flt) acc p
  | PMLambda ((n, {tot=p; per=q}), r) -> fvProp' (n::flt) (fvProp' flt (fvProp' flt acc p) q) r
  | PObligation (bnds, p, q) -> 
      let flt' = (List.map fst bnds) @ flt
      in fvProp' flt' (fvProp' flt' acc p) q

  | PCase (t1, t2, lst) ->
	fvPCaseArms' flt (fvTerm' flt (fvTerm' flt acc t1) t2) lst

and fvPCaseArm' flt acc (_, bnd1, bnd2, t) = 
  let flt1 = match bnd1 with None -> flt | Some (n, _) -> n::flt in
  let flt2 = match bnd2 with None -> flt | Some (n, _) -> n::flt1 in
    fvProp' flt2 acc t

and fvPCaseArms' flt acc arms =
      List.fold_left (fvPCaseArm' flt) acc arms

and fvModest' flt acc {tot=p; per=q} = fvProp' flt (fvProp' flt acc p) q

and fvPropList' flt acc = List.fold_left (fun a t -> fvProp' flt a t) acc

and fvTermList' flt acc = List.fold_left (fun a t -> fvTerm' flt a t) acc

and fvModestList' flt acc = List.fold_left (fun a t -> fvModest' flt a (snd t)) acc


let fvTerm = fvTerm' [] []
let fvProp = fvProp' [] []
let fvModest = fvModest' [] []
let fvPCaseArm = fvPCaseArm' [] []
let fvPCaseArms = fvPCaseArms' [] []
let fvCaseArm = fvCaseArm' [] []
let fvCaseArms = fvCaseArms' [] []

(** ====== SUBSTITUTION FUNCTIONS ========= *)

module NameOrder =
struct
  type t = name
  let compare = Pervasives.compare
end

module TyNameOrder =
struct
  type t = ty_name
  let compare = Pervasives.compare
end

module ModulNameOrder =
struct
  type t = modul_name
  let compare = Pervasives.compare
end

module NameMap = Map.Make(NameOrder)

module TyNameMap = Map.Make(TyNameOrder)

module ModulNameMap = Map.Make(ModulNameOrder)

(** A substitution is a simultaneous map from names, type names and module names. *)

type subst = {terms: term NameMap.t;
              tys: ty TyNameMap.t;
              moduls: modul ModulNameMap.t}

let emptysubst = {terms = NameMap.empty;
		  tys = TyNameMap.empty;
		  moduls = ModulNameMap.empty}

let fvSubst {terms=ts} = NameMap.fold (fun _ t acc -> fvTerm' [] acc t) ts []

let insertTermvar sbst nm trm =
  {sbst with terms = NameMap.add nm trm sbst.terms}

let insertTyvar sbst nm ty =
  {sbst with tys = TyNameMap.add nm ty sbst.tys}

let insertModulvar sbst strng mdl =
  {sbst with moduls = ModulNameMap.add strng mdl sbst.moduls}

let termsSubst lst =
  List.fold_left (fun sbst (nm,trm) -> insertTermvar sbst nm trm) emptysubst lst

let termSubst nm trm = insertTermvar emptysubst nm trm

let getTermvar sbst nm =
   try (NameMap.find nm sbst.terms) with Not_found -> Id (ln_of_name nm)

let getTyvar sbst tynm =
   try (TyNameMap.find tynm sbst.tys) with Not_found -> NamedTy (tln_of_tyname tynm)

let getModulvar sbst mdlnm =
   try (ModulNameMap.find mdlnm sbst.moduls) with Not_found -> ModulName mdlnm

(** see also display_subst below *)

exception FoundName
let occursSubstName sbst nm =
  try
    ignore (NameMap.find nm sbst.terms) ;
    true
  with
      Not_found -> false

let occursSubstTyname sbst str =
  try ignore (TyNameMap.find str sbst.tys) ; true with Not_found -> false

let occursSubstModulname sbst nm =
  try ignore (ModulNameMap.find nm sbst.moduls) ; true with Not_found -> false

let freshVar good ?(bad=[]) ?(occ=(fun _ -> false)) sbst =
  freshName good bad (fun n -> occ n || occursSubstName sbst n)

(* These do not seem to be used anywhere
let freshTyName good bad ?occ sbst =
  match occ with
      None -> freshName good bad (occursSubstTyname sbst)
    | Some occ -> freshName good bad (fun n -> occ n || occursSubstTyname sbst n)

let freshModulName good bad ?occ sbst =
  match occ with
      None -> freshName good bad (occursSubstModulname sbst)
    | Some occ -> freshName good bad (fun n -> occ n || occursSubstModulname sbst n)
*)

(** The substitution functions accept an optional occ argument which
    is used for extra occur checks (for example in a context). The occ
    function accepts a name and returns a bool. No fresh variable
    generated by a substitution will satisfy the occ check. *)

let rec substLN ?occ sbst = function
    (LN (None, _)) as ln -> ln
  | LN (Some mdl, nm) -> LN (Some (substModul ?occ sbst mdl), nm)

and substTLN ?occ sbst = function
    (TLN (None, _)) as tln -> tln
  | TLN (Some mdl, nm) -> TLN (Some (substModul ?occ sbst mdl), nm)

and substModul ?occ sbst = function
    ModulName nm -> getModulvar sbst nm
  | ModulProj (mdl, nm) -> ModulProj (substModul ?occ sbst mdl, nm)
  | ModulApp (mdl1, mdl2) -> ModulApp (substModul ?occ sbst mdl1, substModul ?occ sbst mdl2)

and substProp ?occ sbst = function
    True -> True
  | False -> False
  | IsPer (nm, lst) -> IsPer (nm, substTermList ?occ sbst lst)
  | IsPredicate (n, ty, lst) ->
      IsPredicate (n, substTyOption ?occ sbst ty, lst)
	(* XXX: Broken, because it should substitute also in the binding list lst. *)
  | IsEquiv (r, {ty=t; tot=p; per=q}) ->
      IsEquiv (substProp ?occ sbst r,
	      {ty = substTy ?occ sbst t; tot = substProp ?occ sbst p; per = substProp ?occ sbst q})
  | NamedTotal (tln, lst) -> NamedTotal (substTLN ?occ sbst tln, substTermList ?occ sbst lst)
  | NamedPer (tln, lst) -> NamedPer (substTLN ?occ sbst tln, substTermList ?occ sbst lst)
  | NamedProp (ln, t, lst) -> NamedProp (substLN ?occ sbst ln, substTerm ?occ sbst t, substTermList ?occ sbst lst)
  | Equal (u, v) -> Equal (substTerm ?occ sbst u, substTerm ?occ sbst v)
  | And lst -> And (substPropList ?occ sbst lst)
  | Cor lst -> Cor (substPropList ?occ sbst lst)
  | Imply (p, q) -> Imply (substProp ?occ sbst p, substProp ?occ sbst q)
  | Iff (p, q) -> Iff (substProp ?occ sbst p, substProp ?occ sbst q)
  | Not p -> Not (substProp ?occ sbst p)
  | Forall ((n, ty), q) ->
      let n' = freshVar [n] ~bad:(fvSubst sbst) ?occ sbst in
	Forall ((n', substTy ?occ sbst ty), substProp ?occ (insertTermvar sbst n (id n')) q)
  | ForallTotal ((n, ty), q) ->
      let n' = freshVar [n] ~bad:(fvSubst sbst) ?occ sbst in
	ForallTotal ((n', substTy ?occ sbst ty), substProp ?occ (insertTermvar sbst n (id n')) q)
  | Cexists ((n, ty), q) ->
      let n' = freshVar [n] ~bad:(fvSubst sbst) ?occ sbst in
	Cexists ((n', substTy ?occ sbst ty), substProp ?occ (insertTermvar sbst n (id n')) q)
  | PApp (p, t) -> PApp (substProp ?occ sbst p, substTerm ?occ sbst t)
  | PMApp (p, t) -> PMApp (substProp ?occ sbst p, substTerm ?occ sbst t)
  | PLambda ((n, s), p) ->
      let n' = freshVar [n] ~bad:(fvSubst sbst) ?occ sbst in
	PLambda ((n', s), substProp ?occ (insertTermvar sbst n (id n')) p)
  | PMLambda ((n, {ty=t; tot=p; per=q}), r) ->
      let n' = freshVar [n] ~bad:(fvSubst sbst) ?occ sbst in
	PMLambda ((n', {ty=substTy ?occ sbst t; tot=substProp ?occ sbst p; per=substProp ?occ sbst q}),
		 substProp ?occ (insertTermvar sbst n (id n')) r)
  | PObligation (bnds, p, q) ->
      let (sbst', bnds') = renameBnds ?occ sbst bnds
      in 
	PObligation (bnds', substProp ?occ sbst' p, substProp ?occ sbst' q)

  | PCase (t1, t2, lst) -> 
	PCase (substTerm ?occ sbst t1, substTerm ?occ sbst t2,
	       substPCaseArms ?occ sbst lst)

and substPCaseArm ?occ sbst (lb, bnd1, bnd2, p) =
  let update_subst sbst0 = function
      None -> None, sbst0
    | Some (n, ty) ->
	let n' =  freshVar [n] ?occ sbst0 in
      	  Some (n', substTy ?occ sbst ty), insertTermvar sbst0 n (id n')
  in let bnd1', sbst1 = update_subst sbst  bnd1
  in let bnd2', sbst2 = update_subst sbst1 bnd2 
  in (lb, bnd1', bnd2', substProp ?occ sbst2 p)

and substPCaseArms ?occ sbst arms =
  List.map (substPCaseArm ?occ sbst) arms

and renameBnds ?occ ?bad sbst = function
    [] -> (sbst, [])
  | (n,ty)::bnds -> 
      let bad' = match bad with None -> fvSubst sbst | Some b -> b
      in let n' = freshVar [n] ?occ ~bad:bad' sbst
      in let bnd' = (n', substTy ?occ sbst ty)
      in let sbst' = insertTermvar sbst n (id n')
      in let (sbst'', bnds') = renameBnds ?occ ~bad:(n'::bad') sbst' bnds
      in (sbst'', bnd'::bnds')

and substTerm ?occ sbst = function
    Id (LN (None, nm)) -> getTermvar sbst nm
  | Id (LN (Some mdl, nm)) -> Id (LN (Some (substModul ?occ sbst mdl), nm))
  | EmptyTuple -> EmptyTuple
  | Dagger -> Dagger
  | App (t,u) -> App (substTerm ?occ sbst t, substTerm ?occ sbst u)
  | Lambda ((n, ty), t) ->
      let n' = freshVar [n] ?occ sbst in
	Lambda ((n', substTy ?occ sbst ty), substTerm ?occ (insertTermvar sbst n (id n')) t)
  | Let (n, t, u) ->
      let n' = freshVar [n] ?occ sbst in
	Let (n', substTerm ?occ sbst t, substTerm ?occ (insertTermvar sbst n (id n')) u)
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

and substCaseArm ?occ sbst = function
			  (lb, None, t) -> (lb, None, substTerm ?occ sbst t)
			| (lb, Some (n, ty), t) ->
			    let n' = freshVar [n] ?occ sbst in
			      (lb,
			       Some (n', substTy ?occ sbst ty),
			       substTerm ?occ (insertTermvar sbst n (id n')) t)
		     
and substCaseArms ?occ sbst arms = 
   List.map (substCaseArm ?occ sbst) arms

and substProptype ?occ sbst = function
    Prop -> Prop
  | PropArrow((n,ty),pt) -> 
      let n' = freshVar [n] ?occ sbst in
	PropArrow((n', substTy ?occ sbst ty), 
		 substProptype ?occ (insertTermvar sbst n (id n')) pt)
  | PropMArrow((n,m),pt) ->
      let n' = freshVar [n] ~bad:(fvSubst sbst) ?occ sbst in
	PropMArrow((n', substModest ?occ sbst m),
		 substProptype ?occ (insertTermvar sbst n (id n')) pt)

and substTermList ?occ sbst = List.map (substTerm ?occ sbst)

and substPropList ?occ sbst = List.map (substProp ?occ sbst)

and substModestList ?occ sbst = List.map (substModest ?occ sbst)

and substTy ?occ sbst = function
    NamedTy (TLN (None, tynm)) -> getTyvar sbst tynm
  | NamedTy (TLN (Some mdl, tynm)) -> NamedTy (TLN (Some (substModul ?occ sbst mdl), tynm))
  | UnitTy -> UnitTy
  | VoidTy -> VoidTy
  | TopTy -> TopTy
  | SumTy lst -> SumTy (List.map (function
				      (lbl, None) -> (lbl, None)
				    | (lbl, Some ty) -> (lbl, Some (substTy ?occ sbst ty))) lst)
  | TupleTy lst -> TupleTy (List.map (substTy ?occ sbst) lst)
  | ArrowTy (ty1, ty2) -> ArrowTy (substTy ?occ sbst ty1, substTy ?occ sbst ty2)

and substTyOption ?occ sbst = function
    None -> None
  | Some ty -> Some ( substTy ?occ sbst ty )

and substModest ?occ sbst {ty=ty; tot=p; per=q} =
  { ty = substTy ?occ sbst ty;
    tot = substProp ?occ sbst p;
    per = substProp ?occ sbst q
  }

and substSignat ?occ sbst = function
    SignatName nm -> SignatName nm
  | Signat lst -> Signat (substSignatElements ?occ sbst lst)
  | SignatFunctor ((m,sgnt1), sgnt2) ->
      let sbst' = insertModulvar sbst m (ModulName m) in
	SignatFunctor ((m, substSignat ?occ sbst sgnt1), substSignat ?occ sbst' sgnt2)
  | SignatApp (sgnt1, mdl, sgnt2) ->
      SignatApp (substSignat ?occ sbst sgnt1,
		 substModul ?occ sbst mdl,
		 substSignat ?occ sbst sgnt2)

and substSignatElements ?occ sbst =
  let rec subst sbst = function
      [] -> []
    | ValSpec (nm, ty, lst) :: rest ->
	ValSpec (nm, substTy ?occ sbst ty, List.map (substAssertion ?occ sbst) lst) ::
	  (subst (insertTermvar sbst nm (id nm)) rest)
    | ModulSpec (mdlnm, sgnt) :: rest ->
	ModulSpec (mdlnm, substSignat ?occ sbst sgnt) ::
	  (subst (insertModulvar sbst mdlnm (ModulName mdlnm)) rest)
    | AssertionSpec assr :: rest ->
	AssertionSpec (substAssertion ?occ sbst assr) ::
	  (subst sbst rest)
    | TySpec (tynm, ty, lst) :: rest ->
	TySpec (tynm, substTyOption ?occ sbst ty, List.map (substAssertion ?occ sbst) lst) ::
	  (subst (insertTyvar sbst tynm (namedty tynm)) rest)
    | (Comment _ as cmnt) :: rest ->
	cmnt :: (subst sbst rest)
  in
    subst sbst

and substSignatElement ?occ sbst elem =
  List.hd (substSignatElements ?occ sbst [elem])

and substAssertion ?occ sbst (nm, prop) = (nm, substProp ?occ sbst prop)

and substBinding ?occ sbst (nm, ty) = (nm, substTy ?occ sbst ty)



(**** SOMEWHAT OLD CODE OLD CODE OLD CODE OLD CODE IS STILL USED IS STILL USED *)

let rec collectSignatApps = function
    SignatApp (s, m, n) ->
      let hd, args, _ = collectSignatApps s in
	hd, args @ [m], n
  | s -> s, [], s

let rec string_of_modul = function
    ModulName nm -> string_of_name nm
  | ModulProj (mdl, nm) -> (string_of_modul mdl) ^ "." ^ string_of_name nm
  | ModulApp (mdl1, mdl2) -> (string_of_modul mdl1) ^ "(" ^ (string_of_modul mdl2) ^ ")"

let rec string_of_ln = function
    LN (None, nm) -> string_of_name nm
  | LN (Some mdl, nm) -> (string_of_modul mdl) ^ "."  ^ (string_of_name nm)

let rec string_of_tln = function
    TLN (None, nm) -> string_of_name nm
  | TLN (Some mdl, nm) -> (string_of_modul mdl) ^ "."  ^ string_of_name nm


let rec string_of_ty' level t =
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
            NamedTy lname  -> (0, string_of_tln lname)
	  | UnitTy         -> (0, "unit")
	  | TopTy          -> (0, "top")
	  | VoidTy         -> (0, "void")
	  | SumTy ts       -> (1, makeSumTy ts)
          | TupleTy ts     -> (2, makeTupleTy ts)
          | ArrowTy(t1,t2) -> (3, (string_of_ty' 2 t1) ^ " -> " ^ (string_of_ty' 3 t2))
       )
  in
    if (level' > level) then 
       "(" ^ str ^ ")"
    else
       str

let string_of_ty t = string_of_ty' 999 t

let string_of_infix t op u =
  match op with
      LN(None, N(str,_)) -> t ^ " " ^ str ^ " " ^ u
    | ln -> (string_of_ln ln) ^ " " ^ t ^ " " ^ u

let rec string_of_term' level t =
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
	      (List.map (function
			     (lb, None, u) -> "`" ^ lb ^ " -> " ^  (string_of_term' 11 u)
			   | (lb, Some (n,ty), u) -> 
			       "`" ^ lb ^ " (" ^ (string_of_name n) ^ " : " ^
			       (string_of_ty ty) ^ ") -> " ^
			       (string_of_term' 11 u)) lst)))
    | Let (n, t, u) ->
	(13, "let " ^ (string_of_name n) ^ " = " ^
	   (string_of_term' 13 t) ^ " in " ^ (string_of_term' 13 u))
    | Obligation (bnds, p, trm) ->
	(12,
	 "assure " ^ (string_of_bnds bnds) ^ " . " ^
	 (string_of_proposition p) ^ " in " ^ (string_of_term trm) ^ " end")
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
    | IsPer (t, lst) -> (0, "PER(=_" ^ string_of_name_app (string_of_name t) lst ^ ")")
    | IsPredicate (p, None, _) ->
	(0, "PREDICATE(" ^ string_of_name p ^ ", ...)")
    | IsPredicate (p, Some ty, _) ->
	(0, "PREDICATE(" ^ string_of_name p ^ "," ^ string_of_ty ty ^ ", ...)")
    | IsEquiv (p, ms) ->
	(0, "EQUIVALENCE(" ^ string_of_prop 0 p ^ ", " ^ string_of_modest ms ^ ")")
    | NamedTotal (n, []) -> (0, "||" ^ (string_of_tln n) ^ "||")
    | NamedTotal (n, lst) -> (0, "||" ^ string_of_name_app (string_of_tln n) lst ^ "||")
    | NamedPer (n, lst) -> (0, "(=" ^ string_of_name_app (string_of_tln n) lst ^"=)")
    | NamedProp (n, Dagger, lst) -> (0, string_of_name_app (string_of_ln n) lst)
    | NamedProp (n, t, lst) -> (9, string_of_term t ^ " |= " ^ string_of_name_app (string_of_ln n) lst)
    | Equal (t, u) -> (9, (string_of_term' 9 t) ^ " = " ^ (string_of_term' 9 u))
    | And [] -> (0, "true")
    | And lst -> (10, string_of_prop_list " and " 10 lst)
    | Cor [] -> (0, "false")
    | Cor lst -> (11, string_of_prop_list " or " 11 lst)
    | Imply (p, q) -> (13, (string_of_prop 12 p) ^ " ==> " ^ (string_of_prop 13 q))
    | Iff (p, q) -> (13, (string_of_prop 12 p) ^ " <=> " ^ (string_of_prop 12 q))
    | Not p -> (9, "not " ^ (string_of_prop 9 p))
    | Forall ((n, ty), p) -> (14, "all (" ^ (string_of_name n) ^ " : " ^
			      (string_of_ty ty) ^ ") . " ^ (string_of_prop 14 p))
    | ForallTotal ((n, ty), p) -> (14, "all (" ^ (string_of_name n) ^ " : ||" ^
			      (string_of_ty ty) ^ "||) . " ^ (string_of_prop 14 p))
    | Cexists ((n, ty), p) -> (14, "some (" ^ (string_of_name n) ^ " : " ^
			      (string_of_ty ty) ^ ") . " ^ (string_of_prop 14 p))
    | PLambda ((n, ty), p) ->
	(14, "Pfun " ^ string_of_name n ^ " : " ^ string_of_ty ty ^ " => " ^ string_of_prop 14 p)
    | PMLambda ((n, {ty=ty; tot=p}), q) ->
	(14, "PMfun " ^ string_of_name n ^ " : " ^ (string_of_ty ty) ^ " (" ^ string_of_prop 0 p^ ") => " ^
	  string_of_prop 14 q)
    | PApp (NamedTotal (n, lst), t) -> (0, (string_of_term t) ^ " : ||" ^ string_of_name_app (string_of_tln n) lst ^ "||")
    | PApp (PApp (NamedPer (n, []), t), u) ->
	(9, (string_of_term' 9 t) ^ " =" ^ (string_of_tln n) ^ "= " ^ (string_of_term' 9 u))
    | PApp (PApp (NamedPer (n, lst), t), u) ->
	(9, (string_of_term' 9 t) ^ " =(" ^ string_of_name_app (string_of_tln n) lst ^ ")= " ^ (string_of_term' 9 u))
    | PApp (PApp (NamedProp (LN(_,N(_,(Infix0|Infix1|Infix2|Infix3|Infix4))) as op, Dagger, []), u), t) ->
	(8, (string_of_infix (string_of_term u) op (string_of_term t)))
    | PApp (PApp (NamedProp (LN(_,N(_,(Infix0|Infix1|Infix2|Infix3|Infix4))) as op, r, []), u), t) ->
	(9, string_of_term r ^ " |= " ^ (string_of_infix (string_of_term u) op (string_of_term t)))
    | PMApp (p, t) -> (9, (string_of_prop 9 p) ^ "" ^ (string_of_term' 9 t))
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

    | PCase (t1, t2, lst) ->
	let s_of_b lb = function
	    None -> "`" ^ lb
	  | Some (n, ty) -> "`" ^ lb ^ " (" ^ string_of_name n ^ ":" ^ string_of_ty ty ^ ")"
	in
	  (14, "match " ^ (string_of_term' 13 t1) ^ ", " ^ (string_of_term' 13 t2) ^ " with " ^
	    (String.concat " | "
	      (List.map (fun (lb, bnd1, bnd2, p) ->
		s_of_b lb bnd1  ^ " " ^ s_of_b lb bnd2 ^ " => " ^ (string_of_prop 14 p)) lst)) ^
	    " | _, _ -> false")
  in
    if level' > level then "(" ^ str ^ ")" else str

and string_of_proposition p = string_of_prop 999 p

and string_of_proptype' level pt = 
  let (level', str) = match pt with
      Prop -> (0, "Prop")
    | PropArrow((n,t),pt) ->
	(12, "(" ^ (string_of_name n) ^ " : " ^ (string_of_ty t) ^ ") -> " ^
	  (string_of_proptype' 12 pt))
    | PropMArrow((n,m),pt) ->
	(12, "(" ^ (string_of_name n) ^ " : " ^ (string_of_modest m) ^ ") -> " ^
	  (string_of_proptype' 12 pt))
  in
    if level' > level then "(" ^ str ^ ")" else str

and string_of_proptype pt = string_of_proptype' 999 pt

and string_of_bnd (n,t) = 
  string_of_name n ^ " : " ^ string_of_ty t

and string_of_bnds bnds : string =
    String.concat ", " (List.map string_of_bnd bnds)

let string_of_assertion (nm, p) =
  "(** Assertion " ^ nm ^ ":\n" ^ (string_of_proposition p) ^ "\n*)"

let string_of_assertions assertions = 
  (String.concat "\n" (List.map string_of_assertion assertions))

let rec string_of_spec = function
    ValSpec (nm, ty, assertions) ->
      "val " ^ (string_of_name nm) ^ " : " ^ (string_of_ty ty) ^ "\n"
      ^ string_of_assertions assertions
    | TySpec (nm, None, assertions) -> 
	"type " ^ string_of_name nm ^ "\n" ^ string_of_assertions assertions
    | TySpec (nm, Some ty, assertions) -> 
	"type " ^ string_of_name nm ^ " = " ^ (string_of_ty ty) ^ "\n" ^ 
	string_of_assertions assertions
    | AssertionSpec assertion ->
	string_of_assertion assertion
    | ModulSpec (nm, sgntr) ->
	"module " ^ string_of_name nm ^ " : " ^ (string_of_signat sgntr)
    | Comment cmmnt -> "(*" ^ cmmnt ^ "*)\n"

and string_of_signat = function
    SignatName nm -> string_of_name nm
  | Signat body  -> "sig\n" ^ (String.concat "\n\n" (List.map string_of_spec body)) ^ "\nend\n"
  | SignatFunctor ((n,t), body) -> 
      "functor (" ^ string_of_name n ^ " : " ^ (string_of_signat t) ^ ") ->\n" ^
      (string_of_signat body) ^ "\n"
  | (SignatApp _) as s ->
      let hd, args, res = collectSignatApps s in
	"(** " ^ (string_of_signat hd) ^
	(String.concat " " (List.map (fun m -> "(" ^ (string_of_modul m) ^ ")") args)) ^
	" *) " ^
	(string_of_signat res)

let string_of_toplevel = function
    (Signatdef (s, signat)) ->
      "module type " ^ string_of_name s ^ " =\n" ^ (string_of_signat signat) ^ "\n"
  | TopComment cmmnt -> "(**" ^ cmmnt ^ "*)"
  | TopModul (mdlnm, signat) ->
      "module " ^ string_of_name mdlnm ^ " : " ^ string_of_signat signat

let display_subst sbst =
  let do_term nm trm = print_string ("[" ^ string_of_name nm ^ "~>" ^ 
					  string_of_term trm ^ "]")
  in let do_ty tynm ty = print_string ("[" ^ string_of_name tynm ^ "~>" ^ 
					string_of_ty ty ^ "]")
  in let do_modul mdlnm mdl = print_string ("[" ^ string_of_name mdlnm ^ "~>" ^ 
					    string_of_modul mdl ^ "]")
  in  (print_string "Terms: ";
       NameMap.iter do_term sbst.terms;
       print_string "\nTypes: ";
       TyNameMap.iter do_ty sbst.tys;
       print_string "\nModuls: ";
       ModulNameMap.iter do_modul sbst.moduls)





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

let renaming' subst n n' = insertTermvar subst n (Id(LN(None,n')))
let renaming n n' = renaming' emptysubst n n'

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


let merge2Obs fvFun1 fvFun2 substFn1 substFn2 obs1 obs2 x1 x2 = 
(*  let _ = print_endline "Obs1"; printObs obs1
  in let _ = print_endline "Obs2"; printObs obs2 in *)

  (* Delete exact duplicates.
     Correctness relies on the invariant that obs1 and obs2 never
     bind the same variable twice. *)
  let (deletedNames2, obs2) = obsListminus obs2 obs1

(*  in let _ = print_endline "Obs2'"; printObs obs2  *)

  (* Get the bound variables in an obligation list *)
  in let nms2 = bvObs obs2

  in let (obs1', subst1) = 
    renameObs ((listminus (fvFun2 x2) deletedNames2) @ 
		  (fvObs obs2) @ nms2) 
      emptysubst obs1
  in let x1' = substFn1 subst1 x1
  
  in let (obs2', subst2) = 
    renameObs (fvFun1 x1') emptysubst obs2
  in let x2' = substFn2 subst2 x2

  in let obs' = obs1' @ obs2'

(*  in let _ = print_endline "Obs'"; printObs obs' *)

  in (obs', x1', x2')

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


let merge2ObsTerm = merge2Obs fvTerm fvTerm substTerm substTerm

let merge2ObsTermTerms obs1 obs2 trm trms =
  match (merge2ObsTerm obs1 obs2 trm (Tuple trms)) with
      (obs', trm', Tuple trms') -> (obs', trm', trms')
    | _ -> failwith "Obj.merge2ObsTermTerms: impossible"

let merge2ObsProp = merge2Obs fvProp fvProp substProp substProp

let merge2ObsPropProps obs1 obs2 prp prps =
  match (merge2ObsProp obs1 obs2 prp (And prps)) with
      (obs', prp', And prps') -> (obs', prp', prps')
    | _ -> failwith "Obj.merge2ObsPropProps: impossible"



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

    | Case(trm,arms) ->
	let (obs1, trm') = hoist trm
	in let (obs2, arms') = hoistCaseArms arms
        in let (obs', trm'', arms'') = 
           merge2Obs fvTerm fvCaseArms substTerm substCaseArms
             obs1 obs2 trm' arms'
        in (obs', Case(trm'', arms''))

    | Let(nm, trm1, trm2) ->
	(* BEFORE (assuming only assure is in body):
	      let nm = trm1 in (assure n:ty.p(n,nm) in trm2'(n))

           AFTER:
              assure n':ty. p(n',trm1)
           &
              let nm = trm1 in trm2'
        *)
	(*XXX Using a PLet would be much preferred to substitution! *)

	let (obs1, trm1') = hoist trm1
	in let (preobs2, trm2') = hoist trm2
	in let addPremise (bnds,p) =
	  let (subst', bnds') = 
	    renameBnds ~bad:((List.map fst bnds) @ fvTerm trm1') emptysubst bnds
	  in let p' = substProp subst' p
	  in (bnds', substProp (termSubst nm trm1') p')
	in let obs2 = List.map addPremise preobs2
	in let (obs', trm1'', trm2'') = merge2ObsTerm obs1 obs2 trm1' trm2'
	in (obs', reduce (Let(nm, trm1'', trm2'')))

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

and hoistPCaseArm (lbl, bndopt1, bndopt2, prp) =
  let (obs,prp') = hoistProp prp
  in let obs' = 
    match bndopt1 with
	None -> obs
      | Some (nm,ty) -> List.map (quantifyOb nm ty) obs
  in let obs'' = 
    match bndopt2 with
	None -> obs'
      | Some (nm,ty) -> List.map (quantifyOb nm ty) obs'
  in (obs'', (lbl, bndopt1, bndopt2, prp'))

and hoistCaseArm (lbl, bndopt, trm) =
  let (obs,trm') = hoist trm
  in let obs' = 
    match bndopt with
	None -> obs
      | Some (nm,ty) -> List.map (quantifyOb nm ty) obs
  in (obs', (lbl, bndopt, trm'))

(* Fortunately, terms cannot appear in types, so we only have
   to universally quantify the proposition parts of the
   obligations *)
and quantifyOb nm ty (bnd, prp) = (bnd, Forall((nm,ty), prp))

and quantifyObTotal nm ty (bnd, prp) = (bnd, ForallTotal((nm,ty), prp))
  
and substOb nm trm ((n,ty),p) =
  let sbst = termSubst nm trm
  in let n' = freshVar [n] sbst 
  in let sbst' = insertTermvar sbst n (id n') 
  in ((n', ty), substProp sbst' p)

and hoistProp prp =
  let ans = 
    match prp with
	True
      | False -> ([], prp)
	  
      | IsPer(nm, trms) ->
	  let (obs, trms') = hoistTerms trms
	    (* XXX: is it correct that the obligations never refer to nm? *)
	  (* Check to make sure *)
	in if (List.mem nm (fvTerm (Tuple trms'))) then
	    failwith "Outsyn: hoistProp: IsPer "
	  else
	    (obs, IsPer(nm, trms'))
	      
    | IsPredicate(nm, tyopt, nmmods) ->
	let process_nmmod(nm, modest) =
	  let (obs,modest') = hoistModest modest
	  in (obs, (nm,modest'))
	    (* XXX: is it correct that the obligations never refer to nm?
               or to tyopt or to bound variables in nmmods? *)
	in let (obss, nmmods') = List.split (List.map process_nmmod nmmods)
	in let obs = List.flatten obss
	in (obs, IsPredicate(nm, tyopt, nmmods'))

    | IsEquiv(prp,modest) ->
	let (obs1, prp') = hoistProp prp
	in let (obs2, modest') = hoistModest modest
	in let (obs', prp'', modest'') = 
	  merge2ObsPropModest obs1 obs2 prp' modest'
	in (obs', IsEquiv(prp'',modest''))

    | NamedTotal(nm, trms) ->
	let (obs, trms') = hoistTerms trms
	in (obs, NamedTotal(nm,trms'))

    | NamedPer(nm, trms) ->
	let (obs, trms') = hoistTerms trms
	in (obs, NamedPer(nm,trms'))

    | NamedProp(lnm, trm, trms) ->
	let (obs1, trm') = hoist trm
	in let (obs2, trms') = hoistTerms trms
	in let (obs', trm'', trms'') = merge2ObsTermTerms obs1 obs2 trm' trms'
	in (obs', NamedProp(lnm, trm'', trms''))

    | Equal(trm1, trm2) ->
	let (obs1, trm1') = hoist trm1
	in let (obs2, trm2') = hoist trm2
	in let (obs', trm1'', trm2'') = merge2ObsTerm obs1 obs2 trm1' trm2'
	in (obs', Equal(trm1'', trm2''))

    | And prps ->
	let (obs, prps') = hoistProps prps
	in (obs, And prps')

    | Cor prps ->
	let (obs, prps') = hoistProps prps
	in (obs, Cor prps')

    | Imply(prp1, prp2) ->
	let (obs1, prp1') = hoistProp prp1
	in let (obs2, prp2') = hoistProp prp2
	in let (obs', prp1'', prp2'') = merge2ObsProp obs1 obs2 prp1' prp2'
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

    | ForallTotal((nm,ty),prp) ->
	let (obs, prp') = hoistProp prp
	in let obs' = List.map (quantifyObTotal nm ty) obs
	in (obs', ForallTotal((nm,ty), prp') )

    | Cexists((nm,ty), prp) ->
	let (obs, prp') = hoistProp prp
	in let obs' = List.map (quantifyOb nm ty) obs
	in (obs', Cexists((nm,ty), prp') )

    | PLambda((nm,ty), prp) ->
	let (obs, prp') = hoistProp prp
	in let obs' = List.map (quantifyOb nm ty) obs
	in (obs', PLambda((nm,ty), prp') )

    | PMLambda((nm,ty), prp) ->
	let (obs, prp') = hoistProp prp
(*	in let obs' = List.map (quantifyMOb nm ty) obs *)
	in let rec check = function
	    [] -> true
	  | (_,prp)::rest -> 
	      not (List.mem nm (fvProp prp)) && check rest
	in if check obs then
	    (obs, PMLambda((nm,ty), prp') )
	  else
	    failwith "Outsyn.hoistProp: PMLambda"

    | PApp(prp, trm) ->
	let (obs1, prp') = hoistProp prp
	in let (obs2, trm') = hoist trm
	in let (obs', prp'', trm'') = 
	  merge2Obs fvProp fvTerm substProp substTerm obs1 obs2 prp' trm'
	in (obs', PApp(prp'', trm''))

    | PMApp(prp, trm) ->
	let (obs1, prp') = hoistProp prp
	in let (obs2, trm') = hoist trm
	in let (obs', prp'', trm'') = 
	  merge2Obs fvProp fvTerm substProp substTerm obs1 obs2 prp' trm'
	in (obs', PMApp(prp'', trm''))

    | PCase(trm1, trm2, arms) -> 
	let (obs1, trm1') = hoist trm1
	in let (obs2, trm2') = hoist trm2
	in let (obs3, arms') = hoistPCaseArms arms
	in let (obs', trm1'', trm2'', arms'') =
	     merge3Obs fvTerm fvTerm fvPCaseArms
                       substTerm substTerm substPCaseArms
                       obs1 obs2 obs3 trm1' trm2' arms'
	in (obs', PCase(trm1', trm2', arms''))

    | PObligation(bnd, prp1, prp2) ->
        (* For justification of this code, see the comments for 
           the Obligation case of the hoist function. *)
	let (obsp, prp1') = hoistProp prp1
	in let obs1 = [(bnd, foldPObligation obsp prp1')]
	in let (obs2, prp2') = hoistProp prp2
	in (obs1 @ obs2, prp2') 

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


(******************)
(** {2 Reductions *)


and simpleTerm = function
    Id _ -> true
  | EmptyTuple -> true
  | Dagger -> true
  | Inj(_, None) -> true
  | Inj(_, Some t) -> simpleTerm t
  | Proj(_,t) -> simpleTerm t
  | App(Id _, t) -> simpleTerm t
  | _ -> false

and reduce trm =
  match trm with 
    App(Lambda ((nm, _), trm1), trm2) ->
      reduce (Let(nm, trm2, trm1))

  | App(Obligation(bnd,prp,trm1), trm2) ->
      Obligation(bnd, prp, reduce (App(trm1,trm2)))
  | Proj(n, Obligation(bnd,prp,trm1)) ->
      Obligation(bnd, prp, reduce (Proj(n,trm1)))

  | Lambda((nm1,_), App(trm1, Id(LN(None,nm2)))) when nm1 = nm2 ->
      (** Eta-reduction ! *)
      if (List.mem nm1 (fvTerm trm1)) then
	trm
      else
	reduce trm1

  | Let (nm1, trm2, trm3) ->
      if (simpleTerm trm2) then
	reduce (substTerm (insertTermvar emptysubst nm1 trm2) trm3)
      else
	trm

  | Proj(n, trm) ->
      begin
	match reduce trm with
	    Tuple trms -> 
	      let (obs, trms') = hoistTerms trms
	      in foldObligation obs (reduce (List.nth trms' n))
	  | Let (nm1, trm2, trm3) -> 
	      Let (nm1, trm2, reduce (Proj (n, trm3)))
	  | Obligation (bnd1, prp2, trm3) ->
	      Obligation (bnd1, prp2, reduce (Proj (n, trm3)))
          | trm' -> Proj(n, trm')
      end

  | Case(trm1, arms) as trm ->
      begin
	let rec findArmNone lbl = function
	    (l,None,t)::rest -> 
	      if (lbl = l) then t else findArmNone lbl rest
	  | (_,Some _, _)::rest -> findArmNone lbl rest
	  | _ ->
	      failwith "Impossible:  Opt.reduce Case/findArmNone"
		
	in let rec findArmSome lbl = function
	    (l,Some(v,_),t)::rest -> 
	      if (lbl = l) then (v, t) else findArmSome lbl rest
	  | (_,None, _)::rest -> findArmSome lbl rest
	  | _ ->
	      failwith "Impossible:  Opt.reduce Case/findArmSome"

	in let (obs, trm1', arms') = 
	  (match hoist trm with
	      (obs, Case(trm1', arms')) -> (obs, trm1', arms')
	    | _ -> failwith "Impossible: Opt.reduce Case/hoist")

	in
	     match reduce trm1' with
                 Inj(lbl,None) -> 
		   foldObligation obs (reduce (findArmNone lbl arms'))

	       | Inj(lbl,Some trm3) -> 
		   foldObligation obs 
		     (let (nm,trm2) = findArmSome lbl arms'
		       in reduce (Let(nm,trm3,trm2)))
		     
	       | _ -> trm (* unhoisted! *)
      end
  | trm -> trm

let rec reduceProp prp = 
  match prp with
    PApp(PLambda ((nm, _), prp1), trm2) as trm ->
      if (simpleTerm trm2) then
        reduceProp (substProp (termSubst nm trm2) prp1)
      else
        trm

  | PApp(PObligation(bnds,prp1,prp2), trm3) ->
      (* Complicated but short method of renaming bnds to
	 avoid the free variables of trm3 *)
      let nm = wildName() 
      in let prp' = PObligation(bnds,prp1,PApp(prp2,id nm))
      in let prp'' = substProp (termSubst nm trm3) prp'
      in reduceProp prp''

  | PMApp(PObligation(bnds,prp1,prp2), trm3) ->
      (* Complicated but short method of renaming bnds to
	 avoid the free variables of trm3 *)
      let nm = wildName() 
      in let prp' = PObligation(bnds,prp1,PMApp(prp2,id nm))
      in let prp'' = substProp (termSubst nm trm3) prp'
      in reduceProp prp''
	
  |  PObligation(bnds, prp1, prp2) -> 
       PObligation(bnds, prp1, reduceProp prp2)



  | PMApp(PMLambda ((nm, _), prp1), trm2) as trm ->
      if (simpleTerm trm2) then
        reduceProp (substProp (termSubst nm trm2) prp1)
      else
        trm

  | (PLambda((nm1,_), PApp(prp1, Id(LN(None,nm2)))) |
     PMLambda((nm1,_), PMApp(prp1, Id(LN(None,nm2)))))  ->
      (** Eta-reduction ! *)
      (print_endline (Name.string_of_name nm1);
       print_endline (Name.string_of_name nm2);
       if (List.mem nm1 (fvProp prp1)) then
	prp
      else
	reduceProp prp1)

(* We don't eta-reduce NamedProp's because (according to Andrej)
   they are supposed to always be fully-applied to arguments.
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

  | prp -> prp
