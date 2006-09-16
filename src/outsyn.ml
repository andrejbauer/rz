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
  | Obligation of binding * proposition * term

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
  | PObligation of binding * proposition * proposition   (* obligation *)
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

let rec fvModest flt acc {tot=p; per=q} = fvProp' flt (fvProp' flt acc p) q

and fvTerm' flt acc = function
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
      List.fold_left
      (fun a (_, bnd, t) -> fvTerm' (match bnd with None -> flt | Some (n, _) -> n::flt) a t)
      (fvTerm' flt acc t) lst
  | Let (n, t1, t2) -> fvTerm' flt (fvTerm' (n::flt) acc t2) t1
  | Obligation ((n, s), p, t) -> fvTerm' (n::flt) (fvProp' (n::flt) acc p) t

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
  | PObligation ((n, _), p, q) -> fvProp' (n::flt) (fvProp' (n::flt) acc p) q
  | PCase (t1, t2, lst) ->
      List.fold_left
	(fun a (_, bnd1, bnd2, t) ->
	  let flt1 = match bnd1 with None -> flt | Some (n, _) -> n::flt in
	  let flt2 = match bnd2 with None -> flt | Some (n, _) -> n::flt1 in
	    fvProp' flt2 a t)
	(fvTerm' flt (fvTerm' flt acc t1) t2) lst

and fvModest' flt acc {tot=p; per=q} = fvProp' flt (fvProp' flt acc p) q

and fvPropList' flt acc = List.fold_left (fun a t -> fvProp' flt a t) acc

and fvTermList' flt acc = List.fold_left (fun a t -> fvTerm' flt a t) acc

and fvModestList' flt acc = List.fold_left (fun a t -> fvModest' flt a (snd t)) acc


let fvTerm = fvTerm' [] []
let fvProp = fvProp' [] []

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
  | PObligation ((n, s), p, q) ->
      let n' = freshVar [n] ~bad:(fvSubst sbst) ?occ sbst in
      let sbst' = insertTermvar sbst n (id n') in
	PObligation ((n', s), substProp ?occ sbst' p, substProp ?occ sbst' q)

  | PCase (t1, t2, lst) -> 
      let update_subst sbst0 = function
	  None -> None, sbst0
	| Some (n, ty) ->
	    let n' =  freshVar [n] ?occ sbst0 in
      	      Some (n', substTy ?occ sbst ty), insertTermvar sbst0 n (id n')
      in
	PCase (substTerm ?occ sbst t1, substTerm ?occ sbst t2,
	      List.map (function (lb, bnd1, bnd2, p) ->
		let bnd1', sbst1 = update_subst sbst  bnd1 in
		let bnd2', sbst2 = update_subst sbst1 bnd2 in
		  (lb, bnd1', bnd2', substProp ?occ sbst2 p))
		lst)

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
	    List.map (function
			  (lb, None, t) -> (lb, None, substTerm ?occ sbst t)
			| (lb, Some (n, ty), t) ->
			    let n' = freshVar [n] ?occ sbst in
			      (lb,
			       Some (n', substTy ?occ sbst ty),
			       substTerm ?occ (insertTermvar sbst n (id n')) t)
		     )
	      lst)
  | Obligation ((n, ty), p, trm) ->
      let n' = freshVar [n] ?occ sbst in
      let sbst' = insertTermvar sbst n (id n') in
	Obligation ((n', substTy ?occ sbst ty), substProp ?occ sbst' p, substTerm ?occ sbst' trm)

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
    | Tuple [t] -> (0, string_of_term' 0 t)
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
    | Obligation ((n, ty), p, trm) ->
	(12,
	 "assure " ^ (string_of_name n) ^ " : " ^ (string_of_ty ty) ^ " . " ^
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
    | PObligation ((_, TopTy), p, q) -> (14, "assure " ^ string_of_prop 14 p ^ " in " ^ string_of_prop 14 q)
    | PObligation ((n, ty), p, q) ->
	(14,
	"assure " ^ (string_of_name n) ^ " : " ^ (string_of_ty ty) ^ " . " ^
	  (string_of_prop 14 p) ^ " in " ^ string_of_prop 14 q ^ " end")


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

let rec string_of_proptype' level pt = 
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


let string_of_bind bind =
    String.concat ", " (List.map (fun (n,t) -> (string_of_name n) ^ " : " ^ (string_of_ty t)) bind)

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


let renaming' subst n n' = insertTermvar subst n (Id(LN(None,n')))
let renaming n n' = renaming' emptysubst n n'

let mergeObs obs1 obs2 bad0 subst0 = 
  let nms1 = List.map (fun ((n,_),_) -> n) obs1
  in let rec loop bad subst = function
      [] -> ([], subst)
    | ((nm2,ty2),prp2)::rest ->
	let nm2' = freshVar [nm2] ~bad:bad subst
	in let subst' = renaming' subst nm2 nm2'
	in let prp2' = substProp subst' prp2
	in let (rest', subst'') = loop (nm2'::bad) subst' rest
	in ( ((nm2',ty2),prp2') ::rest', subst'')
  in let (obs2', subst') = loop (nms1 @ bad0) subst0 obs2
  in (obs1 @ obs2', subst')

let rec listminus lst1 lst2 =
  match lst1 with
      [] -> []
    | x::xs ->
	if (List.mem x lst2) || (List.mem x xs) then 
	  listminus xs lst2
	else 
	  x :: (listminus xs lst2)

let merge2ObsTerm obs1 obs2 trm =
  let nms2 = List.map (fun ((nm,_),_) -> nm) obs2
  in let bad = listminus (fvTerm trm) nms2
  in let (obs', subst) = mergeObs obs1 obs2 bad emptysubst
  in (obs', substTerm subst trm)

let merge2ObsTerms obs1 obs2 trms =
  let nms2 = List.map (fun ((nm,_),_) -> nm) obs2
  in let bad = listminus (List.flatten (List.map fvTerm trms)) nms2
  in let (obs', subst) = mergeObs obs1 obs2 bad emptysubst
  in (obs', List.map (substTerm subst) trms)


let merge2ObsProp obs1 obs2 prp =
  let nms2 = List.map (fun ((nm,_),_) -> nm) obs2
  in let bad = listminus (fvProp prp) nms2
  in let (obs', subst) = mergeObs obs1 obs2 bad emptysubst
  in (obs', substProp subst prp)

let merge2ObsModest obs1 obs2 {ty=ty;per=per;tot=tot} =
  let nms2 = List.map (fun ((nm,_),_) -> nm) obs2
  in let bad = listminus (fvProp per @ fvProp tot) nms2
  in let (obs', subst) = mergeObs obs1 obs2 bad emptysubst
  in (obs', {ty=ty;
	     per = substProp subst per;
	     tot = substProp subst tot})

let rec hoistArm trm (lbl, bndopt, x) =
  match bndopt with
      None -> 
	let addPremise ((n,ty), p) = 
	  (* Alpha-vary so that n doesn't capture any variables in trm *)
	  let n' = freshVar [n] ~bad:(fvTerm trm) emptysubst
	  in let p' = substProp ( renaming n n' ) p
	  in ((n',ty), Imply(Equal(trm,Inj(lbl,None)), p'))
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
	let addPremise ((n,t), p) = 
	  (* Alpha-vary so that n doesn't capture any variables in trm
             or get shadowed by nm *)
	  let n' = freshVar [n] ~bad:(nm :: fvTerm trm) emptysubst
	  in let p' = substProp ( termSubst n (Id(LN(None,n'))) ) p
	  in ( (n',t), 
	       Forall( (nm,ty), 
		     Imply( Equal(trm, Inj(lbl,Some(Id(LN(None,nm))))), p' ) ) )
	in let (obs, x') = hoist x
	in let obs' = List.map addPremise obs
	in (obs', (lbl, Some(nm,ty), x'))

and hoistPropArm _ _ = 
  failwith "Outsyn.hoistPropArm:  unimplemented"

and hoist trm =
  match trm with
      Id _ 
    | EmptyTuple 
    | Dagger 
    | Inj(_, None) -> ([], trm)

    | App(trm1, trm2) ->
	let    (obs1,trm1') = hoist trm1
	in let (obs2, trm2') = hoist trm2
	in (obs1 @ obs2, App(trm1',trm2'))

    | Lambda((nm,ty),trm) ->
	(* Fortunately, terms cannot appear in types, so we
	   only have to universally quantify the proposition parts
	   of the obligations *)
	let (obs1, trm1') = hoist trm
	in let obs1' = List.map (quantifyOb nm ty) obs1
	in (obs1', Lambda((nm,ty), trm1'))

    | Tuple trms ->
	let (obs, trms') = hoistTerms trms
	in (obs, Tuple trms')

    | Proj(n, trm) ->
	let (obs, trm') = hoist trm
	in (obs, Proj(n,trm'))

    | Inj(lbl, Some trm) ->
	let (obs, trm') = hoist trm
	in (obs, Inj(lbl, Some trm'))

    | Case(trm,arms) ->
	let (obs1, trm') = hoist trm
	in let (obs2s, arms') = List.split (List.map (hoistArm trm) arms)
	in let obs2 = List.flatten obs2s
	in (obs1 @ obs2, Case(trm',arms'))

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
	in let addPremise ((n,ty),p) =
	  let n' = freshVar [n] ~bad:(nm :: fvTerm trm1) emptysubst
	  in let p' = substProp (termSubst n (Id(LN(None,n')))) p
	  in ((n',ty), substProp (termSubst nm trm1) p')
	in let obs2 = List.map addPremise preobs2
	in (obs1 @ obs2, Let(nm, trm1', trm2'))

    | Obligation(bnd, prp, trm) ->
	let (obs, trm') = hoist trm
	in ((bnd,prp) :: obs, trm')

and hoistTerms trms =
  let (obss, trms') = List.split (List.map hoist trms)
  in let obs = List.flatten obss
  in (obs, trms')

and quantifyOb nm ty (bnd, prp) = (bnd, Forall((nm,ty), prp))
  
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
	in let (obs', modest'') = merge2ObsModest obs1 obs2 modest'
	in (obs', IsEquiv(prp',modest''))

    | NamedTotal(nm, trms) ->
	let (obs, trms') = hoistTerms trms
	in (obs, NamedTotal(nm,trms'))

    | NamedPer(nm, trms) ->
	let (obs, trms') = hoistTerms trms
	in (obs, NamedPer(nm,trms'))

    | NamedProp(lnm, trm, trms) ->
	let (obs1, trm') = hoist trm
	in let (obs2, trms') = hoistTerms trms
	in let (obs', trms'') = merge2ObsTerms obs1 obs2 trms'
	in (obs', NamedProp(lnm, trm', trms''))

    | Equal(trm1, trm2) ->
	let (obs1, trm1') = hoist trm1
	in let (obs2, trm2') = hoist trm2
	in let (obs', trm2'') = merge2ObsTerm obs1 obs2 trm2'
	in (obs', Equal(trm1', trm2''))

    | And prps ->
	let (obs, prps') = hoistProps prps
	in (obs, And prps')

    | Cor prps ->
	let (obs, prps') = hoistProps prps
	in (obs, Cor prps')

    | Imply(prp1, prp2) ->
	let (obs1, prp1') = hoistProp prp1
	in let (obs2, prp2') = hoistProp prp2
	in let (obs', prp2'') = merge2ObsProp obs1 obs2 prp2'
	in (obs', Imply(prp1', prp2''))

    | Iff(prp1, prp2) ->
	let (obs1, prp1') = hoistProp prp1
	in let (obs2, prp2') = hoistProp prp2
	in let (obs', prp2'') = merge2ObsProp obs1 obs2 prp2'
	in (obs', Iff(prp1', prp2''))

    | Not prp ->
	let (obs, prp') = hoistProp prp
	in (obs, Not prp')

    | Forall((nm,ty),prp) ->
	(* Fortunately, terms cannot appear in types, so we
	   only have to universally quantify the proposition parts
	   of the obligations *)
	let (obs, prp') = hoistProp prp
	in let obs' = List.map (quantifyOb nm ty) obs
	in (obs', Forall((nm,ty), prp') )

    | ForallTotal((nm,ty),prp) ->
	let (obs, prp') = hoistProp prp
	in let obs' = List.map (quantifyOb nm ty) obs
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
	in let (obs', trm'') = merge2ObsTerm obs1 obs2 trm'
	in (obs', PApp(prp', trm''))

    | PMApp(prp, trm) ->
	let (obs1, prp') = hoistProp prp
	in let (obs2, trm') = hoist trm
	in let (obs', trm'') = merge2ObsTerm obs1 obs2 trm'
	in (obs', PApp(prp', trm''))

    | PCase(trm1, trm2, parms) -> 
	let (obs1, trm1') = hoist trm1
	in let (obs2, trm2') = hoist trm2
	in let (obs3s, parms') = 
	  List.split (List.map (hoistPropArm trm1 trm2) parms)
	in let obs3 = List.flatten obs3s
	in (obs1 @ obs2 @ obs3, PCase(trm1', trm2', parms')) (* XXX *)

    | PObligation(bnd, prp1, prp2) ->
	let (obs1, prp1') = hoistProp prp1
	in let (obs2, prp2') = hoistProp prp2
	in ((bnd, prp1')::obs1 @ obs2, prp2') (* XXX *)
  in
(
(*  print_endline "hoistProp";
  print_endline (string_of_proposition prp);
  print_endline ((string_of_proposition (snd ans)));	 *)
   ans)

and hoistModest {ty=ty; tot=tot; per=per} =
  let (obs1, tot') = hoistProp tot
  in let (obs2, per') = hoistProp per
  in (obs1 @ obs2, {ty=ty; tot=tot'; per=per'})

and hoistProps = function
    [] -> ([], [])
  | prp::rest as prps ->
      let (obs1,prp') = hoistProp prp
      in let (obs2,rest') = hoistProps rest
      in let nms2 = List.map (fun((n,_),_) -> n) obs2
      in let bad = listminus (List.flatten (List.map fvProp rest')) nms2
      in let (obs', subst) = mergeObs obs1 obs2 bad emptysubst
      in let rest'' = List.map (substProp subst) rest'
      in let prps' = prp' :: rest''
      in 

(*
       (print_endline "AA"; 
	List.iter (fun p -> print_endline (string_of_proposition p)) prps;
	print_endline "BB";
	List.iter (fun p -> print_endline (string_of_proposition p)) prps';
*)
	(obs', prps')
(* ) *)

(*
and hoistProps prps =
  let rec loop = function
      [] -> ([], [], [])
    | prp::rest -> 
	let (obs1,prp') = hoistProp prp
	in let (obs2,rest',fvrest') = loop rest
	in let (obs', subst) = mergeObs obs1 obs2 fvrest' emptysubst
	in let rest'' = List.map (substProp subst) rest'
	in (obs', prp'::rest'', (fvProp prp') @ fvrest')
  in let (obs, prps', _) = loop prps
  in 
       (print_endline "AA"; 
	List.iter (fun p -> print_endline (string_of_proposition p)) prps;
	print_endline "BB";
	List.iter (fun p -> print_endline (string_of_proposition p)) prps';
        (obs, prps'))
*)

and foldPObligation args body = 
  List.fold_right (fun (bnd,prp) x -> PObligation(bnd,prp,x)) args body
