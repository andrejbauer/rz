(* Abstract Syntax for the Output Code *)

module L = Logic


type label = string

type name = L.name

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
    NamedTy of ty_longname     (* 0 *)
  | UnitTy                     (* 0 *)
  | VoidTy                     (* 0 *)
  | TopTy                      (* 0 *)
  | SumTy of (label * ty option) list (* 1 *)
  | TupleTy of ty list         (* 2 *)
  | ArrowTy of ty * ty         (* 3 *)
  | TYPE

type modest = {
  ty : ty;
  tot : name *  proposition;
  per : name * name * proposition
}

and binding = name * ty

and term =
    Id of longname
  | Star
  | Dagger
  | App of term * term
  | Lambda of binding * term
  | Tuple of term list
  | Proj of int * term
  | Inj of label * term option
  | Case of term * (label * binding option * term) list
  | Let of name * term * term
  | Obligation of binding * proposition * term

(** specifications are expressed in classical logic
    (negative fragment to be exact)
*)
and proposition =
  | True
  | False
  | IsPer of ty_name
  | IsPredicate of name
  | NamedTotal of ty_longname * term
  | NamedPer of ty_longname * term * term
  | NamedProp of longname * term * term list
  | Equal of term * term
  | And of proposition list
  | Cor of proposition list (** classical or *)
  | Imply of proposition * proposition
  | Iff of proposition * proposition
  | Not of proposition
  | Forall of binding * proposition
  | ForallTotal of binding * proposition
  | Cexists of binding * proposition (** classical existential *)

type assertion = string * binding list * proposition

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

and modul_binding = modul_name * signat

and toplevel = 
    Signatdef  of signat_name * signat
  | TopComment of string
  | TopModul   of modul_name  * signat
    

let tln_of_tyname nm = TLN (None, nm)
let ln_of_name nm = LN (None, nm)
let string_of_name = Syntax.string_of_name

let id nm = Id (ln_of_name nm)

let mk_word str = Syntax.N(str, Syntax.Word)
let mk_id str = Id (LN(None, Syntax.N(str,Syntax.Word)))
let tuplify = function [] -> Dagger | [t] -> t | ts -> Tuple ts

let tupleOrDagger = function
    [] -> Dagger
  | xs -> Tuple xs

let tupleOrTopTy = function
    [] -> TopTy
  | ts -> TupleTy ts

(** ======== FREE VARIABLES ======= *)

let rec fvModest flt acc {tot=(x,p); per=(u,v,q)} =
  fvProp' (u::v::flt) (fvProp' (x::flt) acc p) q

and fvTerm' flt acc = function
  | Id (LN(None,nm)) -> 
      if List.mem nm flt then acc else nm :: acc
  | Star -> acc
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
  | Obligation ((n, s), p, t) -> fvTerm' (n::flt) (fvProp' (n::flt) acc p) t

and fvProp' flt acc = function
    True -> acc
  | False -> acc
  | IsPer _ -> acc
  | IsPredicate _ -> acc
  | NamedTotal (s, t) -> fvTerm' flt acc t
  | NamedPer (s, u, v) -> fvTerm' flt (fvTerm' flt acc v) u
  | Equal (u, v) -> fvTerm' flt (fvTerm' flt acc u) v
  | And lst -> List.fold_left (fun a t -> fvProp' flt a t) acc lst
  | Cor lst -> List.fold_left (fun a t -> fvProp' flt a t) acc lst
  | Imply (u, v) -> fvProp' flt (fvProp' flt acc v) u
  | Forall ((n, _), p) -> fvProp' (n::flt) acc p
  | ForallTotal ((n, _), p) -> fvProp' (n::flt) acc p
  | Cexists ((n, _), p) -> fvProp' (n::flt) acc p
  | Not p -> fvProp' flt acc p
  | Iff (p, q) -> fvProp' flt (fvProp' flt acc p) q
  | NamedProp (_, t, lst) -> List.fold_left (fvTerm' flt) (fvTerm' flt acc t) lst

let fvTerm = fvTerm' [] []
let fvProp = fvProp' [] []

(** ====== SUBSTITUTION FUNCTIONS ========= *)

module NameOrder   = struct
                       type t = name
                       let compare = Pervasives.compare
                     end

module TyNameOrder = struct
                       type t = ty_name
                       let compare = Pervasives.compare
                     end

module ModulNameOrder = struct
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

let occursSubst sbst str =
  (NameMap.fold (fun (Syntax.N(nm,_)) _ b -> b || str = nm) sbst.terms false) ||
  (try ignore (TyNameMap.find str sbst.tys) ; true with Not_found -> false) ||
  (try ignore (ModulNameMap.find str sbst.moduls) ; true with Not_found -> false)

let freshName good bad ?occ sbst =
    match occ with
	None -> Syntax.freshName good bad (occursSubst sbst)
      | Some occ -> Syntax.freshName good bad (fun n -> occ n || occursSubst sbst n)

let freshTyName good bad ?occ sbst =
  match occ with
      None -> Syntax.freshString good bad (occursSubst sbst)
    | Some occ -> Syntax.freshString good bad (fun n -> occ n || occursSubst sbst n)

let freshModulName good bad ?occ sbst =
  match occ with
      None -> Syntax.freshString good bad (occursSubst sbst)
    | Some occ -> Syntax.freshString good bad (fun n -> occ n || occursSubst sbst n)

(** The substitution functions accept an optional occ argument which is
    used for extra occur checks (for example in a context). The occ function
    accepts a string and returns a bool. No fresh variable generated by
    a substitution will satisfy the occ check. *)

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
  | IsPer nm -> IsPer nm
  | IsPredicate prdct -> IsPredicate prdct
  | NamedTotal (tln, t) -> NamedTotal (substTLN ?occ sbst tln, substTerm ?occ sbst t)
  | NamedPer (tln, u, v) -> NamedPer (substTLN ?occ sbst tln, substTerm ?occ sbst u, substTerm ?occ sbst v)
  | NamedProp (ln, u, vs) ->
      NamedProp (substLN ?occ sbst ln, substTerm ?occ sbst u, List.map (substTerm ?occ sbst) vs)
  | Equal (u, v) -> Equal (substTerm ?occ sbst u, substTerm ?occ sbst v)
  | And lst -> And (List.map (substProp ?occ sbst) lst)
  | Cor lst -> Cor (List.map (substProp ?occ sbst) lst)
  | Imply (p, q) -> Imply (substProp ?occ sbst p, substProp ?occ sbst q)
  | Iff (p, q) -> Iff (substProp ?occ sbst p, substProp ?occ sbst q)
  | Not p -> Not (substProp ?occ sbst p)
  | Forall ((n, ty), q) ->
      let sbst' = insertTermvar sbst n (id n) in
      let n' = freshName [n] [] ?occ sbst in
	Forall ((n', substTy ?occ sbst ty), substProp ?occ (insertTermvar sbst' n (id n')) q)
  | ForallTotal ((n, ty), q) ->
      let sbst' = insertTermvar sbst n (id n) in
      let n' = freshName [n] [] ?occ sbst in
	ForallTotal ((n', substTy ?occ sbst ty), substProp ?occ (insertTermvar sbst' n (id n')) q)
  | Cexists ((n, ty), q) ->
      let sbst' = insertTermvar sbst n (id n) in
      let n' = freshName [n] [] ?occ sbst in
	Cexists ((n', substTy ?occ sbst ty), substProp ?occ (insertTermvar sbst' n (id n')) q)

and substTerm ?occ sbst = function
    Id (LN (None, nm)) -> getTermvar sbst nm
  | Id (LN (Some mdl, nm)) -> Id (LN (Some (substModul ?occ sbst mdl), nm))
  | Star -> Star
  | Dagger -> Dagger
  | App (t,u) -> App (substTerm ?occ sbst t, substTerm ?occ sbst u)
  | Lambda ((n, ty), t) ->
      let sbst' = insertTermvar sbst n (id n) in
      let n' = freshName [n] [] ?occ sbst in
	Lambda ((n', substTy ?occ sbst ty), substTerm ?occ (insertTermvar sbst' n (id n')) t)
  | Let (n, t, u) ->
      let sbst' = insertTermvar sbst n (id n) in
      let n' = freshName [n] [] ?occ sbst in
	Let (n', substTerm ?occ sbst' t, substTerm ?occ (insertTermvar sbst' n (id n')) u)
  | Tuple lst -> Tuple (List.map (substTerm ?occ sbst) lst)
  | Proj (k, t) -> Proj (k, substTerm ?occ sbst t)
  | Inj (k, None) -> Inj (k, None)
  | Inj (k, Some t) -> Inj (k, Some (substTerm ?occ sbst t))
  | Case (t, lst) -> 
      Case (substTerm ?occ sbst t,
	     List.map (function
			   (lb, None, t) -> (lb, None, substTerm ?occ sbst t)
			 | (lb, Some (n, ty), t) ->
			     let sbst' = insertTermvar sbst n (id n) in
			     let n' = freshName [n] [] ?occ sbst in
			       (lb,
				Some (n', substTy ?occ sbst ty),
				substTerm ?occ (insertTermvar sbst' n (id n')) t)
		      )
	       lst)
  | Obligation ((n, ty), p, trm) ->
      let sbst' = insertTermvar sbst n (id n) in
      let n' = freshName [n] [] ?occ sbst in
      let sbst'' = insertTermvar sbst' n (id n') in
	Obligation ((n', substTy ?occ sbst ty), substProp ?occ sbst'' p, substTerm ?occ sbst'' trm)

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
  | TYPE -> TYPE

and substTyOption ?occ sbst = function
    None -> None
  | Some ty -> Some ( substTy ?occ sbst ty )

and substModest ?occ sbst {ty=ty; tot=(x,p); per=(y,z,q)} =
  { ty = substTy ?occ sbst ty;
    tot = (let x' = freshName [x] [] ?occ sbst in
	     (x', substProp ?occ (insertTermvar sbst x (id x')) p));
    per = (let y' = freshName [y] [] ?occ sbst in
	   let z' = freshName [z] [y'] ?occ sbst in
	     (y',z', substProp ?occ (insertTermvar (insertTermvar sbst y (id y')) z (id z')) q));
  }

and substSignat ?occ sbst = failwith "substSignat: not implemented"
    

(**** SOMEWHAT OLD CODE OLD CODE OLD CODE OLD CODE IS STILL USED IS STILL USED *)

let rec collectSignatApps = function
    SignatApp (s, m, n) ->
      let hd, args, _ = collectSignatApps s in
	hd, args @ [m], n
  | s -> s, [], s

let string_of_name = L.string_of_name

let rec string_of_modul = function
    ModulName nm -> nm
  | ModulProj (mdl, nm) -> (string_of_modul mdl) ^ "." ^ nm
  | ModulApp (mdl1, mdl2) -> (string_of_modul mdl1) ^ "(" ^ (string_of_modul mdl2) ^ ")"

let rec string_of_ln = function
    LN (None, nm) -> string_of_name nm
  | LN (Some mdl, nm) -> (string_of_modul mdl) ^ "."  ^ (string_of_name nm)

let rec string_of_tln = function
    TLN (None, nm) -> nm
  | TLN (Some mdl, nm) -> (string_of_modul mdl) ^ "."  ^ nm


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
	  | SumTy ts       -> (1, makeSumTy ts)
          | TupleTy ts     -> (2, makeTupleTy ts)
          | ArrowTy(t1,t2) -> (3, (string_of_ty' 2 t1) ^ " -> " ^ (string_of_ty' 3 t2))
	  | TYPE           -> (0, "TYPE"))

  in
    if (level' > level) then 
       "(" ^ str ^ ")"
    else
       str

let string_of_ty t = string_of_ty' 999 t

let string_of_infix t op u =
  match op with
      LN(None, Syntax.N(str,_)) -> t ^ " " ^ str ^ " " ^ u
    | ln -> (string_of_ln ln) ^ " " ^ t ^ " " ^ u

let rec string_of_term' level t =
  let (level', str) = match t with
      Id ln -> (0, string_of_ln ln)
    | Star -> (0, "()")
    | Dagger -> (0, "DAGGER")
    | App (App (Id (LN(_,Syntax.N(_, Syntax.Infix0)) as ln), t), u) -> 
	(9, string_of_infix (string_of_term' 9 t) ln (string_of_term' 8 u))
    | App (App (Id (LN(_,Syntax.N(_, Syntax.Infix1)) as ln), t), u) -> 
	(8, string_of_infix (string_of_term' 8 t) ln (string_of_term' 7 u))
    | App (App (Id (LN(_,Syntax.N(_, Syntax.Infix2)) as ln), t), u) -> 
	(7, string_of_infix (string_of_term' 7 t) ln (string_of_term' 6 u))
    | App (App (Id (LN(_,Syntax.N(_, Syntax.Infix3)) as ln), t), u) -> 
	(6, string_of_infix (string_of_term' 6 t) ln (string_of_term' 5 u))
    | App (App (Id (LN(_,Syntax.N(_, Syntax.Infix4)) as  ln), t), u) -> 
	(5, string_of_infix (string_of_term' 5 t) ln (string_of_term' 4 u))
    | App (t, u) -> 
	(4, (string_of_term' 4 t) ^ " " ^ (string_of_term' 3 u))
    | Lambda ((n, ty), t) ->
	(12, "fun (" ^ (Syntax.string_of_name n) ^ " : " ^ (string_of_ty ty) ^ ") -> " ^
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
			       "`" ^ lb ^ " (" ^ (Syntax.string_of_name n) ^ " : " ^
			       (string_of_ty ty) ^ ") -> " ^
			       (string_of_term' 11 u)) lst)))
    | Let (n, t, u) ->
	(13, "let " ^ (Syntax.string_of_name n) ^ " = " ^
	   (string_of_term' 13 t) ^ " in " ^ (string_of_term' 13 u))
    | Obligation ((n, ty), p, trm) ->
	(12,
	 "assure " ^ (Syntax.string_of_name n) ^ " : " ^ (string_of_ty ty) ^ " . " ^
	 (string_of_proposition p) ^ " in " ^ (string_of_term trm))
  in
    if level' > level then "(" ^ str ^ ")" else str

and string_of_term t = string_of_term' 999 t

and string_of_app = function
    (LN(_,Syntax.N(_,(Syntax.Infix0|Syntax.Infix1|Syntax.Infix2|Syntax.Infix3|Syntax.Infix4))) as ln, [Tuple [u;v]]) ->
      string_of_infix (string_of_term u) ln (string_of_term v)
  | (ln, trms) -> (string_of_ln ln) ^ (String.concat " " (List.map string_of_term trms))
      
and string_of_prop level p =
  let (level', str) = match p with
      True -> (0, "true")
    | False -> (0, "false")
    | IsPer nm -> (0, "PER(=_" ^ nm ^ ")")
    | IsPredicate prdct -> (0, "PREDICATE(" ^ (string_of_name prdct) ^ ")")
    | NamedTotal (n, t) -> (0, (string_of_term t) ^ " : ||" ^ (string_of_tln n) ^ "||")
    | NamedPer (n, t, u) -> (9, (string_of_term' 9 t) ^ " =_" ^
			       (string_of_tln n) ^ " " ^ (string_of_term' 9 u))
    | NamedProp (n, Dagger, us) -> (0, string_of_app (n, us))
    | NamedProp (n, t, u) -> (9, (string_of_term t) ^ " |= " ^ (string_of_app (n, u)))
    | Equal (t, u) -> (9, (string_of_term' 9 t) ^ " = " ^ (string_of_term' 9 u))
    | And [] -> (0, "true")
    | And lst -> (10, String.concat " and " (List.map (string_of_prop 10) lst))
    | Cor [] -> (0, "false")
    | Cor lst -> (11, String.concat " cor " (List.map (string_of_prop 11) lst))
    | Imply (p, q) -> (13, (string_of_prop 12 p) ^ " ==> " ^ (string_of_prop 13 q))
    | Iff (p, q) -> (13, (string_of_prop 12 p) ^ " <=> " ^ (string_of_prop 12 q))
    | Not p -> (9, "not " ^ (string_of_prop 9 p))
    | Forall ((n, ty), p) -> (14, "all (" ^ (Syntax.string_of_name n) ^ " : " ^
			      (string_of_ty ty) ^ ") . " ^ (string_of_prop 14 p))
    | ForallTotal ((n, ty), p) -> (14, "all (" ^ (Syntax.string_of_name n) ^ " : ||" ^
			      (string_of_ty ty) ^ "||) . " ^ (string_of_prop 14 p))
    | Cexists ((n, ty), p) -> (14, "some (" ^ (Syntax.string_of_name n) ^ " : " ^
			      (string_of_ty ty) ^ ") . " ^ (string_of_prop 14 p))
  in
    if level' > level then "(" ^ str ^ ")" else str
    
and string_of_proposition p = string_of_prop 999 p

let string_of_bind bind =
    String.concat ", " (List.map (fun (n,t) -> (Syntax.string_of_name n) ^ " : " ^ (string_of_ty t)) bind)

let string_of_assertion (nm, bind, p) =
  "(** Assertion " ^ nm ^ ":\n" ^
  (if bind = [] then "" else (string_of_bind bind) ^ ":\n") ^
  (string_of_proposition p) ^ "\n*)"

let string_of_assertions assertions = 
  (String.concat "\n" (List.map string_of_assertion assertions))

let rec string_of_spec = function
    ValSpec (nm, ty, assertions) ->
      "val " ^ (Syntax.string_of_name nm) ^ " : " ^ (string_of_ty ty) ^ "\n"
      ^ string_of_assertions assertions
    | TySpec (nm, None, assertions) -> 
	"type " ^ nm ^ "\n" ^ string_of_assertions assertions
    | TySpec (nm, Some ty, assertions) -> 
	"type " ^ nm ^ " = " ^ (string_of_ty ty) ^ "\n" ^ 
	string_of_assertions assertions
    | AssertionSpec assertion ->
	string_of_assertion assertion
    | ModulSpec (nm, sgntr) ->
	"module " ^ nm ^ " : " ^ (string_of_signat sgntr)
    | Comment cmmnt -> "(*" ^ cmmnt ^ "*)\n"

and string_of_signat = function
    SignatName s -> s
  | Signat body  -> "sig\n" ^ (String.concat "\n\n" (List.map string_of_spec body)) ^ "\nend\n"
  | SignatFunctor ((n,t), body) -> 
      "functor (" ^ n ^ " : " ^ (string_of_signat t) ^ ") ->\n" ^
      (string_of_signat body) ^ "\n"
  | (SignatApp _) as s ->
      let hd, args, res = collectSignatApps s in
	"(** " ^ (string_of_signat hd) ^
	(String.concat " " (List.map (fun m -> "(" ^ (string_of_modul m) ^ ")") args)) ^
	" *) " ^
	(string_of_signat res)

let string_of_toplevel = function
    (Signatdef (s, signat)) ->
      "module type " ^ s ^ " =\n" ^ (string_of_signat signat) ^ "\n"
  | TopComment cmmnt -> "(**" ^ cmmnt ^ "*)"
  | TopModul (mdlnm, signat) ->
      "module " ^ mdlnm ^ " : " ^ string_of_signat signat

let display_subst sbst =
  let do_term nm trm = print_string ("[" ^ string_of_name nm ^ "~>" ^ 
					  string_of_term trm ^ "]")
  in let do_ty tynm ty = print_string ("[" ^ tynm ^ "~>" ^ 
					string_of_ty ty ^ "]")
  in let do_modul mdlnm mdl = print_string ("[" ^ mdlnm ^ "~>" ^ 
					    string_of_modul mdl ^ "]")
  in  (print_string "Terms: ";
       NameMap.iter do_term sbst.terms;
       print_string "\nTypes: ";
       TyNameMap.iter do_ty sbst.tys;
       print_string "\nModuls: ";
       ModulNameMap.iter do_modul sbst.moduls)
