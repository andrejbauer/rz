(* Abstract Syntax for the Output Code *)

type label = string

type name = Syntax.name
type longname = Logic.longname

type set_name = Syntax.set_name
type set_longname = Logic.set_longname
type structure_name = Syntax.theory_name

type ty =
    NamedTy of set_longname    (* 0 *)
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
  | IsPer of set_name
  | IsPredicate of name
  | NamedTotal of set_longname * term
  | NamedPer of set_longname * term * term
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

type signat_element =
    ValSpec of name * ty
  | StructureSpec of structure_name * struct_binding list * signat
  | AssertionSpec of string * binding list * proposition
  | TySpec of set_name * ty option
  | Comment of string

and signat =
    SignatID of string
  | Signat of signat_element list

and struct_binding = string * signat

and toplevel = 
    Signatdef of string * struct_binding list * signat
  | TopComment of string
  | TopModule of string * signat
    

let mk_word str = Syntax.N(str, Syntax.Word)
let mk_longword = Logic.ln_of_string
let ln_of_name = Logic.ln_of_name
let mk_id str = Id (mk_longword str)
let mk_poly (Syntax.N(str, _)) = mk_longword ("'" ^ str)
let tuplify = function [] -> Dagger | [t] -> t | ts -> Tuple ts

let tupleOrDagger = function
    [] -> Dagger
  | xs -> Tuple xs

let tupleOrTopTy = function
    [] -> TopTy
  | ts -> TupleTy ts

let nameSubscript s =
  try
    let k = String.rindex s '_' in
      String.sub s 0 k, Some (String.sub s (k+1) (String.length s - k - 1))
  with Not_found -> s, None

let namePrime s =
  try
    let k = String.index s '\'' in
      String.sub s 0 k, Some (String.sub s k (String.length s - k))
  with Not_found -> s, None

let splitName n =
  let m, p = namePrime n in
  let r, s = nameSubscript m in
    r, s, p

let nextName (Syntax.N(n,nt)) =
  let r, s, p = splitName n in
    Syntax.N(r ^ (match s, p with
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
	   ),
       nt)

let fresh good bad ctx =
  let rec find g =
    try
      List.find (fun x -> not (List.mem x bad) && List.for_all (fun (y,_) -> x <> y) ctx) g
    with Not_found -> find (List.map nextName g)
  in
    find good

let rec fvModest flt acc {tot=(x,p); per=(u,v,q)} =
  fvProp' (u::v::flt) (fvProp' (x::flt) acc p) q

and fvTerm' flt acc = function
  | Id (Logic.LN(s,_,_)) -> 
        let n = mk_word s in
          if List.mem n flt then acc else n :: acc
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

let fvTerm = fvTerm' [] []
let fvProp = fvProp' [] []

exception BadSubst

let fvSubst subst = List.concat (List.map (fun (_, t) -> fvTerm t) subst)

let substRemove n subst = List.filter (fun (m,_) -> n <> m) subst

let substAdd (n, n') subst =
  if n = n' then subst else (n, Id (ln_of_name n'))::subst

let rec substProp ctx s = function
    True -> True
  | False -> False
  | IsPer nm -> IsPer nm
  | IsPredicate prdct -> IsPredicate prdct
  | NamedTotal (r, t) -> NamedTotal (r, substTerm ctx s t)
  | NamedPer (r, u, v) -> NamedPer (r, substTerm ctx s u, substTerm ctx s v)
  | NamedProp (n, u, vs) -> NamedProp (n, substTerm ctx s u, List.map (substTerm ctx s) vs)
  | Equal (u, v) -> Equal (substTerm ctx s u, substTerm ctx s v)
  | And lst -> And (List.map (substProp ctx s) lst)
  | Cor lst -> Cor (List.map (substProp ctx s) lst)
  | Imply (p, q) -> Imply (substProp ctx s p, substProp ctx s q)
  | Iff (p, q) -> Iff (substProp ctx s p, substProp ctx s q)
  | Not p -> Not (substProp ctx s p)
  | Forall ((n, ty), q) as p ->
      let s' = substRemove n s in
      let n' = fresh [n] (fvSubst s') ctx in
	Forall ((n', ty), substProp ctx (substAdd (n,n') s') q)
  | ForallTotal ((n, ty), q) as p ->
      let s' = substRemove n s in
      let n' = fresh [n] (fvSubst s') ctx in
	ForallTotal ((n', ty), substProp ctx (substAdd (n,n') s') q)
  | Cexists ((n, ty), q) as p ->
      let s' = substRemove n s in
      let n' = fresh [n] (fvSubst s') ctx in
	Cexists ((n', ty), substProp ctx (substAdd (n,n') s') q)

and substTerm ctx s = function
    Id (Logic.LN(str, labels, sort) as ln) ->
      (try 
          (match (List.assoc (Syntax.N(str,Syntax.Word)) s, labels)  with
            (term',[]) -> term'
          | (Id(Logic.LN(str',labels',sort')),_) ->
               Id(Logic.LN(str',labels' @ labels, sort'))
          | (_,_) -> raise BadSubst)  (* Can't replace a model variable *)
                                      (* with anything other than a longname *)
       with Not_found -> Id ln)
  | Star -> Star
  | Dagger -> Dagger
  | App (t, u) -> App (substTerm ctx s t, substTerm ctx s u)
  | Lambda ((n, ty), t) ->
      let s' = substRemove n s in
      let n' = fresh [n] (fvSubst s') ctx in
	Lambda ((n', ty), substTerm ctx (substAdd (n,n') s') t)
  | Let (n, t, u) ->
      let s' = substRemove n s in
      let n' = fresh [n] (fvSubst s') ctx in
	Let (n', substTerm ctx s t, substTerm ctx (substAdd (n,n') s') u)
  | Tuple lst -> Tuple (List.map (substTerm ctx s) lst)
  | Proj (k, t) -> Proj (k, substTerm ctx s t)
  | Inj (k, None) -> Inj (k, None)
  | Inj (k, Some t) -> Inj (k, Some (substTerm ctx s t))
  | Case (t, lst) -> 
      Case (substTerm ctx s t,
	     List.map (function
			   (lb, None, t) -> (lb, None, substTerm ctx s t)
			 | (lb, Some (n, ty), t) ->
			     let s' = substRemove n s in
			     let n' = fresh [n] (fvSubst s') ctx in
			       (lb, Some (n', ty), substTerm ctx (substAdd (n,n') s') t)
		      ) lst)
  | Obligation ((x, ty), p, trm) ->
      let s' = substRemove x s in
	Obligation ((x, ty), substProp ctx s' p, substTerm ctx s' trm)


and substModest ctx s {ty=t; tot=(x,p); per=(y,z,q)} =
  { ty = t;
    tot = (let x' = fresh [x] [] s in
	     (x', substProp ctx (substAdd (x,x') s) p));
    per = (let y' = fresh [y] [] s in
	   let z' = fresh [z] [y'] s in
	     (y',z', substProp ctx (substAdd (y,y') (substAdd (z,z') s)) q));
  }

(*
let rec namesLNSubst = function
    [] -> []
  | (_, Logic.LN(n,[],t)) :: s -> Syntax.N(n,t) :: (namesLNSubst s)
  | _ :: s -> namesLNSubst s

let string_of_lnSubst s =
  "[" ^
  (String.concat "," (
     List.map (fun (n,m) -> (Logic.string_of_ln n) ^ "->" ^ (Logic.string_of_ln m)) s
   ))
  ^ "]"

let rec substLNTerm ctx s = function
  | Id ln -> 
      Id (try List.assoc ln s with Not_found -> ln)
  | Star -> Star
  | Dagger -> Dagger
  | App (t, u) -> App (substLNTerm ctx s t, substLNTerm ctx s u)
  | Lambda ((n, ty), t) ->
      let n' = fresh [n] (namesLNSubst s) ctx in
	Lambda ((n', ty), substLNTerm ctx s (substTerm ctx [(n,Id(ln_of_name n'))] t))
  | Let (n, t, u) ->
      let n' = fresh [n] (namesLNSubst s) ctx in
	Let (n', substLNTerm ctx s t,
	     substLNTerm ctx s (substTerm ctx [(n, Id(ln_of_name n'))] t))
  | Tuple lst -> Tuple (List.map (substLNTerm ctx s) lst)
  | Proj (k, t) -> Proj (k, substLNTerm ctx s t)
  | Inj (k, None) -> Inj (k, None)
  | Inj (k, Some t) -> Inj (k, Some (substLNTerm ctx s t))
  | Case (t, lst) -> 
      Case (substLNTerm ctx s t,
	     List.map (function
			   (lb, None, t) -> (lb, None, substLNTerm ctx s t)
			 | (lb, Some (n, ty), t) ->
			     let n' = fresh [n] (namesLNSubst s) ctx in
			       (lb, Some (n', ty),
				substLNTerm ctx s (substTerm ctx [(n, Id (ln_of_name n'))] t))
		      ) lst)
  | Obligation ((x, ty), p) ->
      let x' = fresh [x] (namesLNSubst s) ctx in
	Obligation ((x', ty), substLNProp ctx s (substProp ctx [(x,Id (ln_of_name x'))] p))

and substLNProp ctx s = function
  | True -> True
  | False -> False
  | IsPer nm -> IsPer nm
  | IsPredicate prdct -> IsPredicate prdct
  | NamedTotal (r, t) -> NamedTotal (r, substLNTerm ctx s t)
  | NamedPer (r, u, v) -> NamedPer (r, substLNTerm ctx s u, substLNTerm ctx s v)
  | NamedProp (n, u, vs) -> NamedProp (n, substLNTerm ctx s u, List.map (substLNTerm ctx s) vs)
  | Equal (u, v) -> Equal (substLNTerm ctx s u, substLNTerm ctx s v)
  | And lst -> And (List.map (substLNProp ctx s) lst)
  | Cor lst -> Cor (List.map (substLNProp ctx s) lst)
  | Imply (p, q) -> Imply (substLNProp ctx s p, substLNProp ctx s q)
  | Iff (p, q) -> Iff (substLNProp ctx s p, substLNProp ctx s q)
  | Not p -> Not (substLNProp ctx s p)
  | Forall ((n, ty), q) ->
      let n' = fresh [n] (namesLNSubst s) ctx in
	Forall ((n', ty), substLNProp ctx s (substProp ctx [(n,Id(ln_of_name n'))] q))
  | ForallTotal ((n, ty), q) ->
      let n' = fresh [n] (namesLNSubst s) ctx in
	ForallTotal ((n', ty), substLNProp ctx s (substProp ctx [(n,Id(ln_of_name n'))] q))
  | Cexists ((n, ty), q) ->
      let n' = fresh [n] (namesLNSubst s) ctx in
	Cexists ((n', ty), substLNProp ctx s (substProp ctx [(n,Id(ln_of_name n'))] q))

let replaceType s n =
  try List.assoc n s with Not_found -> n

let rec substTYTerm ctx s = function
  | Id ln -> Id ln
  | Star -> Star
  | Dagger -> Dagger
  | App (t, u) -> App (substTYTerm ctx s t, substTYTerm ctx s u)
  | Lambda ((n, ty), t) -> Lambda ((n, substTYType ctx s ty), t)
  | Let (n, t, u) -> Let (n, substTYTerm ctx s t, substTYTerm ctx s u)
  | Tuple lst -> Tuple (List.map (substTYTerm ctx s) lst)
  | Proj (k, t) -> Proj (k, substTYTerm ctx s t)
  | Inj (k, None) -> Inj (k, None)
  | Inj (k, Some t) -> Inj (k, Some (substTYTerm ctx s t))
  | Case (t, lst) -> 
      Case (substTYTerm ctx s t,
	     List.map (function
			   (lb, None, t) -> (lb, None, substTYTerm ctx s t)
			 | (lb, Some (n, ty), t) ->
			     (lb, Some (n, substTYType ctx s ty), substTYTerm ctx s t)
		      ) lst)
  | Obligation ((x, ty), p) -> Obligation ((x, substTYType ctx s ty), substTYProp ctx s p)

and substTYProp ctx s = function
  | True -> True
  | False -> False
  | IsPer nm -> IsPer (replaceType s nm)
  | IsPredicate prdct -> IsPredicate prdct
  | NamedTotal (r, t) -> NamedTotal (r, substTYTerm ctx s t)
  | NamedPer (r, u, v) ->
      NamedPer (r, substTYTerm ctx s u, substTYTerm ctx s v)
  | NamedProp (n, u, vs) -> NamedProp (n, substTYTerm ctx s u, List.map (substTYTerm ctx s) vs)
  | Equal (u, v) -> Equal (substTYTerm ctx s u, substTYTerm ctx s v)
  | And lst -> And (List.map (substTYProp ctx s) lst)
  | Cor lst -> Cor (List.map (substTYProp ctx s) lst)
  | Imply (p, q) -> Imply (substTYProp ctx s p, substTYProp ctx s q)
  | Iff (p, q) -> Iff (substTYProp ctx s p, substTYProp ctx s q)
  | Not p -> Not (substTYProp ctx s p)
  | Forall ((n, ty), q) ->
      Forall ((n, substTYType ctx s ty), substTYProp ctx s q)
  | ForallTotal ((n, ty), q) ->
      ForallTotal ((n, substTYType ctx s ty), substTYProp ctx s q)
  | Cexists ((n, ty), q) ->
      Cexists ((n, substTYType ctx s ty), substTYProp ctx s q)

and substTYType ctx s = function
    NamedTy ln -> NamedTy ln (* XXX: this might be wrong (AB) *)
  | UnitTy -> UnitTy
  | VoidTy -> VoidTy
  | TopTy -> TopTy
  | SumTy lst -> SumTy (List.map
			  (function
			       (lb, None) -> (lb, None)
			     | (lb, Some ty) -> (lb, Some (substTYType ctx s ty))) lst)
  | TupleTy lst -> TupleTy (List.map (substTYType ctx s) lst)
  | ArrowTy (u, v) -> ArrowTy (substTYType ctx s u, substTYType ctx s v)
  | TYPE -> TYPE
*)

let string_of_ln = Logic.string_of_ln

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
            NamedTy lname  -> (0, string_of_ln lname)
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
      Logic.LN(str,[],_) -> t ^ " " ^ str ^ " " ^ u
    | ln -> (string_of_ln ln) ^ " " ^ t ^ " " ^ u

let rec string_of_term' level t =
  let (level', str) = match t with
      Id ln -> (0, string_of_ln ln)
    | Star -> (0, "()")
    | Dagger -> (0, "DAGGER")
    | App (App (Id (Logic.LN(_,_, Syntax.Infix0) as ln), t), u) -> 
	(9, string_of_infix (string_of_term' 9 t) ln (string_of_term' 8 u))
    | App (App (Id (Logic.LN(_,_, Syntax.Infix1) as ln), t), u) -> 
	(8, string_of_infix (string_of_term' 8 t) ln (string_of_term' 7 u))
    | App (App (Id (Logic.LN(_,_, Syntax.Infix2) as ln), t), u) -> 
	(7, string_of_infix (string_of_term' 7 t) ln (string_of_term' 6 u))
    | App (App (Id (Logic.LN(_,_, Syntax.Infix3) as ln), t), u) -> 
	(6, string_of_infix (string_of_term' 6 t) ln (string_of_term' 5 u))
    | App (App (Id (Logic.LN(_,_, Syntax.Infix4) as  ln), t), u) -> 
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
    (Logic.LN(_,_, (Syntax.Infix0|Syntax.Infix1|Syntax.Infix2|Syntax.Infix3|Syntax.Infix4)) as ln, [Tuple [u;v]]) ->
      string_of_infix (string_of_term u) ln (string_of_term v)
  | (ln, trms) -> (string_of_ln ln) ^ (String.concat " " (List.map string_of_term trms))
      
and string_of_prop level p =
  let (level', str) = match p with
      True -> (0, "true")
    | False -> (0, "false")
    | IsPer nm -> (0, "PER(=_" ^ nm ^ ")")
    | IsPredicate prdct -> (0, "PREDICATE(" ^ (Syntax.string_of_name prdct) ^ ")")
    | NamedTotal (n, t) -> (0, (string_of_term t) ^ " : ||" ^ (string_of_ln n) ^ "||")
    | NamedPer (n, t, u) -> (9, (string_of_term' 9 t) ^ " =_" ^
			       (string_of_ln n) ^ " " ^ (string_of_term' 9 u))
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

let rec string_of_spec = function
    ValSpec (nm, ty) ->
      "val " ^ (Syntax.string_of_name nm) ^ " : " ^ (string_of_ty ty)
    | TySpec (nm, None) -> "type " ^ nm
    | TySpec (nm, Some ty) -> "type " ^ nm ^ " = " ^ (string_of_ty ty)
    | AssertionSpec (nm, bind, p) ->
	"(** Assertion " ^ nm ^ ":\n" ^
	(if bind = [] then "" else (string_of_bind bind) ^ ":\n") ^
	(string_of_proposition p) ^ "\n*)"
    | StructureSpec (nm, [], sgntr) ->
	"module " ^ nm ^ " : " ^ (string_of_signat sgntr)
    | StructureSpec (nm, mdlbind, sgntr) ->
	"module " ^ nm ^ (String.concat " "
			    (List.map (fun (nm, sgntr) ->
					 "(" ^ nm ^ " : " ^ (string_of_signat sgntr) ^ ")")
			       mdlbind)) ^ " : " ^ (string_of_signat sgntr)
    | Comment cmmnt -> "(*" ^ cmmnt ^ "*)\n"

and string_of_signat = function
    SignatID s -> s
  | Signat body -> "sig\n" ^ (String.concat "\n\n" (List.map string_of_spec body)) ^ "\nend\n"

let string_of_toplevel = function
    (Signatdef (s, args, body)) ->
      "module type " ^ s ^ " =\n" ^
      (if args = [] then "" else
	 String.concat "\n"
	   (List.map
	      (fun (n, t) -> "functor (" ^ n ^ " : " ^ (string_of_signat t) ^ ") ->\n")
	      args)) ^
      (string_of_signat body) ^ "\n"
  | TopComment cmmnt -> "(**" ^ cmmnt ^ "*)"
  | TopModule (mdlnm, signat) ->
      "module " ^ mdlnm ^ " : " ^ string_of_signat signat
