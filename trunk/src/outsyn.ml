(* Abstract Syntax for the Output Code *)

type label = string

(** XXX CS: Why isn't this NamedTy of set_name? *)

type ty =
    NamedTy of string          (* 0 *)
  | UnitTy                     (* 0 *)
  | VoidTy                     (* 0 *)
  | TopTy                      (* 0 *)
  | ListTy of ty               (* 1 *)
  | SumTy of (label * ty) list (* 1 *)
  | TupleTy of ty list         (* 2 *)
  | ArrowTy of ty * ty         (* 3 *)

type name = Syntax.name

type set_name = Syntax.set_name

type modest = {
  ty : ty;
  tot : name *  proposition;
  per : name * name * proposition
}

and binding = name * ty

and term =
    Id of name
  | Star
  | Dagger
  | App of term * term
  | Lambda of binding * term
  | Tuple of term list
  | Proj of int * term
  | Inj of label * term
  | Cases of term * (label * binding * term) list
  | Let of name * term * term
  | Obligation of binding * proposition

(** specifications are expressed in classical logic
    (negative fragment to be exact)
*)
and proposition =
  | True
  | False
  | NamedTotal of set_name * term
  | NamedPer of set_name * term * term
  | NamedProp of set_name * term * term
  | Equal of term * term
  | And of proposition list
  | Cor of proposition list (** classical or *)
  | Imply of proposition * proposition
  | Iff of proposition * proposition
  | Not of proposition
  | Forall of binding * proposition

type signat_element =
    ValSpec of name * ty
  | AssertionSpec of binding list * proposition
  | TySpec of set_name * ty option

type signat = {
  s_name : string;
  s_arg : signat_element list option;
  s_body : signat_element list
}

let mk_word n = (n, Syntax.Word)
let mk_id n = Id (mk_word n)

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

let nextName (n,nt) =
  let r, s, p = splitName n in
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
	   ),
    nt


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
    Id n -> if List.mem n flt then acc else n :: acc
  | Star -> acc
  | App (u, v) -> fvTerm' flt (fvTerm' flt acc u) v
  | Lambda ((n, s), t) -> fvTerm' (n::flt) acc t
  | Tuple lst -> List.fold_left (fun a t -> fvTerm' flt a t) acc lst
  | Proj (_, t) -> fvTerm' flt acc t
  | Inj (_, t) -> fvTerm' flt acc t
  | Cases (t, lst) -> List.fold_left (fun a (_, (n, _), t) -> fvTerm' (n::flt) a t) (fvTerm' flt acc t) lst

and fvProp' flt acc = function
    True -> acc
  | False -> acc
  | NamedTotal (s, t) -> fvTerm' flt acc t
  | NamedPer (s, u, v) -> fvTerm' flt (fvTerm' flt acc v) u
  | Equal (u, v) -> fvTerm' flt (fvTerm' flt acc u) v
  | And lst -> List.fold_left (fun a t -> fvProp' flt a t) acc lst
  | Cor lst -> List.fold_left (fun a t -> fvProp' flt a t) acc lst
  | Imply (u, v) -> fvProp' flt (fvProp' flt acc v) u
  | Forall ((n, _), p) -> fvProp' (n::flt) acc p

let fvTerm = fvTerm' [] []
let fvProp = fvProp' [] []

let substRemove n subst = List.filter (fun (m,_) -> n <> m) subst

let substAdd (n, n') s = (if n = n' then s else (n, Id n')::s)

let rec substProp ctx s = function
    True -> True
  | False -> False
  | NamedTotal (r, t) -> NamedTotal (r, substTerm ctx s t)
  | NamedPer (r, u, v) -> NamedPer (r, substTerm ctx s u, substTerm ctx s v)
  | NamedProp (n, u, v) -> NamedProp (n, substTerm ctx s u, substTerm ctx s v)
  | Equal (u, v) -> Equal (substTerm ctx s u, substTerm ctx s v)
  | And lst -> And (List.map (substProp ctx s) lst)
  | Cor lst -> Cor (List.map (substProp ctx s) lst)
  | Imply (p, q) -> Imply (substProp ctx s p, substProp ctx s q)
  | Iff (p, q) -> Iff (substProp ctx s p, substProp ctx s q)
  | Not p -> Not (substProp ctx s p)
  | Forall ((n, ty), q) as p ->
      let n' = fresh [n] (List.map fst s) ctx in
      let s' = substAdd (n,n') (substRemove n s) in
	Forall ((n, ty), substProp ctx s' q)

and substTerm ctx s = function
    Id n ->
      (try List.assoc n s with Not_found -> Id n)
  | Star -> Star
  | App (t, u) -> App (substTerm ctx s t, substTerm ctx s u)
  | Lambda ((n, ty), t) ->
      let s = substRemove n s in
      let n' = fresh [n] [] s in
	Lambda ((n, ty), substTerm ctx (substAdd (n,n') s) t)
  | Tuple lst -> Tuple (List.map (substTerm ctx s) lst)
  | Proj (k, t) -> Proj (k, substTerm ctx s t)
  | Inj (k, t) -> Inj (k, substTerm ctx s t)
  | Cases (t, lst) -> 
      Cases (substTerm ctx s t,
	     List.map (fun (lb, (n, ty), t) ->
			 let s = substRemove n s in
			 let n' = fresh [n] [] s in
			 (lb, (n', ty), substTerm ctx (substAdd (n,n') s) t)
		      ) lst)
  | Obligation ((x, ty), p) ->
	Obligation ((x, ty), substProp ctx (substRemove x s) p)

and substModest ctx s {ty=t; tot=(x,p); per=(y,z,q)} =
  { ty = t;
    tot = (let x' = fresh [x] [] s in
	     (x', substProp ctx (substAdd (x,x') s) p));
    per = (let y' = fresh [y] [] s in
	   let z' = fresh [z] [y'] s in
	     (y',z', substProp ctx (substAdd (y,y') (substAdd (z,z') s)) q));
  }


let string_of_name = function
    (n, Syntax.Word) -> n
  | (n, _) -> "( " ^ n ^ " )"


let rec string_of_ty' level t =
  let rec makeTupleTy = function
      []    -> "top"
    | [t]   -> string_of_ty' 1 t
    | t::ts -> (string_of_ty' 1 t) ^ " * " ^ (makeTupleTy ts)

  in let rec makeSumTy = function
      [] -> "void"
    | ts -> 
	"[" ^ (String.concat " | " (List.map (fun (lb,t) -> "`" ^ lb ^ " of " ^ (string_of_ty' 1 t)) ts)) ^ "]"
		
  in let (level', str ) = 
       (match t with
            NamedTy name   -> (0, name)
	  | UnitTy         -> (0, "unit")
	  | TopTy          -> (0, "top")
          | ListTy t       -> (1, (string_of_ty' 1 t) ^ "list")
	  | SumTy ts       -> (1, makeSumTy ts)
          | TupleTy ts     -> (2, makeTupleTy ts)
          | ArrowTy(t1,t2) -> (3, (string_of_ty' 2 t1) ^ " -> " ^ (string_of_ty' 3 t2)))
  in
    if (level' > level) then 
       "(" ^ str ^ ")"
    else
       str

let string_of_ty t = string_of_ty' 999 t

let rec string_of_app = function
    ((op, (Syntax.Infix0|Syntax.Infix1|Syntax.Infix2|Syntax.Infix3|Syntax.Infix4)), Tuple [u;v]) ->
      (string_of_term u) ^ " " ^ op ^ " " ^ (string_of_term v)
  | (n, (Tuple _ as t)) -> (string_of_name n) ^ (string_of_term t)
  | (n, t) -> (string_of_name n) ^ "(" ^ (string_of_term t) ^ ")"

and string_of_term' level t =
  let (level', str) = match t with
      Id n -> (0, string_of_name n)
    | Star -> (0, "()")
    | Dagger -> failwith "Is this a dagger which I see before me?"
    | App (App (Id (n, Syntax.Infix0), t), u) -> 
	(9, (string_of_term' 9 t) ^ " " ^ n ^ " " ^ (string_of_term' 8 u))
    | App (App (Id (n, Syntax.Infix1), t), u) -> 
	(8, (string_of_term' 8 t) ^ " " ^ n ^ " " ^ (string_of_term' 7 u))
    | App (App (Id (n, Syntax.Infix2), t), u) -> 
	(7, (string_of_term' 7 t) ^ " " ^ n ^ " " ^ (string_of_term' 6 u))
    | App (App (Id (n, Syntax.Infix3), t), u) -> 
	(6, (string_of_term' 6 t) ^ " " ^ n ^ " " ^ (string_of_term' 5 u))
    | App (App (Id (n, Syntax.Infix4), t), u) -> 
	(5, (string_of_term' 5 t) ^ " " ^ n ^ " " ^ (string_of_term' 4 u))
    | App (t, u) -> 
	(4, (string_of_term' 4 t) ^ " " ^ (string_of_term' 3 u))
    | Lambda ((n, ty), t) ->
	(12, "fun (" ^ (string_of_name n) ^ " : " ^ (string_of_ty ty) ^ ") -> " ^
	   (string_of_term' 12 t))
    | Tuple [] -> (0, "()")
    | Tuple [t] -> (0, string_of_term' 0 t)
    | Tuple lst -> (0, "{{" ^ (String.concat ", " (List.map (string_of_term' 11) lst)) ^ "}}")
    | Proj (k, t) -> (4, ("pi" ^ (string_of_int k) ^ " " ^ (string_of_term' 3 t)))
    | Inj (lb, t) -> (4, (lb ^ " " ^ (string_of_term' 3 t)))
    | Cases (t, lst) ->
	(13, "match " ^ (string_of_term' 13 t) ^ " with " ^
	   (String.concat " | " (List.map (fun (lb,(n,ty),u) -> 
					     lb ^ " (" ^ (string_of_name n) ^ " : " ^
					     (string_of_ty ty) ^ ") -> " ^
					     (string_of_term' 11 u)) lst)))
    | Let (n, t, u) ->
	(13, "let " ^ (string_of_name n) ^ " = " ^
	   (string_of_term' 13 t) ^ " in " ^ (string_of_term' 13 u))
    | Obligation ((n, ty), p) ->
	(12,
	 "[? " ^ (string_of_name n) ^ " : " ^ (string_of_ty ty) ^ " . " ^
	 (string_of_proposition p) ^ "]")
  in
    if level' > level then "(" ^ str ^ ")" else str

and string_of_term t = string_of_term' 999 t

and string_of_prop level p =
  let (level', str) = match p with
      True -> (0, "true")
    | False -> (0, "false")
    | NamedTotal (n, t) -> (0, "Tot_" ^ (string_of_name n) ^ "(" ^ (string_of_term t) ^ ")")
    | NamedPer (n, t, u) -> (9, (string_of_term' 9 u) ^ " =_" ^
			       (string_of_name n) ^ " " ^ (string_of_term' 9 t))
    | NamedProp (n, Dagger, u) -> (0, string_of_app (n, u))
    | NamedProp (n, t, u) -> (9, (string_of_term t) ^ " |= " ^ (string_of_app (n, u)))
    | Equal (t, u) -> (9, (string_of_term' 9 t) ^ " = " ^ (string_of_term' 9 u))
    | And [] -> (0, "true")
    | And lst -> (10, String.concat " and " (List.map (string_of_prop 10) lst))
    | Cor [] -> (0, "false")
    | Cor lst -> (11, String.concat " cor " (List.map (string_of_prop 11) lst))
    | Imply (p, q) -> (13, (string_of_prop 12 p) ^ " ==> " ^ (string_of_prop 13 q))
    | Iff (p, q) -> (13, (string_of_prop 12 p) ^ " <=> " ^ (string_of_prop 12 q))
    | Not p -> (9, "not " ^ (string_of_prop 9 p))
    | Forall ((n, ty), p) -> (14, "all (" ^ (string_of_name n) ^ " : " ^
			      (string_of_ty ty) ^ ") . " ^ (string_of_prop 14 p))
  in
    if level' > level then "(" ^ str ^ ")" else str
    
and string_of_proposition p = string_of_prop 999 p

let string_of_bind bind =
    String.concat ", " (List.map (fun (n,t) -> (string_of_name n) ^ " : " ^ (string_of_ty t)) bind)

let string_of_spec ctx = function
    ValSpec (name, ty) ->
      "val " ^ (string_of_name name) ^ " : " ^ (string_of_ty ty)
    | TySpec (name, None) -> "type " ^ (string_of_name name)
    | TySpec (name, Some ty) -> "type " ^ (string_of_name name) ^ " = " ^ (string_of_ty ty)
    | AssertionSpec (bind, p) ->
	"(**\n" ^
	(if bind = [] then "" else (string_of_bind bind) ^ ":\n") ^
	(string_of_proposition p) ^ "\n*)"

let string_of_signat { s_name = s; s_arg = arg; s_body = body } = 
  "module type " ^ s ^
  (match arg with
       None -> ""
     | Some a -> "(\n" ^ (String.concat "\n\t" (List.map (string_of_spec []) a)) ^ "\n)"
  ) ^ " =\n" ^ "sig\n" ^
  (String.concat "\n\n" (List.map (string_of_spec []) body)) ^
  "\nend\n"
