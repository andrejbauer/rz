(* Abstract Syntax for the Output Code *)

type label = string

type ty =
    NamedTy of string          (* 0 *)
  | UnitTy                     (* 0 *)
  | InvisibleUnitTy            (* 0 *)
  | VoidTy                     (* 0 *)
  | ListTy of ty               (* 1 *)
  | SumTy of (label * ty) list (* 1 *)
  | TupleTy of ty list         (* 2 *)
  | ArrowTy of ty * ty         (* 3 *)

type name = Syntax.name

type modest = {
  ty : ty;
  tot : name *  proposition;
  per : name * name * proposition
}

and binding = name * ty

and term =
    Id of name
  | Star
  | App of term * term
  | Lambda of binding * term
  | Tuple of term list
  | Proj of int * term
  | Inj of label * term
  | Cases of term * (label * binding * term) list
  | Let of name * term * term
  | Questionmark (** used for unknown proofs *)

(** specifications are expressed in classical logic
    (negative fragment to be exact)
*)
and proposition =
  | True
  | False
  | NamedTotal of string * term
  | NamedPer of string * term * term
  | NamedProp of string * term * term
  | Equal of term * term
  | And of proposition list
  | Cor of proposition list (** classical or *)
  | Imply of proposition * proposition
  | Iff of proposition * proposition
  | Not of proposition
  | Forall of binding * proposition

type signat_element =
    ValSpec of name * modest * term option
  | TySpec of string * modest option  (* monomorphic for now *)
  | SentenceSpec of name * binding list * (ty * name * proposition)

type signat = {
  s_name : string;
  s_arg : signat_element list option;
  s_body : signat_element list
}

let mk_word n = (n, Syntax.Word)
let mk_id n = Id (mk_word n)

let name_subscript s =
  try
    let k = String.rindex s '_' in
      String.sub s 0 k, Some (String.sub s (k+1) (String.length s - k - 1))
  with Not_found -> s, None

let name_prime s =
  try
    let k = String.index s '\'' in
      String.sub s 0 k, Some (String.sub s k (String.length s - k))
  with Not_found -> s, None

let split_name n =
  let m, p = name_prime n in
  let r, s = name_subscript m in
    r, s, p

let next_name (n,nt) =
  let r, s, p = split_name n in
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


let rec find_name good bad =
  try
    List.find (fun x -> not (List.mem x bad)) good
  with Not_found -> find_name (List.map next_name good) bad

let rec fv_modest flt acc {tot=(x,p); per=(u,v,q)} =
  fv_neg (u::v::flt) (fv_neg (x::flt) acc p) q

and fv_term flt acc = function
    Id n -> if List.mem n flt then acc else n :: acc
  | Star -> acc
  | App (u, v) -> fv_term flt (fv_term flt acc u) v
  | Lambda ((n, s), t) -> fv_term (n::flt) acc t
  | Tuple lst -> List.fold_left (fun a t -> fv_term flt a t) acc lst
  | Proj (_, t) -> fv_term flt acc t
  | Inj (_, t) -> fv_term flt acc t
  | Cases (t, lst) -> List.fold_left (fun a (_, (n, _), t) -> fv_term (n::flt) a t) (fv_term flt acc t) lst

and fv_neg flt acc = function
    True -> acc
  | False -> acc
  | NamedTotal (s, t) -> fv_term flt acc t
  | NamedPer (s, u, v) -> fv_term flt (fv_term flt acc v) u
  | Equal (u, v) -> fv_term flt (fv_term flt acc u) v
  | And lst -> List.fold_left (fun a t -> fv_neg flt a t) acc lst
  | Cor lst -> List.fold_left (fun a t -> fv_neg flt a t) acc lst
  | Imply (u, v) -> fv_neg flt (fv_neg flt acc v) u
  | Forall ((n, _), p) -> fv_neg (n::flt) acc p

let free_vars_term = fv_term [] []
let free_vars_neg = fv_neg [] []

let find_name_subst good bad subst =
  find_name good ((List.flatten (List.map (fun t -> free_vars_term (snd t)) subst)) @ bad)

let subst_remove n subst = List.filter (fun (m,_) -> n <> m) subst

let subst_add (n,n') s = (if n = n' then s else (n, Id n')::s)

let rec subst_proposition s = function
    True -> True
  | False -> False
  | NamedTotal (r, t) -> NamedTotal (r, subst_term s t)
  | NamedPer (r, u, v) -> NamedPer (r, subst_term s u, subst_term s v)
  | NamedProp (n, u, v) -> NamedProp (n, subst_term s u, subst_term s v)
  | Equal (u, v) -> Equal (subst_term s u, subst_term s v)
  | And lst -> And (List.map (subst_proposition s) lst)
  | Cor lst -> Cor (List.map (subst_proposition s) lst)
  | Imply (p, q) -> Imply (subst_proposition s p, subst_proposition s q)
  | Not p -> Not (subst_proposition s p)
  | Forall ((n, ty), q) as p ->
      let s = subst_remove n s in
      let n' = find_name_subst [n] [] s in
	Forall ((n', ty), subst_proposition (subst_add (n,n') s) q)

and subst_term s = function
    Id n ->
      (try List.assoc n s with Not_found -> Id n)
  | Questionmark -> Questionmark
  | Star -> Star
  | App (t, u) -> App (subst_term s t, subst_term s u)
  | Lambda ((n, ty), t) ->
      let s = subst_remove n s in
      let n' = find_name_subst [n] [] s in
	Lambda ((n, ty), subst_term (subst_add (n,n') s) t)
  | Tuple lst -> Tuple (List.map (subst_term s) lst)
  | Proj (k, t) -> Proj (k, subst_term s t)
  | Inj (k, t) -> Inj (k, subst_term s t)
  | Cases (t, lst) -> 
      Cases (subst_term s t,
	     List.map (fun (lb, (n, ty), t) ->
			 let s = subst_remove n s in
			 let n' = find_name_subst [n] [] s in
			 (lb, (n', ty), subst_term (subst_add (n,n') s) t)
		      ) lst)

and subst_modest s {ty=t; tot=(x,p); per=(y,z,q)} =
  { ty = t;
    tot = (let x' = find_name_subst [x] [] s in
	     (x', subst_proposition (subst_add (x,x') s) p));
    per = (let y' = find_name_subst [y] [] s in
	   let z' = find_name_subst [z] [y'] s in
	     (y',z', subst_proposition (subst_add (y,y') (subst_add (z,z') s)) q));
  }

let string_of_name = function
    (n, Syntax.Word) -> n
  | (n, _) -> "( " ^ n ^ " )"

let rec string_of_ty' level t =
  let rec makeTupleTy = function
      []    -> "unit"
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
	  | InvisibleUnitTy -> (0, "invisible_unit")
	  | VoidTy         -> (0, "void")
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

let rec string_of_term' level t =
  let (level', str) = match t with
      Id n -> (0, string_of_name n)
    | Questionmark -> (0, "?")
    | Star -> (0, "()")
    | App (App (Id (n, Syntax.Infix0), t), u) -> 
	(9, (string_of_term' 9 t) ^ " " ^ n ^ " " ^ (string_of_term' 9 u))
    | App (App (Id (n, Syntax.Infix1), t), u) -> 
	(8, (string_of_term' 8 t) ^ " " ^ n ^ " " ^ (string_of_term' 8 u))
    | App (App (Id (n, Syntax.Infix2), t), u) -> 
	(7, (string_of_term' 7 t) ^ " " ^ n ^ " " ^ (string_of_term' 7 u))
    | App (App (Id (n, Syntax.Infix3), t), u) -> 
	(6, (string_of_term' 6 t) ^ " " ^ n ^ " " ^ (string_of_term' 6 u))
    | App (App (Id (n, Syntax.Infix4), t), u) -> 
	(5, (string_of_term' 5 t) ^ " " ^ n ^ " " ^ (string_of_term' 5 u))
    | App (t, u) -> 
	(4, (string_of_term' 4 t) ^ " " ^ (string_of_term' 3 u))
    | Lambda ((n, ty), t) ->
	(12, "fun (" ^ (string_of_name n) ^ " : " ^ (string_of_ty ty) ^ ") -> " ^
	   (string_of_term' 12 t))
    | Tuple [] -> (0, "()")
    | Tuple [t] -> (0, string_of_term' 0 t)
    | Tuple lst -> (0, "(" ^ (String.concat ", " (List.map (string_of_term' 11) lst)) ^ ")")
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
  in
    if level' > level then "(" ^ str ^ ")" else str

let string_of_term t = string_of_term' 999 t

let rec string_of_prop level p =
  let (level', str) = match p with
      True -> (0, "true")
    | False -> (0, "false")
    | NamedTotal (n, t) -> (0, "Tot_" ^ n ^ "(" ^ (string_of_term t) ^ ")")
    | NamedPer (n, t, u) -> (9, (string_of_term' 9 u) ^ " =_" ^ n ^ " " ^ (string_of_term' 9 t))
    | NamedProp (n, t, u) -> (9, "Rz_" ^ n ^ "(" ^ (string_of_term t) ^ ", " ^
				(string_of_term u) ^ ")")
    | Equal (t, u) -> (9, (string_of_term' 9 t) ^ " = " ^ (string_of_term' 9 u))
    | And [] -> (0, "true")
    | And lst -> (10, String.concat " and " (List.map (string_of_prop 10) lst))
    | Cor [] -> (0, "false")
    | Cor lst -> (11, String.concat " cor " (List.map (string_of_prop 11) lst))
    | Imply (p, q) -> (13, (string_of_prop 12 p) ^ " ==> " ^ (string_of_prop 13 q))
    | Iff (p, q) -> (13, (string_of_prop 12 p) ^ " <=> " ^ (string_of_prop 12 q))
    | Not p -> (9, "not " ^ (string_of_prop 9 p))
    | Forall ((n, ty), p) -> (14, "forall (" ^ (string_of_name n) ^ " : " ^
			      (string_of_ty ty) ^ ") . " ^ (string_of_prop 14 p))
  in
    if level' > level then "(" ^ str ^ ")" else str
    
let string_of_proposition p = string_of_prop 999 p


let string_of_spec = function
      ValSpec (name, {ty=t; tot=(x,p); per=(y,z,q)}, v) ->
	"val " ^ (string_of_name name) ^ " : " ^ (string_of_ty t) ^ "\n" ^
	"(** " ^ (string_of_proposition (subst_proposition [(x, Id name)] p)) ^ " *)" ^
	(match v with
	     None -> ""
	   | Some v -> " (** " ^ (string_of_proposition (subst_proposition [(y, Id name); (z, v)] q)) ^ " *)\n"
	)
    | TySpec  (name, None) ->
	"type " ^ name
    | TySpec  (name, Some {ty=t; tot=(x,p); per=(y,z,q)}) ->
	"type " ^ name ^ " = " ^ (string_of_ty t) ^ "\n(**\n" ^ (
	  (string_of_name x) ^ " : " ^ (string_of_proposition p) ^ "\n" ^
	  (string_of_name y) ^ ", " ^ (string_of_name z) ^ " : " ^
	  (string_of_proposition q)
	) ^ "\n*)"
    | SentenceSpec (name, bind, (t, n, p)) ->
	let u = ArrowTy (TupleTy (List.map snd bind), t) in
	let tp = Tuple (List.map (fun b -> Id (fst b)) bind)
	in
	  "val " ^ (string_of_name name) ^ " : " ^ (string_of_ty u) ^ "\n(** " ^
	  (string_of_term tp) ^ " : " ^
	  (string_of_proposition (subst_proposition [(n, App (Id name, tp))] p)
	  ) ^ " *)"

let string_of_signat { s_name = s; s_arg = arg; s_body = body } = 
  "module type " ^ s ^
  (match arg with
       None -> ""
     | Some a -> "(\n" ^ (String.concat "\n\t" (List.map string_of_spec a)) ^ "\n)"
  ) ^ " =\n" ^ "sig\n" ^
  (String.concat "\n\n" (List.map string_of_spec body)) ^
  "\nend\n"
