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

(** specifications are expressed in the negative fragment *)
type name = string

type modest = {
  ty : ty;
  tot : name * negative;
  per : name * name * negative
}

and term =
    Ident of name
  | Star
  | App of term * term
  | Lambda of name * modest * term
  | Tuple of term list
  | Proj of int * term
  | Inj of label * term
  | Cases of term * (label * name * ty * term) list
  | Let of name * term * term

and negative =
  | True
  | False
  | Total of modest * term
  | Per of modest * term * term
  | Equal of term * term
  | And of negative list
  | Cor of negative list (** classical or *)
  | Imply of negative * negative
  | Iff of negative * negative
  | Forall of name * ty * negative

type spec =
    ValSpec of name * modest * term option
  | TySpec of name * modest option  (* monomorphic for now *)
  | AxSpec of name * ty * name * negative

type signat = spec list


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

let next_name n =
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
	   )


let rec find_name good bad =
  try
    List.find (fun x -> not (List.mem x bad)) bad
  with Not_found -> find_name (List.map next_name good) bad

let rec fv_modest flt acc {tot=(x,p); per=(u,v,q)} =
  fv_neg (u::v::flt) (fv_neg (x::flt) acc p) q

and fv_term flt acc = function
    Ident n -> if List.mem n flt then acc else n :: acc
  | Star -> acc
  | App (u, v) -> fv_term flt (fv_term flt acc u) v
  | Lambda (n, s, t) -> fv_modest flt (fv_term (n::flt) acc t) s
  | Tuple lst -> List.fold_left (fun a t -> fv_term flt a t) acc lst
  | Proj (_, t) -> fv_term flt acc t
  | Inj (_, t) -> fv_term flt acc t
  | Cases (t, lst) -> List.fold_left (fun a (_, n, _, t) -> fv_term (n::flt) a t) (fv_term flt acc t) lst

and fv_neg flt acc = function
    True -> acc
  | False -> acc
  | Total (s, t) -> fv_modest flt (fv_term flt acc t) s
  | Per (s, u, v) -> fv_modest flt (fv_term flt (fv_term flt acc v) u) s
  | Equal (u, v) -> fv_term flt (fv_term flt acc u) v
  | And lst -> List.fold_left (fun a t -> fv_neg flt a t) acc lst
  | Cor lst -> List.fold_left (fun a t -> fv_neg flt a t) acc lst
  | Imply (u, v) -> fv_neg flt (fv_neg flt acc v) u
  | Forall (n, _, p) -> fv_neg (n::flt) acc p

let free_vars_term = fv_term [] []
let free_vars_neg = fv_neg [] []

let find_name_subst good bad subst =
  find_name good ((List.flatten (List.map (fun t -> free_vars_term (snd t)) subst)) @ bad)

let subst_remove n subst = List.filter (fun (m,_) -> n <> m) subst

let subst_add (n,n') s = (if n = n' then s else (n, Ident n')::s)

let rec subst_negative s = function
    True -> True
  | False -> False
  | Total (r, t) -> Total (subst_modest s r, subst_term s t)
  | Per (r, u, v) -> Per (subst_modest s r, subst_term s u, subst_term s v)
  | Equal (u, v) -> Equal (subst_term s u, subst_term s v)
  | And lst -> And (List.map (subst_negative s) lst)
  | Cor lst -> Cor (List.map (subst_negative s) lst)
  | Imply (p, q) -> Imply (subst_negative s p, subst_negative s q)
  | Forall (n, ty, q) as p ->
      let s = subst_remove n s in
      let n' = find_name_subst [n] [] s in
	Forall (n', ty, subst_negative (subst_add (n,n') s) q)

and subst_term s = function
    Ident n ->
      (try List.assoc n s with Not_found -> Ident n)
  | Star -> Star
  | App (t, u) -> App (subst_term s t, subst_term s u)
  | Lambda (n, md, t) ->
      let s = subst_remove n s in
      let n' = find_name_subst [n] [] s in
	Lambda (n, md, subst_term (subst_add (n,n') s) t)
  | Tuple lst -> Tuple (List.map (subst_term s) lst)
  | Proj (k, t) -> Proj (k, subst_term s t)
  | Inj (k, t) -> Inj (k, subst_term s t)
  | Cases (t, lst) -> 
      Cases (subst_term s t,
	     List.map (fun (lb, n, ty, t) ->
			 let s = subst_remove n s in
			 let n' = find_name_subst [n] [] s in
			 (lb, n', ty, subst_term (subst_add (n,n') s) t)
		      ) lst)

and subst_modest s {ty=t; tot=(x,p); per=(y,z,q)} =
  { ty = t;
    tot = (let x' = find_name_subst [x] [] s in
	     (x', subst_negative (subst_add (x,x') s) p));
    per = (let y' = find_name_subst [y] [] s in
	   let z' = find_name_subst [z] [y'] s in
	     (y',z', subst_negative (subst_add (y,y') (subst_add (z,z') s)) q));
  }


let rec string_of_neg p = "(string_of_neg)"

let rec string_of_term t = "(string_of_term)"

let rec string_of_ty' level (t : ty) =
  let rec makeTupleTy = function
      []    -> "void"
    | [t]   -> string_of_ty' 1 t
    | t::ts -> (string_of_ty' 1 t) ^ " * " ^ (makeTupleTy ts)

  in let rec makeSumTy = function
      [] -> "void"
    | ts -> 
	"[" ^ (String.concat " | " (List.map (fun (lb,t) -> "`" ^ lb ^ " of " ^ (string_of_ty' 1 t)) ts)) ^ "]"
		
  in let (level', str ) = 
       (match (t:ty) with
          NamedTy name   -> (0, name)
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

let string_of_spec = function
      ValSpec (name, {ty=t; tot=(x,p); per=(y,z,q)}, v) ->
	"val " ^ name ^ " : " ^ (string_of_ty t) ^ "\n" ^
	"(** " ^ (string_of_neg (subst_negative [(x, Ident name)] p)) ^ " *)\n" ^
	(match v with
	     None -> ""
	   | Some v -> "(** " ^ (string_of_neg (subst_negative [(y, Ident name); (z, v)] q)) ^ " *)\n"
	)

    | TySpec  (name, None) ->
	"type " ^ name
    | TySpec  (name, Some {ty=t}) ->
	"type " ^ name ^ " = " ^ (string_of_ty t) ^ " (** per and tot missing here *)"

let string_of_signat specs = 
  "sig\n" ^
  (String.concat "\n" (List.map string_of_spec specs)) ^
  "\nend\n"
