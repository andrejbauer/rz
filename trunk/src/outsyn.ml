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

type term =
    Ident of name
  | Star
  | App of term * term
  | Lambda of name * modest * term
  | Tuple of term list
  | Proj of int * term
  | Inj of int * term
  | Cases of term * (label * name * ty * term) list

type negative =
  | True
  | False
  | Total of name * term
  | Per of name * term * term
  | Equal of term * term
  | And of prop list
  | Cor of prop list (** classical or *)
  | Imply of prop * prop
  | Forall of name * ty * negative

type spec =
    ValSpec of name * modest * term option
  | TySpec of name * modest option  (* monomorphic for now *)
  | AxSpec of name * ty * negative

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

let free_vars =
  let rec fv acc = function
    True -> acc
  | False -> acc
  | Total (_, t) -> fv acc t
  | Per (_, u, v) -> fv (fv acc v) u 
  | Equal (u, v) -> fv (fv acc v) u
  | And lst -> List.fold_left (fun a t -> fv a t) acc lst
  | Cor lst -> List.fold_left (fun a t -> fv a t) acc lst
  | Imply (u, v) -> fv (fv acc v) u
  | Forall (n, _, p) -> List.filter ((<>) n) (fv acc p)
  in
    fv []

let rec subst_negative s = function
    True -> True
  | False -> False
  | Total (n, t) -> (n, subst_term s t)
  | Per (n, u, v) -> Per (n, subst_term u, subst_term v)
  | Equal (u, v) -> Equal (subst_term u, subst_term v)
  | And lst -> And (List.map (subst_negative s) lst)
  | Cor lst -> Cor (List.map (subst_negative s) lst)
  | Imply (p, q) -> Imply (subst_negative s p, subst_negative s q)
  | Forall (n, ty, q) as p ->
      if List.mem n (List.map fst s) then p
      else
	let n' = find_name [n] (List.flatten (List.map (fun t -> free_vars (snd t)) s))
	in
	  failwith "had to go home here"

let rec tyToString' level (t : ty) =
  let rec makeTupleTy = function
      []    -> "void"
    | [t]   -> tyToString' 1 t
    | t::ts -> (tyToString' 1 t) ^ " * " ^ (makeTupleTy ts)

  in let rec makeSumTy = function
      [] -> "void"
    | [t] -> tyToString' 1 t
    | ts -> 
	let rec make k = function
	    [] -> []
	  | t::ts -> ("`in" ^ (string_of_int k) ^ " of " ^ (tyToString' 1 t)) :: (make (k+1) ts)
	in
	  "[" ^ (String.concat " | " (make 0 ts)) ^ "]"
		
  in let (level', str ) = 
       (match (t:ty) with
          NamedTy name   -> (0, name)
        | ListTy t       -> (1, (tyToString' 1 t) ^ "list")
	| SumTy ts       -> (1, makeSumTy ts)
        | TupleTy ts     -> (2, makeTupleTy ts)
        | ArrowTy(t1,t2) -> (3, (tyToString' 2 t1) ^ " -> " ^ (tyToString' 3 t2)))
  in
    if (level' > level) then 
       "(" ^ str ^ ")"
    else
       str

let tyToString t = tyToString' 999 t

let specToString = function
      ValSpec (name,t) -> "val " ^ name ^ " : " ^ (tyToString t)
    | TySpec  (name,None) -> "type " ^ name
    | TySpec  (name,Some t) -> "type " ^ name ^ " = " ^ (tyToString t)

let signatToString specs = 
  "sig\n" ^
  (String.concat "\n" (List.map specToString specs)) ^
  "\nend\n"
