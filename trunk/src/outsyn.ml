(* Abstract Syntax for the Output Code *)

type label = string

type ty = NamedTy of string          (* 0 *)
        | ListTy of ty               (* 1 *)
	| SumTy of ty list           (* 1 *)
        | TupleTy of ty list         (* 2 *)
        | ArrowTy of ty * ty         (* 3 *)

type spec = ValSpec of label * ty
          | TySpec of label * ty option  (* monomorphic for now *)

type signat = spec list

let unitTy = TupleTy []
let voidTy = SumTy []

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
	  "[" ^ (String.concat " | " (make 0 ts) ^ "]"

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
