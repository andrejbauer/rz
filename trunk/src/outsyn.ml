(* Abstract Syntax for the Output Code *)

type label = string

type ty = NamedTy of string          (* 0 *)
        | ListTy of ty               (* 1 *)
        | TupleTy of ty list         (* 2 *)
        | ArrowTy of ty * ty         (* 3 *)

type spec = ValSpec of label * ty
          | TySpec of label * ty option  (* monomorphic for now *)

type signat = spec list

let rec tyToString' level (t : ty) =
  let rec makeTupleTy = function
         []   -> "unit"
      | [t]   -> tyToString' 1 t
      | t::ts -> (tyToString' 1 t) ^ "*" ^ (makeTupleTy ts)

  in let (level', str ) = 
       (match (t:ty) with
          NamedTy name   -> (0, name)
        | ListTy t       -> (1, (tyToString' 1 t) ^ "list")
        | TupleTy ts     -> (2, makeTupleTy ts)
        | ArrowTy(t1,t2) -> (3, (tyToString' 2 t1)^" -> "^(tyToString' 3 t2)))
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
 let rec specsToString = function
          []    -> ""
       |  s::ss -> "   " ^ (specToString s) ^ "\n" ^ 
                             (specsToString ss)
 in
   "sig\n" ^ (specsToString specs) ^ " end\n "
