type label = string

type name_type = Word | Prefix | Infix0 | Infix1 | Infix2 | Infix3 | Infix4

type set_name = string

type name = string * name_type

type binding = name * set

and set =
    Empty
  | Unit
  | Bool
  | Set_name of set_name
  | Product of set list
  | Sum of (label * set option) list
  | Exp of set * set
  | Subset of binding * term
  | Quotient of set * term
  | RZ of set

and term =
    Var of name
  | Constraint of term * set
  | Star
  | False
  | True
  | Tuple of term list
  | Proj of int * term
  | App of term * term
  | Inj of label * term
  | Case of term * (label * binding * term) list
  | Quot of term * term
  | Choose of binding * term * term
  | And of term list
  | Imply of term * term
  | Iff of term * term
  | Or of term list
  | Not of term
  | Equal of set option * term * term
  | Let of binding * term * term
  | Lambda of binding * term
  | Forall of binding * term
  | Exists of binding * term

    
