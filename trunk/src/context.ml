(** manipulation of contexts *)

type 'a context = (string * 'a) list

let empty = []

let get ctx a = List.assoc a ctx

let update ctx a v = (a, v) :: ctx

let occurs ctx a = List.exists (fun (b,_) -> a = b) ctx

exception Occurs

let fresh ctx a v =
  if occurs ctx a then raise Occurs else (a, v) :: ctx
