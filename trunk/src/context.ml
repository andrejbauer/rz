(** manipulation of contexts *)

(** There are two namespaces, one is for sets the other one is
    shared by terms and axioms (because axioms and terms both get
    translated to values)
*)

type namespace = Ns_term | Ns_set

type context = ((namespace * string) * Syntax.theory_element) list

let (empty : context) = []

let get ctx ns a = List.assoc (ns, a) ctx

let add ctx ns a v = ((ns, a), v) :: ctx

let occurs ctx ns a =
  try
    ignore (get ctx ns a); true
    )
  with Not_found -> false

exception Occurs

let add_fresh ctx a v =
  if occurs ctx a then raise Occurs else (a, v) :: ctx
