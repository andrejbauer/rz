(** manipulation of contexts *)

let emptyCtx = []

let addCtx n v ctx = (n,v) :: ctx

let getCtx n ctx = List.assoc n ctx

let occursCtx n ctx =
  try
    ignore (getCtx n ctx); true
  with Not_found -> false
