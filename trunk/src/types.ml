(**
  infer types & transform abstract syntax trees to
*)

let inferTheory = function
    Theory elems ->
      Theory (snd (List.fold_left
		     (fun (ctx, els) el -> let ctx', el' = inferElement ctx el in (ctx', el' :: els))
		     ([], []) elems
		  )
	     )
  | TheoryId _ as s -> s

let inferElement ctx = function
    Set (n, None) as s -> (ctx, s)
  | Set (n, Some s) ->
      let ctx', s' = inferSet ctx s in (ctx', Set (n, s'))
  | Predicate (n, st, s) -> let ctx', s' = inferSet ctx s in (ctx', Predicate (n, st, s))
  | 
