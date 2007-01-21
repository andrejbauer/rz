theory PriorityQueue =
thy
  set a (* elements of queues *)

  stable relation ( <= ) : a -> a -> Prop

  set queue (* the set of all queues *)

  stable relation elem : a -> queue -> Prop

  const empty : queue

  relation is_least (x : a) (q : queue) =
    (elem x q) and
    all (y : a) . (elem y q => x <= y)

  relation is_join (x : a) (r : queue) (q : queue) =
    not (elem x r) and
    (all (y :a) . (elem y q <=> (x = y || elem y r)))
(*
    (elem x q) and not (elem x r) and
    (all (y : a) . (elem y q => elem y r))
*)

  axiom empty_queue (x : a) = not (elem x empty)

  axiom dequeue (q : queue) =
    q = empty or
    some (x : a) . (
      is_least x q and 
      some (r : queue) . (is_join x r q)
    )

  axiom enqueue (x : a) (q : queue) =
    some (r : queue) . is_join x q r

end