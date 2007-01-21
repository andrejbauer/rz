theory Queue =
thy
  set a (* elements of queues *)

  set queue (* the set of all queues *)

  implicit q,q' : queue
  implicit x,y : a

  const empty : queue

  const enqueue : a * queue -> queue
  const dequeue : queue -> `some : (a * queue) + `none

  axiom dequeue0 =
    dequeue (empty) = `none

  axiom dequeue1 x =
    dequeue (enqueue (x, empty)) = `some(x, empty)
	

  axiom dequeue2 x q =
    not ( q = empty ) => 
	some y. some q'. (dequeue q = `some(y,q')  and
                          dequeue(enqueue(x,q)) = `some(y, enqueue(x,q')))

  (* Is the following axiom redundant? *)

  axiom enqueue1 q y q' =
    (dequeue q = `some(y,q')) <=> (enqueue (y,q') = q)


end