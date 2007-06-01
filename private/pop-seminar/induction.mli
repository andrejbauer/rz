val induction : 'ty_p -> (nat -> 'ty_p -> 'ty_p) -> nat -> 'ty_p
(**  assertion 'ty_p [p:nat -> 'ty_p -> bool] induction : 
  (forall x:nat, a:'ty_p,  p x a -> x : ||nat||) ->
  (forall x:nat, y:nat, a:'ty_p,  x =nat= y -> p x a -> p y a) ->
  forall x:'ty_p,  p (assure (leq zero zero) in zero) x ->
  forall f:nat -> 'ty_p -> 'ty_p,
  (forall (k:||nat||), forall y:'ty_p,  p k y -> p (succ k) (f k y)) ->
  forall (k:||nat||),  p k (induction x f k)
*)
