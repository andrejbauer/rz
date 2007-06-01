Axiom induction :
  forall M : thy Parameter p : nat -> Prop. end,
  M.p zero ->
  (forall k, M.p k -> M.p (succ k)) ->
  forall k, M.p k.    
