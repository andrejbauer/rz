type nat
 
(** predicate (=nat=) : nat -> nat -> bool *)
(**  Assertion symmetric_nat =  forall x:nat, y:nat,  x =nat= y -> y =nat= x
      
     Assertion transitive_nat = 
       forall x:nat, y:nat, z:nat,  x =nat= y /\ y =nat= z -> x =nat= z
*)
 
val zero : nat
(**  Assertion zero_support =  zero : ||nat||
*)
 
val s : nat -> nat
(**  Assertion s_support =  forall x:nat, y:nat,  x =nat= y -> s x =nat= s y
*)
 
val (+) : nat -> nat -> nat
(**  Assertion (+)_support = 
       forall x:nat, y:nat,  x =nat= y ->
         forall z:nat, w:nat,  z =nat= w -> (x + z) =nat= (y + w)
*)
 

(**  Assertion plus_zero =  forall (k:||nat||),  (k + zero) =nat= k
*)
 

(**  Assertion plus_succ = 
       forall (k:||nat||, m:||nat||),  (s k + m) =nat= s (k + m)
*)
 
type ty_leq = nat
 
(** predicate (<=) : nat -> nat -> ty_leq -> bool *)
(**  Assertion (<=)_def = 
       forall (k:||nat||, m:||nat||), 
         forall a:ty_leq,  (<=) k m a <-> a : ||nat|| /\ (k + a) =nat= m
*)
 
(** predicate eq_prefix : nat -> (nat -> nat) -> (nat -> nat) -> bool *)
(**  Assertion eq_prefix_def = 
       forall (k:||nat||), 
         forall a:nat -> nat, 
           (forall x:nat, y:nat,  x =nat= y -> a x =nat= a y) ->
           forall b:nat -> nat, 
             (forall x:nat, y:nat,  x =nat= y -> b x =nat= b y) ->
             eq_prefix k a b <->
             (forall (m:||nat||), 
                forall x:ty_leq,  (<=) m k x -> a m =nat= b m)
*)
 
val continuity : ((nat -> nat) -> nat) -> (nat -> nat) -> nat
(**  Assertion continuity = 
       forall f:(nat -> nat) -> nat, 
         (forall g:nat -> nat, h:nat -> nat, 
            (forall x:nat, y:nat,  x =nat= y -> g x =nat= h y) ->
            f g =nat= f h) ->
         forall a:nat -> nat, 
           (forall x:nat, y:nat,  x =nat= y -> a x =nat= a y) ->
           let p = continuity f a in p : ||nat|| /\ 
           (forall b:nat -> nat, 
              (forall x:nat, y:nat,  x =nat= y -> b x =nat= b y) ->
              eq_prefix p a b -> f a =nat= f b)
*)

