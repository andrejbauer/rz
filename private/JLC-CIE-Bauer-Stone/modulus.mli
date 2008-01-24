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
(**  Assertion s_support =  s : ||nat -> nat||
*)
 
val (+) : nat -> nat -> nat
(**  Assertion (+)_support =  (+) : ||nat -> nat -> nat||
*)
 

(**  Assertion plus_zero =  forall (k:||nat||),  (k + zero) =nat= k
*)
 

(**  Assertion plus_succ = 
       forall (k:||nat||, m:||nat||),  (s k + m) =nat= s (k + m)
*)
 
(** predicate (<=) : nat -> nat -> bool *)
(**  Assertion (<=)_def = 
       forall (k:||nat||, m:||nat||),  (<=) k m <->
         not (forall (n:||nat||),  not ((k + n) =nat= m))
*)
 
val continuity : ((nat -> nat) -> nat) -> (nat -> nat) -> nat
(**  Assertion continuity = 
       forall (f:||(nat -> nat) -> nat||, a:||nat -> nat||), 
         let p = continuity f a in p : ||nat|| /\ 
         (forall (b:||nat -> nat||), 
            (forall (m:||nat||),  (<=) m p -> a m =nat= b m) -> f a =nat= 
            f b)
*)

