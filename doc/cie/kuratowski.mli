module type Semilattice =
 sig
   type s
    
   (** predicate (=s=) : s -> s -> bool *)
   (**  Assertion symmetric_s =  forall x:s, y:s,  x =s= y -> y =s= x
         
        Assertion transitive_s = 
          forall x:s, y:s, z:s,  x =s= y /\ y =s= z -> x =s= z
   *)
    
   val zero : s
   (**  Assertion zero_support =  zero : ||s||
   *)
    
   val join : s -> s -> s
   (**  Assertion join_support =  join : ||s -> s -> s||
   *)
    
   
   (**  Assertion commutative = 
          forall (x:||s||, y:||s||),  join x y =s= join y x
   *)
    
   
   (**  Assertion associative = 
          forall (x:||s||, y:||s||, z:||s||), 
            join (join x y) z =s= join x (join y z)
   *)
    
   
   (**  Assertion idempotent =  forall (x:||s||),  join x x =s= x
   *)
    
   
   (**  Assertion neutral =  forall (x:||s||),  join x zero =s= x
   *)
 end
 
module type K =
 functor (A : sig
                type a
                 
                (** predicate (=a=) : a -> a -> bool *)
                (**  Assertion symmetric_a = 
                       forall x:a, y:a,  x =a= y -> y =a= x
                      
                     Assertion transitive_a = 
                       forall x:a, y:a, z:a,  x =a= y /\ y =a= z -> x =a= z
                *)
              end) ->
 sig
   type s
    
   (** predicate (=s=) : s -> s -> bool *)
   (**  Assertion symmetric_s =  forall x:s, y:s,  x =s= y -> y =s= x
         
        Assertion transitive_s = 
          forall x:s, y:s, z:s,  x =s= y /\ y =s= z -> x =s= z
   *)
    
   val zero : s
   (**  Assertion zero_support =  zero : ||s||
   *)
    
   val join : s -> s -> s
   (**  Assertion join_support =  join : ||s -> s -> s||
   *)
    
   
   (**  Assertion commutative = 
          forall (x:||s||, y:||s||),  join x y =s= join y x
   *)
    
   
   (**  Assertion associative = 
          forall (x:||s||, y:||s||, z:||s||), 
            join (join x y) z =s= join x (join y z)
   *)
    
   
   (**  Assertion idempotent =  forall (x:||s||),  join x x =s= x
   *)
    
   
   (**  Assertion neutral =  forall (x:||s||),  join x zero =s= x
   *)
    
   val singleton : A.a -> s
   (**  Assertion singleton_support =  singleton : ||A.a -> s||
   *)
    
   type fin = s
    
   (** predicate ||fin|| : fin -> bool *)
   (**  Assertion fin_def_support =  forall x:fin,  x : ||fin|| <-> x : ||s||
   *)
    
   (** predicate (=fin=) : fin -> fin -> bool *)
   (**  Assertion fin_def_per =  forall x:fin, y:fin,  x =fin= y <-> x =s= y
   *)
    
   val emptyset : s
   (**  Assertion emptyset_def =  emptyset =s= zero
   *)
    
   val union : s -> s -> s
   (**  Assertion union_def = 
          forall x:s, y:s,  x =s= y ->
            forall z:s, w:s,  z =s= w -> union x z =s= join y w
   *)
    
   module Free : functor (S : Semilattice) ->
                 sig
                   val free : (A.a -> S.s) -> fin -> S.s
                   (**  Assertion free = 
                          forall (f:||A.a -> S.s||), 
                            let g = free f in g : ||fin -> S.s|| /\ 
                            g emptyset =S.s= S.zero /\ 
                            (forall (x:||A.a||),  f x =S.s= g (singleton x)) /\ 
                            (forall (u:||fin||, v:||fin||), 
                               g (union u v) =S.s= S.join (g u) (g v)) /\ 
                            (forall h:fin -> S.s,  h : ||fin -> S.s|| /\ 
                               h emptyset =S.s= S.zero /\ 
                               (forall (x:||A.a||), 
                                  f x =S.s= h (singleton x)) /\ 
                               (forall (u:||fin||, v:||fin||), 
                                  h (union u v) =S.s= S.join (h u) (h v)) ->
                               forall x:fin, y:fin,  x =fin= y ->
                                 g x =S.s= h y)
                   *)
                 end
 end

