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
    
   val emptySet : s
   (**  Assertion emptySet_support =  emptySet : ||s||
   *)
    
   val add : A.a -> s -> s
   (**  Assertion add_support = 
          forall x:A.a, y:A.a,  x =A.a= y ->
            forall z:s, w:s,  z =s= w -> add x z =s= add y w
   *)
    
   type fin = A.a
    
   (** predicate ||fin|| : s -> fin -> bool *)
   (**  Assertion fin_def_support = 
          forall u:s, p:fin,  p : ||fin u|| <-> p : ||A.a|| /\ u =s= add p u
   *)
    
   (** predicate (=fin=) : s -> fin -> fin -> bool *)
   (**  Assertion fin_def_per = 
          forall u:s, p:fin, q:fin,  p =(fin u)= q <-> u =s= add p u /\ 
            u =s= add q u /\ p =A.a= q
   *)
    
   
   (**  Assertion emptySet_empty = 
          forall (x:||A.a||),  not (emptySet =s= add x emptySet)
   *)
    
   
   (**  Assertion add_idem = 
          forall (x:||A.a||, u:||s||),  add x (add x u) =s= add x u
   *)
    
   
   (**  Assertion add_comm = 
          forall (x:||A.a||, y:||A.a||, u:||s||), 
            add x (add y u) =s= add y (add x u)
   *)
    
   module Induction : functor (P : sig
                                     type ty_p
                                      
                                     (** predicate p : s -> ty_p -> bool *)
                                     (**  Assertion strict_p = 
                                            forall x:s, a:ty_p,  p x a ->
                                              x : ||s||
                                           
                                          Assertion extensional_p = 
                                            forall x:s, y:s, a:ty_p, 
                                              x =s= y -> p x a -> p y a
                                     *)
                                   end) ->
                      sig
                        val induction : P.ty_p -> (A.a -> s -> P.ty_p -> P.ty_p) -> s -> P.ty_p
                        (**  Assertion induction = 
                               forall x:P.ty_p,  P.p emptySet x ->
                                 forall f:A.a -> s -> P.ty_p -> P.ty_p, 
                                   (forall (x':||A.a||, u:||s||), 
                                      forall y:P.ty_p,  P.p u y ->
                                        P.p (add x' u) (f x' u y)) ->
                                   forall (u:||s||),  P.p u (induction x f u)
                        *)
                      end
 end

