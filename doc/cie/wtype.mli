module type Branching =
 sig
   type s
    
   (** predicate (=s=) : s -> s -> bool *)
   (**  Assertion symmetric_s =  forall x:s, y:s,  x =s= y -> y =s= x
         
        Assertion transitive_s = 
          forall x:s, y:s, z:s,  x =s= y /\ y =s= z -> x =s= z
   *)
    
   (** predicate ||s|| : s -> bool *)
   (**  Assertion total_def_s =  forall x:s,  x : ||s|| <-> x =s= x
   *)
    
   (** branching types *)
    
   type t
    
   (** predicate (=t=) : s -> t -> t -> bool *)
   (**  Assertion strict_t =  forall x:s, y:t, z:t,  y =(t x)= z -> x : ||s||
         
        Assertion extensional_t = 
          forall x:s, y:s, z:t, w:t,  x =s= y -> z =(t x)= w -> z =(t y)= w
         
        Assertion symmetric_t = 
          forall x:s, y:t, z:t,  y =(t x)= z -> z =(t x)= y
         
        Assertion transitive_t = 
          forall x:s, y:t, z:t, w:t,  y =(t x)= z /\ z =(t x)= w ->
            y =(t x)= w
   *)
    
   (** predicate ||t|| : s -> t -> bool *)
   (**  Assertion total_def_t = 
          forall x:s, y:t,  y : ||t x|| <-> y =(t x)= y
   *)
    
   (** branch labels *)
 end
 
module W : functor (B : Branching) ->
           sig
             type w
              
             (** predicate (=w=) : w -> w -> bool *)
             (**  Assertion symmetric_w = 
                    forall x:w, y:w,  x =w= y -> y =w= x
                   
                  Assertion transitive_w = 
                    forall x:w, y:w, z:w,  x =w= y /\ y =w= z -> x =w= z
             *)
              
             (** predicate ||w|| : w -> bool *)
             (**  Assertion total_def_w =  forall x:w,  x : ||w|| <-> x =w= x
             *)
              
             val tree : B.s -> (B.t -> w) -> w
             (**  Assertion tree_support = 
                    forall x:B.s, y:B.s,  x =B.s= y ->
                      forall f:B.t -> w, g:B.t -> w, 
                        (forall z:B.t, t:B.t,  z =(B.t x)= t -> f z =w= g t) ->
                        tree x f =w= tree y g
             *)
              
             val induction : (B.s -> (B.t -> w) -> (B.t -> 'ty_p) -> 'ty_p) -> w -> 'ty_p
             (**  Assertion 'ty_p [p:w -> 'ty_p -> bool] induction = 
                    (forall x:w, a:'ty_p,  p x a -> x : ||w||) ->
                    (forall x:w, y:w, a:'ty_p,  x =w= y -> p x a -> p y a) ->
                    forall f:B.s -> (B.t -> w) -> (B.t -> 'ty_p) -> 'ty_p, 
                      (forall (x:||B.s||), 
                         forall f':B.t -> w, 
                           (forall y:B.t, z:B.t,  y =(B.t x)= z ->
                              f' y =w= f' z) ->
                           forall g:B.t -> 'ty_p, 
                             (forall y:B.t,  y : ||B.t x|| -> p (f' y) (g y)) ->
                             p (tree x f') (f x f' g)) ->
                      forall (t:||w||),  p t (induction f t)
             *)
           end

