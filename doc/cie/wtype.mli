module type Branching =
 sig
   type s
    
   (** predicate (=s=) : s -> s -> bool *)
   (**  Assertion symmetric_s =  forall x:s, y:s,  x =s= y -> y =s= x
         
        Assertion transitive_s = 
          forall x:s, y:s, z:s,  x =s= y /\ y =s= z -> x =s= z
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
              
             val tree : B.s -> (B.t -> w) -> w
             (**  Assertion tree_support = 
                    forall x:B.s, y:B.s,  x =B.s= y ->
                      forall f:B.t -> w, g:B.t -> w, 
                        (forall z:B.t, t:B.t,  z =(B.t x)= t -> f z =w= g t) ->
                        tree x f =w= tree y g
             *)
              
             module Induction : functor (M : sig
                                               type ty_p
                                                
                                               (** predicate p : w -> ty_p -> bool *)
                                               (**  Assertion strict_p = 
                                                      forall x:w, a:ty_p, 
                                                        p x a -> x : ||w||
                                                     
                                                    Assertion extensional_p = 
                                                      forall x:w, y:w, 
                                                        a:ty_p,  x =w= y ->
                                                        p x a -> p y a
                                               *)
                                             end) ->
                                sig
                                  val induction : (B.s -> (B.t -> w) -> (B.t -> M.ty_p) -> M.ty_p) -> w -> M.ty_p
                                  (**  Assertion induction = 
                                         forall f:B.s -> (B.t -> w) -> (B.t -> M.ty_p) -> M.ty_p, 
                                           (forall (x:||B.s||), 
                                              forall f':B.t -> w, 
                                                (forall y:B.t, z:B.t, 
                                                   y =(B.t x)= z ->
                                                   f' y =w= f' z) ->
                                                forall g:B.t -> M.ty_p, 
                                                  (forall y:B.t, 
                                                     y : ||B.t x|| ->
                                                     M.p (f' y) (g y)) ->
                                                  M.p (tree x f') (f x f' g)) ->
                                           forall (t:||w||), 
                                             M.p t (induction f t)
                                  *)
                                end
           end

