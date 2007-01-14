module type List =
 functor (S : sig
                type s
                 
                (** predicate (=s=) : s -> s -> bool *)
                (**  Assertion symmetric_s = 
                       forall x:s, y:s,  x =s= y -> y =s= x
                      
                     Assertion transitive_s = 
                       forall x:s, y:s, z:s,  x =s= y /\ y =s= z -> x =s= z
                *)
              end) ->
 sig
   type list
    
   (** predicate (=list=) : list -> list -> bool *)
   (**  Assertion symmetric_list = 
          forall x:list, y:list,  x =list= y -> y =list= x
         
        Assertion transitive_list = 
          forall x:list, y:list, z:list,  x =list= y /\ y =list= z ->
            x =list= z
   *)
    
   val nil : list
   (**  Assertion nil_support =  nil : ||list||
   *)
    
   val cons : S.s -> list -> list
   (**  Assertion cons_support =  cons : ||S.s -> list -> list||
   *)
    
   module Fold : functor (P : sig
                                type ty_p
                                 
                                (** predicate p : list -> ty_p -> bool *)
                                (**  Assertion strict_p = 
                                       forall x:list, a:ty_p,  p x a ->
                                         x : ||list||
                                      
                                     Assertion extensional_p = 
                                       forall x:list, y:list, a:ty_p, 
                                         x =list= y -> p x a -> p y a
                                *)
                              end) ->
                 sig
                   val fold : P.ty_p -> (S.s -> list -> P.ty_p -> P.ty_p) -> list -> P.ty_p
                   (**  Assertion fold = 
                          forall x:P.ty_p,  P.p nil x ->
                            forall f:S.s -> list -> P.ty_p -> P.ty_p, 
                              (forall (x':||S.s||, u:||list||), 
                                 forall y:P.ty_p,  P.p u y ->
                                   P.p (cons x' u) (f x' u y)) ->
                              forall (u:||list||),  P.p u (fold x f u)
                   *)
                 end
 end

