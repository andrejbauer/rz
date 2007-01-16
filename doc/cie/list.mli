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
    
   val fold : 'ty_p -> (S.s -> list -> 'ty_p -> 'ty_p) -> list -> 'ty_p
   (**  Assertion 'ty_p [p:list -> 'ty_p -> bool] fold = 
          (forall x:list, a:'ty_p,  p x a -> x : ||list||) ->
          (forall x:list, y:list, a:'ty_p,  x =list= y -> p x a -> p y a) ->
          forall x:'ty_p,  p nil x ->
            forall f:S.s -> list -> 'ty_p -> 'ty_p, 
              (forall (x':||S.s||, u:||list||), 
                 forall y:'ty_p,  p u y -> p (cons x' u) (f x' u y)) ->
              forall (u:||list||),  p u (fold x f u)
   *)
 end

