type a
 
(** predicate (=a=) : a -> a -> bool *)
(**  Assertion symmetric_a =  forall x:a, y:a,  x =a= y -> y =a= x
      
     Assertion transitive_a = 
       forall x:a, y:a, z:a,  x =a= y /\ y =a= z -> x =a= z
*)
 
type b
 
(** predicate (=b=) : b -> b -> bool *)
(**  Assertion symmetric_b =  forall x:b, y:b,  x =b= y -> y =b= x
      
     Assertion transitive_b = 
       forall x:b, y:b, z:b,  x =b= y /\ y =b= z -> x =b= z
*)
 
type ty_r
 
(** predicate r : a -> b -> ty_r -> bool *)
(**  Assertion strict_r = 
       forall x:a, y:b, c:ty_r,  r x y c -> x : ||a|| /\ y : ||b||
      
     Assertion extensional_r = 
       forall x:a, y:b, z:a, w:b, c:ty_r,  x =a= z /\ y =b= w -> r x y c ->
         r z w c
*)
 
val iac : (a -> b * ty_r) -> (a -> b) * (a -> ty_r)
(**  Assertion iac = 
       forall f:a -> b * ty_r, 
         (forall (x:||a||),  let (p,q) = f x in p : ||b|| /\ r x p q) ->
         let (g,h) = iac f in (forall x:a,  x : ||a|| -> g x : ||b||) /\ 
         (forall (x:||a||),  r x (g x) (h x))
*)

