type s
 
(** predicate (=s=) : s -> s -> bool *)
(**  Assertion symmetric_s =  forall x:s, y:s,  x =s= y -> y =s= x
      
     Assertion transitive_s = 
       forall x:s, y:s, z:s,  x =s= y /\ y =s= z -> x =s= z
*)
 
val decidable_eq : s -> s -> [`or0 | `or1]
(**  Assertion decidable_eq = 
       forall (x:||s||, y:||s||), 
         (match decidable_eq x y with
            `or0 => x =s= y 
          | `or1 => not (x =s= y) 
          )
*)

