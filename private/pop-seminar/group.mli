module type Group =
 sig
   type s
    
   (** predicate (=s=) : s -> s -> bool *)
   (**  assertion symmetric_s :  forall x:s, y:s,  x =s= y -> y =s= x
         
        assertion transitive_s : 
          forall x:s, y:s, z:s,  x =s= y /\ y =s= z -> x =s= z
   *)
    
   (** predicate ||s|| : s -> bool *)
   (**  assertion support_def_s :  forall x:s,  x : ||s|| <-> x =s= x
   *)
    
   val e : s
   (**  assertion e_support :  e : ||s||
   *)
    
   val mul : s -> s -> s
   (**  assertion mul_support :  mul : ||s -> s -> s||
   *)
    
   val inv : s -> s
   (**  assertion inv_support :  inv : ||s -> s||
   *)
    
   
   (**  assertion associative : 
          forall (x:||s||, y:||s||, z:||s||), 
            mul (mul x y) z =s= mul x (mul y z)
   *)
    
   
   (**  assertion neutral : 
          forall (x:||s||),  mul e x =s= x /\ mul x e =s= x
   *)
    
   
   (**  assertion inverse : 
          forall (x:||s||),  mul (inv x) x =s= e /\ mul x (inv x) =s= e
   *)
 end

