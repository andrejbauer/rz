module type SQGROUP = 
sig
  type s
  (**  Assertion per_s =  PER(=s=)
  *)
   
  val e : s
  (**  Assertion e_total =  e : ||s||
  *)
   
  val ( * ) : s -> s -> s
  (**  Assertion ( * )_total = 
         all (x:s,y:s).  x =s= y =>
           all (x':s,y':s).  x' =s= y' => 
	     x * x' =s= y * y'
  *)
   
  
  (**  Assertion unit (x:s) =  
	 x * e =s= x and e * x =s= x
  *)
   
  
  (**  Assertion assoc (x:s,y:s,z:s) =  
	 x * (y * z) =s= (x * y) * z
  *)
   
  val sqrt : s -> s
  (**  Assertion sqrt (x:s) =  
	sqrt x : ||s||  and 
        sqrt x * sqrt x =s= x
  *)
end

