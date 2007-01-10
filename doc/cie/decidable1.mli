type s
 
(* predicate (=s=) : s->s->prop *)
(**  Assertion per_s [Definitional] = 
       (forall x:s, y:s,  x =s= y -> y =s= x) /\ 
       (forall x:s, y:s, z:s,  x =s= y /\ y =s= z -> x =s= z)
*)
 
val decidable_eq : s -> s -> [`or0 | `or1]
(**  Assertion decidable_eq = 
       forall (x:||s||, y:||s||), 
         (match decidable_eq x y with
            `or0 => x =s= y 
          | `or1 => not (x =s= y) 
          )
*)

