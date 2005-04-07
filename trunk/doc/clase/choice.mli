module type Choice = 
sig
  type a
  (** Assertion per_a =  PER(=a=) *)
  type b
  (** Assertion per_b =  PER(=b=) *)
  type r
  (** Assertion predicate_r = 
    PREDICATE(r, a * b,
      lam t u.(pi0 t =a= pi0 u and pi1 t =b= pi1 u))
  *)
   
  val choice : (a -> b * r) -> (a -> b) * (a -> r)
  (**  Assertion choice = 
    all (f:a -> b * r). 
      (all (x:||a||).  pi0 (f x) : ||b|| and 
         pi1 (f x) |= r (x,pi0 (f x))) =>
      (all (x:a, y:a).  x =a= y => pi0 (choice f) x =b= pi0 (choice f) y) and 
      (all (x:||a||).  pi1 (choice f) x |= r (x,pi0 (choice f) x))
  *)
end
