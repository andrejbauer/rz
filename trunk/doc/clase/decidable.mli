module type DecidableSet = 
sig
  type s
  (** Assertion per_s = PER(=s=) *)
   
  val decidable : s -> s -> [`or0 | `or1]
  (** Assertion
    decidable (x:||s||, y:||s||) =
      decidable x y = `or0 and x =s= y cor
      decidable x y = `or1 and not (x =s= y)
  *)
end
