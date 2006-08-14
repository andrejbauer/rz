module type Iteration = 
sig
 type s
 (**  Assertion per_s =  PER(=s=) *)
 val zero : s
 (**  Assertion zero_total =  zero : ||s|| *)   
 val succ : s -> s
 (**  Assertion succ_total =
   all (x:s, y:s).  x =s= y => succ x =s= succ y *)
end

module type Nat = 
sig
 module N : Iteration   
 module Initial : functor (I : Iteration) ->
  sig
   val initial : N.s -> I.s
    (**  Assertion initial = 
      (all (x:N.s, y:N.s).  x =N.s= y => initial x =I.s= initial y) and 
      initial N.zero =I.s= I.zero and 
      (all (n:||N.s||). initial (N.succ n) =I.s= I.succ (initial n)) and 
      (all (u:N.s -> I.s). 
        (all (x:N.s, y:N.s).  x =N.s= y => u x =I.s= u y) =>
        u N.zero =I.s= I.zero and
        (all (n:||N.s||). u (N.succ n) =I.s= I.succ (u n)) =>
        all (x:N.s, y:N.s).  x =N.s= y => initial x =I.s= u y)
     *)
 end
end
