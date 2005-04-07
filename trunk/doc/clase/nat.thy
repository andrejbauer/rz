theory Iteration = thy
 set s
 const zero : s
 const succ : s -> s
end

theory Nat = thy
 model N : Iteration

 axiom initial [I : Iteration] =
   unique (f : N.s -> I.s). 
    (f N.zero = I.zero  and  all (n : N.s) . f (N.succ n) = I.succ (f n))
end