Definition T := thy
  Parameter a : Set.
# THE FOLLOWING LINE CRASHES IT
#  Parameter t : a. # This line crashes it
end.

Definition F (M : T) := thy end.

Definition G := [M : T] -> thy
  include F(M).
end.

Definition H := [M : T] -> thy
  include F(M).
  Parameter x : M.a.
end.

Parameter M0 : T.

Parameter G0 : G.

Parameter H0 : H.

Definition PSI (X:G) :=  thy
#  Definition y := X(M0).x.  # And what should this be?
end.

Definition RHO (X:H) := 
thy
#  Definition y := X(M0).xx. # This is weird
#  Definition z := X(M0).x.  # This shouldn't die.
end.

Definition PHI := [X:G] -> thy end.

Parameter Q : PSI(G0). # ok
Parameter R : PSI(H0). # ok
# Parameter S : RHO(G0). # not ok, ERROR
Parameter W : RHO(H0). # ok
