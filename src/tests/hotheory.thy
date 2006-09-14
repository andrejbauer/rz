theory T := thy
  Parameter a : Set.
# THE FOLLOWING LINE CRASHES IT
#  Parameter t : a. # This line crashes it
end

theory F (M : T) := thy end

theory G := [M : T] -> thy
  include F(M).
end

theory H := [M : T] -> thy
  include F(M).
  Parameter x : M.a.
end

model M0 : T

model G0 : G

model H0 : H

theory PSI (X:G) :=  thy
#  Definition y := X(M0).x.  # And what should this be?
end

theory RHO (X:H) := 
thy
#  Definition y := X(M0).xx. # This is weird
#  Definition z := X(M0).x.  # This shouldn't die.
end

theory PHI := [X:G] -> thy end

model Q : PSI(G0) # ok
model R : PSI(H0) # ok
model S : RHO(G0) # not ok, ERROR

