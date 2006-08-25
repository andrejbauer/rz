theory A :=
thy
        Parameter a : Set.
	Parameter n : a. 
	Axiom q : forall (x:a), x=x. 
end

theory B :=
thy
        Parameter a : Set.
	Axiom q : forall (x:a), x=x.
	Parameter n m : a.
end

theory C := 
       fun (M : A) => 
       	   thy 
	       Definition b := M.a.
	       Definition c := M.a.
      	   end

model X : B

theory D := C X

