Definition A :=
thy
        Parameter a : Set.
	Parameter n : a.
	Definition m: a := n. 
	Axiom q : forall (x:a), x=x. 
end.

Definition B :=
thy
        Parameter a : Set.
	Parameter n p : a.
	Axiom q : forall (x:a), x= (let y = (n,x,p).1 in y).
	Definition m : a :=
	   match `yes n with
	     `no => p 
	     | `yes (z:a) => ((fun x:a => x)z,p).0
           end.
end.

Definition C := 
       fun (M : A) => 
       	   thy 
	       Definition b := M.a.
	       Definition c := M.a.
      	   end.

Parameter X : B.

Definition D := C X.

