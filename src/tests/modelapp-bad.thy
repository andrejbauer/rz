theory A :=
thy
   Parameter a : Set.
   Parameter c : a.

   Parameter E : thy Parameter e : Set. Definition f := e.  end.
end

theory B :=
thy
  Parameter a : Set.
  Definition b : Set := a.
  Parameter b' : Set.
  Parameter c : a.
  Parameter d : b.
  Parameter E : thy  Definition e := a.  Definition f := b'. end.
end

theory C :=
thy
  Parameter BB : B.
  Parameter FF : [X : A] -> A.
  Definition a := (FF BB).a .
end


