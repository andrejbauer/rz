Definition A := thy
       Parameter a : Set.
end.

Definition B := thy
       include A.
       Parameter b : Set.
end.

Definition C := thy
       include B.
       Definition d := a * b.
end.
