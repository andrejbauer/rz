theory A := thy
       Parameter a : Set.
end

theory B := thy
       include A.
       Parameter b : Set.
end

theory C := thy
       include B.
       Definition d := a * b.
end
