theory A :=
thy
        Parameter a : Set.
end

theory B :=  
       fun M : A => 
           thy 
               Definition b := M.a.  
               Definition c := M.a.
           end

model X : A

theory C := B X

