theory List(S : thy set a end) =
thy
  set list
  const nil : list
  const cons : S.a -> list -> list

  axiom initial [T : thy set a
                         const x : a
                         const f : S.a -> a -> a
                     end] =
    some (g : list -> T.a) . (
       g nil = T.x and
       all (u : S.a) . all (us : list) . (
         g (cons u us) = T.f u (g us)
       )
    )
end