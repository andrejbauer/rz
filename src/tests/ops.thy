Definition T := thy
Parameter s : Set.

Parameter ?? : s -> s.
Parameter ++ : s -> s -> s.
Parameter (&&) : s -> s -> s.
Parameter x : s.

Parameter f : s -> s.
Definition y := f (?? x).  
Definition z := x ++ x.
Definition w := x && x.

Parameter g : (s -> s -> s) -> s.
Definition u := g (&&).

end.

Parameter M : T.

Definition Q := thy
   Parameter a : M.s.
   Parameter f : M.s -> M.s.
   Definition b := f (M.?? a).
   Definition c := M.(++) a a.  
   Definition d := M.++ a a.     
    (* Unfortunately, we can't parse
            a M.++ a
       So we might as well make the parens optional
       in the input.
     *)

end.