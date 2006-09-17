theory HoistTerms :=
thy
  Parameter s : Set.
  Parameter a b c : s.
  Parameter p : s -> Prop.
  Parameter f : s -> s.

  Implicit Type x y : s.

  Definition emptyTuple  := ().
  Definition var         := a.
  Definition tuple       := (the x, p x, b, the x, p (f x)).
  Definition proj        := (the x, p x, b, the x, p (f b)).1.
  Definition g           := fun (f : s -> s) => f (the x, p x).
  Definition application := (the h:(s->s)->s, g=h) (fun x : s => (the y, p(y)) :< s).
  Definition description := the x : s,  p (the y, y=x).
  Definition cases       := match `foo a with 
     `foo (x:s) => the x, x=b
   | `bar => the x, x=c end.

  Parameter r : rz s.
  Definition rzquot      := rz (the q:rz s, q=r).
  Definition rzchoose    := let rz x = ((the x, a=x) :< s) in rz ((the q:rz s, q=x) :< rz s).

  Parameter eq : Equiv s.
  Definition quot        := ((the x, x=a) :< s) % eq.
  Definition choose_term := let [x] = (the w : s % eq, w=quot) in ((the y, x=y) :< s) % eq.
  Definition let_term    := let x = (the x, x=a) :< s in (x, ((the y, x=y) :< s)).
  Definition subin       := a :> {x:s | p x}. (* fishy *)

  Parameter d : {x:s | p x}.
  Definition subout      := d :< s.
  # assure cannot be tested directly
end
