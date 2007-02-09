Definition Terms :=
thy
  Parameter s : Set.
  Parameter a b c : s.
  Parameter p : s -> Prop.

  Definition emptyTuple  := ().
  Definition var         := a.
  Definition tuple       := (a, b, c).
  Definition proj        := (a, b, c).1.
  Definition g           := fun (f : s -> s) => f.
  Definition application := g (fun x : s => a).
  Definition description := the x : s,  p x.
  Definition cases       := match `foo a with `foo (x:s) => b | `bar => c end.

  Parameter r : rz s.
  Definition rzquot      := rz r.
  Definition rzchoose    := let rz x = a in rz x.

  Parameter eq : Equiv s.
  Definition quot        := a % eq.
  Definition choose_term := let [x] = quot in x % eq.
  Definition let_term    := let x = a in (x, x).
  Definition subin       := a :> {x:s | p x}. (* fishy *)

  Parameter d : {x:s | p x}.
  Definition subout      := d :< s.
  # assure cannot be tested directly

  Parameter impossible : empty.
  Definition magic : s  :=  impossible.  (* subset *)

end.
