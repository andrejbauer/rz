Require Export Setoid.
Require Export EqNat.

Record ModestSet : Type :=
  mkModest {
    ty : Set; (* the type *)
    st : Set; (* the set *)
    rz : ty -> st -> Prop; (* the realizability relation *)
    rz_total : forall x : st, exists u : ty, rz u x; (* everybody is realized *)
    rz_modest : forall u : ty, forall x y : st, rz u x -> rz u y -> x = y
  }.

Definition eq (A : ModestSet) (u v : ty A) :=
  exists x : st A, rz A u x /\ rz A v x.

Definition trackers (A B : ModestSet) (g : st A -> st B) :=
  { f : ty A -> ty B | forall u : ty A, forall x : st A, rz A u x -> rz B (f u) (g x) }.

Definition Nats : ModestSet.
Proof.
  Check mkModest.
  eapply mkModest with (ty := nat) (st := nat) (rz := fun (x :nat) (y :nat) => x = y).
  intros; exists x; auto.
  intros.
  rewrite <- H.
  rewrite <- H0.
  auto.
Qed.


(**** UNFINISHED BELOW *)

(*********

Definition Hom (A B : ModestSet) : ModestSet.

Definition app (A B : ModestSet) (h : Hom A B) (x : st A) :=
  let (g, _) := h in g x.

Record Signature : Type := 
    mkSignature 
      { s : ModestSet;
        t : st s -> ModestSet
      }.

Record W(B : Signature) : Type :=
   mkW
     {
       w : ModestSet;
       tree : forall a : st (s B), Hom (t B a

st (s B), (st (t B a) -> st w) -> st w;
       induction : forall p : w -> Set,
         (forall a : s B, forall f : t B a -> w, (forall x : t B a, p (f x)) -> p (tree a f)) -> forall t : w, p t
    }.

***)
(*
Module Type SIGNATURE.

  Parameter s : Set.
  Parameter eq_s : relation s.
  Axiom per_s : Setoid_Theory s eq_s.

  Parameter t : Set.
  Parameter eq_t : s -> relation t.
  Axiom eq_t_extensional: 
     forall x y : s, eq_s x y -> 
        forall u v : t,
           eq_t x u v <-> eq_t y u v.

  Axiom per_t : forall x : s, eq_s x x -> Setoid_Theory t (eq_t x).
  
End SIGNATURE.


Module W (S : SIGNATURE).

  Parameter w : Set.
  Parameter eq_w : relation w.
  Axiom per_w : Setoid_Theory w eq_w.
  
  Parameter tree : S.s -> (S.t -> w) -> w.

  Axiom tree_total :
    forall x y:S.s,  S.eq_s x y ->
       forall f g:S.t -> w, 
           (forall z t:S.t,  S.eq_t x z t -> eq_w (f z) (g t)) ->
            eq_w (tree x f) (tree y g).

  Parameter induction : 
    forall p : Set, 
       (S.s -> (S.t -> w) -> (S.t -> p) -> p) -> w -> p.

             (**  Assertion predicate_p = 
                    (forall x:w, a:p,  a |= p x -> x : ||w||) /\ 
                    (forall (x:||w||, y:||w||), 
                       forall a:p,  x =w= y -> a |= p x -> a |= p y)
                   
                  Assertion 'p p:w->p->prop induction = 
                    forall f:S.s -> (S.t -> w) -> (S.t -> 'p) -> 'p, 
                      (forall (x:||S.s||), 
                         forall f':S.t -> w, 
                           (forall y:S.t, z:S.t,  y =(S.t x)= z ->
                              f' y =w= f' z) ->
                           forall g:S.t -> 'p, 
                             (forall y:S.t,  y : ||S.t x|| -> g y |= p (f' y)) ->
                             f x f' g |= p (tree x f')) ->
                      forall (t:||w||),  induction f t |= p t
             *)   
End W.

Module Test.

 Declare Module TestMod : SIGNATURE.

End Test.
    
Extraction W.
*)