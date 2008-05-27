Require Export Setoid.
Require Export EqNat.


Record ModestSet_Theory (ty : Set) : Type :=
  mkModest_Theory {
    equ : ty -> ty -> Prop;
    symm : forall x y : ty, equ x y -> equ y x;
    tran : forall x y z : ty, equ x y -> equ y z -> equ x z
  }.

Record ModestSet : Type :=
  mkModest {
    ty :> Set;
    modesty : ModestSet_Theory ty
  }.

Definition total (A : ModestSet) (x : A) := equ A (modesty A) x x.


Record ModestFamily (A : ModestSet) : Type :=
  mkModestFamily {
    fam : A -> ModestSet;
    strict :
      forall (x : A) (u v : fam x), equ (fam x) u v -> equ A x x;
    uniform :
      forall (x y : A), equ A x y -> fam x = fam y
  }.


Definition ext_eq (A B : ModestSet) (f g : A -> B) :=
  forall x y : A, equ A x y -> equ B (f x) (g y).

Definition extensional (A B : ModestSet) (f : A -> B) :=
  ext_eq A B f f.

Definition Ext (A B : ModestSet) :=
  { f : A -> B | extensional A B f }.

Definition func_of_ext (A B : ModestSet) (f : Ext A B) :=
  let (g, _) := f in g.

Coercion func_of_ext : Ext >-> Funclass.


Definition Product : ModestSet -> ModestSet -> ModestSet.
Proof.
  intros A B.
  apply mkModest with
    (ty := (A * B)%type)
    (equ := fun (p q : A * B) =>
      equ A (fst p) (fst q) /\ equ B (snd p) (snd q)).
  intros p q.
  intuition.
  apply symm; assumption.
  apply symm; assumption.
  intros p q r.
  intuition.
  eauto using tran.
  eauto using tran.
Defined.

Definition proj1 : forall (A B : ModestSet), Ext (Product A B) A.
Proof.
  intros A B.
  exists (fun p : (Product A B) => fst p).
  red.
  intros p q H.
  simpl in H.
  intuition.
Defined.
  
Definition proj2 : forall (A B : ModestSet), Ext (Product A B) B.
Proof.
  intros A B.
  exists (fun p : (Product A B) => snd p).
  red.
  intros p q H.
  simpl in H.
  intuition.
Defined.
  
Lemma prod_eta :
  forall (A B : ModestSet) (p : Product A B),
    total (Product A B) p -> equ (Product A B) p (fst p, snd p).
Proof.
  intros.
  red.
  simpl.
  red in H.
  simpl in H.
  assumption.
Qed.


Definition Hom : ModestSet -> ModestSet -> ModestSet.
Proof.
  intros A B.
  apply mkModest with
    (ty := A -> B)
    (equ := fun (f g : A -> B) =>
      extensional A B f /\ extensional A B g /\ ext_eq A B f g).
  intros f g.
  unfold ext_eq.
  intuition.
  apply symm.
  apply H2.
  apply symm.
  assumption.
  intros f g h.
  unfold ext_eq.
  intuition.
  apply tran with (h x).
  apply tran with (g y).
  auto.
  apply symm in H3.
  auto.
  apply H2.
  assumption.
Qed.





Definition Projective (A : Set) : ModestSet.
Proof.
  intro A.
  eapply mkModest with
    (ty := A)
    (total := (fun (_ : A) => True))
    (equ := (fun (x y : {z : A | True}) => x = y)).
  auto.
  intuition.
  intuition.
  rewrite H; auto.
Qed.

Definition Nats := Projective nat.

(*** UNFINISHED BELOW *)


(** W-types

Record BranchingType : Type := 
    mkSignature 
      { index : ModestSet;
        branch :  -> ModestSet
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