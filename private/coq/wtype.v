Require Export Setoid.
Require Export EqNat.

Record ModestSet : Type :=
  mkModest {
    ty : Set; (* the type *)
    total : ty -> Prop;
    supp := { x : ty | total x };
    equ : supp -> supp -> Prop;
    refl : forall x : supp, equ x x;
    symm : forall x y : supp, equ x y -> equ y x;
    tran : forall x y z : supp, equ x y -> equ y z -> equ x z
  }.

Definition incl_supp (A : ModestSet) (x : supp A) :=
  let (y, _) := x in y.

Coercion incl_supp : supp >-> ty.

Definition extensional (A B : ModestSet) (f : ty A -> supp B) :=
  forall x y : supp A, equ A x y -> equ B (f x) (f y).

Definition Ext (A B : ModestSet) :=
  { f : ty A -> supp B | extensional A B f }.

Definition func_of_ext (A B : ModestSet) (f : Ext A B) :=
  let (g, _) := f in g.

Coercion func_of_ext : Ext >-> Funclass.

Definition Hom : ModestSet -> ModestSet -> ModestSet.
Proof.
  intros A B.
  eapply mkModest with
    (ty := ty A -> supp B)
    (total := extensional A B)
    (equ := fun (f g : Ext A B) =>
      forall x y : supp A, equ A x y -> equ B (f x) (g y)).
  intros f u v H.
  case f.
  intros g e.
  unfold extensional in e.
  firstorder.
  intros f g H u v G.
  apply symm.
  apply H.
  apply symm.
  assumption.
  intros f g h H G u v K.
  eapply (tran B).
  apply H.
  apply K.
  apply G.
  apply (refl A).
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