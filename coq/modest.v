(* An attempt to formalize modest sets [well, really, pers] in Coq.
*)


(* Module M. *)

(*********************************************************************)
(*
The type ModestSet(u) classifies Modest sets whose where the
domain of realizers (sometimes written |.| ) is u.

Any such modest set contains
  The underlying type from which realizers are drawn, called t;
  A binary relation on t, called eq;
  A proof that eq is symmetric;
  A proof that eq is transitive.

Actualy, since the set of realizers is already in the type of the
modest set, there's not actually any need to make this type a
components of the record.  But it doesn't seem to hurt anything either
--- even if you take it out, Coq still won't let ModestSet(u) be a Set
rather than a Type [impredicativity constraints still prevent it].

*)
(*********************************************************************)

Record ModestSet(u : Set) : Type := mkModest
  {t : Set := u;
   eq: t -> t -> Prop;
   Modest_per_cond1: forall x y : t, eq x y -> eq y x;
   Modest_per_cond2: forall x y z : t,  eq x y -> eq y z -> eq x z}.

Implicit Arguments t [u].
Implicit Arguments eq [u].
Implicit Arguments Modest_per_cond1 [u].
Implicit Arguments Modest_per_cond2 [u].

(*********************************************************************)
(*
Although the set of per-respecting functions between modest sets is
itself naturally a modest set, it turns out to be much more useful
to additionally tag this function space with the source and target 
modest sets.

The way coq records work, by the way, means that all record labels
must be distinct within a scope.  Hence MA_t and MA_eq instead of
t and eq again.
*)
(*********************************************************************)

Record ModestArrows(u v: Set) : Type := mkMA
  {MA_src : ModestSet(u);
   MA_tgt : ModestSet(v);
   MA_t : Set := u -> v;
   MA_eq: MA_t -> MA_t -> Prop :=
      fun (f g : MA_t) => 
                 forall x y: u, MA_src.(eq) x y -> MA_tgt.(eq) (f x) (g y);
   MA_Modest_per_cond1: 
      forall x y : MA_t, MA_eq x y -> MA_eq y x;
   MA_Modest_per_cond2:
      forall x y z : MA_t,  MA_eq x y -> MA_eq y z -> MA_eq x z}.


Implicit Arguments MA_src [u v].
Implicit Arguments MA_tgt [u v].
Implicit Arguments MA_t [u v].
Implicit Arguments MA_eq [u v].
Implicit Arguments MA_Modest_per_cond1 [u v].
Implicit Arguments MA_Modest_per_cond2 [u v].
Implicit Arguments mkMA [u v].


(* A proof that "eq" members of the modest-set of functions
   really do preserve per equivalence.

   There might be a simpler way to do this.
*)
Definition MA_Modest_arrows_cond :
      forall (u v : Set) (m : ModestArrows u v) (f g : m.(MA_t)), m.(MA_eq) f g 
        -> forall x y : u, m.(MA_src).(eq) x y 
          -> m.(MA_tgt).(eq) (f x) (g y)
  := fun (u v : Set) (m : ModestArrows u v) (f g : m.(MA_t)) (H : m.(MA_eq) f g) (x y : u) (H0 : eq m.(MA_src) x y) => H x y H0.

Implicit Arguments MA_Modest_arrows_cond [u v].


(* Interactive Proof of MA_Modest_arrows_cond:

red in |- *.
intros.
red in H.
apply H.
apply H0.

*)

(*********************************************************************)
(* Given two modest sets, we can automatically construct the function
   space between them, as follows.  (The ugliness is due to the proof
   terms showing that the induced equivalence is indeed symmetric
   and transitive
*)
(*********************************************************************)


Definition MakeFnSpace (u1 u2 : Set) (m1 : ModestSet(u1)) (m2 : ModestSet(u2)) : (ModestArrows u1 u2) :=
  let MA_t' := u1->u2
  in let MA_eq' := fun (f g : MA_t') => 
                 forall x y: m1.(t), m1.(eq) x y -> m2.(eq) (f x) (g y)
  in let MA_sym' : forall f g : MA_t', MA_eq' f g -> MA_eq' g f := 
        fun (f g : MA_t') (H : MA_eq' f g) (x y : t m1) (H0 : eq m1 x y) =>
         Modest_per_cond1 m2 (f y) (g x) 
               (H y x (Modest_per_cond1 m1 x y H0))
   in let MA_trans' : forall f g h : MA_t', MA_eq' f g -> MA_eq' g h -> MA_eq' f h :=
        fun (f g h : MA_t') (H : MA_eq' f g) (H0 : MA_eq' g h) (x y : t m1) (H1 : eq m1 x y) =>
         Modest_per_cond2 m2 (f x) (g y) (h y) (H x y H1)
         (H0 y y
            (let H2 := Modest_per_cond1 m1 x y H1 
             in Modest_per_cond2 m1 y x y H2 H1))
  in mkMA m1 m2 MA_sym' MA_trans'.

Implicit Arguments MakeFnSpace [u1 u2].

(* Interactive symmetry proof for function spaces:

intros.
red in |- *.
intros.
apply (Modest_per_cond1 m2).
apply (H y0 x0).
apply (Modest_per_cond1 m1).
assumption.


Transitivity proof:

intros.
red in |- *.
intros.
apply (Modest_per_cond2 m2 (f x) (g y) (h y)).
 apply H.
   assumption.
 apply H0.
   assert (H2 := Modest_per_cond1 m1 x y H1).
   exact (Modest_per_cond2 m1 y x y H2 H1).

*)


(********)
(* We add an infix operator that, given two modest sets, constructs
   the induced function space.
*)
(********)

Infix "-->" := MakeFnSpace (at level 75, right associativity).

(*********************************************************************)
(* By ignoring the source and target of the modest-set-function-space,
   we get a modest set.  

   The following function defines an automatic coercion that coq
   can use when a function-space is supplied where any modest
   set would suffice.
*)
(*********************************************************************)


Definition MA_underlying (u v : Set) (M : ModestArrows u v) : ModestSet(u->v) :=
   mkModest (u->v) M.(MA_eq) M.(MA_Modest_per_cond1) M.(MA_Modest_per_cond2).

Coercion MA_underlying : ModestArrows >-> ModestSet.

(*********************************************************************)
(* A value of a modest set is defined as the combination of the
   value itself plus a proof that this value is a total value.

   The type constructor ModestVal(m) classifies values in the modest
   set (value) m.  Note the number of layers here.  In place of RZ's

        set s
        val x : s

   we have something more like

        Parameter s_rz : Set.
        Parameter s : ModestSet(s_rz).

        Parameter x : ModestVal(s).

*)
(*********************************************************************)

Record ModestVal(u : Set) (MS : ModestSet(u)) : Set := mkMV
  {val : MS.(t);
   total : MS.(eq) val val}.

Implicit Arguments mkMV [u].
Implicit Arguments ModestVal [u].
Implicit Arguments val [u MS].
Implicit Arguments total [u MS].


(*********************************************************************)
(* A couple quick examples *)
(*********************************************************************)

(* A modest set of natural numbers realizing themselves.
   
   The proof terms are much more complicated than necessary because the
   PER is the recursively-defined eq_nat function in the coq library
   instead of coq's built-in equality.  
*)

Require Export EqNat.

Definition ModestNat : ModestSet(nat) :=
  let mysym      :=  fun (x y : nat) (H : eq_nat x y) => 
                      eq_eq_nat y x (sym_eq (eq_nat_eq x y H))
  in let mytrans := fun (x y z : nat) (H1 : eq_nat x y) (H2 : eq_nat y z) =>
                      eq_eq_nat x z (trans_eq (eq_nat_eq x y H1) 
                                              (eq_nat_eq y z H2))
  in 
    mkModest nat eq_nat mysym mytrans.


(* A member of that modest set 
*)
Definition zero : ModestVal(ModestNat) :=
  mkMV ModestNat 0 (eq_nat_refl 0).


(* Some modest function spaces
 *)

Definition ModestNatNat := ModestNat --> ModestNat.

Definition ModestNatNatNat := ModestNat --> ModestNat --> ModestNat.



(*********************************************************************)
(* Since members of a modest set of functions have type
      ModestVal(m)
   (where m is a modest-set function space)
   instead of an arrow type, they can't be directly applied.

   So, here's the function that does application (of f to x). The
   proof that (f x) is total comes directly from the 
   (badly named) MA_Modest_arrows_cond proof above.
*)
(*********************************************************************)

Definition manifestApp (u2 u : Set) (m1 : ModestArrows u2 u) 
                       (f : ModestVal(m1)) (x : ModestVal(m1.(MA_src))) 
     : ModestVal(m1.(MA_tgt)) :=
  let    val' := f.(val) x.(val)
  in let total' : m1.(MA_tgt).(eq) val' val' := 
            MA_Modest_arrows_cond m1 (val f) (val f) (total f) 
                                     (val x) (val x) (total x)
  in mkMV m1.(MA_tgt) val' total'.

Implicit Arguments manifestApp [u2 u m1].

(* Interactive roof of total':

unfold val' in |- *.
apply (MA_Modest_arrows_cond m1 (val f) (val f)).
 exact (total f).
 exact (total x).

*)


(*********************************************************************)
(* Some better notation for application: the infix @@ operator.

   Unfortunately, because the above application works not for every
   modest value f but only modest values over Modest-function-spaces,
   coq's built-in coercions don't let use manifestApp as an
   implicit conversion.  So, an explicit application operator
   is required.
*)
(*********************************************************************)
Infix "@@" := manifestApp (at level 25, left associativity).



(* Test code *)
Parameter test1 : ModestVal(ModestNat).     (* Assuming we have a nat *)
Parameter test2 : ModestVal(ModestNatNat).  (*  And a function on nats *)
Definition test3 := (test2 @@ test1).       (* We can apply them. *)


(* End M. *)


(*********************************************************************)
(* Translating RZ.
   
   From here, I started translating field.  Sets and constants are
   still OK, but I still don't know how to translate relations
   and propositions reasonably into Coq.

   There is one thing that even this much points out, though,
   if you look at the coq output.

   I've built up a lot of machinery so that the specifications below
   ensure that the set s is a per, that the neg function respects
   the per, etc.  

   If you look at the signature that Coq generates, all these
   requirements are missing from the executable code.  This is
   entirely reasonable, and in fact what we want --- there's not
   desire to make require "set s" require that the user implement both
   a "type s" *and* a function "eq : s -> s -> bool".

   But these requirements don't even appear as comments: there's
   no hint in the NEQ_AS_SET signature what the specified values
   and functions are suppose to do.  Note also that the definition 
   of "two" below is entirely lost in the ML output.

   *This* may be the reason why we can't use Coq [at least as currently
   implemented] as a replacement for RZ.  It assumes that the entire
   program is extracted from a Coq proof, and doesn't appear to provide
   any support for describing interfaces only...
*)
(*********************************************************************)



Module Type NEQ_AS_SET.
  Parameter s_rz : Set.
  Parameter s : ModestSet(s_rz).


  Parameter zero  : ModestVal(s).
  Parameter one   : ModestVal(s).	
  Parameter plus  : ModestVal(s --> s --> s).
  Parameter neg   : ModestVal(s --> s).
  Parameter times : ModestVal(s --> s --> s).

  Definition two := plus @@ one @@ one.



(*

  Parameter neq_rz : Set.
  Parameter neq : s --> s --> neq_rz.

  Definition nonzero : s -> Set := fun w => neq w zero.

  Definition s' := {x:s & nonzero x}.

  Parameter inv : s' -> s.

(* Wrong. 
   But how to handle equality and negation? 
 *)
  Definition apart1 := forall x y : s, (neq x y) .

(* Works because implication == function arrow *)
  Definition apart2 := forall x y : s, (neq x y) -> (neq y x).

(* Replace logical \/ with set + *)
  Definition apart3 := forall x y z : s, neq x y -> (neq x z + neq y z).

(* This axiom disappears in the output because I've used the equality proposition and
   logical conjunction.  But probably this isn't the "right" translation.
 *)
  Definition inverse :=
     forall x : s, forall n : neq x zero, (times x (inv (existS nonzero x n)) = one) /\
                                          (times (inv (existS nonzero x n)) x = one).

*)
End NEQ_AS_SET.

Module Type NULL.
End NULL.


Module TestNeqAsSet (Thing : NEQ_AS_SET) : NULL.
End TestNeqAsSet.

(*Extraction M.
*)
Extraction TestNeqAsSet.

Extraction zero.
