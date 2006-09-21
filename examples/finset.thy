(** The theory of Kuratowski-style finite sets. *)

theory ASet := thy Parameter s : Set. end

theory Iterative(S : ASet) :=
thy
  Parameter t : Set.
  Parameter x : t.
  Parameter f : S.s -> t -> t.
end

(** First we define lists. *)
theory List(S : ASet) :=
thy
  Parameter list : Set.
  Parameter nil : list.
  Parameter cons : S.s -> list -> list.

  (* We would prefer to define the notion of a homomorphism of
     iterative algebras first, but there seems to be no good way
     of doing that. *)

  (** This axiom expresses the fact that lists are    *)
  (** an initial algebra for the functor t -> S.s * t *)
  Axiom list_initial:
    forall T : Iterative(S),
    exists1 h : list -> T.t,
        h nil = T.x /\
        forall y : S.s, forall l : list,
          h (cons y l) = T.f y (h l).
end