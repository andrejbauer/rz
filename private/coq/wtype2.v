(** W-types with Danko. *)

Require Import Setoid.





Section WType.

Parameter s : Setoid_Theory.

End WType.


Section WType2.

Parameter s : Set.

Parameter t : s -> Set.

(* Record w : Type := { *)
(*   car :> Set; *)
(*   tree : forall (x : s) (f : t x -> car), car; *)
(*   wind : *)
(*     forall p : car -> Set, *)
(*       (forall (x : s) (f : t x -> car), *)
(*         (forall y : t x, p (f y)) -> p (tree x f)) -> *)
(*       forall y : car, p y *)
(* }. *)

Parameter car : Set.
Parameter tree : forall (x : s) (f : t x -> car), car.
Parameter   wind :
    forall p : car -> Set,
      (forall (x : s) (f : t x -> car),
        (forall y : t x, p (f y)) -> p (tree x f)) ->
      forall y : car, p y.

Inductive audi : Set :=
  | Tree : forall (x : s) (f : t x -> audi), audi.

(*
Definition makew : w.
Proof.
  apply (Build_w audi (fun x => fun f => Tree x f)).
  intros.
  induction y.
  auto.
Defined.
*)
End WType2.

Recursive Extraction t.
Recursive Extraction makew.
