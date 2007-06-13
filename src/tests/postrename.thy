Definition T :=
thy
  Parameter s : Set.
end.

Definition U :=
thy
  Parameter s : Set.
  Parameter X : T.
end.

Definition V (X : U) (X : U) :=
thy
  Parameter X : U.
end.

Definition W (X : U) (Y : U) :=
thy
  Parameter Y : T.
end.