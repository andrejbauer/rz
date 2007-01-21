module type Signature =
sig
  type s
  type t
end

module W (S : Signature) =
struct
  type w = Tree of S.s * (S.t -> w)

  let tree x y = Tree (x, y)

  module Induction (M : sig type ty_p end) =
    struct
      let rec induction h (Tree (x, f)) : M.ty_p =
	h x f (fun y -> induction h (f y))
    end
end

(** Example: natural numbers *)

module NSig =
struct
  type s = Zero | Succ
  type t = unit
end

module Nat = W(NSig)

(** conversion from int to nat and back *)
let rec bottom x = failwith "bottom hit"

let rec of_int = function
    0 -> Nat.tree NSig.Zero bottom
  | n -> Nat.tree NSig.Succ (fun _ -> of_int (n-1))

let to_int =
  let module S = struct type ty_p = int end in
  let module N = Nat.Induction(S) in
    N.induction
      (fun x f h ->
	 match x with
	     NSig.Zero -> 0
	   | NSig.Succ -> 1 + h ()
      )
