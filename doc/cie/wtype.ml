module type Branching =
sig
  type s
  type t
end

module W (S : Branching) =
struct
  type w = Tree of S.s * (S.t -> w)

  let tree x y = Tree (x, y)

  module Induction (M : sig type ty_p end) =
    struct
      let rec induction h (Tree (x, f)) : M.ty_p =
	h x f (fun y -> induction h (f y))
    end
end
