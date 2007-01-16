module type Branching =
sig
  type s
  type t
end

module W (S : Branching) =
struct
  type w = Tree of S.s * (S.t -> w)
  let tree x y = Tree (x, y)
  let rec induction f (Tree (x, g)) =
    f x g (fun y -> induction f (g y))
end
