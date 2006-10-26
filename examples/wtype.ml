module type Signature =
sig
  type s
  type t
end

module W (S : Signature) =
struct
  type w = Tree of S.s * (S.t -> w)

  let tree x y = Tree (x, y)

  let rec induction h t =
    let Tree (x, f) = t in
      h x f (fun y -> induction h (f y))
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
  Nat.induction (fun x f h ->
		   match x with
		       NSig.Zero -> 0
		     | NSig.Succ -> 1 + h ()
		)

(** Example: binary trees *)

module BTSig =
struct
  type s = Empty | Node
  type t = Left | Right
end

module BTree = W(BTSig)

(* Conversion to and from ordinary trees *)

type btree = Empty | Node of btree * btree

let rec of_btree = function
    Empty -> BTree.tree BTSig.Empty bottom
  | Node (t1, t2) ->
      BTree.tree BTSig.Node (function BTSig.Left -> of_btree t1 | BTSig.Right -> of_btree t2)

let to_btree =
  BTree.induction (fun x f h ->
		     match x with
			 BTSig.Empty -> Empty
		       | BTSig.Node -> Node (h BTSig.Left, h BTSig.Right))

(* size of a tree (number of nodes) *)
let size =
  BTree.induction (fun x f h ->
		     match x with
			 BTSig.Empty -> 0
		       | BTSig.Node -> 1 + h BTSig.Left + h BTSig.Right)


(** Example: trees with arbitrary finite branching *)
module TSig =
struct
  type s = int
  type t = int
end

module Tree = W(TSig)

(* conversion *)
type tree = Tree of tree list

let rec of_tree = function
    Tree [] -> Tree.tree 0 bottom
  | Tree lst -> Tree.tree (List.length lst) (fun n -> of_tree (List.nth lst n))

let rec range f i j =
  if i > j then [] else (f i) :: (range f (i+1) j)

let rec to_tree =
  Tree.induction (fun x f h -> Tree (range (fun k -> h k) 0 (x-1)))
