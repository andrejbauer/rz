(** An implementation of integers. *)

open Big_int

type s = big_int

let add = add_big_int

let zero = zero_big_int

let neg = minus_big_int

let sub = sub_big_int

let one = unit_big_int

let mul = mult_big_int

type integer = s

let add1 = succ_big_int

let two = big_int_of_int 2

module Initial (R : Algebra.CommutativeRingWithUnit) =
struct
  let rec initial n =
    match sign_big_int n with
      | -1 -> R.neg (initial (minus_big_int n))
      |  0 -> R.zero
      |  1 ->
	   begin
	     let (q, r) = quomod_big_int n two in
	     let x = initial q in
	       match sign_big_int r with
		   0 -> R.mul x x
		 | 1 -> R.add (R.mul x x) R.one
		 | _ -> failwith "Impossible result of quomod_big_int"
	   end
      | _ -> failwith "Impossible result of sign_big_int"
end

let compare m n =
  match compare_big_int m n with
      -1 -> `less
    |  0 -> `equal
    |  1 -> `greater
    |  _ -> failwith "Impossible result of compare_big_int"

type nat = integer

let lt_dichotomy m n =
  match compare m n with
      `less    -> `or0
    | `equal   -> `or1
    | `greater -> `or2

type positiveInteger = integer

let pow = power_big_int_positive_big_int


