module type Ab =
sig
  type t
  val zero : t
  val neg : t -> t
  val add : t * t -> t
end

module Z7 : Ab =
struct
  type t = int
  let zero = 0
  let neg k = - (k mod 7)
  let add (k,m) = k mod 7 + m mod 7
  let eq (k,m) = (k mod 7 - m mod 7) mod 7 = 0
end
