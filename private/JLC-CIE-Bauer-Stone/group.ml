module type Ab =
sig
  type t
  val zero : t
  val neg : t -> t
  val add : t * t -> t
end