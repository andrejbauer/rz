type nat = int

let zero = 0

let s n = n + 1

let old_plus = Pervasives.(+)

let (+) = old_plus

let continuity f a =
  let p = ref 0 in
  let a' n = (p := max !p n; a n) in
    f a' ; !p
