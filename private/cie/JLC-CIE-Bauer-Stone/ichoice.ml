module Abstract : sig type a type b type r_ty end =
struct
  type a = unit
  type b = unit
  type r_ty = unit
end

type a = Abstract.a

type b = Abstract.b

type ty_r = Abstract.r_ty

let iac f = (fun x -> fst (f x)), (fun x -> snd (f x))
