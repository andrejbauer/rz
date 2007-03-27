(** Global flags controlling the system *)

(* Should the optimizer run? *)
let do_opt = ref true

(* Should the optimizer run? *)
let do_thin = ref true

(* Preamble file to load *)
let preamble = ref (None : string option)

(* Should output be sent to stdout too? *)
let do_print = ref true

(* Should output be sent to a file? *)
let do_save = ref true

(* Should signature applications be retained, instead of being beta-expanded? *)
let do_sigapp = ref false

let do_dumpinfer = ref false (* Should result of infer be written to stdout? *)

let do_hoist = ref false (* Should obligations be hoisted in assertions? *)

let do_poly  = ref true  (* Should we try to replace functors by polymorphism? *)
