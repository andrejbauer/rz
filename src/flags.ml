(** Global flags controlling the system *)

(* Should the optimizer run? *)
let do_opt = ref true

(* Should the optimizer run? *)
let do_thin = ref true

(* Preamble file to load *)
let preamble = ref (None : string option)

(* List of directories to search *)
let include_dir = ref ([] : string list)

(* Should output be sent to stdout too? *)
let do_print = ref true

(* Should output be sent to a file? *)
let do_save = ref true

(* Should signature applications be retained, instead of being beta-expanded? *)
let do_sigapp = ref false

let do_dumpinfer = ref false (* Should result of infer be written to stdout? *)

let do_hoist = ref false (* Should obligations be hoisted in assertions? *)

let do_fullhoist = ref false (* When doing hoisting, 
                                Should we do full, or partial, hoisting? *)

let do_poly  = ref true  (* Should we try to replace functors by polymorphism? *)

let do_coq = ref false
