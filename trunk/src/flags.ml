(** Global flags controlling the system *)

let do_opt = ref true   (* Should the optimizer run? *)

let do_print = ref true (* Should output be sent to stdout too? *)

let do_save = ref true  (* Should output be sent to a file? *)

let do_sigapp = ref false (* Should signature applications be retained,
			     instead of being beta-expanded? *)
