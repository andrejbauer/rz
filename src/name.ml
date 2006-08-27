(** Utility functions for manipulating names. This was mostly moved from Syntax. *)

(* We follow ocaml's notions of infix and prefix operations *)

type label = string

type fixity = Word | Prefix | Infix0 | Infix1 | Infix2 | Infix3 | Infix4 | Wild

type name = N of string * fixity

module NameOrder =
struct
  type t = name
  let compare = Pervasives.compare
end

module StringOrder =
struct
  type t = string
  let compare = Pervasives.compare
end

module NameMap = Map.Make(NameOrder)

module StringMap = Map.Make(StringOrder)

module NameSet = Set.Make(NameOrder)

let unionNameSetList = List.fold_left NameSet.union NameSet.empty

module StringSet = Set.Make(StringOrder)

let capitalize_name (N(nm, fxty)) = N(String.capitalize nm, fxty)

(** [stringSubscript s] splits name [s] into everything that comes beofore
    and after the first underscore ['_'] appearing in [s]. *)
let stringSubscript s =
  try
    let k = String.rindex s '_' in
      String.sub s 0 k, Some (String.sub s (k+1) (String.length s - k - 1))
  with Not_found -> s, None

(** [stringPrime s] splits name [s] into everything that comes beofore
    and after the first apostrophe ['''] appearing in [s]. *)
let stringPrime s =
  try
    let k = String.index s '\'' in
      String.sub s 0 k, Some (String.sub s k (String.length s - k))
  with Not_found -> s, None

(** [splitString s] splits name [s] into three parts: everything
    appearing before the first underscore, between the first underscore
    and first prime, and after first prime. *)
let splitString n =
  let m, p = stringPrime n in
  let r, s = stringSubscript m in
    r, s, p

(** [nextString s] generates a name different from [s] that can be
    used as a substitute for it. It does so by adjoining primes and
    subscripts to [s] in an intelligent way. *)
let nextString n =
  let r, s, p = splitString n in
    r ^ (match s, p with
	     None, None -> "'"
	   | None, Some "'" -> "''"
	   | None, Some p -> "_1"
	   | Some s, _ ->
	       "_" ^ (
		 try
		   string_of_int (1 + int_of_string s)
		 with
		     Failure "int_of_string" -> "1"
	       )
	)

(** [freshString good bad occurs] generates a fresh string. It uses
    one of the strings in list [good], possibly adding primes and
    subscripts to it, it avoids strings in the list [bad], and it makes sure
    the [occurs] function returns [false] on it.
*)
let freshString good bad occurs =
  let rec find g =
    try
      List.find (fun x -> not (List.mem x bad) && not (occurs x)) g
    with Not_found -> find (List.map nextString g)
  in
    find good

(** [nextName n] computes a subtitute for name [n], just like
    [nextString] does for strings. *)
let nextName = function
    N(nm, Word) -> N(nextString nm, Word)
  | N(_, fixity) -> N(nextString "op", fixity)

(** [freshName good bad occurs] generates a fresh name. It uses
    one of the names in list [good], possibly adding primes and
    subscripts to it, it avoids names in the list [bad], and it makes sure
    the [occurs] function returns [false] on it.
*)
let freshName good bad occurs =
  let rec find g =
    try
      List.find (fun nm -> not (List.mem nm bad) && not (occurs nm)) g
    with Not_found -> find (List.map nextName g)
  in
    find good

(** [freshName2 good1 good2 bad occurs] generates two fresh names. *)
let freshName2 good1 good2 bad occurs =
  let x1 = freshName good1 bad occurs in
  let x2 = freshName good2 (x1::bad) occurs in
    x1, x2

(** [freshName3 good1 good2 good3 bad occurs] generates three fresh names. *)
let freshName3 good1 good2 good3 bad occurs =
  let x1 = freshName good1 bad occurs in
  let x2 = freshName good2 (x1::bad) occurs in
  let x3 = freshName good3 (x1::x2::bad) occurs in
    x1, x2, x3

(** [freshName4 good1 good2 good3 good4 bad occurs] generates four fresh names. *)
let freshName4 good1 good2 good3 good4 bad occurs =
  let x1 = freshName good1 bad occurs in
  let x2 = freshName good2 (x1::bad) occurs in
  let x3 = freshName good3 (x1::x2::bad) occurs in
  let x4 = freshName good4 (x1::x2::x3::bad) occurs in
    x1, x2, x3, x4

(** [freshNameList goods bad occurs] generates a list of fresh names. *)
let rec freshNameList goods bad occurs =
  match goods with
      [] -> []
    | g::gs ->
	let n = freshName g bad occurs in
	  n :: (freshNameList gs (n::bad) occurs)

(** [string_of_name n] converts a name [n] to its string representation. *)
let rec string_of_name = function 
  | N(_, Wild) -> "_"
  | N(str,Word) -> str
  | N("*",_) -> "( * )"
  | N(str,_) -> "(" ^ str ^ ")"

(** [wildName ()] generates a new wildcard (an anonymous name). *)
let (wildName, wildModelName) =
  let k = ref 0 in
    ((fun () -> incr k; N ("__" ^ string_of_int !k, Wild)),
     (fun () -> incr k; N ("Z__" ^ string_of_int !k, Wild)))

let wildName =
  let k = ref 0 in
    fun () -> incr k; N ("_" ^ string_of_int !k, Wild)

let isWild = function
    N(_, Wild) -> true
  | _ -> false

let validTermName = function
    N(str, Word) -> (str = String.uncapitalize str) 
  | N(_, Wild) -> true
  | _ -> true

let validSetName = validTermName

let validPropName = validTermName

let validModelName = function
    N(str, Word) -> (str = String.capitalize str)
  | N(_, Wild) -> true
  | _ -> false

let validTheoryName = validModelName

let (freshNameString, freshModelNameString) = 
  let counter = ref 0
  in
     ((function () -> (incr counter;
	               "___" ^ string_of_int (!counter))),
     (function () -> (incr counter;
		      "Z__" ^ string_of_int (!counter))))


(** Given two names of the same "sort" (wildness, capitalization), 
    find a name suitable for replacing them both.
*)
let jointName nm1 nm2 =
  if (nm1 = nm2) then 
    (* We assume the inputs are well-formed without shadowing, so
       if they both use exactly the same bound variable there's no
       point in replacing this bound variable by a fresh one. *)
    nm1
  else
    begin
      (* nm1 and nm2 should be the same "sort", so if nm1 is a model name
	 we know that nm2 is too.
      *)
      match (isWild nm1 && isWild nm2, validModelName nm1) with
	  (true, false)  -> wildName()
	| (true, true)   -> wildModelName()
	| (false, false) -> N(freshNameString(), Word)
	| (false, true)  -> N(freshModelNameString(), Word)
    end

