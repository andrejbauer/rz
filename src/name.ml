(** Utility functions for manipulating names. This was mostly moved from Syntax. *)

(* We follow ocaml's notions of infix and prefix operations *)

type label = string

type fixity = Word | Prefix | Infix0 | Infix1 | Infix2 | Infix3 | Infix4 | Wild

type bare_name = string * fixity

type gensym = int * bare_name list

type name = N of bare_name | G of gensym

(********************************)
(** {2:Simple utility functions *)
(********************************)

(** mk_word: string -> name *)
let mk_word str = N (str, Word)

let gensym =
  let k = ref 0 in
    function
	[] ->  incr k; G (!k, [("gen", Word)])
      | lst -> incr k ; G (!k, lst)  

let string_of_name =
  let string_of_bare_name = function 
    | (n,   Wild) -> n
    | (str, Word) -> str
    | ("*"  ,_) -> "( * )"
    | (str,_) -> "(" ^ str ^ ")"
  in
    function
	N nm -> string_of_bare_name nm
      | G (k, lst) -> "gen" ^ string_of_int k ^ " (* " ^
	  String.concat ", " (List.map string_of_bare_name lst) ^ " *)"

(** capitalize_name: name -> name *)
let capitalize_name = function
    N (nm, fxty) -> N (String.capitalize nm, fxty)
  | G (k, lst) -> G (k, List.map (fun (nm, fxty) -> String.capitalize nm, fxty) lst)

(** wildName:      unit -> name
    wildModelName: unit -> name 

    [wildName ()] generates a new wildcard (an anonymous name).
    [wildModelName ()] does the same, but returns a name suitable
    for a model or theory, i.e., capitalized. *)
let (wildName, wildModelName) =
  let k = ref 0 in
    ((fun () -> incr k; N ("__" ^ string_of_int !k, Wild)),
     (fun () -> incr k; N ("Z__" ^ string_of_int !k, Wild)))

let isBareWild (_, fxty) = fxty = Wild

(** isWild: name -> bool

    [isWild n] checks whether [n] is a wildcard variable. *)
let isWild = function
    N bn -> isBareWild bn
  | G (_, lst) -> List.for_all isBareWild lst

(************************************)
(** {2: Name-indexed Sets and Maps} *)
(************************************)

module NameOrder =
struct
  type t = name
  let compare = Pervasives.compare
end

module NameMap = Map.Make(NameOrder)

module NameSet = Set.Make(NameOrder)

let unionNameSetList = List.fold_left NameSet.union NameSet.empty

(*************************************)
(* {2: String-indexed Sets and Maps} *)
(*************************************)

module StringOrder =
struct
  type t = string
  let compare = Pervasives.compare
end

module StringMap = Map.Make(StringOrder)

module StringSet = Set.Make(StringOrder)



(********************************************************)
(** {2: Utility functions for the string parts of names *)
(********************************************************)

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


let freshNameString = gensym [("___1", Word)]

let freshModelNameString = gensym [("Z__1", Word)]

(*******************************)
(** {2: Fresh Name Generation} *)
(*******************************)


(** [nextName n] computes a subtitute for name [n], just like
    [nextString] does for strings. *)
let nextBareName = function
    (nm, Word) -> (nextString nm, Word)
  | (_, Wild) -> ("wild", Word)
  | (_, fixity) -> (nextString "op", Word)

let nextName = function
    N(nm, Word) -> N(nextString nm, Word)
  | N(_, Wild) -> N("wild", Word)
  | N(_, fixity) -> N(nextString "op", fixity)
  | G (k, lst) -> gensym lst

(** [freshName' good bad] generates a fresh name. It uses
    one of the names in list [good], possibly adding primes and
    subscripts to it, it avoids names in the list [bad].
*)
let freshName' good bad =
  let rec find g =
    try
      List.find (fun nm -> not (isBareWild nm || StringSet.mem (fst nm) bad)) g
    with Not_found -> find (List.map nextBareName g)
  in
    find good

(** [freshName lst] gensyms a fresh name with hints from [lst]. The hints must
    be words, i.e., not infix operators and such. *)
let freshName good = gensym (List.map (fun s -> (s, Word)) good)

(** [refresh nm] gensyms a fresh name from [nm]. *)
let refresh = function
    N bnm -> gensym [bnm]
  | G (_, lst) -> gensym lst

(** [refreshList lst] refreshes a list of names. *)
let rec refreshList nms = List.map refresh nms

let isForbidden = NameSet.mem

(** [rename lst nm] renames [nm], if necessary, while avoiding names
    in [lst]. *)
let rename bad = function
    N bn -> bn
  | G (_, good) -> freshName' good bad

(** [makeTypename str] computes a valid type name from [str]. *)
let makeTypename = function
  | "<" -> "ty_less"
  | ">" -> "ty_greater"
  | "<=" -> "ty_leq"
  | ">=" -> "ty_geq"
  | "=" -> "ty_equal"
  | "<>" -> "ty_neq"
  | str -> begin
      let names =
	[('!',"_bang"); ('$',"_dollar"); ('%',"_percent");
	 ('&',"_and"); ('*',"_star"); ('+',"_plus");
	 ('-',"_minus"); ('.',"_dot"); ('/',"_slash");
	 (':',"_colon"); ('<',"_less"); ('=',"_equal");
	 ('>',"_greater"); ('?',"_question"); ('@',"_at");
	 ('^',"_carat"); ('|',"_vert"); ('~',"_tilde")] in
      let n = String.length str in
      let rec map i =
	if i < n then (List.assoc str.[i] names) ^ (map (i+1)) else ""
      in
	try "ty" ^ map 0 with Not_found -> failwith "Name.makeTypename: unexpected character"
    end

(*****************************)
(** {2: Name Validity Tests} *)
(*****************************)

(** Theory and term names must be capitalized; all others are
    lowercased or symbolic (infixed) *)

let validTermName = function
    N(str, Word) -> (str = String.uncapitalize str) 
  | N(_,   Wild) -> true
  | _            -> true    (* infixed *)

let validSetName = validTermName

let validPropName = validTermName

let rec validModelName nm =
 let valid (str, fxty) =
   fxty = Wild ||
   fxty = Word && (String.length str > 0 && 'A' <= str.[0] && str.[0] <= 'Z')
 in
   match nm with
       N bn      -> valid bn
     | G(_, lst) -> List.for_all valid lst

let validTheoryName = validModelName

let validSentenceName _ = 
  (* Sentences might translate to terms or functors, so we let the user
     use whatever capitalization they want and fix it later. *)
  (* XXX: Make sure we really do fix this! *)
  true

(***********************)
(** {2: Merging Names} *)
(***********************)

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
      let gensym' lst =
	gensym (List.rev
		  (List.fold_right
		     (fun nm nms ->
			match nm with
			    N bn -> bn :: nms
			  | G (_, ns) -> ns @ nms)
		     lst
		     []))
      in
	match validModelName nm1, validModelName nm2 with
	    true, true   -> gensym' [nm1; nm2]
	  | true, false  -> gensym' [nm1]
	  | false, true  -> gensym' [nm2]
	  | false, false -> freshModelNameString
    end
