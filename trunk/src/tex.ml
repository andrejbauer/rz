(** Convert to TeX/LaTeX expressions *)

open Logic

(** Auxiliary tags *)

let mathrm s = "\\mathrm{" ^ s ^ "}"
let mathsf s = "\\mathsf{" ^ s ^ "}"
let mathtt s = "\\mathtt{" ^ s ^ "}"

let paren s = "(" ^ s ^ ")"

let cparen b s = if b then s else paren s

let greek = function
  | "Alpha" -> "\\Alpha"
  | "Beta" -> "\\Beta"
  | "Delta" -> "\\Delta"
  | "Epsilon" -> "\\Epsilon"
  | "Eta" -> "\\Eta"
  | "Gamma" -> "\\Gamma"
  | "Iota" -> "\\Iota"
  | "Kappa" -> "\\Kappa"
  | "Lambda" -> "\\Lambda"
  | "Mu" -> "\\Mu"
  | "Nu" -> "\\Nu"
  | "Omega" -> "\\Omega"
  | "Phi" -> "\\Phi"
  | "Pi" -> "\\Pi"
  | "Psi" -> "\\Psi"
  | "Rho" -> "\\Rho"
  | "Sigma" -> "\\Sigma"
  | "Tau" -> "\\Tau"
  | "Theta" -> "\\Theta"
  | "Xi" -> "\\Xi"
  | "Zeta" -> "\\Zeta"
  | "alpha" -> "\\alpha"
  | "beta" -> "\\beta"
  | "delta" -> "\\delta"
  | "epsilon" -> "\\epsilon"
  | "eta" -> "\\eta"
  | "gamma" -> "\\gamma"
  | "iota" -> "\\iota"
  | "kappa" -> "\\kappa"
  | "lambda" -> "\\lambda"
  | "mu" -> "\\mu"
  | "nu" -> "\\nu"
  | "omega" -> "\\omega"
  | "phi" -> "\\phi"
  | "pi" -> "\\pi"
  | "psi" -> "\\psi"
  | "rho" -> "\\rho"
  | "sigma" -> "\\sigma"
  | "tau" -> "\\tau"
  | "theta" -> "\\theta"
  | "xi" -> "\\xi"
  | "zeta" -> "\\zeta"
  | _ -> raise Not_found

let name_subscript s =
  try
    let k = String.rindex s '_' in
      String.sub s 0 k, Some (String.sub s (k+1) (String.length s - k - 1))
  with Not_found -> s, None

let name_prime s =
  try
    let k = String.index s '\'' in
      String.sub s 0 k, Some (String.sub s k (String.length s - k))
  with Not_found -> s, None

let tex_of_string wrap1 wrap2 v =
  let v, p = name_prime v in
  let v, s = name_subscript v in
    (if String.length v = 1 then
       wrap1 v
     else
       try greek v with Not_found -> wrap2 v
    ) ^
    (match s with None -> "" | Some u -> "_{" ^ u ^ "}") ^
    (match p with None -> "" | Some u -> u)

let tex_of_name = tex_of_string (fun x -> x) mathrm

let tex_of_names vs = String.concat ", " (List.map tex_of_name vs)

let tex_of_label = tex_of_string mathsf mathsf

let tex_of_basic = tex_of_string mathtt mathtt

let rec tex_of_prop =
  let precedence = begin
    function
	False | True | Atomic (_, _) -> 1000
      | Equal (_, _, _) -> 900
      | Not _ -> 600
      | And (_, _) -> 500
      | Or (_, _) -> 400
      | Imply (_, _) -> 300
      | Iff (_, _) -> 200
      | Forall (_, _, _) -> 100
      | Exists (_, _, _) -> 100
  end
  in
    function
	False -> "\\perp"
      | True -> "\\top"
      | Atomic ((p, _), ts) ->
	  (tex_of_name p) ^ (if ts = [] then "" else "(" ^ (tex_of_terms ts) ^ ")")
      | Equal (_, t, u) ->
	  (tex_of_term t) ^ " = " ^ (tex_of_term u)
      | (Not a) as p ->
	  "\\lnot " ^ (cparen (precedence a >= precedence p) (tex_of_prop a))
      | (And (a, b)) as p ->
	  (cparen (precedence a >= precedence p) (tex_of_prop a)) ^
	  " \\land " ^
	  (cparen (precedence b >= precedence p) (tex_of_prop b))
      | (Or (a, b)) as p ->
	  (cparen (precedence a >= precedence p) (tex_of_prop a)) ^
	  " \\lor " ^
	  (cparen (precedence b >= precedence p) (tex_of_prop b))
      | (Imply (a, b)) as p ->
	  (cparen (precedence a > precedence p) (tex_of_prop a)) ^
	  " \\implies " ^
	  (cparen (precedence b >= precedence p) (tex_of_prop b))
      | (Iff (a, b)) as p ->
	  (cparen (precedence a > precedence p) (tex_of_prop a)) ^
	  " \\iff " ^
	  (cparen (precedence b > precedence p) (tex_of_prop b))
      | (Forall (x, s, a)) as p ->
	  " \\forall " ^ (tex_of_name x) ^ " \\in " ^ (tex_of_set s) ^ ". \\," ^
	  (cparen (precedence a >= 600 || precedence a <= 100) (tex_of_prop a))
      | (Exists (x, s, a)) as p ->
	  " \\exists " ^ (tex_of_name x) ^ " \\in " ^ (tex_of_set s) ^ ". \\," ^
	  (cparen (precedence a >= 600 || precedence a <= 100) (tex_of_prop a))
	  
and tex_of_set =
  let precedence = begin
    function
	Empty
      | Unit
      | Basic _ -> 1000
      | Subset (_, _, _) -> 900
      | RZ _ -> 800
      | Quotient (_, _, _, _) -> 600
      | Product (_, _) -> 500
      | Sum _ -> 400
      | Exp (_, _) -> 300
  end
  in
    function
	Empty -> "\\emptyset"
      | Unit -> "\\mathsf{1}"
      | Basic s -> tex_of_name s
      | Subset (s, x, a) ->
	  "\\{" ^
	  (tex_of_name x) ^ " \\in " ^ (tex_of_set s) ^
	  "\\;|\\;" ^
	  (tex_of_prop a) ^
	  "\\}"
      | RZ s -> "|" ^ (tex_of_set s) ^ "|"
      | (Quotient (s, x, y, a)) as u ->
	  (cparen (precedence s > precedence u) (tex_of_set s)) ^
	  "/_{" ^ (tex_of_name x) ^ "," ^ (tex_of_name y) ^ "}" ^
	  "(" ^ (tex_of_prop a) ^ ")"
      | (Product (s, t)) as u ->
	  (cparen (precedence s >= precedence u) (tex_of_set s)) ^
	  " \\times " ^
	  (cparen (precedence t >= precedence u) (tex_of_set t))
      | (Sum []) -> "\\emptyset"
      | (Sum ss) as u ->
	  String.concat " + " (
	    List.map (fun (l, s) ->
			(tex_of_label l) ^ " : " ^
			(cparen (precedence s > precedence u) (tex_of_set s))
		     ) ss
	  )
      | (Exp (s, t)) as u ->
	  (cparen (precedence s > precedence u) (tex_of_set s)) ^
	  " \\to " ^
	  (cparen (precedence t >= precedence u) (tex_of_set t))

and tex_of_term =
  let precedence = begin
    function
	Var _
      | Star -> 1000
      | Quot _ -> 950
      | App (_, _) -> 900
      | Fst _ -> 900
      | Snd _ -> 900
      | Inj (_, _) -> 900
      | Pair (_, _) -> 800
      | Lambda (_, _, _) -> 700
      | Case _ -> 600
      | Choose (_, _, _) -> 500
      | Let (_, _, _) -> 500
  end
  in
    function
	Var (v, _) -> tex_of_name v
      | Star -> "\\star"
      | Quot t -> "[" ^ (tex_of_term t) ^ "]"
      | App (t, u) as s ->
	  (cparen (precedence t >= precedence s) (tex_of_term t)) ^
	  "\\, " ^
	  (cparen (precedence u > precedence s) (tex_of_term u))
      | (Fst t) as s ->
	  "\\mathsf{fst}\\, " ^
	  (cparen (precedence t > precedence s) (tex_of_term t))
      | (Snd t) as s ->
	  "\\mathsf{snd}\\," ^
	  (cparen (precedence t > precedence s) (tex_of_term t))
      | (Inj  (l, t)) as s ->
	  (tex_of_label l) ^ " \\, " ^
	  (cparen (precedence t > precedence s) (tex_of_term t))
      | (Pair (t, u)) as s ->
	  "\\langle " ^ (cparen (precedence t >= precedence s) (tex_of_term t)) ^
	  ", " ^
	  (cparen (precedence u >= precedence s) (tex_of_term u)) ^
	  "\\rangle"
      | (Lambda (x, s, t)) as u ->
	  "\\lambda " ^ (tex_of_name x) ^ " \\in " ^ (tex_of_set s) ^ " . \\, " ^
	  (cparen (precedence t >= precedence u) (tex_of_term t))
      | (Case (t, cs)) as u ->
	  "\\mathsf{match}\\;" ^ (tex_of_term t) ^ "\\;\\mathsf{with}\\; \\langle\\!| " ^
	  (String.concat " ;\\; "
	     (List.map (fun (l, x, s) ->
			  (tex_of_label l) ^ " \\, " ^ (tex_of_name x) ^ " \\Rightarrow " ^
			  (cparen (precedence s > precedence u) (tex_of_term s))
		       ) cs)
	  ) ^
	  "|\\!\\rangle"
      | (Choose (x, s, t)) as u ->
	  "\\mathsf{let}\\; [" ^ (tex_of_name x) ^ "] = " ^
	  (cparen (precedence s > precedence u) (tex_of_term s)) ^
	  "\\; \\mathsf{in} \\; " ^
	  (cparen (precedence t >= precedence u) (tex_of_term t))
      | (Let (x, s, t)) as u ->
	  "\\mathsf{let}\\; " ^ (tex_of_name x) ^ " = " ^
	  (cparen (precedence s > precedence u) (tex_of_term s)) ^
	  "\\; \\mathsf{in} \\; " ^
	  (cparen (precedence t >= precedence u) (tex_of_term t))

and tex_of_terms ts = String.concat ", " (List.map tex_of_term ts)

let rec tex_of_sort =
  let precedence = begin
    function
	TEmpty
      | TUnit
      | TBasic _ -> 1000
      | TProduct (_, _) -> 800
      | TSum _ -> 700
      | TExp (_, _) -> 600
  end
  in
    function
	TEmpty -> "\\mathtt{0}"
      | TUnit -> "\\mathtt{1}"
      | TBasic b -> tex_of_basic b
      | TProduct (a, b) as s ->
	  (cparen (precedence a >= precedence s) (tex_of_sort a)) ^
	  "\\times " ^
	  (cparen (precedence b >= precedence s) (tex_of_sort b))
      | (TSum ts) as u ->
	  String.concat " + " (
	    List.map (fun (l, s) ->
			(tex_of_string mathtt mathtt l) ^ "\\;\\mathtt{of}\\; " ^
			(cparen (precedence s >= precedence u) (tex_of_sort s))
		     ) ts)
      | TExp (a, b) as s ->
	  (cparen (precedence a >= precedence s) (tex_of_sort a)) ^
	  "\\to " ^
	  (cparen (precedence b >= precedence s) (tex_of_sort b))
