(******************************************************)
(* logic.ml                                           *)
(*                                                    *)
(* Internal representation of theories plus related   *)
(* helper functions.                                  *)
(*                                                    *)
(* We retain infixness information, but all variables *)
(* must be explicitly annotated.                      *)
(******************************************************)

(**************)
(* Exceptions *)
(**************)

exception Unimplemented

exception HOL             (* If the input is trying to do HOL *)

(*******************)
(* Abstract Syntax *)
(*******************)

module S = Syntax

(** labels in sums and model components *)
type label = S.label

(** names of identifiers *)
type name = S.name

(** names of models; must be capitalized *)
type model_name = S.model_name

type model = 
    ModelName of model_name
  | ModelProj of model * model_name
  | ModelApp of model * model

(** names of components inside models *)
type longname = LN of model option * name

(** short names of sets *)
type set_name = S.set_name

(** long names of sets *)
type set_longname = SLN of model option * set_name

(** names of theories *)
type theory_name = S.theory_name

(** sorts of sentences *)
type sentence_type = S.sentence_type

(** a binding in a quantifier or lambda *)
type binding = name * set

(** a binding in a parameterized theory *)
and model_binding = model_name * theory

(** first-order proposition, without accompanying context  *)
and proposition =
    False
  | True
  | Atomic of longname
  | PApp    of proposition * term
  | PLambda of binding * proposition
  | And    of proposition list
  | Imply  of proposition * proposition
  | Iff    of proposition * proposition
  | Or     of proposition list
  | Forall of binding * proposition
  | Exists of binding * proposition
  | Unique of binding * proposition
  | Not    of proposition
  | Equal  of set * term * term


and set =
    Empty
  | Unit  (* Unit is the singleton containing Star *)
  | Bool  (* Bool is isomorphic/equivalent to to Unit+Unit *)
  | Basic    of set_longname
  | Product  of (name option * set) list
  | Exp      of name option * set * set
  | Sum      of (label * set option) list
  | Subset   of binding * proposition
  | Rz       of set (** the set of realizers *)
  | Quotient of set * term
  | SApp     of set * term
  | SLambda  of binding * set

and proptype =
    Prop of S.propKind
  | PExp of name option * set * proptype

and kind =
    KindSet
  | KindProp of S.propKind
  | KindArrow of name * set * kind

and term =
    Star
(** missing terms for type Bool *)
  | Var      of longname
  | Tuple    of term list
  | Proj     of int * term
  | App      of term * term
  | Lambda   of binding  * term
  | The      of binding  * proposition (* description operator *)
  | Inj      of label * term option
  | Case     of term * (label * binding option * term) list
  | RzQuot   of term
  | RzChoose of binding * term * term * set
  | Quot     of term * term
  | Choose   of binding * longname * term * term * set
  | Let      of binding * term * term * set  (* set is type of the whole let *)
  | Subin    of term * set
  | Subout   of term * set

and theory_element =
    Set of set_name * kind
  | Let_set of set_name * set
  | Predicate of name * kind
  | Let_predicate of name * kind * proposition
  | Let_term of name * set * term
  | Value of name * set
  | Sentence of sentence_type * name * model_binding list * binding list * proposition
  | Model of model_name * theory
  | Comment of string

and theory = 
    Theory of theory_element list
  | TheoryName of theory_name
  | TheoryFunctor of model_binding * theory
  | TheoryApp of theory * model
    
and toplevel =
    Theorydef of theory_name * theory
  | TopComment of string
  | TopModel  of model_name * theory


(****************************************)
(* Substitution functions for Logic.xxx *)
(****************************************)

(** The function [substMXXX m mdl] substitutes mode name (string) [m]
    for model [mdl] *)

let rec substMModel m mdl = function
    (ModelName m') as mdl' -> if m = m' then mdl else mdl'
  | ModelProj (mdl', n) -> ModelProj (substMModel m mdl mdl', n)
  | ModelApp (mdl1, mdl2) -> ModelApp (substMModel m mdl mdl1, substMModel m mdl mdl2)
      
and substMLN m mdl = function
    (LN (None, _)) as ln -> ln
  | LN (Some mdl', nm) -> LN (Some (substMModel m mdl mdl'), nm)
      
and substMSLN m mdl = function
    (SLN (None, _)) as ln -> ln
  | SLN (Some mdl', nm) -> SLN (Some (substMModel m mdl mdl'), nm)
      
and substMProp m mdl p =
  let rec subst = function
      False -> False
    | True -> True
    | Atomic lnm -> Atomic (substMLN m mdl lnm)
    | PApp (p,t) -> PApp (subst p, substMTerm m mdl t)
    | PLambda ((n,s),p) -> PLambda ((n, substMSet m mdl s), subst p)
    | And lst -> And (List.map subst lst)
    | Imply (p, q) -> Imply (subst p, subst q)
    | Iff (p, q) -> Iff (subst p, subst q)
    | Or lst -> Or (List.map subst lst)
    | Forall ((n,s),p) -> Forall ((n, substMSet m mdl s), subst p)
    | Exists ((n,s),p) -> Exists ((n, substMSet m mdl s), subst p)
    | Unique ((n,s),p) -> Unique ((n, substMSet m mdl s), subst p)
    | Not p -> Not (subst p)
    | Equal (s, t, u) -> Equal (substMSet m mdl s, substMTerm m mdl t, substMTerm m mdl u)
  in
    subst p

and substMTerm m mdl t =
  let rec subst = function
      Star -> Star
    | Var ln -> Var (substMLN m mdl ln)
    | Tuple lst -> Tuple (List.map subst lst)
    | Proj (i,t) -> Proj (i, subst t)
    | App (t, u) -> App (subst t, subst u)
    | Lambda ((n,s), t) -> Lambda ((n, substMSet m mdl s), subst t)
    | The ((n,s), p) -> The ((n, substMSet m mdl s), substMProp m mdl p)
    | Inj (_, None) as t -> t
    | Inj (lbl, Some t) -> Inj (lbl, Some (subst t))
    | Case (t, lst) -> Case (subst t,
			     List.map (function
					   lbl, None, t -> lbl, None, subst t
					 | lbl, Some (n,s), t -> lbl, Some (n, substMSet m mdl s), subst t)
			       lst)
    | RzQuot t -> RzQuot (subst t)
    | RzChoose ((n,s), t, u, s') ->
	RzChoose ((n, substMSet m mdl s), subst t, subst u, substMSet m mdl s')
    | Quot (t, ln) -> Quot (subst t, substMLN m mdl ln)
    | Choose ((n,s),ln,t,u,s') ->
	Choose ((n, substMSet m mdl s), substMLN m mdl ln, subst t, subst u, substMSet m mdl s')
    | Let ((n,s), t, u, s') -> Let ((n, substMSet m mdl s), subst t, subst u, substMSet m mdl s')
    | Subin (t, s) -> Subin (subst t, substMSet m mdl s)
    | Subout (t, s) -> Subout (subst t, substMSet m mdl s)
  in
    subst t

and substMSet m mdl s =
  let rec subst = function
      Empty -> Empty
    | Unit -> Unit
    | Bool -> Bool
    | Basic ln -> Basic (substMSLN m mdl ln)
    | Product lst -> Product (List.map (fun (n,s) -> (n, subst s)) lst)
    | Exp (n, s, t) -> Exp (n, subst s, subst t)
    | Sum lst -> Sum (List.map
			(function lbl, None -> lbl, None | lbl, Some s -> lbl, Some (subst s))
			lst)
    | Subset ((n,s),p) -> Subset((n, subst s), substMProp m mdl p)
    | Rz s -> Rz (subst s)
    | Quotient (s, ln) -> Quotient (subst s, substMLN m mdl ln)
    | SApp (s, t) -> SApp (subst s, substMTerm m mdl t)
    | SLambda ((n,s), t) -> SLambda ((n, subst s), subst t)
  in
    subst s

(*
  substProp:  name -> term -> proposition -> proposition
  substSet :  name -> term -> set -> set
  subst    :  name -> term -> term -> term

  WARNING:  Not capture-avoiding, so either use this
  only for closed terms or terms with free variables that
  are "fresh".
*)

(* AB: These seem not to be used anywhere?
let rec substProp x t =
  (let rec sub = function
      And ps           -> And  (List.map sub ps)
    | Imply (p1,p2)    -> Imply (sub p1, sub p2)
    | Iff (p1,p2)      -> Iff  (sub p1, sub p2)
    | Or  ps           -> Or   (List.map sub ps)
    | Forall((y,s),p1) -> Forall ((y,substSet x t s), 
				    if (x=y) then p1 else sub p1)
    | Exists((y,s),p1) -> Exists ((y,substSet x t s), 
				    if (x=y) then p1 else sub p1)
    | Not p1           -> Not (sub p1)
    | Equal (s,t1,t2)  -> Equal (substSet x t s, subst x t t1, subst x t t2)
    | t                -> t (* False, True, Atomic n *)
  in sub)

and substSet x t =
     (let rec sub = function
           Product ss       -> Product (List.map sub ss)
         | Exp (s1,s2)      -> Exp (sub s1, sub s2)
         | Sum lss          -> Sum (List.map 
                                      (function (l,sopt) -> (l, subOpt sopt)) 
                                    lss)
         | Subset ((y,s),p) -> Subset ((y,sub s),
				       if (x=y) then p else substProp x t p )
         | Rz s             -> Rz (sub s)
(*         | Quotient(s,u)   -> Quotient(sub s, subst x t u) *)
         | s                    -> s  (* Empty, Unit, Bool, and Basic *)
     and subOpt = function
           None -> None
         | Some s -> Some (sub s)
     in sub)

and subst x t = 
    (let rec sub = function
          Var y             -> if (x=y) then t else Var y
        | Tuple ts          -> Tuple (List.map sub ts)
        | Proj (n,t1)       -> Proj (n, sub t1)
        | App (t1,t2)       -> App (sub t1, sub t2)
        | Inj (l,t1)        -> Inj (l, sub t1)
        | Case (t1,arms)    -> Case (t1, subarms arms)
        | Let ((y,s),t1,t2,s2) -> Let((y,substSet x t s),
                                      sub t1, 
				      if (x=y) then t2 else sub t2,
                                      substSet x t s2)
(*
        | Choose((y,s),t1,t2) ->
            Choose((y,substSet x t s),
                     sub t1, 
                     if (x=y) then t2 else sub t2)
*)
        | Star          -> Star

     and subarms = function
          [] -> []
        | (l,Some (y,s),u)::rest ->
              (l, Some (y,substSet x t s),
               if (x=y) then u else sub u ) :: (subarms rest)
        | (l,None,u)::rest ->
              (l, None, sub u) :: (subarms rest)
     in sub)
*)

let string_of_name = S.string_of_name

let rec string_of_model = function
    ModelName strng -> strng
  | ModelApp (mdl1, mdl2) ->
      string_of_model mdl1 ^ "(" ^ string_of_model mdl2 ^ ")"
  | ModelProj (mdl, lbl) -> string_of_model mdl ^ "." ^ lbl

let rec string_of_ln = function
    LN (None, nm) -> string_of_name nm
  | LN (Some mdl, nm) -> (string_of_model mdl) ^ "."  ^ (string_of_name nm)

let rec string_of_sln = function
    SLN (None, nm) -> nm
  | SLN (Some mdl, nm) -> (string_of_model mdl) ^ "."  ^ nm

let rec string_of_set = function
    Empty -> "empty"
  | Unit -> "unit"
  | Bool -> "bool"
  | Basic lname -> string_of_sln lname
  | Product lst ->
      "(" ^ (String.concat " * "
	       (List.map (
		  function
		      (None, s) -> string_of_set s
		    | (Some nm, s) -> string_of_name nm ^ " : " ^ string_of_set s) lst)) ^ ")"
  | Exp (None, s, t) -> "(" ^ (string_of_set s) ^ " -> " ^ (string_of_set t) ^ ")"
  | Exp (Some nm, s, t) ->
      "((" ^ string_of_name nm ^ " : " ^ (string_of_set s) ^ ") -> " ^ (string_of_set t) ^ ")"
  | Sum lst ->
      "[" ^ (
	String.concat " + " (
	  List.map (function
			lb, None -> lb
		      | lb, Some s -> lb ^ " of " ^ (string_of_set s)
	  ) lst)
      ) ^ "]"

  | Subset _ -> "{... with ...}"
  | Rz s -> "rz " ^ (string_of_set s)
  | Quotient (s, n) -> (string_of_set s) ^ " % " ^ (string_of_ln n)
  | SApp (s, t) -> (string_of_set s) ^ " " ^ (string_of_term t)
  | SLambda ((n,s), t) -> "lam " ^ string_of_name n ^ " : " ^ string_of_set s ^ " . " ^ string_of_set t

and string_of_term t = "<term>"

(** *** *)

let rename = function
  | "<" -> "_less"
  | ">" -> "_greater"
  | "<=" -> "_leq"
  | ">=" -> "_geq"
  | "=" -> "_equal"
  | "<>" -> "_neq"
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
	try map 0 with Not_found -> failwith "Logic.rename: unexpected character"
    end

let typename_of_name = function
    Syntax.N(n, Syntax.Word) -> n
  | Syntax.N(str, _) -> rename str

let typename_of_ln = function
    LN (_, S.N(_, S.Word)) as n -> n
  | LN (mdl, S.N(p, _)) -> LN (mdl, S.N(rename p, S.Word))

let sln_of_ln (LN (mdl, nm)) = SLN (mdl, typename_of_name nm)


(************************************)
(* Translation from Syntax to Logic *)
(************************************)

(* make_set           : S.set -> Logic.set
   make_bindings      : S.binding list -> Logic.binding list
   make_proposition   : S.term -> Logic.proposition
   make_term          : S.term -> Logic.term
   make_theoryelement : S.theory_element -> Logic.theory_element
   make_theoryspec    : S.theoryspec -> Logic.theory
   make_theory        : S.theory -> Logic.theory_element list
*)

let rec make_set = function
    S.Empty -> Empty
  | S.Unit -> Unit
  | S.Bool -> Bool
  | S.Set_name (mdl, nm) -> Basic (SLN (make_model_opt mdl, nm))
  | S.Product lst -> Product (List.map (fun (n,s) -> (n, make_set s)) lst)
  | S.Sum lst -> Sum (List.map
			(function (lb, None) -> (lb, None) 
                                | (lb, Some s) -> (lb, Some (make_set s)))
                      lst)
  | S.Exp (nm, s, t) -> Exp (nm, make_set s, make_set t)
  | S.Subset ((n, Some s), phi) -> Subset ((n, make_set s), make_proposition phi)
  | S.Subset ((_, None), _) ->
      print_string "(ERROR: subset without type annotation\n";
      failwith "Logic.make_set"
  | S.Quotient (s, S.Var(mdl,nm)) ->
      Quotient (make_set s, LN(make_model_opt mdl,nm))
  | S.Quotient _ ->
      print_string ("ERROR: Quotient type by anonymous relation\n") ;
      failwith "Logic.make_set"
  | S.Rz s -> Rz (make_set s)
  | S.SetLambda ((_, None), _) ->
      print_string ("ERROR: set lambda without binding");
      failwith "Logic.make_set"
  | S.SetLambda ((n, Some s), t) -> SLambda ((n, make_set s), make_set t)
  | S.SetApp (s, t) -> SApp (make_set s, make_term t)
  | S.Set -> print_string ("ERROR: logic encountered Set"); failwith "Logic.make_set"
  | S.Prop -> print_string ("ERROR: logic encountered Prop"); failwith "Logic.make_set"
  | S.EquivProp -> print_string ("ERROR: logic encountered Equiv"); failwith "Logic.make_set"
  | S.StableProp -> print_string ("ERROR: logic encountered Stable"); failwith "Logic.make_set"

(* Assumes that we have already done Type Inference
   or that the user has specified sets for all variables
 *)
and make_bindings b =
  List.map (function
		(n, Some s) -> (n, make_set s)
	      | (_, None) -> failwith "Logic.make_bindings: annotation expected"
	   ) b

and make_proposition = function
    S.False -> False
  | S.True -> True
  | S.App (p, t) -> PApp (make_proposition p, make_term t)
  | S.Lambda ((n, Some s), p) -> PLambda ((n, make_set s), make_proposition p)
  | S.Lambda ((_, None), _) ->
      print_string "Lambda missing type annotation\n";
      failwith "Logic.make_proposition"
  | S.And lst -> And (List.map make_proposition lst)
  | S.Imply (phi, psi) -> Imply (make_proposition phi, make_proposition psi)
  | S.Iff (phi, psi) -> Iff (make_proposition phi, make_proposition psi)
  | S.Or lst -> Or (List.map make_proposition lst)
  | S.Not phi -> Not (make_proposition phi)
  | S.Equal (Some s, u, v) -> Equal (make_set s, make_term u, make_term v)
  | S.Equal (None, _, v) -> (print_string "Equality missing type annotation\n";
                             raise Unimplemented)
  | S.Forall ((n, Some s), phi) -> Forall ((n, make_set s), make_proposition phi)
  | S.Forall ((_, None), _) -> 
                            (print_string "Forall missing type annotation\n";
                            raise Unimplemented)
  | S.Exists ((n, Some s), phi) -> 
                            Exists ((n, make_set s), make_proposition phi)
  | S.Exists ((_, None), _) -> 
                            (print_string "Exists missing type annotation\n";
                            raise Unimplemented)
  | S.Unique ((n, Some s), phi) -> 
                            Unique ((n, make_set s), make_proposition phi)
  | S.Unique ((_, None), _) -> 
                            (print_string "Exists missing type annotation\n";
                            raise Unimplemented)
  | S.The _ | S.Let _ | S.Subout _ | S.Subin _ | S.RzChoose _
  | S.RzQuot _ | S.Choose _ | S.Quot _ | S.Case _ | S.Inj _
  | S.Proj _ | S.Tuple _ | S.Constraint _ | S.Var _ | S.Star ->
      (print_string "Not a proposition\n"; failwith "Logic.make_proposition")
(*  | _ -> (print_string "unrecognized proposition\n";
	  raise HOL)
*)

and make_term = function
    S.Var (mdl,n) -> Var(LN(make_model_opt mdl, n))
  | S.Constraint (t, _) -> make_term t
  | S.Star -> Star
  | S.Tuple lst -> Tuple (List.map make_term lst)
  | S.Proj (k, t) -> Proj (k, make_term t)
  | S.App (t, u) -> App (make_term t, make_term u)
  | S.Inj (lb, Some t) -> Inj (lb, Some (make_term t))
  | S.Inj (lb, None) -> Inj (lb, None)
  | S.Case (t, lst) ->
      Case (make_term t, List.map
	      (function
		   (lb, Some (n, Some s), u) -> (lb, Some (n, make_set s), make_term u)
		 | (_, Some (_, None), _) ->
		     print_string "Missing type annotation in case\n";
		     failwith "Logic.make_term"
		 | (lb, None, u) -> (lb, None, make_term u))
	      lst)
  | S.Lambda ((n, Some s), t) -> Lambda ((n, make_set s), make_term t)
  | S.The ((n, Some s), t) -> The ((n, make_set s), make_proposition t)
  | S.Subin (t, s) -> Subin (make_term t, make_set s)
  | S.Subout (t, s) -> Subout (make_term t, make_set s)
  | S.Quot (t, S.Var(mdl,r)) -> Quot (make_term t, LN(make_model_opt mdl,r))
  | S.Quot _ ->
      print_string "cannot form quotients by anonymous relations\n";
      failwith "Logic.make_term"
  | S.RzQuot t -> RzQuot (make_term t)
  | S.RzChoose ((n, Some s), t, u, Some st) ->
      RzChoose ((n, make_set s), make_term t, make_term u, make_set st)
  | S.Choose ((n, Some s), S.Var(mdl,nm), t, u, Some st) ->
      Choose ((n, make_set s), LN(make_model_opt mdl,nm),
	      make_term t, make_term u, make_set st)
  | S.Let ((nm, Some st1), trm1, trm2, Some st2) -> 
      Let((nm, make_set st1), make_term trm1, make_term trm2,
	  make_set st2)
  | trm -> (print_string "unrecognized term: ";
	    print_string (S.string_of_term trm);
	  raise HOL)

and make_kind = function
  | S.Prop -> KindProp S.Unstable
  | S.StableProp -> KindProp S.Stable
  | S.EquivProp -> KindProp S.Equivalence
  | S.Set -> KindSet
  | S.SetLambda ((n, Some s), knd) -> KindArrow (n, make_set s, make_kind knd)
  | S.SetLambda ((_, None), _) -> (print_string "SetLambda without type annotation.\n";
				   failwith "Logic.make_kind")
  | _ -> (print_string "Not a kind.\n"; failwith "Logic.make_kind")

and make_theory_element = function
    S.Abstract_set (n, s)-> Set (n, make_kind s)
  | S.Let_set (n, t) -> Let_set (n, make_set t)
  | S.Predicate (n, stab, knd) -> Predicate (n, make_kind knd)
  | S.Let_predicate ((n, Some knd), _, p) -> Let_predicate (n, make_kind knd, make_proposition p)
  | S.Let_predicate ((_, None), _, _) ->
      print_string "Let_predicate without type annotation.\n";
      failwith "Logic.make_theory_element"
  | S.Let_term ((n, Some s), t) -> Let_term (n, make_set s, make_term t)
  | S.Let_term ((_, None), t) -> (print_string "Let_term without ty ann.\n";
                                  raise Unimplemented)
  | S.Sentence (st, n, mb, b, t) ->
      Sentence (st, n, make_model_bindings mb, make_bindings b, make_proposition t)
  | S.Value (n, s) -> Value (n, make_set s)
  | S.Model (str, thr) -> Model(str, make_theory thr)
  | S.Comment cmmnt -> Comment cmmnt
  | S.Implicit _ ->
      print_string "Logic encountered Implicit";
      failwith "Logic.make_theory_element"
  | S.Variable _ ->
      print_string "Logic encountered Variable";
      failwith "Logic.make_theory_element"

and make_theory = function
    S.Theory elems -> Theory (List.map make_theory_element elems)
  | S.TheoryName id -> TheoryName id
  | S.TheoryFunctor ((m,thr1),thr2) -> TheoryFunctor((m, make_theory thr1), make_theory thr2)
  | S.TheoryApp (thy, mdl) -> TheoryApp (make_theory thy, make_model mdl)

and make_toplevel = function
    S.Theorydef(str, thr) -> Theorydef (str, make_theory thr)
  | S.TopComment cmmnt -> TopComment cmmnt
  | S.TopModel (mdlnm, thry) -> TopModel(mdlnm, make_theory thry)

and make_model = function
    S.ModelName mdl -> ModelName mdl
  | S.ModelProj (mdl, lbl) -> ModelProj (make_model mdl, lbl)
  | S.ModelApp (mdl1, mdl2) -> ModelApp (make_model mdl1, make_model mdl2)

and make_model_opt = function
    None -> None
  | Some mdl -> Some (make_model mdl)

and make_model_bindings bnd = List.map (fun (m,th) -> (m, make_theory th)) bnd
