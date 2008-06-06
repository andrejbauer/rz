open Name
open Outsyn


(* If we ever let obligations appear in *types*, this will have
   to be modified! *)

(*****************)
(** {2 Hoisting} *)
(*****************)

(* The hoist functions are intended to be run on optimized code *)

let rec listminus lst1 lst2 =
  match lst1 with
      [] -> []
    | x::xs ->
        if (List.mem x lst2) || (List.mem x xs) then 
          listminus xs lst2
        else 
          x :: (listminus xs lst2)

(* The next two functions are used in reduce, but we need to pull them
   out of the (very large) mutually-recursive nest so that they can be
   used polymorphically.
*)
type 'a pattern_match =
    Yes of 'a | Maybe | No

let rec pmatch (fLet : pattern * term * 'a -> 'a) matchee pat (trm:'a) = 
  match matchee, pat with 
    (_, WildPat) ->
      Yes (fLet(WildPat, matchee, trm))
  | (_, VarPat nm) ->
      Yes (fLet(VarPat nm, matchee, trm))
  | (Tuple matchees, TuplePat pats ) -> 
      pmatches fLet matchees pats trm
  | (Inj(lbl1,None, _), ConstrPat(lbl2,None)) when lbl1 = lbl2 ->
      Yes trm
  | (Inj(lbl1,Some trm1, _), ConstrPat(lbl2, Some(nm2,_))) when lbl1 = lbl2 ->
      Yes (fLet(VarPat nm2,trm1, trm))
  | (Inj _, ConstrPat _) -> No
  | _                    -> Maybe

and pmatches fLet matchees pats trm =
  match matchees, pats with
    [], [] -> Yes trm
  | m::ms, p::ps ->
      begin
        match pmatches fLet ms ps trm with
          No       -> No
        | Maybe    -> 
	    begin
	      match pmatch fLet m p trm with
		| No -> No
		| _ -> Maybe
	    end 
        | Yes trm' -> pmatch fLet m p trm' 
      end
  | _, _ -> failwith "Outsyn.pmatches"

(*
   Subtleties in hosting obligations.
   ----------------------------------

   Suppose we have the proposition "prp1 /\ prp2" where
   
      (obs1, prp1') = hoistProp prp1
      (obs2, prp2') = hoistProp prp2

   That is, obs1 contains all the obligations in prp1, and prp1' contains
   whatever's left over, and then similarly for obs2 and prp2'.
   
   The "naive" result would then be
      (obs1 @ obs2,  prp1' /\ prp2')

   But this doesn't quite work:
   (1) hoisting obs1 above prp2' might capture free variables
       in obs2 and in prp2'
   (2) hoisting obs2 above prp1' might capture free variables 
       in prp1', including those bound in obs1.

  Now, if the original code contained no shadowing, then some of
  these possibilities might be impossible.  But, hoisting naturally
  creates shadowing:

  (3) bound variables in prp2' might shadow bound variables in obs1
  (4) bound variables in prp1' might shadow bound variables in obs2

  This isn't an issue of correctness; it just breaks any obvious
  no-shadowing invariant we might hope to maintain.  

  In general, there's no easy way to avoid creating shadowing, at
  least if hoisting is a one-pass algorithm; you don't know where to
  alpha-vary prp2' (or obs1) until both have been computed, and
  similarly you don't know where to alpha-vary prp1' (or obs2) until
  both of these have been computed.

  [Well, you could alpha-vary everything as you go along, trying to
  make every bound variable in the entire program distinct, or
  maintain this as an invariant, but that's bad for readability,
  and such an invariant would be very difficult to maintain correctly.]

  [Actually it's possible that this shadowing, where the other variable
  is always an obligation, might not be an issue.  But since it's not
  100% sure that translate doesn't generate shadowing, we might as
  well make the code work even if there is shadowing in the input.]


  So, we need to rename bound variables in obs1 so that they are
  different from the free variables of obs2 and of prp2', and to
  rename prp1' appropriately.

  And, we need to rename bound variables in obs2 so that they are
  different from the free variables of the (renamed!) obs1' and
  of the (renamed) prp1', and then to rename prp2' appropriately.


  In general, if you have obs_1 ... obs_n and prp_1 ... prp_n, for k
  in 1..n you need to rename the bound variables in obs_k so that they
  are different from the free variables in obs_(k+1), ..., obs_n and
  in all the propositions *except* prp_k, and to rename these bound
  variables in prp_k appropriately. [But see below.]

  --------------
  
  A useful refinement is to merge duplicates hoisted out of different
  subexpressions of the same expression, since these frequently occur
  at the moment.  For now, we only merge *syntactically identical*
  obligations.  A further refinement would be to merge
  alpha-equivalent obligations, e.g.

  assure x:nat. x<>0 in assure y:nat. y<>0 in ...

  but I'll wait until this case actually occurs in practice.

  The rule above won't give quite the right result, though, since
  if we're merging
      assure x:nat ... in trm1
  with  
      assure x:nat ... in trm2
  then we *don't* want to rename the first x, even though it's
  free in trm2.  So, we only want to look for free variables in 
  trm2 that do not correspond to an eliminated-duplicate assurance.


  Eliminating duplicates also gets a little tricky if a single list 
  contains multiple bindings for the same name.  E.g., if we have :
     assure x:nat...  
  in the first list and
     assure x:bool ... in assure x:nat ...
  we cannot eliminate the x:nat because then the x:bool will
  shadow the x:nat in the merged list, which may capture
  uses of x (from the first expression) expecting x to be a nat.

  THEREFORE, we maintain the following invariant:
     No list of obligations may bind the same variable more than once.

  Then the general renaming strategy changes to: 

  If you have obs_1 ... obs_n and prp_1 ... prp_n, for k in 1..n you
  need to rename the bound variables in obs_k so that they are
  different from the free variables in obs_(k+1), ..., obs_n, and
  different from the free variables in every proposition prp_i *except*
  prp_k (once you've removed those free variables from each corresponding to
  eliminated obligations in obs_i), and different from the bound
  variables in obs_(k+1), ..., obs_n;  then to rename these bound
  variables in prp_k appropriately.
*)


(* Compute the free variables in a list of obligations.
   Resulting list might have duplicates. *)
let rec fvObs = function
    [] -> []
  | (bnds,prp) :: rest ->
      (fvProp prp) @ (listminus (fvObs rest) (List.map fst bnds))

let bvObs obs =
  List.flatten (List.map (fun (bnds,_) -> List.map fst bnds) obs)


(* Rename a list of obligations, given bound variable names to avoid
   using, and an initial (renaming) substitution.

   Returns the list of renamed obligations, and a (renaming)
   substitution mapping from old obligation names to new ones. *)
let rec renameObs bad subst = function
    []                    -> ([], subst)
  | (bnds,prp) :: rest ->
      let (subst', bnds') = renameBnds ~bad:bad subst bnds
      in let prp' = substProp subst' prp
      in let (rest', subst'') = renameObs bad subst' rest
      in ( (bnds',prp') :: rest', subst'')
        
let rec printObs = function
    [] -> ()
  | (bnd,p)::rest -> print_endline (string_of_term (Obligation(bnd,p,EmptyTuple))); printObs rest

  
(* Returns set difference, but also returns the names of the 
   bound variables that were removed *)

(* 
   Precondition: obs1 doesn't contain 2 obligations with the same name;
     same for obs2.
*)
let rec obsListminus obs1 obs2 =
  match obs1 with
      [] -> ([], [])
    | ((bnds,_) as ob)::obs ->
        let (ns, obs') = obsListminus obs obs2
        in if (List.mem ob obs2) then
            ((List.map fst bnds) @ ns, obs')
          else 
            (ns, ob::obs')


let merge2Obs' ?bad fvFun1 fvFun2 substFn1 substFn2 obs1 obs2 x1 x2 = 
(*  let _ = print_endline "Obs1"; printObs obs1
  in let _ = print_endline "Obs2"; printObs obs2 in *)

  let bad' = match bad with None -> [] | Some nms -> nms

  (* Delete exact duplicates.
     Correctness relies on the invariant that obs1 and obs2 never
     bind the same variable twice. *)
  in let (deletedNames2, obs2) = obsListminus obs2 obs1

(*  in let _ = print_endline "Obs2'"; printObs obs2  *)

  (* Get the bound variables in an obligation list *)
  in let nms2 = bvObs obs2

  in let (obs1', subst1) = 
    renameObs ((listminus (fvFun2 x2) deletedNames2) @ 
                  (fvObs obs2) @ nms2 @ bad') 
      emptysubst obs1
  in let x1' = substFn1 subst1 x1
  
  in let (obs2', subst2) = 
    renameObs (fvFun1 x1') emptysubst obs2
  in let x2' = substFn2 subst2 x2

(*  in let _ = print_endline "Obs'"; printObs obs' *)

  in (obs1', obs2', x1', x2')

let merge2Obs ?bad fvFun1 fvFun2 substFn1 substFn2 obs1 obs2 x1 x2 = 
  let (obs1', obs2', x1', x2') = 
    merge2Obs' ?bad fvFun1 fvFun2 substFn1 substFn2 obs1 obs2 x1 x2 
  in let obs' = obs1' @ obs2'
  in 
    (obs', x1', x2')

let merge3Obs fvFun1 fvFun2 fvFun3 substFn1 substFn2 substFn3 
              obs1 obs2 obs3 x1 x2 x3 = 
  let (obs12, x1', x2') = 
    merge2Obs fvFun1 fvFun2 substFn1 substFn2 obs1 obs2 x1 x2
  in let fvFun12(a,b) = fvFun1 a @ fvFun1 b
  in let substFn12 sbst (a,b) = (substFn1 sbst a, substFn2 sbst b)
  in let (obs', (x1'',x2''), x3') = 
    merge2Obs fvFun12 fvFun3 substFn12 substFn3 obs12 obs3 (x1',x2') x3
  in 
       (obs', x1'', x2'', x3')


let merge2ObsTerm ?bad obs1 obs2 trm1 trm2 = 
  merge2Obs ?bad fvTerm fvTerm substTerm substTerm obs1 obs2 trm1 trm2

let merge2ObsTermTerms obs1 obs2 trm trms =
  match (merge2ObsTerm obs1 obs2 trm (Tuple trms)) with
      (obs', trm', Tuple trms') -> (obs', trm', trms')
    | _ -> failwith "Obj.merge2ObsTermTerms: impossible"

let merge2ObsProp = merge2Obs fvProp fvProp substProp substProp

let merge2ObsPropProps obs1 obs2 prp prps =
  match (merge2ObsProp obs1 obs2 prp (And prps)) with
      (obs', prp', And prps') -> (obs', prp', prps')
    | _ -> failwith "Obj.merge2ObsPropProps: impossible"

let merge2ObsTermProp ?bad obs1 obs2 trm prp =
  merge2Obs ?bad fvTerm fvProp substTerm substProp obs1 obs2 trm prp


let merge2ObsPropModest =  merge2Obs fvProp fvModest substProp substModest

let hoistList hoistFn fvFn substFn =
   let rec nodups = function
       [] -> []
     | x::xs -> 
         let z = nodups xs
         in if (List.mem x z) then z else x::z
   in let fvsFn xs = nodups (List.flatten (List.map fvFn xs))
   in let substsFn sbst xs = List.map (substFn sbst) xs
   in let rec loop = function
      [] -> ([], [])
    | x::xs -> 
       let (obs1, x') = hoistFn x
       in let (obs2, xs') = loop xs
       in let (obs', x'', xs'') = 
         merge2Obs fvFn fvsFn substFn substsFn obs1 obs2 x' xs'
       in (obs', x''::xs'')
    in loop

let rec hoist trm =
  match trm with
      Id _ 
    | EmptyTuple 
    | BConst _
    | Dagger 
    | Inj(_, None, _) -> ([], trm)

    | App(trm1, trm2) ->
        let    (obs1,trm1') = hoist trm1
        in let (obs2, trm2') = hoist trm2
        in let (obs', trm1'', trm2'') = merge2ObsTerm obs1 obs2 trm1' trm2'
        in (obs', reduce (App(trm1'',trm2'')) )

    | BNot trm ->
        let (obs, trm') = hoist trm in
        (obs, reduce (BNot trm'))
        
    | BOp(bop, trms) ->
        let (obs, trms') = hoistTerms trms in
        (obs, reduce (BOp(bop,trms')))

    | Lambda((nm,ty),trm) ->
        let (obs1, trm1') = hoist trm
        in let obs1' = List.map (quantifyOb nm ty) obs1
        in (obs1', Lambda((nm,ty), trm1'))

    | Tuple trms ->
        let (obs, trms') = hoistTerms trms
        in (obs, Tuple trms')

    | Proj(n, trm) ->
        let (obs, trm') = hoist trm
        in (obs, reduce (Proj(n,trm')))

    | Inj(lbl, Some trm, ty) ->
        let (obs, trm') = hoist trm
        in (obs, Inj(lbl, Some trm', ty))

    | PolyInst(trm, tys) ->
        let (obs, trm') = hoist trm
        in (obs, PolyInst(trm', tys))

    | Case(trm,arms) ->
        let (obs1, trm') = hoist trm
        in let (obs2, arms') = hoistCaseArms arms
        in let (obs', trm'', arms'') = 
           merge2Obs fvTerm fvCaseArms substTerm substCaseArms
             obs1 obs2 trm' arms'
        in (obs', Case(trm'', arms''))

    | Let(pat, trm1, trm2) ->
        (* See comments for PLet *)

        let (obs1, trm1') = hoist trm1
        in let (preobs2, trm2') = hoist trm2

        in let (obs1', preobs2', trm1'', trm2'') = 
          merge2Obs' ~bad:(bvPat pat) fvTerm fvTerm substTerm substTerm
             obs1 preobs2 trm1' trm2'

        in let addPremise (bnds,prp) =
          (bnds, reduceProp (PLet(pat, trm1'', prp)))
        in let obs2' = List.map addPremise preobs2'

        in let obs' = obs1' @ obs2'

        in (obs', reduce (Let(pat, trm1'', trm2'')))

(*

  Turned off for now; pulling obligations out of prp extends their scope,
  which leads to more renaming without any obviously-big gains

    | Obligation([], prp, trm) ->
        let (obs1a, prp') = hoistProp prp
        in let obs1b = [([], prp')] 
        in let obs1 = obs1a @ obs1b
        in let (obs2, trm') = hoist trm
        in let (obs', _, trm'') = 
          (* We need to merge the obligations, and rename obs1 propositions
             so that they don't capture any free variables of trm' *)
          (* EmptyTuple stands for anything without free variables *)
          merge2ObsTerm obs1 obs2 EmptyTuple trm'
        in (obs', trm'')
*)

    | Obligation(bnds, prp, trm) ->
        (** What should be the result of hoisting
               assure x:s . (assure y:t. phi(x,y) in psi(x,y)) in trm ?
            It's not entirely clear; perhaps
               assure z:s*t. (phi(z.0,z.1) /\ psi(z.0,z.1)) in trm
            But for our purposes it doesn't really matter; we can just
            pull off
               ((x,s), assure y:t.phi(x,y) in psi(x,y)) 
            as a single assurance; the really important invariant is that
            the residue trm' of trm contains no assurances, *not* that
            all assurances are at top level.
         *)
        (* But, to get a little closer to the assurances-at-top-level
           idea, and in case we can do some duplicate-assurance elimination,
           we'll at least move assurances to the top of prp.
         *)
        let (obsp, prp') = hoistProp prp
        in let obs1 = [(bnds, foldPObligation obsp prp')]
        in let (obs2, trm') = hoist trm
        (* It's ok to use @ rather than a merge function here;
        obs2 was already in the scope of obs1, and trm' was
        already in the scope of both. *)
        in (obs1 @ obs2, trm') 

and hoistTerms trms = hoistList hoist fvTerm substTerm trms

and hoistProps prps = hoistList hoistProp fvProp substProp prps

and hoistPCaseArms arms = hoistList hoistPCaseArm fvPCaseArm substPCaseArm arms

and hoistCaseArms arms = hoistList hoistCaseArm fvCaseArm substCaseArm arms

and hoistPCaseArm (pat, prp) =
  let (obs,prp') = hoistProp prp
  in let obs' = List.map (quantifyObPat pat) obs
  in (obs', (pat, prp'))

and hoistCaseArm (pat, trm) =
  let (obs,trm') = hoist trm
  in let obs' = List.map (quantifyObPat pat) obs
  in (obs', (pat, trm'))

(* Fortunately, terms cannot appear in types, so we only have
   to universally quantify the proposition parts of the
   obligations *)
and quantifyOb nm ty (bnd, prp) = (bnd, Forall((nm,ty), prp))

and quantifyObTotal nm sty (bnd, prp) = (bnd, ForallSupport((nm,sty), prp))

and quantifyObPat pat (ob : binding list * proposition) =
  match pat with
    WildPat -> ob
  | VarPat _ -> failwith "quantifyObPat: can't infer variable's type"
  | TuplePat pats -> quantifyObPats pats ob
  | ConstrPat(_,None) -> ob
  | ConstrPat(_,Some(nm,ty)) -> quantifyOb nm ty ob
  
and premiseOb hyp (bnd, prp) = (bnd, Imply(hyp, prp))
  
and quantifyObPats pats ob = 
  List.fold_right quantifyObPat pats ob

and hoistProp orig_prp =
  let (obs, prp') = 
    match orig_prp with
        True
      | False -> ([], orig_prp)
          
      | SimpleSupport _ | SimplePer _ -> ([], orig_prp)
          (* XXX this ain't gonna work if simple types contain variables. *)

      | BasicProp _ -> ([], orig_prp)
      
      | PBool trm ->
          let (obs, trm') = hoist trm in
          (obs, PBool trm')
            
      | Equal(trm1, trm2) ->
          let (obs1, trm1') = hoist trm1
          in let (obs2, trm2') = hoist trm2
          in let (obs', trm1'', trm2'') = merge2ObsTerm obs1 obs2 trm1' trm2'
          in (obs', Equal(trm1'', trm2''))
            
      | And prps ->
          let (obs, prps') = hoistProps prps
          in (obs, And prps')
            
      | Imply(prp1, prp2) ->
          let (obs1, prp1') = hoistProp prp1
          in let (obs2, prp2') = hoistProp prp2
      in let obs2' = List.map (premiseOb prp1') obs2
          in let (obs', prp1'', prp2'') = merge2ObsProp obs1 obs2' prp1' prp2'
          in (obs', Imply(prp1'', prp2''))
            
      | Iff(prp1, prp2) ->
          let (obs1, prp1') = hoistProp prp1
          in let (obs2, prp2') = hoistProp prp2
          in let (obs', prp1'', prp2'') = merge2ObsProp obs1 obs2 prp1' prp2'
          in (obs', Iff(prp1'', prp2''))
            
      | Not prp ->
          let (obs, prp') = hoistProp prp
          in (obs, Not prp')
            
      | Forall((nm,ty),prp) ->
          let (obs, prp') = hoistProp prp
          in let obs' = List.map (quantifyOb nm ty) obs
          in (obs', Forall((nm,ty), prp') )
            
      | ForallSupport((nm,sty),prp) ->
          let (obs, prp') = hoistProp prp
          in let obs' = List.map (quantifyObTotal nm sty) obs
          in (obs', ForallSupport((nm,sty), prp') )
            
      | PLambda((nm,ty), prp) ->
          let (obs, prp') = hoistProp prp
          in let obs' = List.map (quantifyOb nm ty) obs
          in (obs', PLambda((nm,ty), prp') )
            
      | PApp(prp, trm) ->
          let (obs1, prp') = hoistProp prp
          in let (obs2, trm') = hoist trm
          in let (obs', prp'', trm'') = 
            merge2Obs fvProp fvTerm substProp substTerm obs1 obs2 prp' trm'
          in (obs', PApp(prp'', trm''))
            
      | PCase(trm, arms) -> 
          let (obs1, trm') = hoist trm
          in let (obs2, arms') = hoistPCaseArms arms
          in let (obs', trm'', arms'') =
            merge2Obs fvTerm fvPCaseArms substTerm substPCaseArms
              obs1 obs2 trm' arms'
          in (obs', PCase(trm'', arms''))
            
      | PObligation(bnd, prp1, prp2) ->
          (* For justification of this code, see the comments for 
             the Obligation case of the hoist function. *)
          let (obsp, prp1') = hoistProp prp1
          in let obs1 = [(bnd, foldPObligation obsp prp1')]
        in let (obs2, prp2') = hoistProp prp2
        in (obs1 @ obs2, prp2') 
          
    | PLet(pat, trm, prp) ->
        (* BEFORE (assuming only assure is in body):
           let nm = (assure m:t.q(m) in trm(m)) 
                in (assure n:t.p(n,nm) in prp(n,nm))
           
           AFTER:
           assure m':t. q(m')
           assure n':t. let nm = trm'(m'[!]) in p(n',nm)
           &
           let nm = trm'(m') in prp(n',nm)
           
        *)
        
        let (obs1, trm') = hoist trm
        in let (preobs2, prp') = hoistProp prp
          
        in let (obs1', preobs2', trm'', prp'') = 
          merge2Obs' ~bad:(bvPat pat) fvTerm fvProp substTerm substProp
             obs1 preobs2 trm' prp'

        (* Normally we'd call addPremise before merging the
           obligations, but there's a glitch.  
            (1) We'd rather wrap the obligations in preobs2 with
                  the definition nm = trm' instead of nm = trm
                  (i.e., not duplicate the obligations in trm)

            (2) But trm' refers to variables bound in obs1.
 
                If we wrap the definition nm = trm' around preobs2
                  to get obs2, then the bound variables in obs1 that 
                  are free in trm' would be free in obs2, and then the
                  merge function would alpha-vary the bound variables
                  in obs1 to avoid capture.  At the very least this
                  is unnecessary renaming, and it's actually going to
                  be wrong --- the occurrences of trm' in the
                  wrappers won't be renamed to match.

            (3) So, we first merge the bindings, get trm''
                  (which reflects any renamings in obs1) and 
                  only then wrap preobs2.
        *)
        in let addPremise (bnds,p) =
          (bnds, reduceProp (PLet(pat, trm'', p)))
        in let obs2' = List.map addPremise preobs2'

        in let obs' = obs1' @ obs2'

        in (obs', reduceProp (PLet(pat, trm'', prp'')))   in

  let ans =
    if (!(Flags.do_fullhoist)) then
      (obs, prp')
    else
      ([], foldPObligation obs prp')
	
  in
    (
      (*  print_endline "hoistProp";
          print_endline (string_of_proposition prp);
          print_endline ((string_of_proposition (snd ans)));     *)
      
   ans)

and hoistModest {ty=ty; tot=tot; per=per} =
  let (obs1, tot') = hoistProp tot
  in let (obs2, per') = hoistProp per
  in let (obs', tot'', per'') = merge2ObsProp obs1 obs2 tot' per'
  in (obs', {ty=ty; tot=tot''; per=per''})


and foldPObligation args body = 
  List.fold_right (fun (bnd,prp) x -> PObligation(bnd,prp,x)) args body

and foldObligation args body = 
  List.fold_right (fun (bnd,prp) x -> Obligation(bnd,prp,x)) args body


(************************)
(** {2 Head-reductions} *)
(************************)

and simpleTerm = function
    Id _ -> true
  | EmptyTuple -> true
  | Dagger -> true
  | Inj(_, None, _) -> true
  | Inj(_, Some t, _) -> simpleTerm t
  | Proj(_,t) -> simpleTerm t
(*  | App(Id _, t) -> simpleTerm t
  | Tuple ts -> List.for_all simpleTerm ts
*)
  | _ -> false

and reduce trm =
  match trm with 
    App(Lambda ((nm, _), trm1), trm2) ->
      reduce (Let(VarPat nm, trm2, trm1))

  | App(Obligation(bnds,prp,trm1), trm2) ->
      (* Complicated but short method of renaming bnds to
         avoid the free variables of trm2 *)
      let nm = wildName() 
      in let trm' = Obligation(bnds,prp,App(trm1,id nm))
      in let trm'' = substTerm (termSubst nm trm2) trm'
      in reduce trm'' 

  | App(Let(pat,trm1,trm2),trm3) ->
      let (pat',sbst) = substPat emptysubst pat (* Side-effect of refreshing *)
      in let trm2' = substTerm sbst trm2
      in let body' = reduce (App(trm2',trm3))
      in reduce (Let(pat',trm1,body'))

  | Obligation(bnds,prp,trm) ->
      Obligation(bnds, prp, reduce trm)

  | Proj(n, Obligation(bnd,prp,trm1)) ->
      Obligation(bnd, prp, reduce (Proj(n,trm1)))

  | Lambda((nm1,_), App(trm1, Id(LN(None,nm2)))) when nm1 = nm2 ->
      (** Eta-reduction ! *)
      if (List.mem nm1 (fvTerm trm1)) then
        trm
      else
        reduce trm1

  | Let (pat1, Let (pat2, trm2a, trm2b), trm3) ->
      (* Side-effect of refreshing *)
      let (pat2',sbst) = substPat emptysubst pat2
      in let trm2b' = substTerm sbst trm2b
      in reduce (Let(pat2', trm2a, Let(pat1, trm2b', trm3)))

  | Let (VarPat nm1, trm2, trm3) ->
      (* XXX May lose obligations *)
      if (simpleTerm trm2) ||
         (countTerm (occurrencesOfTermName nm1) trm3 < 2) then 
        reduce (substTerm (insertTermvar emptysubst nm1 trm2) trm3)
      else
        trm

  | Let (WildPat, trm2, trm3) ->
      (* XXX May lose obligations *)
      trm3

  | Proj(n, trm) ->
      begin
        match reduce trm with
            Tuple trms -> 
(*            let (obs, trms') = hoistTerms trms
              in foldObligation obs (reduce (List.nth trms' n)) *)
              List.nth trms n
          | Let (pat1, trm2, trm3) -> 
              Let (pat1, trm2, reduce (Proj (n, trm3)))
          | Obligation (bnd1, prp2, trm3) ->
              Obligation (bnd1, prp2, reduce (Proj (n, trm3)))
          | trm' -> Proj(n, trm')
      end

  | Case(trm1, arms) as orig_term ->
      let trm1' = reduce trm1
      in let rec armLoop = function
          [] -> failwith "Outsyn.reduce Case: ran out of arms"
        | (pat,trm)::rest ->
            match pmatch fLet trm1' pat trm with
              Yes trm' -> reduce trm'
            | No       -> armLoop rest
            | Maybe    -> orig_term
      in armLoop arms

  | trm -> trm

and reduceProp prp = 
  match prp with
      PApp(PLambda ((nm, _), prp1), trm2) ->
        reduceProp (PLet(VarPat nm, trm2, prp1))

    | PApp(PLet(pat,trm1,prp2),trm3) ->
        let (pat',sbst) = 
          substPat emptysubst pat (* Side-effect of refreshing *)
        in let prp2' = substProp sbst prp2
        in let body' = reduceProp (PApp(prp2',trm3))
        in reduceProp (PLet(pat',trm1,body'))

    | PLet (pat1, Let (pat2, trm2a, trm2b), prp3) ->
        let (pat2',sbst) = 
          substPat emptysubst pat2 (* Side-effect of refreshing *)
        in let trm2b' = substTerm sbst trm2b
        in reduceProp (PLet(pat2', trm2a, PLet(pat1, trm2b', prp3)))
          
    | PLet(VarPat nm, trm1, prp2) ->
        (* XXX: May lose obligations *)
        if (simpleTerm trm1) || 
        (countProp (occurrencesOfTermName nm) prp2 < 2) then
          reduceProp (substProp (termSubst nm trm1) prp2)
        else
          prp

    | PLet(WildPat, trm1, prp2) -> 
        (* XXX: May lose obligations *)
          prp2

    | PApp(PObligation(bnds,prp1,prp2), trm3) ->
      (* Complicated but short method of renaming bnds to
         avoid the free variables of trm3 *)
      let nm = wildName() 
      in let prp' = PObligation(bnds,prp1,PApp(prp2,id nm))
      in let prp'' = substProp (termSubst nm trm3) prp'
      in reduceProp prp''
  |  PObligation(bnds, prp1, prp2) -> 
       PObligation(bnds, prp1, reduceProp prp2)

  | PLambda((nm1,_), PApp(prp1, Id(LN(None,nm2))))  ->
      (** Eta-reduction ! *)
      ((* print_endline (Name.string_of_name nm1);
       print_endline (Name.string_of_name nm2); *)
       if (List.mem nm1 (fvProp prp1)) then
         prp
       else
         reduceProp prp1)
        
(* We don't eta-reduce NamedProp's because
   they are supposed to be fully-applied.

  | PMLambda((nm1,_), NamedProp(n, Dagger, lst))
  | PLambda((nm1,_), NamedProp(n, Dagger, lst)) ->
      begin
        match List.rev lst with
            (Id(LN(None,nm2))::es) -> 
              let p' = NamedProp(n, Dagger, List.rev es)
              in if (nm1 = nm2) && not (List.mem nm1 (fvProp p')) then
                  reduceProp p'
                else
                  prp
          | _ -> prp
      end
*)

  | PCase(trm1, arms) ->
      let trm1' = reduce trm1 in
      let rec tryToEliminatePCase = function
          [] -> False (* Ran out of possible arms *)
        | (pat,prp)::rest ->
	    begin
              match pmatch fPLet trm1' pat prp with
		  Yes prp' -> reduceProp prp'
		| No       -> tryToEliminatePCase rest
		| Maybe    -> 
		    (* Well, we can't statically reduce the PCase.
		       But we can at least get rid of the arms that
		       *don't* match! *)
		    PCase(trm1', (pat,prp)::collectMatchableArms rest)
	    end
	 and collectMatchableArms = function
	   | [] -> []
	   | (pat,prp) :: rest ->
               match pmatch fPLet trm1' pat prp with
		 | No -> (print_endline "collectMatchableArms no";
			  collectMatchableArms rest)
		 | Yes _ -> (print_endline "collectMatchableArms yes";
			 print_endline (Pp.string_of_pattern pat);
			 print_endline (Pp.string_of_term trm1');
			 (pat,prp) :: collectMatchableArms rest)
		 | Maybe -> (print_endline "collectMatchableArms Maybe";
			 print_endline (Pp.string_of_pattern pat);
			 print_endline (Pp.string_of_term trm1');
			 (pat,prp) :: collectMatchableArms rest)
      in tryToEliminatePCase arms

  | PBool (BConst true) -> True
  | PBool (BConst false) -> False
  | PBool (BNot e) -> Not (PBool e)
  | PBool (BOp(AndOp, es)) -> And (List.map fPBool es)
(*   | PBool (BOp(OrOp, es)) -> Or (List.map fPBool es) *)
  | PBool (BOp(ImplyOp, [e1;e2])) -> Imply (PBool e1, PBool e2)
  | PBool (BOp(IffOp, [e1;e2])) -> Iff (PBool e1, PBool e2)
  | prp -> prp



let worthFlatteningInProp nm prp =
  let nUses = countProp (occurrencesOfTermName nm) prp  in
  let nProjs = countProp (occurrencesOfNameInProj nm) prp  in
        nProjs >= max 1 (nUses - 2)
        
let worthFlatteningInTerm nm prp =
  let nUses = countTerm (occurrencesOfTermName nm) prp  in
  let nProjs = countTerm (occurrencesOfNameInProj nm) prp  in
        nProjs >= max 1 (nUses - 2)


(***************************)
(** {2 The Typing Context} *)
(***************************)

(* We must maintain different lookup tables and renamings for each
   "flavor" of identifier because they live in distinct ML namespaces. 

   Any pass that goes through and calls these renaming functions for
   bound variables is then obligated to apply the renaming to uses
   of those variables (in the base cases) 

   Currently we don't bother keeping track of the proptypes of
   propositional variables (since it never comes up), and we 
   don't bother keeping a renaming for signature variables
   (since there are no alpha-varying binders for these in the
   syntax).

*)
type context = {termvars: ty NameMap.t;          (* Type of a term variable *)
		typevars: (ty option) NameMap.t; (* Defn (if any) of ty. var.*)
		modulvars: signat NameMap.t;     (* Signature of a mod. var  *)
		signatvars: signat NameMap.t;    (* Defn of a sig. variable *)

		termrenaming: name NameMap.t;    (* Renaming of term vars *)
		typerenaming: name NameMap.t;    (* Renaming of type vars *)
		modulrenaming: name NameMap.t;   (* Renaming of mod. vars *)
		proprenaming: name NameMap.t;    (* Renaming of prop. vars *)

	        facts: proposition list          (* A list of true props *)
               }

let emptyContext = 
  {termvars   = NameMap.empty;   
   typevars   = NameMap.empty;   
   modulvars  = NameMap.empty;  
   signatvars = NameMap.empty;

   termrenaming  = NameMap.empty;
   typerenaming  = NameMap.empty;
   modulrenaming = NameMap.empty;
   proprenaming  = NameMap.empty;

   facts = []}

(* Displays the variable bindings in the context.
   For now, does not display renamings or the list of facts 
*)
let displayRenaming map = 
  begin
    let showPair nm nm' =
      print_string ("[" ^ string_of_name nm ^ "~>" ^ string_of_name nm' ^ "]")
    in
      NameMap.iter showPair map;
      print_endline "";
  end

let displayContext ctx = 
  begin
    NameMap.iter 
      (fun nm ty -> 
	print_endline("val " ^ string_of_name nm ^ ":" ^ string_of_ty ty)) 
      ctx.termvars;
    displayRenaming ctx.termrenaming;
    NameMap.iter 
      (fun nm tyopt -> 
	print_endline("type " ^ string_of_name nm ^ 
		      (match tyopt with 
			None -> "" | 
			Some ty -> "=" ^ string_of_ty ty))) 
      ctx.typevars;
    displayRenaming ctx.typerenaming;
    NameMap.iter 
      (fun nm sg -> 
	print_endline("module " ^ string_of_name nm ^ " : " ^ 
		      string_of_signat sg)) 
      ctx.modulvars;
    displayRenaming ctx.modulrenaming;
    NameMap.iter 
      (fun nm sg -> 
	print_endline("signature " ^ string_of_name nm ^ " = " ^ 
		      string_of_signat sg)) 
      ctx.signatvars;
    print_endline "and finally, proprenaming:";
    displayRenaming ctx.proprenaming;
  end


(***************)
(** {3 Lookup} *)
(***************)

let notFound sort nm = 
  failwith ("Unbound " ^ sort ^ " variable " ^ string_of_name nm)



(* 
   lookupTermVariable   : context -> name -> ty
   lookupTypeVariable   : context -> name -> ty option
   lookupModulVariable  : context -> name -> signat
   lookupSignatVariable : context -> name -> signat
*)

let lookupTermVariable ctx nm = 
   try (NameMap.find nm ctx.termvars) with 
       Not_found -> notFound "term" nm

let lookupTypeVariable ctx nm = 
   try (NameMap.find nm ctx.typevars) with 
       Not_found -> notFound "type" nm

let lookupModulVariable ctx nm = 
   try (NameMap.find nm ctx.modulvars) with 
       Not_found -> notFound "modul" nm

let lookupSignatVariable ctx nm = 
   try (NameMap.find nm ctx.signatvars) with 
       Not_found -> notFound "signat" nm

(******************)
(** {3 Insertion} *)
(******************)

let insertTermVariable ctx nm ty =
  if NameMap.mem nm ctx.termvars then
    failwith ("Outsyn: shadowing of term variable " ^ (string_of_name nm))
  else
    { ctx with termvars = NameMap.add nm ty ctx.termvars }

let insertTypeVariable ctx nm ty =
  if NameMap.mem nm ctx.typevars then
    failwith ("Outsyn: shadowing of type variable " ^ (string_of_name nm))
  else
  { ctx with typevars = NameMap.add nm ty ctx.typevars }

let insertTypeVariables ctx nms def =
  let defs = List.map (fun _ -> def) nms
  in
     List.fold_left2 insertTypeVariable ctx nms defs

let insertPropVariable ctx _ _ = 
  (* We don't keep track of propositional variables *)
  ctx
  

(** Other insertion functions defined below (after normalization):

   insertModulVariable : context -> name -> signat -> context
   insertSignatVariable: context -> name -> signat -> context

*)

(************************************)
(** {3 Renaming of Bound Variables} *)
(************************************)

let addToRenaming map oldnm newnm =
    NameMap.add oldnm newnm map

let addListToRenaming map oldnms newnms =
  List.fold_left2 addToRenaming map oldnms newnms

(* Stolen from logicrules.ml *)
let renameBoundTermVar ctx nm =
  let nm' = refresh nm in
    ({ctx with termrenaming = addToRenaming ctx.termrenaming nm nm'}, nm')

let renameBoundTermVars ctx nms =
  let nms' = refreshList nms in
    ({ctx with termrenaming = 
        addListToRenaming ctx.termrenaming nms nms'}, nms')

let renameBoundTypeVar ctx nm =
  let nm' = refresh nm in
    ({ctx with termrenaming = addToRenaming ctx.typerenaming nm nm'}, nm')

let renameBoundTypeVars ctx nms = 
  mapWithAccum renameBoundTypeVar ctx nms

let renameBoundModulVar ctx nm =
  let nm' = refresh nm in
    ({ctx with termrenaming = addToRenaming ctx.modulrenaming nm nm'}, nm')

let renameBoundPropVar ctx nm =
  let nm' = refresh nm in
    ({ctx with proprenaming = addToRenaming ctx.proprenaming nm nm'}, nm')
  
let rec renamePattern ctx pat = 
  match pat with
    WildPat -> (ctx, pat)
  | VarPat nm -> 
      failwith "Outsynrules.renamePattern: cannot infer type for VarPat"
  | TuplePat pats ->
      let (ctx', pats') = renamePatterns ctx pats
      in (ctx', TuplePat pats)
  | ConstrPat(_, None) -> (ctx, pat)
  | ConstrPat(lbl, Some (nm,ty)) ->
      let (ctx', nm') = renameBoundTermVar ctx nm
      in let ctx'' = insertTermVariable ctx nm ty
      in (ctx'', ConstrPat(lbl, Some(nm', ty)))

and renamePatterns ctx pats = 
  mapWithAccum renamePattern ctx pats


let applyRenaming map nm = 
  if (NameMap.mem nm map) then
    NameMap.find nm map
  else
    nm

let applyTermRenaming ctx nm =
  applyRenaming ctx.termrenaming nm

let applyTypeRenaming ctx nm =
  applyRenaming ctx.typerenaming nm

let applyModulRenaming ctx nm =
  applyRenaming ctx.modulrenaming nm

let applyPropRenaming ctx nm =
  applyRenaming ctx.proprenaming nm

let applyPropRenamingLN ctx = function
    LN(None, nm) -> LN(None, applyPropRenaming ctx nm)
  | ln -> ln  (* XXX: What if we've renamed modul variables in here??? *)

      

let updateSubstForElem subst mdl = function
    Spec(nm, ValSpec _, _) -> insertTermvar subst nm (Id(LN(Some mdl, nm)))
  | Spec(nm, TySpec _, _) ->  insertTyvar subst nm (NamedTy(LN(Some mdl, nm)))
  | Spec(nm, ModulSpec _, _) -> insertModulvar subst nm (ModulProj(mdl, nm))
  | Spec(nm, SignatSpec _, _) -> subst (* No substituting for signature vars *)
  | _ -> subst

let rec findModulvarInElems elts mdl nm =
  let rec loop subst = function
      [] -> failwith ("Outsynrules.findModulvarInElems: " ^ string_of_name nm)
    | Spec(nm', ModulSpec sg, _) :: _ when nm=nm' -> substSignat subst sg
    | elem :: rest -> loop (updateSubstForElem subst mdl elem) rest
  in loop emptysubst elts

let rec findTermvarInElems elts mdl nm =
  let rec loop subst = function
      [] -> failwith ("Outsynrules.findTermvarInElems: " ^ string_of_name nm)
    | Spec(nm', ValSpec ([],ty), _) :: _ when nm=nm' -> substTy subst ty
    | Spec(nm', ValSpec (_,ty), _) :: _ when nm=nm' -> 
	failwith ("Outsynrules.findTermvarInElems: polymorphic valspec " ^ 
	  string_of_name nm)
    | elem :: rest -> loop (updateSubstForElem subst mdl elem) rest
  in loop emptysubst elts

let rec findTypevarInElems elts mdl nm =
  let rec loop subst = function
      [] -> failwith ("Outsynrules.findTypevarInElems: " ^ string_of_name nm)
    | Spec(nm', TySpec tyopt, _) :: _ when nm=nm' -> substTyOption subst tyopt
    | elem :: rest -> loop (updateSubstForElem subst mdl elem) rest
  in loop emptysubst elts

let rec findSignatvarInElems elts mdl nm =
  let rec loop subst = function
      [] -> failwith ("Outsynrules.findSignatvarInElems: " ^ string_of_name nm)
    | Spec(nm', SignatSpec sg, _) :: _ when nm=nm' -> substSignat subst sg
    | elem :: rest -> loop (updateSubstForElem subst mdl elem) rest
  in loop emptysubst elts


let rec hnfSignat ctx = function
    SignatApp(sg1,mdl2) -> 
      begin
	match hnfSignat ctx sg1 with
	    SignatFunctor((nm,_),sg1b) ->
	      let sg' = substSignat (insertModulvar emptysubst nm mdl2) sg1b
	      in hnfSignat ctx sg'
	  | _ -> failwith "Outsynrules.hnfSignat 1"
      end
  | SignatName nm -> hnfSignat ctx (lookupSignatVariable ctx nm)
  | SignatProj (mdl, nm) ->
       begin
	 match hnfSignat ctx (modulToSignat ctx mdl) with
             Signat elts -> findSignatvarInElems elts mdl nm
	   | _ -> failwith "Outsynrules.hnfSignat 2"
       end
  | sg -> sg

and modulToSignat ctx = function
    ModulName nm        -> 
      let nm = applyModulRenaming ctx nm
      in lookupModulVariable ctx nm
  | ModulProj (mdl, nm) ->
       begin
	 match hnfSignat ctx (modulToSignat ctx mdl) with
             Signat elts -> findModulvarInElems elts mdl nm
	   | _ -> failwith "Outsynrules.modulToSignat 1"
       end
  | ModulApp (mdl1, mdl2)  -> 
       begin
	 match hnfSignat ctx (modulToSignat ctx mdl1) with
             SignatFunctor((nm,_),sg) -> 
	       let subst = insertModulvar emptysubst nm mdl2
	       in substSignat subst sg
	   | _ -> failwith "Outsynrules.modulToSignat 2"
       end
  | ModulStruct defs -> 
      let rec loop ctx = function
	  [] -> []
	| DefTerm(nm,ty,_) :: rest ->
	    Spec(nm, ValSpec ([], ty), []) :: 
	      loop (insertTermVariable ctx nm ty) rest
	| DefType(nm,ty) :: rest ->
	    Spec(nm, TySpec (Some ty), []) :: 
	      loop (insertTypeVariable ctx nm (Some ty)) rest
	| DefModul(nm,sg,_) :: rest ->
	    Spec(nm, ModulSpec sg, []) :: 
	      loop (insertModulVariable ctx nm sg) rest
        | DefSignat(nm,sg) :: rest ->
	    Spec(nm, SignatSpec sg, []) ::
	      loop (insertSignatVariable ctx nm sg) rest
      in Signat (loop ctx defs)


and insertModulVariable ctx nm sg =
  if NameMap.mem nm ctx.modulvars then
    failwith ("Outsyn: shadowing of modul variable " ^ (string_of_name nm))
  else
    let sg' =  hnfSignat ctx sg
    in
    { ctx with modulvars = NameMap.add nm sg' ctx.modulvars }

and insertSignatVariable ctx nm sg =
  if NameMap.mem nm ctx.signatvars then
    failwith ("Outsyn: shadowing of signat variable " ^ (string_of_name nm))
  else
    let sg' =  hnfSignat ctx sg
    in
    { ctx with signatvars = NameMap.add nm sg' ctx.signatvars }



(***********************************)
(** {2 Utility functions for types *)
(***********************************)

(** Expand out any top-level definitions for a type *)
let rec hnfTy ctx orig_ty = 
  match orig_ty with
      NamedTy (LN(None, nm)) ->
	begin
	  match lookupTypeVariable ctx nm with
	    | None -> orig_ty
	    | Some ty -> hnfTy ctx ty
	end
    | NamedTy (LN(Some mdl, nm)) ->
	begin
	  match hnfSignat ctx (modulToSignat ctx mdl) with
	    Signat elems ->
	      begin
		match findTypevarInElems elems mdl nm with
		    None -> orig_ty
		  | Some ty -> hnfTy ctx ty
	      end
	    | sg' -> (print_endline "Found unprojectable signature:";
		      print_endline (string_of_signat sg');
		      failwith "hnfTy")
	end
    | _ -> orig_ty


let rec insertTermVariableLet ctx pat ty =
  match pat with
    WildPat       -> ctx
  | VarPat nm     -> insertTermVariable ctx nm ty
  | TuplePat pats -> 
      begin
	match hnfTy ctx ty with
	  TupleTy tys ->
	    List.fold_left2 insertTermVariableLet ctx pats tys
	| _ -> failwith "Outsynrules.insertTermVariableLet 1"
      end
  | ConstrPat _ -> failwith "Outsynrules.insertTermVariableLet 2"

  

let joinTy ctx s1 s2 = 
   if (s1 = s2) then
      (* Short circuting *)
      s1
   else
      let    s1' = hnfTy ctx s1
      in let s2' = hnfTy ctx s2

      in let rec joinSums = function 
	  ([], s2s) -> s2s
	| ((l1,t)::s1s, s2s) ->
	    if List.mem_assoc l1 s2s then
	      joinSums (s1s, s2s)
	    else
	      (l1,t) :: (joinSums (s1s, s2s))

      in match (s1',s2') with
        | (SumTy lsos1, SumTy lsos2) -> SumTy (joinSums (lsos1, lsos2))
        | _ -> s1 (** We're assuming the input typechecks! *)



(* checkFact : ctx -> prop -> bool

   Check whether the given proposition is a logical consequence 
   of the facts we already know to be true.

   This isn't even close to being a theorem prover; it doesn't even
   check for alpha-equivalence of propositions or know about modus
   ponens.  It only checks for a very few "easy" inferences. 
*)
let rec checkFact ({facts = facts} as ctx) prp =
  List.mem prp facts ||
    (match prp with 
	And prps -> List.for_all (checkFact ctx) prps
      | Imply (prp1,prp2) -> 
	  checkFact (insertFact ctx prp1) prp2
      | Iff(prp1,prp2) ->
	  checkFact ctx (Imply(prp1,prp2)) &&
	    checkFact ctx (Imply(prp2,prp1))
      | Not(Not(prp)) ->
	  (** We are guaranteed that all propositions/assertions
	      are classically valid; the "constructive" parts have
	      already been removed. *)
	  checkFact ctx prp
      | Equal(t1,t2) ->
	  (* Don't call checkFact recursively here, or we'll
	     go into an infinite loop *)
	  List.mem (Equal(t2,t1)) facts
      | PApp(PApp (p, t1), t2) when isPerProp p ->
	  (* Ditto *)
	  List.mem (PApp(PApp(p, t2), t1)) facts
      | _ -> false)

and insertFact ({facts=facts} as ctx) prp =
  if checkFact ctx prp then
    ctx
  else
    (match prp with
	And prps -> insertFacts ctx prps
      | Not (Not prp) -> insertFact ctx prp (* Classical logic! *)
      | Iff(prp1,prp2) ->
	  insertFact (insertFact ctx (Imply(prp1,prp2))) (Imply(prp2,prp1))
      | _ -> { ctx with facts = prp::facts })

and insertFacts ctx prps =
  List.fold_left insertFact ctx prps

let rec insertPattern ctx = function
    WildPat  -> ctx
  | VarPat _ -> 
      failwith "Outsynrules.insertPattern: Can't infer type of pattern"
  | TuplePat pats -> 
      List.fold_left insertPattern ctx pats
  | ConstrPat(lbl, None) -> ctx
  | ConstrPat(lbl, Some(nm,ty)) ->
      insertTermVariable ctx nm ty

(***************************************)
(** {2: Type Reconstruction for Terms} *)
(***************************************)

(* Given a context and a well-formed term, return the type
   of that term.

   Does not actually check that the term is well-formed!
   Returned type will be correct, but need not be head-normal.
 *)
let rec typeOf ctx = function
  | Id(LN(None,nm)) -> 
      let nm = applyTermRenaming ctx nm
      in lookupTermVariable ctx nm
  | Id(LN(Some mdl, nm)) ->
       begin
	 match hnfSignat ctx (modulToSignat ctx mdl) with
             Signat elts -> findTermvarInElems elts mdl nm
	   | _ -> failwith "Outsynrules.typeOf: Id"
       end
  | EmptyTuple -> UnitTy
  | BConst _
  | BNot _
  | BOp _ -> BoolTy
  | Dagger     -> TopTy
  | App(trm1, _) ->
      begin
	match hnfTy ctx (typeOf ctx trm1) with
	  ArrowTy(_,ty) -> ty
	| _ -> failwith "Outsynrules.typeOf App"
      end
  | Lambda((nm,ty1),trm2) -> 
      let ctx' = insertTermVariable ctx nm ty1
      in ArrowTy(ty1, typeOf ctx' trm2)
  | Tuple trms ->
      TupleTy (List.map (typeOf ctx) trms)
  | Proj(n, trm) ->
      begin
	match (hnfTy ctx (typeOf ctx trm)) with
	  TupleTy tys -> List.nth tys n
	| _ -> failwith "Outsynrules.typeOf: Proj"
      end
  | Inj(lbl, _, ty) -> ty
  | Case(_, arms) ->
      begin
	let typeOfArm (pat,trm) =
	      let ctx' = insertPattern ctx pat
	      in typeOf ctx' trm
	in let armTys = List.map typeOfArm arms
	in match armTys with
	  []        -> VoidTy
	| (ty::tys) -> List.fold_left (joinTy ctx) ty tys
      end
  | Let(pat,trm1,trm2) ->
      let ctx' = insertTermVariableLet ctx pat (typeOf ctx trm1)
      in typeOf ctx' trm2
  | Obligation(bnds,_,trm) ->
      let insertTermBnd ctx (nm,ty) = insertTermVariable ctx nm ty
      in let ctx' = List.fold_left insertTermBnd ctx bnds 
      in typeOf ctx' trm
  | PolyInst (trm,tys) ->
      failwith "Outsynrules.typeOf PolyInst unimplemented"



