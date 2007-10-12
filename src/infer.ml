(*****************************************)
(** {1 Type Reconstruction and Checking} *)                         
(*****************************************)

(** For now we assume that all bound variables are annotated, either
    when declared or through a prior "implicit" statement.
*)

module S = Syntax
module L = Logic
module LR = Logicrules
module E = Error
open Syntax 
open Name

exception Impossible

exception NotBoolTerm

(**********************)
(** Utility Functions *)
(**********************)

let noDuplicates strngs =
  let sset = List.fold_right StringSet.add strngs StringSet.empty
  in
    List.length strngs = StringSet.cardinal sset
    
let rec gatherSomes = function
    [] -> []
  | None   :: rest -> gatherSomes rest
  | Some x :: rest -> x :: gatherSomes rest

(*************************)
(** {3 Inference proper} *)
(*************************)

type inferResult =
    ResPropType of L.proptype
  | ResKind     of L.setkind
  | ResSet      of L.set         * L.setkind
  | ResTerm     of L.term        * L.set
  | ResProp     of L.proposition * L.proptype
  | ResModel    of L.model       * L.theory 
  | ResTheory   of L.theory      * L.theorykind
  | ResSentence of L.model_binding list * L.proposition

let rec annotateExpr cntxt orig_expr = 
  try
    match orig_expr with  
    | Set -> ResKind (L.KindSet)

    | Empty    -> ResSet(L.Empty, L.KindSet)
    | Unit     -> ResSet(L.Unit,  L.KindSet)
    | Bool     -> ResSet(L.Bool,  L.KindSet)
    | Sum lsos -> annotateSum cntxt orig_expr lsos
    | Subset (sbnd1, expr2)  -> annotateSubset cntxt orig_expr sbnd1 expr2

    | EmptyTuple       -> ResTerm ( L.EmptyTuple, L.Unit )
    | BFalse           -> ResTerm ( L.BConst false, L.Bool )
    | BTrue            -> ResTerm ( L.BConst true, L.Bool )
    | Label label      -> ResTerm ( L.Inj(label, None), L.Sum[(label, None)] )

    | Tuple exprs      -> annotateTuple cntxt orig_expr exprs
    | Proj(n1, expr2)  -> annotateProj cntxt orig_expr n1 expr2
    | App(Label label, expr2) -> 
                              annotateAppLabel cntxt orig_expr label expr2
    | Choose(nm1, expr2, expr3) -> 
                              annotateChoose cntxt orig_expr nm1 expr2 expr3
    | RzChoose(nm1, expr2, expr3) -> 
                              annotateRzChoose cntxt orig_expr nm1 expr2 expr3
    | Subin(expr1, expr2)  -> annotateSubin cntxt orig_expr expr1 expr2
    | Subout(expr1, expr2) -> annotateSubout cntxt orig_expr expr1 expr2
    | The(sbnd1, expr2)    -> annotateThe cntxt orig_expr sbnd1 expr2

    | Prop         -> ResPropType (L.Prop)
    | Stable       -> ResPropType (L.StableProp)
    | Equiv expr1  -> annotateEquiv cntxt orig_expr expr1

    | False                 -> ResProp(L.False, L.StableProp)
    | True                  -> ResProp(L.True, L.StableProp)
    | And exprs             -> annotateAnd cntxt orig_expr exprs
    | Or exprs              -> annotateOr cntxt orig_expr exprs
    | Not expr1             -> annotateNot cntxt orig_expr expr1
    | Iff (expr1, expr2)    -> annotateIff cntxt orig_expr expr1 expr2
    | Equal (expr1, expr2)  -> annotateEqual cntxt orig_expr expr1 expr2
    | Exists (bnd1, expr2)  -> annotateExists cntxt orig_expr false bnd1 expr2
    | Unique (bnd1, expr2)  -> annotateExists cntxt orig_expr true bnd1 expr2
    | Forall (bnd1, expr2)  -> annotateForall cntxt orig_expr bnd1 expr2

    | Thy elems -> annotateThy cntxt orig_expr elems
    | Rename (thy, nm, nm') -> annotateRename cntxt orig_expr thy nm nm'

    | Ident nm                 -> annotateIdent cntxt orig_expr nm
    | MProj (expr1, nm2)       -> annotateMProj cntxt orig_expr expr1 nm2
    | Rz expr1                 -> annotateRz cntxt orig_expr expr1
    | Product sbnds            -> annotateProduct cntxt orig_expr sbnds
    | Constraint (expr1, expr2) -> annotateConstraint cntxt orig_expr expr1 expr2
    | Quotient (expr1, expr2)  -> annotateQuotient cntxt orig_expr expr1 expr2
    | App (expr1, expr2)       -> annotateApp cntxt orig_expr expr1 expr2    
    | Lambda (binding1, expr2) -> annotateLambda cntxt orig_expr binding1 expr2
    | Arrow (nm, expr1, expr2) -> annotateArrow cntxt orig_expr nm expr1 expr2
    | Let(sbnd1, expr2, expr3) -> annotateLet cntxt orig_expr sbnd1 expr2 expr3
    | Case (expr1, arms2)      -> annotateCase cntxt orig_expr expr1 arms2

  with
    | E.TypeError msgs -> 
        E.generalizeError msgs (E.inMsg orig_expr)
    | e                -> 
        E.tyGenericErrors 
          (("Caught unexpected exception " ^ Printexc.to_string e) ::
           [E.inMsg orig_expr])
  

(* Ident nm *)
and annotateIdent cntxt orig_expr nm =
  let nm = LR.applyContextSubst cntxt nm 
  in
    match LR.lookupId cntxt nm with
    | Some( L.DeclProp(_, pty) ) -> 
        ResProp(L.Atomic(L.longname_of_name nm, pty), pty)
    | Some( L.DeclSet(_, knd) ) -> 
        ResSet(L.Basic(L.set_longname_of_name nm, knd), knd)
    | Some( L.DeclTerm (_, ty) )  -> 
        ResTerm(L.Var(L.longname_of_name nm), ty)
    | Some( L.DeclModel  thry ) -> 
        ResModel(L.ModelName(L.model_name_of_name nm), thry )
    | Some( L.DeclTheory (thry, tk) ) -> 
        ResTheory (L.TheoryName(L.theory_name_of_name nm), tk)
    | Some( L.DeclSentence _ ) -> 
        E.tyGenericError "Cannot *use* an axiom in a theory."
    | None -> 
        E.tyUnboundError nm  

and annotateRename cntxt orig_expr expr1 nm nm' =
  let (thy, tk) = annotateTheory cntxt orig_expr expr1 in
  match LR.hnfTheory cntxt thy with 
  | L.Theory elems -> ResTheory(L.Theory (LR.renameElem nm nm' elems), tk)
  | _ -> E.notWhatsExpectedInError expr1 "theory of a model" orig_expr
  
(* MProj(expr1, nm2) *)
and annotateMProj cntxt orig_expr expr1 nm2 =
  let (mdl, thry) = annotateModel cntxt orig_expr expr1  in
  match LR.hnfTheory cntxt thry with
  | L.Theory elems ->
      begin
        match LR.searchElems cntxt nm2 mdl elems with
        | Some ( L.DeclSet (_,knd) ) -> 
            ResSet(L.Basic(L.SLN(Some mdl, nm2), knd), knd)
        | Some ( L.DeclProp (_,pt) ) -> 
            ResProp(L.Atomic(L.LN(Some mdl, nm2), pt), pt)
        | Some ( L.DeclTerm (_,ty) ) -> 
            ResTerm(L.Var(L.LN(Some mdl, nm2)), ty)
        | Some ( L.DeclModel thry ) -> 
            ResModel(L.ModelProj(mdl,nm2), thry)
        | Some ( L.DeclTheory (thry, thryknd) ) ->
            ResTheory(L.TheoryProj(mdl,nm2), thryknd)
        | Some ( L.DeclSentence _ ) -> 
            E.badModelProjectionError nm2 orig_expr 
              "Axioms cannot be projected from a theory"
        | None -> 
            E.badModelProjectionError nm2 orig_expr "Name not found"
      end
  | _ -> 
    E.notWhatsExpectedInError expr1 "theory of a model" orig_expr
  
(* App(Label label, expr2) *)
and annotateAppLabel cntxt orig_expr label expr2 =
  (** Special case:  a label applied to an expression is the parser's
      way of writing an injection into a sum *)
  let (trm2', ty2') = annotateTerm cntxt orig_expr expr2
  in 
    ResTerm ( L.Inj(label, Some trm2'),
              L.Sum[ (label, Some ty2') ] )

(* Proj(n1, expr2) *)
and annotateProj cntxt orig_expr n1 expr2 = 
  let    (trm2',  ty2' ) = annotateTerm cntxt orig_expr expr2 in
  let (trm2'', ty2'') = LR.coerceFromSubset cntxt trm2' ty2' in
  match ty2'' with 
    L.Product nmtys ->
      begin
        match (LR.typeOfProj cntxt nmtys trm2'' n1) with
          None -> E.tyGenericError ( "Projection " ^ string_of_int n1 ^ 
                                     " out of bounds in " ^
                                     string_of_expr orig_expr )
        | Some ty -> ResTerm ( L.Proj(n1, trm2''), ty )
      end
  | _ -> E.wrongTypeError expr2 ty2' "tuple"  orig_expr    
  
(* Sum lsos *)
and annotateSum cntxt orig_expr lsos = 
  (* We assume that the parser has figured out this is really a sum type
     and not a use of the term operator +. *)
  let process = function 
      (lbl, None) -> (lbl, None)
    | (lbl, Some expr) -> (lbl, Some (annotateType cntxt orig_expr expr)) in
  ResSet( L.Sum( List.map process lsos), L.KindSet )

and annotateProduct cntxt orig_expr sbnds = 
  (* Check first item in the product to see whether it's
     a product of sets or a product of terms *)
  match annotateExpr cntxt (snd(List.hd sbnds)) with
    ResSet _ ->
      (* A [possibly dependent] type for a tuple. *)
      let rec loop cntxt = function
          [] -> []
        | (nm,expr) :: rest ->     
            let (cntxt', lbnd) = 
              annotateSimpleBinding cntxt orig_expr (nm, Some expr) in
            lbnd :: loop cntxt' rest   in
      ResSet(L.Product (loop cntxt sbnds), L.KindSet) 

  | ResTerm _ ->
    (* Multiplication, or other operation on terms *)
    let (nms, exprs) = List.split sbnds in 
    if (List.for_all isWild nms) then
      let orig_expr' = 
        List.fold_left 
        (fun e1 e2 -> App(App(Ident(N("*",Infix3)), e1), e2))
        (List.hd exprs) (List.tl exprs)  in 
      annotateExpr cntxt orig_expr'
    else
      E.tyGenericError "Term products can't be labeled"
  | _ -> E.tyGenericError "First component can't appear in a product"

(* Equiv expr1 *)
and annotateEquiv cntxt orig_expr expr1 =
  let equiv_domain_type = annotateType cntxt orig_expr expr1 in
  ResPropType ( L.EquivProp equiv_domain_type )

(* Equal(expr1, expr2) *)
and annotateEqual cntxt orig_expr expr1 expr2 =
  let (trm1, ty1) = annotateTerm cntxt orig_expr expr1 in
  let (trm2, ty2) = annotateTerm cntxt orig_expr expr2 in
  (** Equality in subsets is just equality of the underlying
      value, so it makes sense to allow equality of a value
      and a subtype value, or two values in different subtypes
      of the same type.  Since joinTypes won't coerce from subsets
      we do it ourselves here. *)
  let (trm1',ty1') = LR.coerceFromSubset cntxt trm1 ty1 in
  let (trm2',ty2') = LR.coerceFromSubset cntxt trm2 ty2 in
  let (ty, reqs) = LR.joinTypes cntxt [ty1'; ty2'] in
  ResProp( L.maybePAssure reqs (L.Equal(ty, trm1', trm2')),
           L.StableProp )


(* Subset(sbnd1, expr2) *)
and annotateSubset cntxt orig_expr sbnd1 expr2 = 
  let (cntxt', lbnd1) = annotateSimpleBinding cntxt orig_expr sbnd1
  in
    let (prp2', _) = annotateProperProp cntxt' orig_expr expr2 in
    ResSet( L.Subset(lbnd1, prp2'), L.KindSet )

(* Rz expr1 *)
and annotateRz cntxt orig_expr expr1 =
  match annotateExpr cntxt expr1 with
    ResSet(ty1, L.KindSet) -> 
      (* Rz of a set means that set's realizers *)
      ResSet (L.Rz ty1, L.KindSet)

  | ResTerm(trm1, ty1) ->
      begin
        (* Rz of a term means the value realized/implemented by that term *)
        match LR.coerceFromSubset cntxt trm1 ty1 with
          (trm1', L.Rz ty1') -> ResTerm( L.RzQuot trm1', ty1')
        | _ -> E.wrongTypeError expr1 ty1 "realizer" orig_expr
      end          

  | _ -> E.notWhatsExpectedInError expr1 "realizer or proper set" orig_expr
  
(* And exprs *)
and annotateAnd cntxt orig_expr exprs =
  try
    let trms = List.map (maybeAnnotateBoolTerm cntxt) exprs in
    ResTerm ( L.BOp(L.AndOp, trms), L.Bool)
  with NotBoolTerm ->
    let pairs = List.map (annotateProperProp cntxt orig_expr) exprs in
    let (prps, pts) = List.split pairs in
    ResProp ( L.And prps, LR.joinProperPropTypes pts )

(* Not expr1 *)
and annotateNot cntxt orig_expr expr1 =
  try
    let trm = maybeAnnotateBoolTerm cntxt expr1 in
    ResTerm ( L.BNot trm, L.Bool)
  with NotBoolTerm ->
    let (prp, _) = annotateProperProp cntxt orig_expr expr1 in
    ResProp ( L.Not prp, L.StableProp )

(* Iff(expr1, expr2) *)
and annotateIff cntxt orig_expr expr1 expr2 = 
  try
    let trm1 = maybeAnnotateBoolTerm cntxt expr1 in
    let trm2 = maybeAnnotateBoolTerm cntxt expr2 in
    ResTerm ( L.BOp(L.IffOp, [trm1;trm2]), L.Bool)
  with NotBoolTerm ->
    let (prp1, pt1) = annotateProperProp cntxt orig_expr expr1 in
    let (prp2, pt2) = annotateProperProp cntxt orig_expr expr2 in
    ResProp ( L.Iff(prp1, prp2), LR.joinProperPropTypes [pt1; pt2] )

(* Or exprs *)
and annotateOr cntxt orig_expr exprs = 
  let orig_labels = gatherSomes (List.map fst exprs) in
  if noDuplicates (orig_labels) then
    let rec processDisjuncts used_lbls = function
        [] -> ([], [])
      | (lblopt,e) :: rest -> 
          let lbl = (match lblopt with 
                       None -> Name.freshLabel used_lbls 
                     | Some lbl -> lbl) in
          let (lbls, lprps) = processDisjuncts (lbl :: used_lbls) rest in
          let (prp, _) = annotateProperProp cntxt orig_expr e in
          (lbl :: lbls, prp :: lprps)   in

    if (orig_labels = []) then
       try
         let trms = List.map (maybeAnnotateBoolTerm cntxt) (List.map snd exprs) in
         ResTerm( L.BOp(L.OrOp, trms), L.Bool )
       with NotBoolTerm ->
         let lbls, prps = processDisjuncts orig_labels exprs in
         ResProp (L.Or (List.combine lbls prps), L.Prop)
    else    
       let lbls, prps = processDisjuncts orig_labels exprs in
       ResProp (L.Or (List.combine lbls prps), L.Prop)
  else
     E.tyGenericError ( "There are duplicate labels in " ^ 
                        string_of_expr orig_expr )

(* Exists(bnd1, expr2)    --- isUnique false
   Unique(bnd1, expr2)    --- isUnique true  *)
and annotateExists cntxt orig_expr isUnique bnd1 expr2 =
  let (cntxt', lbnds1) = annotateInnerBinding cntxt orig_expr bnd1 in
  let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2 in
  let wrapperFn = if isUnique then
                    fun lbnd p -> L.Unique(lbnd, p)
                  else
                    fun lbnd p -> L.Exists(lbnd, p)  in
  let prp = List.fold_right wrapperFn lbnds1 prp2 in
  ResProp ( prp, L.Prop )

(* Forall(bnd1, expr2) *)
and annotateForall cntxt orig_expr bnd1 expr2 =
  match annotateBinding cntxt orig_expr bnd1 with
    (cntxt', [], lbnds1) -> 
      (* No model bindings, so it's just an ordinary abstraction *)
      let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2 in
      let forallprp = 
        List.fold_right (fun lbnd p -> L.Forall(lbnd, p)) lbnds1 prp2  in
      ResProp ( forallprp, stab2 )
   
  | (cntxt', mbnds, []) ->
      (* There are model bindings, so it's a (top-level) sentence.
         The rest could be another top-level sentence, or just an
         ordinary proposition. *)
      begin
        match annotateExpr cntxt' expr2 with
          ResSentence(mbnds_rest, prp) -> ResSentence(mbnds @ mbnds_rest, prp)
        | ResProp(prp, (L.Prop|L.StableProp)) -> ResSentence(mbnds, prp)
        | _ -> E.notWhatsExpectedInError expr2 "sentence" orig_expr
      end
  
  | (cntxt', mbnds, lbnds1) ->
      (* There are model bindings, so it's an (top-level) sentence.
         But there are also term bindings, so the "rest" of the
         sentence has to be an ordinary proposition. *)
      let (prp2,_) = annotateProperProp cntxt' orig_expr expr2  in
      let forallprp = 
        List.fold_right (fun lbnd p -> L.Forall(lbnd, p)) lbnds1 prp2 in
      ResSentence(mbnds, forallprp)

(* RzChoose (nm1, expr2, expr3) *)   
and annotateRzChoose cntxt orig_expr nm1 expr2 expr3 =
  let (trm2, ty2) = annotateTerm cntxt orig_expr expr2 in
  let (cntxt, nm) = LR.renameBoundVar cntxt nm1 in
  let cntxt' = LR.insertTermVariable cntxt nm (L.Rz ty2) None in
  let (trm3, ty3) = annotateTerm cntxt' orig_expr expr3 in
  if NameSet.mem nm1 (L.fnSet ty3) then
    E.cantElimError nm ty3 orig_expr
  else 
    ResTerm ( L.RzChoose ((nm,L.Rz ty2), trm2, trm3, ty3),
              ty3 )

(* Choose(nm1, expr2, expr3) *)
and annotateChoose cntxt orig_expr nm1 expr2 expr3 =
  let (trm2, ty2) = annotateTerm cntxt orig_expr expr2 in
  let (trm2', ty2') = LR.coerceFromSubset cntxt trm2 ty2 in
  match ty2' with
    L.Quotient(dom2, prp2) ->
      begin
        let (cntxt, nm) = LR.renameBoundVar cntxt nm1 in
        let cntxt' = LR.insertTermVariable cntxt nm dom2 None in
        let (trm3, ty3) = annotateTerm cntxt' orig_expr expr3 in
        if NameSet.mem nm1 (L.fnSet ty3) then
          E.cantElimError nm ty3 orig_expr
        else 
          ResTerm ( L.Choose ((nm,dom2), prp2, trm2', trm3, ty3),
                    ty3 )
      end
  | _ -> E.notWhatsExpectedInError 
            expr2 "equivalence class" orig_expr

(* Tuple exprs *)
and annotateTuple cntxt orig_expr exprs =
  let pairs = List.map (annotateTerm cntxt orig_expr) exprs in
  let (trms',tys') = List.split pairs in
  let addName t = (wildName(), t) in
  ResTerm( L.Tuple trms', 
           L.Product (List.map addName tys') )
        
(* Subin(expr1, expr2) *)        
and annotateSubin cntxt orig_expr expr1 expr2 = 
  (* Injection into a subset; even if succesful, this will 
     incur an obligation *)
  let  (trm1, ty1) = annotateTerm cntxt orig_expr expr1 in
  let ty2          = annotateType cntxt orig_expr expr2 in
  match (LR.hnfSet cntxt ty2) with
    L.Subset ((_,domty2), _) -> 
      begin
        try
          ResTerm ( LR.coerce cntxt trm1 ty1 ty2,
                    ty2 )
        with
          E.TypeError msgs ->
            (* LR.coerce failed *)
            E.specificateError msgs (E.tyMismatchMsg expr1 domty2 ty1)
      end
   | _ -> E.notWhatsExpectedInError expr2 "subset type" orig_expr
        
(* Subout(expr1, expr2) *)
and annotateSubout cntxt orig_expr expr1 expr2 =
  let (trm1, ty1) = annotateTerm cntxt orig_expr expr1 in
  let ty2       = annotateType cntxt orig_expr expr2 in
  match (LR.hnfSet cntxt ty1) with
    L.Subset _ -> 
      begin
        try
          let trm1' = LR.coerce cntxt trm1 ty1 ty2 in
          ResTerm ( trm1', ty2)
        with 
          E.TypeError msgs ->
            E.specificateError msgs
              ("Could not coerce the subset term " ^ string_of_expr expr1 ^ 
                " to type " ^ string_of_expr expr2 ^ " in " ^ 
                string_of_expr orig_expr)
      end
  | _ -> E.notWhatsExpectedInError expr1 "term in a subset" orig_expr

(* The(sbnd1, expr2) *)
and annotateThe cntxt orig_expr sbnd1 expr2 = 
  let (cntxt', ((nm1,ty1) as lbnd1) ) = 
    (* Careful with error messages; nm1 might have been renamed *)
    annotateSimpleBinding cntxt orig_expr sbnd1 in
  let (prp2,_) = annotateProperProp cntxt' orig_expr expr2 in
  (** We've agreed that Translate will add the appropriate
  assure (that we have a singleton subset), since Logic
  only generates stable assure's, and prp2 isn't necessarily
  stable. (Its computational content gets attached by
  translate to the result anyway, since we've decided
  that "The x:s.phi" now has type "{x:s | phi}").  *)
  ResTerm ( L.The (lbnd1, prp2),
            L.Subset((nm1,ty1), prp2) )
     
(* Thy elems *)
and annotateThy cntxt orig_expr elems =
  let cntxt' = LR.markThy cntxt in
  let (_, lelems) = annotateTheoryElems cntxt' elems in
  ResTheory(L.Theory lelems, L.ModelTheoryKind)
     
             
and annotateApp cntxt orig_expr expr1 expr2 =
  match (annotateExpr cntxt expr1, annotateExpr cntxt expr2) with
  | ResProp(prp1,pt1), ResTerm(trm2,ty2) -> 
    (* Application of a predicate to a term *)
    begin
      let nm, domty, codpt =
        match pt1 with
          L.PropArrow(nm,domty,codpt) -> nm, domty, codpt
        | L.EquivProp(domty) -> 
             (* Partial application of an equivalence relation.
                The result has type domty -> Stable.        *)
             wildName(), domty, L.PropArrow(wildName(),domty,L.StableProp) 
        | _ -> E.wrongPropTypeError expr1 pt1 "predicate" orig_expr  in
      let trm2' = 
        try
          LR.coerce cntxt trm2 ty2 domty 
        with E.TypeError msgs -> 
          E.specificateError msgs (E.tyMismatchMsg expr2 domty ty2) in
      let sub = L.insertTermvar L.emptysubst nm trm2' in
      ResProp( L.PApp(prp1, trm2'), L.substProptype sub codpt )
    end
        
  | ResSet(st1,knd1), ResTerm(trm2,ty2) ->
    (* Application of a parameterized set to a term *)
    begin
      let nm, domty, codknd = 
        match knd1 with
          L.KindArrow(nm,domty,codknd) -> nm, domty, codknd
        | _ -> E.wrongKindError expr1 knd1 "arrow" orig_expr  in
      let trm2' = 
        try 
          LR.coerce cntxt trm2 ty2 domty
        with E.TypeError msgs -> 
          E.specificateError msgs (E.tyMismatchMsg expr2 domty ty2)  in
      let sub = L.insertTermvar L.emptysubst nm trm2' in
      ResSet( L.SApp(st1, trm2'),  L.substSetkind sub codknd )
    end
        
  | (ResTerm(trm1,ty1), ResTerm(trm2,ty2)) -> 
    (* Application of a term to a term *)
    begin
      let trm1', nm, domty, codty =
        match LR.coerceFromSubset cntxt trm1 ty1 with
          (trm1', L.Exp(nm,domty,codty)) -> trm1', nm, domty, codty
        | _ -> E.wrongTypeError expr1 ty1 "function" orig_expr   in
      let trm2' = 
        try
          LR.coerce cntxt trm2 ty2 domty
        with E.TypeError msgs -> 
          E.specificateError msgs (E.tyMismatchMsg expr2 domty ty2)  in
      let sub = L.insertTermvar L.emptysubst nm trm2' in
      ResTerm( L.App(trm1', trm2'),   L.substSet sub codty )
    end

  | (ResModel(mdl1,thry1), ResModel(mdl2,thry2)) ->
    (* Application of a model to an argument. *)
      begin
        let nm1, thry1a, thry1b =
          match LR.hnfTheory cntxt thry1 with
          | L.TheoryArrow((nm1, thry1a), thry1b) -> nm1, thry1a, thry1b
          | _ -> E.wrongTheoryError expr1 thry1 "arrow" orig_expr  in
        let reqs = 
          try 
            LR.checkModelConstraint cntxt mdl2 thry2 thry1a 
          with 
            E.TypeError msgs -> 
              E.specificateError msgs (E.theoryMismatchMsg expr2 thry1a thry2) in
        let _ = if (reqs <> []) then
            (* XXX.  There are non-trivial assurances required, but
               we have no good place to put them in the model we are
               returning. *)
            failwith "UNIMPLEMENTED annotateApp/ResModel"  in
        let subst = L.insertModelvar L.emptysubst nm1 mdl2 in
        let thry = L.substTheory subst thry1b in
        ResModel( L.ModelApp(mdl1, mdl2), thry)
      end
      
  | ResTheory(thry1,L.TheoryKindArrow ((nm3,_),tk1)), ResModel(mdl2,thry2) ->
    (* Application of a theory to an argument. *)
    begin
      let nm1, thry1a, thry1b = 
        match LR.hnfTheory cntxt thry1 with
        | L.TheoryLambda((nm1, thry1a), thry1b) -> nm1, thry1a, thry1b
        | _ -> E.wrongTheoryError expr1 thry1 "parameterized theory" orig_expr  in
      let reqs = 
        try 
          LR.checkModelConstraint cntxt mdl2 thry2 thry1a
        with 
          E.TypeError msgs -> 
            E.specificateError msgs (E.theoryMismatchMsg expr2 thry1a thry2) in
      let _ = if (reqs <> []) then
          (* XXX.  There are non-trivial assurances required, but
             we have no good place to put them in the theory we are
             returning. *)
          failwith "UNIMPLEMENTED annotateApp/ResTheory"  in
      let sub = L.insertModelvar L.emptysubst nm3 mdl2 in
      let tk = L.substTheoryKind sub tk1 in
      ResTheory( L.TheoryApp(thry1, mdl2), tk)
    end

  | ResTheory(thry1, _), _ ->
      begin
        match LR.hnfTheory cntxt thry1 with
          | L.TheoryArrow _ ->
              E.tyGenericError 
                ("Application of theory *arrow* to an argument; " ^ 
                 "was a function intended?")
          | _ -> E.tyGenericError ("Invalid application " ^
              string_of_expr orig_expr)
      end

  | _ -> E.tyGenericError ("Invalid application " ^ string_of_expr orig_expr) 

(* Lambda(binding1, expr2) *)
and annotateLambda cntxt orig_expr binding1 expr2 = 
  match annotateBinding cntxt orig_expr binding1 with
    (cntxt', [], lbnds1) ->
      (* Bindings for term-variables only *)
      begin
        match annotateExpr cntxt' expr2 with
        | ResProp(prp2,pt2) ->
            (* Defining a predicate *)
            ResProp ( List.fold_right L.fPLambda   lbnds1 prp2,
                      List.fold_right L.fPropArrow lbnds1 pt2 )
        | ResSet (st2,knd2) ->
            (* Defining a family of sets *)
            ResSet ( List.fold_right L.fSLambda   lbnds1 st2,
                     List.fold_right L.fKindArrow lbnds1 knd2 )
          
        | ResTerm(trm2,ty2) -> 
            (* Defining a function term *)
            ResTerm ( List.fold_right L.fLambda lbnds1 trm2,
                      List.fold_right L.fExp    lbnds1 ty2 )
        
        | _ ->
            E.notWhatsExpectedInError expr2 
              "proposition, set, or term" orig_expr
      end

  | (cntxt', mbnds, []) ->
    (* Bindings for model-variables only *)
    begin
      match annotateExpr cntxt' expr2 with 
        ResTheory (thry, tknd) ->
          ResTheory( L.foldTheoryLambda mbnds thry,
                     L.foldTheoryKindArrow mbnds tknd)
      | _ -> 
        E.tyGenericError ("Cannot have model parameters in " ^ 
          string_of_expr orig_expr)
    end

    | _ ->
      (* Bindings for both term variables and model variables *)
      E.tyGenericError
        ("Cannot have model and term parameters in " ^ 
         string_of_expr orig_expr)

(* Arrow(nm, expr1, expr2) *)
and annotateArrow cntxt orig_expr nm expr1 expr2 =
  let (cntxt, nm) = LR.renameBoundVar cntxt nm in
  match annotateExpr cntxt expr1 with
  | ResPropType _ ->
      E.noHigherOrderLogicError orig_expr
  | ResKind _ ->
      E.noPolymorphismError orig_expr
  | ResSet (_, L.KindArrow _) 
  | ResModel _ | ResTheory(_, L.TheoryKindArrow _)
  | ResProp (_, (L.PropArrow _ | L.EquivProp _) )
  | ResSentence _ ->
    if (isWild nm) then
      E.notWhatsExpectedInError expr1 "proper type, proposition, or boolean" orig_expr
    else 
      E.notWhatsExpectedInError expr1 "proper type" orig_expr 
   
  | ResTerm _ ->
    if (isWild nm) then
      let trm1 = try
                    maybeAnnotateBoolTerm cntxt expr1 
                 with NotBoolTerm ->
                    E.notWhatsExpectedInError expr1 "boolean" orig_expr  in
      let trm2 = try
                    maybeAnnotateBoolTerm cntxt expr2 
                 with NotBoolTerm ->
                    E.notWhatsExpectedInError expr2 "boolean" orig_expr  in
      ResTerm ( L.BOp(L.ImplyOp, [trm1;trm2]), L.Bool)
    else
      E.notWhatsExpectedInError expr1 "proper type" orig_expr 
         
  | ResProp (prp1, (L.Prop | L.StableProp)) -> 
    if (isWild nm) then
      (* Typechecking an implication *)
      let (prp2, stab2) = annotateProperProp cntxt orig_expr expr2 in
      (* case.pdf: "Almost negative formulas [are]
         built from any combination of 
         /\, ->, forall, =, and those
                           bas ic predicates known to be stable, but 
         \/ and exists are only allowed to appear 
         on the left side of a -> ..." *) 
      ResProp ( L.Imply(prp1, prp2),  stab2 )
    else
      E.tyGenericError "Implications cannot have a named premise"

  | ResSet (ty1, L.KindSet) ->
    (* Typechecking a (possibly dependent) set arrow (i.e., a Pi) *)
    begin
      let cntxt' = LR.insertTermVariable cntxt nm ty1 None in
      match annotateExpr cntxt' expr2 with
        ResSet(st2, knd2) -> 
          (* Typechecking a dependent type of a function *)
          ResSet ( L.Exp (nm, ty1, st2),  L.KindSet )
      | ResPropType(pt2) -> 
          (* Typechecking a dependent type of a proposition *)
          ResPropType( L.PropArrow(nm, ty1, pt2) )
      | ResKind(knd2) ->
          (* Typechecking a dependent kind of a family of sets *)
          ResKind( L.KindArrow(nm, ty1, knd2) )
      | _ ->
          E.notWhatsExpectedInError expr2
            "set, proposition-type, or kind" orig_expr
    end
    
  | ResTheory(thry1, L.ModelTheoryKind) ->
    (* Typechecking a (possibly dependent) theory kind *)
    begin
      let cntxt' = LR.insertModelVariable cntxt nm thry1 in
      match annotateExpr cntxt' expr2 with
        ResTheory(thry2, L.ModelTheoryKind) ->
          ResTheory(L.TheoryArrow((nm, thry1), thry2),  L.ModelTheoryKind) 
      | _ -> 
          E.notWhatsExpectedInError expr2 "theory" orig_expr
    end

and annotateLet cntxt orig_expr sbnd1 expr2 expr3 =
  (* Right now, let-bound variables can only be terms *)
  let (trm2, ty2) = annotateTerm cntxt orig_expr expr2 in

  let (cntxt', (nm1,ty1)) = 
      (* Careful with error messages; nm1 might have been renamed *)

      (* XXX term definitions missing from cntxt', since
         annotateSimpleBinding doesn't know the definition... *)
      annotateSimpleBindingWithDefault cntxt orig_expr ty2 sbnd1 in

  let trm2' =  
    try 
      LR.coerce cntxt trm2 ty2 ty1 
    with 
      E.TypeError msgs ->
        E.specificateError msgs (E.tyMismatchMsg expr2 ty1 ty2)   in

  match annotateExpr cntxt' expr3 with
    ResTerm(trm3,ty3) ->
      let ty3' = 
        (* Eliminate dependencies. *)
        (* A SLet would be nicer here. *)
        L.substSet (L.insertTermvar L.emptysubst nm1 trm2') ty3  in
      ResTerm ( L.Let ((nm1,ty1), trm2', trm3, ty3),   ty3' )
  | ResProp(prp3,pt3) ->
      let pt3' = 
        (* Eliminate dependencies. *)
        L.substProptype (L.insertTermvar L.emptysubst nm1 trm2') pt3  in
      ResProp(L.PLet((nm1,ty1), trm2', prp3),  pt3')
  | _ ->
      E.tyGenericError ("Let body is not a term or proposition")


(* Constraint(expr1, expr2) *)
and annotateConstraint cntxt orig_expr expr1 expr2 =
  match (annotateExpr cntxt expr1, annotateExpr cntxt expr2) with
    (ResTerm(trm1,ty1), ResSet(ty2,L.KindSet)) ->
      (* Typecheck a term constrained by a type *)
      begin
        try 
          ResTerm(LR.coerce cntxt trm1 ty1 ty2,  ty2)
        with 
          E.TypeError msgs ->  (* LR.coerce must have failed *)
            E.specificateError msgs (E.tyMismatchMsg expr1 ty2 ty1)
      end

  | (ResProp(prp1, ( (L.PropArrow(nm1a, st1a, L.PropArrow(_, st1b,  L.StableProp))) as pt1) ), 
     ResPropType( (L.EquivProp st2) as pt2 ) ) ->
      (* Special case of coercion into an equivalence relation!*)
      begin
        let (cntxt, nm1a) = LR.renameBoundVar cntxt nm1a in
        let cntxt' = LR.insertTermVariable cntxt nm1a st1a None in
        try
          (** XXX Is this enough to make translate happy about
              using prp1 as an equivalence relation? *)
          let reqs = (LR.subSet cntxt st2 st1a) @ 
                     (LR.subSet cntxt' st2 st1b) @ 
                     [L.IsEquiv(prp1, st2)] in
          ResProp(L.maybePAssure reqs prp1,  L.EquivProp(st2))
        with
          E.TypeError msgs -> (* LR.subSet must have failed *)
            E.specificateError msgs (E.propTypeMismatchMsg expr1 pt2 pt1)
      end

    | (ResProp(prp1,pt1), ResPropType(pt2)) ->
      (* Typecheck a proposition constrained by a prop. type *)
      begin
        try
          let reqs = LR.subPropType cntxt pt1 pt2 in
          ResProp( L.maybePAssure reqs prp1, pt2 )
        with
          E.TypeError msgs -> (* LR.subPropType must have failed *)
            E.specificateError msgs (E.propTypeMismatchMsg expr1 pt2 pt1)
      end

    | (ResSet(st1,knd1), ResKind(knd2)) ->
      (* Typecheck a set constrained by a kind *)
      begin
        try
          let reqs = LR.subKind cntxt knd1 knd2 in
          if (reqs <> []) then
            (* XXX.  We don't have a way to embed assurances into
               the set we're returning.  *)
            failwith "UNIMPLEMENTED: annotateConstrant/ResSet"
          else 
            ResSet(st1, knd2)
        with 
          E.TypeError msgs -> (* subKind must have failed *)
            E.specificateError msgs (E.kindMismatchMsg expr1 knd2 knd1)
      end

    | (ResModel(mdl1,thry1), ResTheory (thry2, L.ModelTheoryKind)) ->
      (* Typecheck a model constrained by a theory *)
      begin
        try
          let reqs = LR.checkModelConstraint cntxt mdl1 thry1 thry2
          in if (reqs <> []) then
            (* XXX.  We don't have a way to embed assurances into
               the model we're returning. *)
            failwith "UNIMPLEMENTED: annotateConstrant/ResModel"
          else
            ResModel(mdl1, thry2)  
        with 
          E.TypeError msgs -> (* LR.checkModelConstraint must have failed *)
            E.specificateError msgs 
              (E.tyGenericError "Module constraint failed")
      end

    | (ResModel _, ResTheory _) -> 
      E.tyGenericError "Can't constrain a model by a family of theories"

    | _ -> E.tyGenericError 
      ("Incoherent constraint " ^ string_of_expr orig_expr)

(* Quotient(expr1, expr2) *)
and annotateQuotient cntxt orig_expr expr1 expr2 = 
  match (annotateExpr cntxt expr1, annotateProp cntxt orig_expr expr2) with
    ResSet(ty1, L.KindSet), (prp2, L.EquivProp(domty2)) -> 
      (* Quotient of a set *)
      begin
        try 
          let reqs = LR.subSet cntxt ty1 domty2 in
          ResSet( L.Quotient (ty1, L.maybePAssure reqs prp2),
                  L.KindSet )
        with
          E.TypeError msgs -> (* LR.subSet must have failed *)
            E.specificateError msgs (E.notEquivalenceOnMsg expr2 expr1)
      end
      
  | ResTerm(trm1, ty1), (prp2, L.EquivProp(domty2)) ->
    (* Quotient [equivalence class] of a term *)
    begin
      try
        let trm1' = LR.coerce cntxt trm1 ty1 domty2 in
        ResTerm( L.Quot (trm1', prp2),
                 L.Quotient (domty2, prp2) )
      with 
        E.TypeError msgs -> (* LR.coerce must have failed *)
          E.specificateError msgs
            (E.notEquivalenceOnMsg expr2 expr1)

    end

  | (ResSet _ | ResTerm _), _ -> 
    (* First part is a set or a term, so the relation must not
       have been an equivalence. *)
    E.notWhatsExpectedInError expr2 "equivalence relation" orig_expr
      
  | _ -> 
    (* First part wasn't even a set or a term *)
    E.notWhatsExpectedInError expr1 "term or proper set" orig_expr

(* Case(expr1, arms2) *)
and annotateCase cntxt orig_expr expr1 arms2 =
  (* Typecheck the term being cased on *)
  let (trm1, ty1) = annotateTerm cntxt orig_expr expr1 in

  (* Typecheck each arm individually *)   
  let annotateArm = function
    | (lbl, None, expr3) -> 
        (lbl, None, annotateExpr cntxt expr3, expr3)
    | (lbl, Some sbnd, expr3) ->
        let (cntxt', lbnd) = annotateSimpleBinding cntxt orig_expr sbnd in
        (lbl, Some lbnd, annotateExpr cntxt' expr3, expr3) in
  let arms2' = List.map annotateArm arms2 in

  (* Check that there are no duplicate labels *)
  let lbls = List.map (fun (l,_,_) -> l) arms2 in
  let _ = if (noDuplicates lbls) then () 
          else E.tyGenericError( "There are duplicate labels in " ^ 
                                 string_of_expr orig_expr)  in

  (* Check that the bindings match the term being cased on. *)
  let rec createSumtype = function
      [] -> []
    | (lbl, None,_,_)::rest -> (lbl,None) :: createSumtype rest
    | (lbl, Some(_,ty),_,_)::rest -> (lbl, Some ty) :: createSumtype rest  in
  let armty = L.Sum (createSumtype arms2')  in
  let reqs1 = 
    try 
      LR.subSet cntxt ty1 armty
    with 
      E.TypeError msgs -> 
        E.specificateError msgs (E.tyMismatchMsg expr1 armty ty1)  in

  match arms2' with
  | (_,_,ResTerm _,_)::_ ->
      (* Term-level Case *)
      let rec process = function
        | [] -> ([], [])
        | (lbl, None, ResTerm(trm3,ty3), _)::rest -> 
            let (arms, tys) = process rest in
            ( (lbl,None,trm3) :: arms, ty3 :: tys )
        | (lbl, (Some (nm,_) as bopt), ResTerm(trm3,ty3), expr3) :: rest ->
            if (NameSet.mem nm (L.fnSet ty3)) then
              E.cantElimError nm ty3 expr3
            else
              let (arms, tys) = process rest in
              ( (lbl,bopt,trm3) :: arms, ty3 :: tys )
        | (lbl,_,_,_)::_ -> 
            E.tyGenericError ( "Bad case arm " ^ string_of_label lbl ^
                               " in " ^ string_of_expr orig_expr)  in
     let (arms, tys) = process arms2' in
     let (ty,reqs2) = LR.joinTypes cntxt tys in
     let trm = L.Case (trm1, armty, arms, ty) in
     let trm' = L.maybeAssure (reqs1@reqs2) trm ty in
     ResTerm(trm', ty)

  | (_,_,ResProp _, _)::_ ->
      (* Prop-level Case *)
      let rec process = function
        | [] -> ([], [])
        | (lbl, None, ResProp(prp3,pt3), _)::rest -> 
            let (arms, pts) = process rest in
            ( (lbl,None,prp3) :: arms, pt3 :: pts )
        | (lbl, (Some (nm,_) as bopt), ResProp(prp3,pt3), expr3) :: rest ->
            if (NameSet.mem nm (L.fnProptype pt3)) then
              E.cantElimPTError nm pt3 expr3
            else
              let (arms, pts) = process rest in
              ( (lbl,bopt,prp3) :: arms, pt3 :: pts )
        | (lbl,_,_,_)::_ -> 
            E.tyGenericError ("Bad case arm " ^ string_of_label lbl ^
                              " in " ^ string_of_expr orig_expr)   in
      let (arms, pts) = process arms2' in
      let (pt,reqs2) = LR.joinPropTypes cntxt pts in
      let prp = L.PCase (trm1, armty, arms) in
      let prp' = L.maybePAssure (reqs1@reqs2) prp in
      ResProp(prp', pt)

   | _::_ ->
      E.tyGenericError ("Invalid first case in " ^ string_of_expr orig_expr)
      
   | _ ->
      E.tyGenericError ("Case must have at least one arm")

and annotateTerm cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResTerm(trm, ty) -> (trm, ty)
  | _ -> E.notWhatsExpectedInError expr "term" surrounding_expr

and maybeAnnotateBoolTerm cntxt expr =
  match annotateExpr cntxt expr with
  | ResTerm(trm, ty) ->
      (try 
         let reqs = LR.eqSet cntxt ty L.Bool 
         in L.maybeAssure reqs trm L.Bool 
       with 
         E.TypeError _ -> raise NotBoolTerm)
  | _ -> raise NotBoolTerm
    
and annotateSet cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResSet(st, knd) -> (st, knd)
  | _ -> E.notWhatsExpectedInError expr "set" surrounding_expr
    
and annotateType cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResSet(st, L.KindSet) -> st
  | _ -> E.notWhatsExpectedInError expr "proper type" surrounding_expr
    
and annotateProp cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResProp(prp, pt) -> (prp, pt)
  | ResTerm(trm, ty) ->
      (try 
         let reqs = LR.eqSet cntxt ty L.Bool 
         in (L.PBool (L.maybeAssure reqs trm L.Bool), L.StableProp) 
       with NotBoolTerm ->
          E.notWhatsExpectedInError expr "proposition" surrounding_expr)
  | _ -> E.notWhatsExpectedInError expr "proposition" surrounding_expr
    
and annotateProperProp cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResProp(prp, ((L.Prop | L.StableProp) as pt)) -> (prp, pt)
  | ResProp _ -> 
      E.notWhatsExpectedInError expr "proper proposition" surrounding_expr
  | ResTerm(trm, ty) ->
      (try 
         let reqs = LR.eqSet cntxt ty L.Bool 
         in (L.PBool (L.maybeAssure reqs trm L.Bool), L.StableProp) 
       with NotBoolTerm ->
          E.notWhatsExpectedInError expr "proper proposition" surrounding_expr)
  | _ -> E.notWhatsExpectedInError expr "proper proposition" surrounding_expr

and annotateKind cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResKind k -> k
  | _ -> E.notWhatsExpectedInError expr "kind" surrounding_expr

and annotateProptype cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResPropType k -> k
  | _ -> E.notWhatsExpectedInError expr "proposition-type" surrounding_expr
    
and annotateModel cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResModel(mdl, thry) -> (mdl, thry)
  | _ -> E.notWhatsExpectedInError expr "model" surrounding_expr

and annotateTheory cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResTheory(thry, tknd) -> (thry, tknd)
  | _ -> E.notWhatsExpectedInError expr "theory" surrounding_expr

and annotateModelTheory cntxt surrounding_expr expr = 
  match annotateExpr cntxt expr with
  | ResTheory(thry, L.ModelTheoryKind) -> thry
  | _ -> E.notWhatsExpectedInError expr "theory of a model" surrounding_expr



(* annotateBinding: context -> expr -> binding -> L.binding list
  
   A binding consists of a bunch of pairs; each pair contains a list of
   variables and a single set or theory.  So, the code has an outer loop 
   over the pairs, and an inner loop over the variables in that pair.
     
*)
and annotateBinding cntxt surrounding_expr binders =
  (* Loop over variable-list/type pairs *)
  let rec bLoop cntxt' = function
    | []                   -> (cntxt', [], [])
    | ([],_)::rest         -> bLoop cntxt' rest
    | (nms, expropt)::rest ->
        (* Now loop to create this pair's bindings and extended context *)
        let rec nLoop cntxt0 = function 
        | [] -> (cntxt0, [], [])
        | n::ns -> 
            let doTypeBinding ty =
              let (cntxt0', n) = LR.renameBoundVar cntxt0 n in
              let cntxt0'' = LR.insertTermVariable cntxt0' n ty None in
              let (cntxt0''', mbnds, lbnds) = nLoop cntxt0'' ns in
              (cntxt0''', mbnds, (n,ty) :: lbnds)      in

            let doTheoryBinding thry =
              let (cntxt0', n) = LR.renameBoundVar cntxt0 n in
              let cntxt0'' = LR.insertModelVariable cntxt0' n thry in
              let (cntxt0''', mbnds, lbnds) = nLoop cntxt0'' ns in
              if (lbnds = []) then
                (cntxt0''', (n,thry)::mbnds, lbnds)
              else
                E.innerModelBindingError surrounding_expr    in
                
            match expropt with
            | None -> 
              begin
                (* No type annotation; hope the variable was
                   declared in an Implicit *)
                match LR.lookupImplicit cntxt n with
                | Some(L.DeclTerm(_, ty)) ->  doTypeBinding ty
                | Some(L.DeclModel thry) -> doTheoryBinding thry
                | None -> E.noTypeInferenceInError n surrounding_expr
                | Some(L.DeclSet _) -> E.noPolymorphismError surrounding_expr
                | Some(L.DeclProp _) -> E.noHigherOrderLogicError surrounding_expr
                | Some(L.DeclTheory _ | L.DeclSentence _) ->
                  (* Can't implicitly declare a theory name
                     or a sentence *)
                  raise Impossible
            end
          | Some expr ->
            begin
              (* Explicitly-annotated binding *)
              match annotateExpr cntxt0 expr with
              | ResSet( ty, L.KindSet ) -> doTypeBinding ty
              | ResTheory (thry, L.ModelTheoryKind) -> doTheoryBinding thry
              | _ -> E.illegalBindingError n expr surrounding_expr
            end      in
    let (cntxt'', mbnds, lbnds) = nLoop cntxt' nms  in
    
    (* Now handle the rest of the pairs *)
    let (cntxt_final, mbnds_rest, lbnds_rest) = bLoop cntxt'' rest in

    (* Combine results *)
    if (lbnds = [] || mbnds_rest = []) then     
      (cntxt_final, mbnds @ mbnds_rest, lbnds @ lbnds_rest)
    else
      E.innerModelBindingError surrounding_expr     in
  bLoop cntxt binders

(* An inner binding is just an ordinary binding list that should 
   bind only term-variables *)
and annotateInnerBinding cntxt surrounding_expr binders = 
  match annotateBinding cntxt surrounding_expr binders with
      (cntxt', [], lbnds) -> (cntxt', lbnds)
    | _ -> E.innerModelBindingError surrounding_expr

(*
   annotateSimpleBinding : context -> expr -> binding1 -> L.binding
   
   A "simple" binding is just a name/type-option pair.
*)
and annotateSimpleBinding cntxt surrounding_expr (nm, expropt) =
  match annotateInnerBinding cntxt surrounding_expr [([nm], expropt)] with
  | (cntxt', [lbnd]) -> (cntxt', lbnd)
  | _ -> raise Impossible (* Impossible unless annotateInnerBinding's buggy *)

(** Like annotatebinding, but takes a (previously annotated) default set to
    be used if one is not implicitly specified in the binding or
    specified in an implicit declaration.

    Raises an error (indirectly) if the set in the binding is ill-formed
*)
and annotateSimpleBindingWithDefault cntxt surrounding_expr default_ty =
  function
      (nm, None) -> 
  begin
    (** There's a reasonable argument to say that the default_ty
              should always be used, since it's most likely to get the
              input to typecheck.  On the other hand, if you say that n
              ranges over integers unless otherwise specified, and you
              bind it to a boolean, an error seems likely... *)
    let ty = 
      match (LR.lookupImplicit cntxt nm) with
    Some(L.DeclTerm(_, implicit_ty)) -> implicit_ty
        | _                                -> default_ty
    in let (cntxt, nm) = LR.renameBoundVar cntxt nm
    in let cntxt' = LR.insertTermVariable cntxt nm ty None
    in 
         (cntxt',  (nm, ty) )
  end

    | (nm, Some expr) -> 
  let ty = annotateType cntxt surrounding_expr expr
  in let (cntxt, nm) = LR.renameBoundVar cntxt nm
  in 
       (* NB:  No checking of binding annotation vs default! *)
    (LR.insertTermVariable cntxt nm ty None,  (nm, ty) )

(* We explicitly do _not_ rename bound variables in
   annotateTheoryElem, as they will eventually become labels.  Thus, a
   Definition or a Value declaration is not permitted to shadow an
   earlier definition, which can only be an earlier top-level or
   theory-element definition.
*)
and annotateTheoryElem cntxt orig_elem = 
  try
    match orig_elem with
      | Definition(nm1, expropt2, expr3) -> 
    annotateDefinition cntxt orig_elem nm1 expropt2 expr3
      | Value (sentence_type, values) ->
          annotateValue cntxt orig_elem sentence_type values
      | Comment c    -> [L.Comment c]
      | Include expr -> annotateInclude cntxt orig_elem expr
      | Implicit _   -> raise Impossible (* Implicits were already removed *)
  with
      E.TypeError msgs ->
        E.generalizeError msgs (E.inElemMsg orig_elem)

(* Include expr *)
and annotateInclude cntxt orig_elem expr =
  let badTheory () = 
    E.tyGenericError ("Theory " ^ string_of_expr expr ^ "can't be included") in
  match annotateTheory cntxt expr(*XXX*) expr with
  | (thry, L.ModelTheoryKind) ->
    begin
      match LR.hnfTheory cntxt thry with
      | L.Theory elems -> elems
      | _ -> badTheory()  (* Must be a theory for a family of models *)
    end
  | _ -> badTheory() (* Must be a parameterized theory *)

(* Value(sentence_type, values) *)
and annotateValue cntxt orig_elem sentence_type values =
  let process res nm = 
     let nm', decl = match res with
       | ResSet(ty, L.KindSet) -> nm, L.DeclTerm(None, ty)
       | ResPropType pt        -> nm, L.DeclProp(None, pt)
       | ResKind k             -> nm, L.DeclSet (None, k)
       | ResTheory (thry, L.ModelTheoryKind) -> nm, L.DeclModel(thry)
       | ResProp(prp, (L.Prop | L.StableProp)) -> 
           (* refresh *) nm, L.DeclSentence([], prp)
       | ResSentence(mbnds, prp) ->  
           (* refresh *) nm, L.DeclSentence(mbnds, prp)
       | ResSet _ | ResTerm _ | ResProp _ | ResModel _ | ResTheory _ -> 
          E.tyGenericError 
          ("Invalid classifier for " ^ string_of_name nm ^
           " in " ^ string_of_theory_element orig_elem)   in
     L.Declaration(nm', decl) in
  let rec loop cntxt = function
    | [] -> []
    | (nms,expr)::rest ->
        let res = annotateExpr cntxt expr  in
        let elems = List.map (process res) nms  in
        let cntxt', elems' = LR.updateContextForElems cntxt elems  in
        elems' @ (loop cntxt' rest)      in
  loop cntxt values

(* Definition(nm1, expropt2, expr3) *)
and annotateDefinition cntxt orig_elem nm1 expropt2 expr3 =
  match annotateExpr cntxt expr3 with
  | ResTerm(trm3, ty3) ->
    begin
      (* Definition of a term constant *)
      match expropt2 with
      | None -> [ L.Declaration(nm1, L.DeclTerm(Some trm3, ty3)) ]
      | Some expr2 ->
          let ty2 = annotateType cntxt (Ident nm1) expr2  in
            try 
              let trm3' = LR.coerce cntxt trm3 ty3 ty2 in
              [ L.Declaration (nm1, L.DeclTerm(Some trm3', ty2)) ]
            with 
              E.TypeError _ -> (* LR.coerce must have failed *)
                E.tyMismatchError expr3 ty2 ty3 (Ident nm1)
    end 

  | ResSet(st3, k3) ->
    begin
      (* Definition of a set constant *)
      match expropt2 with
      | None -> [ L.Declaration(nm1, L.DeclSet(Some st3, k3)) ]
      | Some expr2 ->
          let k2 = annotateKind cntxt (Ident nm1) expr2  in
          try
            let reqs = LR.subKind cntxt k3 k2  in 
            let _ = if reqs <> [] then
                       (* XXX *)
                       failwith "UNIMPLEMENTED: annotateTheoryElem"   in
            [ L.Declaration(nm1, L.DeclSet(Some st3, k2)) ]
          with
            E.TypeError _ -> (* LR.subKind must have failed *)
              E.kindMismatchError expr3 k2 k3 (Ident nm1)
    end

  | ResProp(prp3, pt3) ->
    begin
      (* Definition of a propositional constant *)
      match expropt2 with
      | None  -> [ L.Declaration(nm1, L.DeclProp(Some prp3, pt3)) ]
      | Some expr2 ->
          let pt2 = annotateProptype cntxt (Ident nm1) expr2  in
          try
            let reqs = LR.subPropType cntxt pt3 pt2 in
            let prp3' = L.maybePAssure reqs prp3 in
            [ L.Declaration(nm1, L.DeclProp(Some prp3', pt2)) ]
          with
            E.TypeError _ -> (* LR.subPropType must have failed *)
              E.propTypeMismatchError expr3 pt2 pt3 (Ident nm1)
    end

  | ResTheory (thry3, tknd3) ->
    begin
      (* Definition of a theory *)
      match expropt2 with
      | None -> [ L.Declaration(nm1, L.DeclTheory(thry3, tknd3)) ]
      | Some _ ->
          E.tyGenericError ("A theory definition cannot have a constraint")
    end

  | ResPropType _ | ResKind _ | ResModel _ | ResSentence _ ->
      E.tyGenericError 
          ("Invalid right-hand-side in " ^ string_of_theory_element orig_elem)


(* context * elem list -> context * L.elem list *)
and annotateTheoryElems cntxt = function
    [] -> cntxt, []

  | Implicit(names, expr)::rest ->    
      (** "implicit" declarations are eliminated here *)
      let cntxt' = 
        match annotateExpr cntxt expr with
        | ResSet(ty, L.KindSet) -> 
            LR.insertImplicits cntxt names (L.DeclTerm(None, ty))
        | ResKind knd ->
            LR.insertImplicits cntxt names (L.DeclSet(None, knd))
        | ResTheory (thry, L.ModelTheoryKind) ->
            LR.insertImplicits cntxt names (L.DeclModel thry)
        | ResPropType pt ->
            LR.insertImplicits cntxt names (L.DeclProp(None, pt))
        | _ -> E.notWhatsExpectedInError expr "classifier" expr    in
      annotateTheoryElems cntxt' rest

  | elem :: rest ->
    (* Anything but "implicit" is handled by annotateTheoryElem *)
      let lelems1 = annotateTheoryElem cntxt elem  in
      let cntxt', lelems1'  = LR.updateContextForElems cntxt lelems1  in
      let cntxt_final, lelems2 = annotateTheoryElems cntxt' rest  in
      cntxt_final, lelems1' @ lelems2
 

and annotateToplevel cntxt = function
  | TopComment c -> (cntxt, L.TopComment c)

  | Theorydef(nm, expr) ->
      let (thry, tknd) = annotateTheory cntxt False(*XXX*) expr  in
      (LR.insertTheoryVariable cntxt nm thry tknd, L.Theorydef(nm, thry))
    
  | TopModel (nm, thry) -> 
      let lthry = annotateModelTheory cntxt False(*XXX*) thry  in
      (LR.insertModelVariable cntxt nm lthry,  L.TopModel(nm, lthry))

and annotateToplevels cntxt = function
    [] -> (cntxt, [])
  | tl::tls -> 
      let cntxt',  tl'  = annotateToplevel cntxt tl  in
      let cntxt'', tls' = annotateToplevels cntxt' tls  in
      cntxt'', tl'::tls'



