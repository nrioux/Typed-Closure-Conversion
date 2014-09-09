module ClosureConversion
    let rec translationType t = 
        match t with
        | SourceLang.Bool ->
            TargetLang.Bool
        | SourceLang.Function(t1, t2) ->
            TargetLang.Existential( 
                TargetLang.Product([TargetLang.Function(TargetLang.BoundTypeVar 0u, 
                                                        TargetLang.Function(translationType t1,
                                                                            translationType t2));
                                    TargetLang.BoundTypeVar 0u]))
        | SourceLang.Product(items) ->
            TargetLang.Product(List.map translationType items)
    
    let incValues amt I = Map.map (fun k v -> v + amt) I

    /// Closure converts a source term to a target term
    let rec convertTerm e =
        /// Converts a source term to a target term
        /// with the given mappings from free source variables to target term (I)
        /// and the given environment (G).
        let rec convert I G e = 
            match e with
            | SourceLang.FreeVar(id) ->
                TargetLang.FreeVar(Map.find id I)
            | SourceLang.True ->
                TargetLang.True
            | SourceLang.False ->
                TargetLang.False
            | SourceLang.Tuple(items) ->
                TargetLang.Tuple(List.map (convert I G) items)
            | SourceLang.If(cond, e1, e2) ->
                TargetLang.If(convert I G cond, convert I G e1, convert I G e2)
            | SourceLang.Application(e1, e2) ->
                let targ_id = TargetLang.genId ()
                let z = TargetLang.FreeVar targ_id
                let closure = TargetLang.Projection(0, z)
                let env = TargetLang.Projection(1, z)
                let app = TargetLang.closeTerm targ_id 
                              <| TargetLang.ApplicationMulti closure [env; convert I G e2]
                TargetLang.Unpack(convert I G e1, app)
                    
            | SourceLang.Lambda(t, e1) ->
                let src_id = SourceLang.genId ()
                let targ_id = TargetLang.genId ()
                let G' = Map.add src_id t G
                let I' = Map.add src_id targ_id I
                let e1' = SourceLang.openTermWithVar e1 src_id
                
                // The free variables in the lambda,
                // which will be added to the environment tuple
                let fv = SourceLang.freeVariables e
                let fvTarg = List.map (fun id -> TargetLang.FreeVar(Map.find id I)) fv
                 
                // the type of the environment tuple
                let tenv = fv
                            |> List.map (fun v -> Map.find v G)
                            |> List.map translationType
                            |> TargetLang.Product
                // a tuple of type tenv containing all free variables in the lambda          
                let env = TargetLang.Tuple (fvTarg)
                let env_id = TargetLang.genId ()

                // substitute free variables for projections on the env tuple
                let inner = List.fold2
                                  <| fun e' id proj -> TargetLang.subst e' id proj
                                  <| convert I' G' e1'
                                  // a list of ids of free target variables
                                  <| List.map (fun var -> Map.find var I') fv
                                  // a list of projections on the env tuple for the corresponding free variables
                                  <| (List.mapi (fun i _ -> 
                                          TargetLang.Projection(i, TargetLang.FreeVar(env_id))) fv)

                // We have beeen using some free variables as a convenience, but
                // we must now replace these with bound variables
                let innerClosed = inner
                                      |> TargetLang.closeTerm targ_id
                                      |> TargetLang.closeRecTerm env_id 1u

                let closure = TargetLang.LambdaType(
                                  TargetLang.LambdaMulti [tenv; translationType t] innerClosed)
                TargetLang.Pack(tenv,
                                TargetLang.Tuple([TargetLang.ApplicationType(closure, tenv); env]),
                                TargetLang.Product(
                                    [TargetLang.FunctionMulti [TargetLang.BoundTypeVar 0u;
                                                                translationType t]
                                                            <| translationType (SourceLang.typeOf G' e1');
                                    TargetLang.BoundTypeVar 0u]))
            | SourceLang.Projection(i, e1) ->
                TargetLang.Projection(i, convert I G e1)
        convert Map.empty Map.empty e
