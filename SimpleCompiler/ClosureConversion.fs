module ClosureConversion
    let rec translationType t = 
        match t with
        | SourceLang.Bool ->
            TargetLang.Bool
        | SourceLang.Function(t1, t2) ->
            TargetLang.Existential( 
                TargetLang.Product([TargetLang.Function(TargetLang.TypeVariable 0, 
                                                        TargetLang.Function(translationType t1,
                                                                            translationType t2));
                                    TargetLang.TypeVariable 0]))
        | SourceLang.Product(items) ->
            TargetLang.Product(List.map translationType items)
    
    let incValues amt I = Map.map (fun k v -> v + amt) I

    /// Closure converts a source term to a target term
    let rec convertTerm e =
        /// Converts a source term to a target term
        /// with the given mappings from source var name to target De Bruijn index (I)
        /// and the given environment (G).
        let rec convert I G e = 
            match e with
            | SourceLang.Variable(id) ->
                TargetLang.Variable <| Map.find id I
            | SourceLang.True ->
                TargetLang.True
            | SourceLang.False ->
                TargetLang.False
            | SourceLang.Tuple(items) ->
                TargetLang.Tuple(List.map (convert I G) items)
            | SourceLang.If(cond, e1, e2) ->
                TargetLang.If(convert I G cond, convert I G e1, convert I G e2)
            | SourceLang.Application(e1, e2) ->
                let z = TargetLang.Variable 0
                let closure = TargetLang.Projection(0, z)
                let env = TargetLang.Projection(1, z)
                let I' = incValues 1 I
                TargetLang.Unpack(convert I G e1, 
                    TargetLang.ApplicationMulti closure [env; convert I' G e2])
            | SourceLang.Lambda(id, t, e1) ->
                let G' = Map.add id t G
                
                // The free variables in the lambda,
                // which will be added to the environment tuple
                let fv = SourceLang.freeVariables e
                let fvTarg = List.map (fun id -> Map.find id I) fv

                // the type of the environment tuple
                let tenv = fv
                            |> List.map (fun v -> Map.find v G')
                            |> List.map translationType
                            |> TargetLang.Product
                // a tuple of type tenv containing all free variables in the lambda          
                let env = fvTarg
                            |> List.map TargetLang.Variable
                            |> TargetLang.Tuple
                assert (TargetLang.typeCheck 0 G env = tenv)

                // substitute free variables for projections on the env tuple
                let mapping = Map.ofList <| List.zip fvTarg
                                                (List.mapi (fun i _ -> TargetLang.Projection(i, TargetLang.Variable 0)) fv)
                let I' = Map.add id 0 <| incValues 2 I
                
                let inner = TargetLang.substitute mapping <| convert I' G' e1
                let closure = TargetLang.LambdaType(TargetLang.LambdaMulti [TargetLang.TypeVariable 0; translationType t] inner)
                TargetLang.Pack(tenv, 
                                TargetLang.Tuple([TargetLang.ApplicationType(closure, tenv); env]),
                                TargetLang.Product(
                                    [TargetLang.FunctionMulti [TargetLang.TypeVariable 0;
                                                                translationType t]
                                                            <| translationType (SourceLang.typeOf G' e1);
                                    TargetLang.TypeVariable 0]))
            | SourceLang.Projection(i, e1) ->
                TargetLang.Projection(i, convert I G e1)
        convert Map.empty Map.empty e