module ClosureConversion
    let rec translationType t = 
        match t with
        | SourceLang.Bool ->
            TargetLang.Bool
        | SourceLang.Function(t1, t2) ->
            TargetLang.Existential("A", 
                TargetLang.Product([TargetLang.Function(List.empty, 
                                                        [TargetLang.TypeVariable "A"; 
                                                            translationType t1],
                                                        translationType t2);
                                    TargetLang.TypeVariable "A"]))
        | SourceLang.Product(items) ->
            TargetLang.Product(List.map translationType items)
    
    /// Closure converts a source term to a target term
    let rec convertTerm e = 
        let rec convert G e = 
            match e with
            | SourceLang.Variable(id) ->
                TargetLang.Variable(id)
            | SourceLang.True ->
                TargetLang.True
            | SourceLang.False ->
                TargetLang.False
            | SourceLang.Tuple(items) ->
                TargetLang.Tuple(List.map (convert G) items)
            | SourceLang.If(cond, e1, e2) ->
                TargetLang.If(convert G cond, convert G e1, convert G e2)
            | SourceLang.Application(e1, e2) ->
                let z = TargetLang.Variable "z"
                let closure = TargetLang.Projection(0, z)
                let env = TargetLang.Projection(1, z)
                TargetLang.Unpack("B", "z", convert G e1, 
                    TargetLang.Application(closure, list.Empty,
                                            [env; convert G e2]))

                //TargetLang.Application(convert G e1, List.empty, [convert G e2])
            | SourceLang.Lambda(id, t, e1) ->
                let G' = Map.add id t G
                
                // The free variables in the lambda,
                // which will be added to the environment tuple
                let fv = SourceLang.freeVariables e
                // the type of the environment tuple
                let tenv = fv
                            |> List.map (fun v -> Map.find v G')
                            |> List.map translationType
                            |> TargetLang.Product
                // a tuple of type tenv containing all free variables in the lambda          
                let env = TargetLang.Tuple(List.map TargetLang.Variable fv)                
                
                // substitute free variables for projections on the env tuple
                let mapping = Map.ofList <| List.zip fv 
                                                (List.mapi (fun i _ -> TargetLang.Projection(i, TargetLang.Variable("env"))) fv)
                let body = TargetLang.substitute mapping <| convert G' e1 

                let closure = TargetLang.Lambda(["B"], 
                                                Map.ofList ["env", (TargetLang.TypeVariable "B");
                                                            id, (translationType t)],
                                                body)
                TargetLang.Pack(tenv, 
                                TargetLang.Tuple([TargetLang.Application(closure, [tenv], List.empty); env]),  
                                "A", 
                                TargetLang.Product(
                                    [TargetLang.Function(List.empty, 
                                                            [TargetLang.TypeVariable("A");
                                                                translationType t],
                                                            translationType (SourceLang.typeOf G' e1));
                                    TargetLang.TypeVariable("A")]))
            | SourceLang.Projection(i, e1) ->
                TargetLang.Projection(i, convert G e1)
        convert Map.empty e