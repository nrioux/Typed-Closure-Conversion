module SourceLang
    type Id = string

    type Type =
        | Bool
        | Product of list<Type>
        | Function of Type * Type

    type Expression =
        | Variable of Id
        | True
        | False
        | Tuple of list<Expression>
        | If of Expression * Expression * Expression
        | Application of Expression * Expression
        | Lambda of Id * Type * Expression
        | Projection of int * Expression

    type TypeEnvironment = Map<Id, Type>

    let rec isValue e =
        match e with
        | True -> true
        | False -> true
        | Tuple(items) -> List.fold (fun s expr -> s && isValue expr) true items
        | Lambda(_, _, _) -> true
        | _ -> false

    // Get all unbound variables in the expression
    let freeVariables expr =
        let rec fv bound e =
            match e with
            | Variable(id) ->
                    if List.exists id.Equals bound then 
                        [] else [id]
            | Lambda(id, _, body) ->
                fv (id :: bound) body
            | Tuple(items) ->
                List.collect (fv bound) items
            | If(e1, e2, e3) ->
                (fv bound e1) @ (fv bound e2) @ (fv bound e3)
            | Application(e1, e2) ->
                (fv bound e1) @ (fv bound e2)
            | Projection(_, e1) ->
                (fv bound e1)
            | _ -> []
        fv [] expr
        
    /// Run f on the direct children of e and return the result
    let rec map f e =
        match e with
        | Tuple(items) -> Tuple (List.map f items)
        | If(e1, e2, e3) -> If(f e1, f e2, f e3)
        | Application(e1, e2) ->
            Application(f e1, f e2)
        | Lambda(id, t, body) -> Lambda(id, t, f body)
        | Projection(i, e1) -> Projection(i, f e1)
        | _ -> e

    /// Replace all variables in e with ids that are keys in mapping with their associated values
    let rec substitute mapping e =
        match e with
        | Variable id -> if Map.containsKey id mapping then
                            Map.find id mapping else e
        | _ -> map (substitute mapping) e

    /// Determine the type of the expression e in environment G
    let rec typeOf G e =
        match e with
        | Variable id -> Map.find id G
        | True | False -> Bool
        | Tuple items ->
            items 
            |> List.map (typeOf G)
            |> Product
        | If(_, e1, _) -> typeOf G e1
        | Application(e1, _) ->
             match typeOf G e1 with
             | Function(t1, t2) -> t2
        | Lambda(id, t, body) ->
            Function(t, typeOf (Map.add id t G) body)
        | Projection(i, e1) ->
            match typeOf G e1 with
            | Product(items) -> (List.nth items i) 

    /// Evaluate the given expression
    let rec eval e =
        match e with
        | True | False | Lambda(_, _, _) -> e
        | Tuple items -> 
            Tuple(List.map eval items)
        | If(e1, e2, e3) ->
            match eval e1 with
            | True -> eval e2
            | False -> eval e3
        | Application(e1, e2) ->
            let e1' = eval e1
            let e2' = eval e2
            match e1' with
            | Lambda(x, _, body) ->
                eval (substitute (Map.add x e2' Map.empty) body) 
        | Projection(i, e1) ->
            match e1 with 
            | Tuple(items) -> (eval (List.nth items i))










