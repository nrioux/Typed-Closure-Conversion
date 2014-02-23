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

    (*let rec filter f e =
        let filterRest = 
            match e with
            | Tuple(items) -> (List.choose f items)
            | If(e1, e2, e3) -> (filter f e1) @ (filter f e2) @ (filter f e3)
            | Application(e1, e2) -> (filter f e1) @ (filter f e2)
            | Lambda(_, _, e1) -> filter f e1
            | Projection(_, e1) -> filter f e1
            | _ -> []
        if (f e) then e :: filterRest else filterRest*)








