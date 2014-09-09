module SourceLang
    type Id = uint64

    let mutable lastid : uint64 = 0UL
    let genId () =
        let result = lastid
        lastid <- lastid + 1UL
        result

    type Type =
        | Bool
        | Product of list<Type>
        | Function of Type * Type

    type Expression =
        /// A bound variable, represented by a De Bruijin index
        | BoundVar of uint32
        /// A free variable, represented by a unique ID
        | FreeVar of Id
        | True
        | False
        | Tuple of list<Expression>
        | If of Expression * Expression * Expression
        | Application of Expression * Expression
        | Lambda of Type * Expression
        | Projection of int * Expression

    type TypeEnvironment = Map<Id, Type>

    let rec isValue e =
        match e with
        | True -> true
        | False -> true
        | Tuple(items) -> List.fold (fun s expr -> s && isValue expr) true items
        | Lambda(_, _) -> true
        | _ -> false

    // Get all unbound variables in the expression
    let rec freeVariables e =
        match e with
        | FreeVar(id) -> [id]
        | Lambda(_, body) ->
            freeVariables body
        | Tuple(items) ->
            List.collect freeVariables items
        | If(e1, e2, e3) ->
            (freeVariables e1) @ (freeVariables e2) @ (freeVariables e3)
        | Application(e1, e2) ->
            (freeVariables e1) @ (freeVariables e2)
        | Projection(_, e1) ->
            (freeVariables e1)
        | _ -> []
                    
    /// Run f on the direct children of e and return the result
    let rec map f e =
        match e with
        | Tuple(items) -> Tuple (List.map f items)
        | If(e1, e2, e3) -> If(f e1, f e2, f e3)
        | Application(e1, e2) ->
            Application(f e1, f e2)
        | Lambda(t, body) -> Lambda(t, f body)
        | Projection(i, e1) -> Projection(i, f e1)
        | _ -> e

    let rec openRecTerm e trm k =
        match e with
        | BoundVar(i) -> if i = k then trm else BoundVar i
        | Lambda(t, body) -> Lambda(t, openRecTerm body trm (k + 1u))
        | _ -> map (fun e' -> openRecTerm e' trm k) e

    let rec openTerm e trm =
        openRecTerm e trm 0u

    let rec openTermWithVar e x =
        openTerm e (FreeVar x)


    /// Replace all variables in e with ids that are keys in mapping with their associated values
    let rec subst e x trm =
        match e with
        | FreeVar(y) -> if x = y then trm else FreeVar(y)
        | _ -> map (fun e' -> subst e' x trm) e

    /// Determine the type of the expression e in environment G
    let rec typeOf G e =
        match e with
        | FreeVar(id) -> Map.find id G
        | True | False -> Bool
        | Tuple items ->
            items 
            |> List.map (typeOf G)
            |> Product
        | If(_, e1, _) -> typeOf G e1
        | Application(e1, _) ->
             match typeOf G e1 with
             | Function(t1, t2) -> t2
        | Lambda(t, body) ->
            let x = genId ()
            Function(t, typeOf 
                <| Map.add x t G
                <| openTermWithVar body x)
        | Projection(i, e1) ->
            match typeOf G e1 with
            | Product(items) -> (List.nth items i) 

    /// Evaluate the given expression
    let rec eval e =
        match e with
        | True | False | Lambda(_, _) -> e
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
            | Lambda(_, body) ->
                eval (openTerm body e2')
        | Projection(i, e1) ->
            match e1 with 
            | Tuple(items) -> (eval (List.nth items i))










