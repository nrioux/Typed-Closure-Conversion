module TargetLang
    /// Variables are referened by integer Id's, which are
    /// 0-based De Bruijn indices.
    type Id = int

    type Type =
        | TypeVariable of Id
        | Bool
        /// The type for tuples.
        | Product of list<Type>
        /// The type for functions (lambda expressions).
        /// Takes the number of type arguments, a list of types of arguments, and the return type.
        | Function of int * list<Type> * Type
        | Existential of Type

    type Expression =
        | Variable of Id
        | True
        | False
        | Tuple of list<Expression>
        | If of Expression * Expression * Expression
        | Application of Expression * list<Type> * list<Expression>
        /// A lambda expression representing a function.
        /// Takes the number of type arguments, a list of types of arguments, and a function body.
        /// Note that the last parameter is referened by the De Bruijn index 0, while the first parameter in the 
        /// list is referenced by the highest index.
        | Lambda of int * List<Type> * Expression
        | Projection of int * Expression
        (*pack   <t,     e> as       Ea.   t>*)
        | Pack of Type * Expression * Type
        (*unpack   <a,   x> = e         in e*)
        | Unpack of Expression * Expression

    let rec isValue e =
        match e with
        | True -> true
        | False -> true
        | Tuple(items) -> List.forall isValue items
        | Lambda(_, _, _) -> true
        | Pack(_, e, _) -> isValue(e)
        | _ -> false

    /// Run f on the direct children of e and return the result
    let rec map f e =
        match e with
        | Tuple(items) -> Tuple (List.map f items)
        | If(e1, e2, e3) -> If(f e1, f e2, f e3)
        | Application(e1, typeArgs, args) ->
            Application(f e1, typeArgs, List.map f args)
        | Lambda(id, t, body) -> Lambda(id, t, f body)
        | Projection(i, e1) -> Projection(i, f e1)
        (*pack   <t,     e> as       Ea.   t>*)
        | Pack(t1, e1, t2) -> Pack(t1, f e1, t2)
        (*unpack   <a,   x> = e         in e*)
        | Unpack(e1, e2) -> Unpack(f e1, f e2)
        | _ -> e

    /// Replace variables in e with corresponding indices
    let rec substitute mapping e =
        let incMapping i = mapping
                        |> Map.toList
                        |> List.map (fun (k, v) -> (k + i, v))
                        |> Map.ofList
        let sub = substitute mapping
        match e with
        | Variable id -> if Map.containsKey id mapping then
                            Map.find id mapping else e
        | Lambda(num, args, body) ->
            let sub' = substitute <| incMapping (List.length args)
            Lambda(num, args, sub' body)
        | Unpack(e1, e2) ->
            let sub' = substitute (incMapping 1)
            // e1 is bound to 0 in e2
            Unpack(sub e1, sub' e2)
        | _ ->
            map sub e

    // apply a function to the next element in the list that isn't a value
    let rec applyToNextExpr f items =
        match items with
        | e::tail -> if isValue e then e::(applyToNextExpr f tail)
                     else (f e)::tail
        | [] -> []

    let rec step (e: Expression) =
        match e with
        // values step to themselves
        | True | False | Lambda(_, _, _) -> e

        // Product and existential types are values when all of their components are values
        | Tuple items -> 
            if List.forall isValue items then e
            else Tuple(applyToNextExpr step items)
        | Pack(t, e1, ex_type) ->
            if isValue e1 then e
            else Pack(t, step e1, ex_type)

        | If(True, e1, _) -> e1
        | If(False, _, e2) -> e2
        | If(e1, e2, e3) -> If(step e1, e2, e3)

        | Application(e1, type_args, e2::args) ->
            // step the function or the first argument if either are not values
            if not <| isValue e1 then Application(step e1, type_args, e2::args)
            else if not <| isValue e2 then Application(e1, type_args, (step e2)::args)
            // if both are values, then substitute the first argument into the lambda
            else match e1 with
                    | Lambda(num, t::arg_types, body) ->
                        let body' = substitute (Map.ofList [List.length arg_types, e2]) body
                        Application(Lambda(num, arg_types, body'), type_args, args) 
        | Application(e1, type_args, _) ->
            // step the function if it isn't a value
            if not <| isValue e1 then Application(step e1, type_args, [])
            // if the function is a value and takes no arguments, just return its body
            // if it takes some arguments, return the function itself when it is nothing
            else match e1 with
                | Lambda(_, _::_, _) -> e1
                | Lambda(_, [], body) -> body

        | Projection(i, e1) ->
            if isValue e1 then
                match e1 with 
                | Tuple(items) -> List.nth items i
            else Projection(i, step e1)

    let rec eval e =
        if isValue e then e
        else eval (step e)