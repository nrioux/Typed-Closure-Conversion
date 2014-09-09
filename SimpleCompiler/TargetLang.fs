module TargetLang

    type Id = uint64

    let mutable lastid : uint64 = 0UL
    let genId () =
        let result = lastid
        lastid <- lastid + 1UL
        result

    type Type =
        | BoundTypeVar of uint32
        | FreeTypeVar of Id
        | Bool
        /// The type for tuples.
        | Product of list<Type>
        /// The type for functions (lambda expressions).
        /// Takes the number of type arguments, a list of types of arguments, and the return type.
        | Function of Type * Type
        | Forall of Type
        | Existential of Type

    type Expression =
        /// A bound variable, represented by a De Bruijin index
        | BoundVar of uint32
        /// A free variable, represented by a unique ID
        | FreeVar of Id
        | True
        | False
        | Tuple of list<Expression>
        | If of Expression * Expression * Expression
        | ApplicationTerm of Expression * Expression
        | ApplicationType of Expression * Type
        /// A lambda expression representing a function from a term to a term
        | LambdaTerm of Type * Expression
        /// A lambda expression representing a function from a type to a term
        | LambdaType of Expression
        | Projection of int * Expression
        (*pack   <t,     e> as       Ea.   t>*)
        | Pack of Type * Expression * Type
        (*unpack   <a,   x> = e         in e*)
        | Unpack of Expression * Expression

    let rec formatType t =
        match t with
        | Bool -> "Bool"
        | BoundTypeVar i -> sprintf "BTV(%s)" <| i.ToString()
        | FreeTypeVar id -> sprintf "FTV(%s)" <| id.ToString()
        | Product [] -> "Unit"
        | Product types -> sprintf "<%s>" <| (Util.join " * " <| List.map formatType types)
        | Function(t1, t2) -> sprintf "%s → %s" <| formatType t1 <| formatType t2
        | Existential(t1) -> sprintf "∃.%s" <| formatType t1
        | Forall(t1) -> sprintf "∀.%s" <| formatType t1
        
    let rec formatExpr e =
        match e with
        | True -> "true"
        | False -> "false"
        | Tuple [] -> "unit"
        | Tuple(items) -> 
                let ls = List.map formatExpr items
                sprintf "<%s>" (Util.join ", " ls)
        | If(e1, e2, e3) ->
                sprintf "if %s then %s else %s" <| formatExpr e1 <| formatExpr e2 <| formatExpr e3
        | BoundVar(i) -> sprintf "BOUND(%d)" i
        | FreeVar(id) -> sprintf "FREE(%d)" id
        | LambdaTerm(t, e1) -> sprintf "λ%s.%s" (formatType t) (formatExpr e1)
        | LambdaType(e1) -> sprintf "Λ.%s" (formatExpr e1)
        | ApplicationTerm(e1, e2) -> sprintf "(%s) (%s)" (formatExpr e1) (formatExpr e2)
        | ApplicationType(e1, t) -> sprintf "%s [%s]" (formatExpr e1) (formatType t)
        | Projection(i, tuple) -> sprintf "π%s %s" <| i.ToString() <| formatExpr tuple
        | Pack(t1, e1, t2) -> sprintf "pack <%s, %s> as %s" <| formatType t1 <| formatExpr e1 <| formatType t2
        | Unpack(e1, e2) -> sprintf "unpack %s in %s" <| formatExpr e1 <| formatExpr e2

    let rec ApplicationMulti e1 args =
        match args with
        | [] -> e1
        | e2 :: args' -> ApplicationMulti (ApplicationTerm(e1, e2)) args'

    let rec FunctionMulti argTypes returnType =
        match argTypes with
        | [] -> returnType
        | t :: argTypes' -> Function(t, FunctionMulti argTypes' returnType)

    let rec LambdaMulti argTypes body =
        match argTypes with
        | [] -> body
        | t :: argTypes' -> LambdaTerm(t, LambdaMulti argTypes' body)

    let rec isValue e =
        match e with
        | True -> true
        | False -> true
        | Tuple(items) -> List.forall isValue items
        | LambdaTerm(_) -> true
        | LambdaType(_) -> true
        | Pack(_, e, _) -> isValue(e)
        | _ -> false

    /// Run f on the direct children of e and return the result
    let rec map f e =
        match e with
        | Tuple(items) -> Tuple (List.map f items)
        | If(e1, e2, e3) -> If(f e1, f e2, f e3)
        | ApplicationTerm(e1, e2) ->
            ApplicationTerm(f e1, f e2)
        | ApplicationType(e1, t) ->
            ApplicationType(f e1, t)

        | LambdaTerm(t, body) -> LambdaTerm(t, f body)
        | LambdaType(body) -> LambdaType(f body)

        | Projection(i, e1) -> Projection(i, f e1)
        (*pack   <t,     e> as       Ea.   t>*)
        | Pack(t1, e1, t2) -> Pack(t1, f e1, t2)
        (*unpack   <a,   x> = e         in e*)
        | Unpack(e1, e2) -> Unpack(f e1, f e2)
        | _ -> e

    let rec mapType f t =
        match t with
        | Function(t1, t2) -> Function(f t1, f t2)
        | Product(types) -> Product(List.map (mapType f) types)
        | Forall(body) -> Forall(f body)
        | Existential(body) -> Existential(f body)
        | _ -> t

    let rec openRecTerm trm k e =
        match e with
        | BoundVar(i) -> if i = k then trm else BoundVar i
        | LambdaTerm(t, body) -> LambdaTerm(t, openRecTerm trm (k + 1u) body)
        | Unpack(e1, e2) -> Unpack(openRecTerm trm k e1, openRecTerm trm (k + 1u) e2)
        | _ -> map (openRecTerm trm k) e

    /// Replace the outermost bound variable with a term
    let openTerm trm e =
        openRecTerm trm 0u e

    let openTermWithVar x e =
        openTerm (FreeVar x) e

    let rec openRecType typ k t =
        match t with
        | BoundTypeVar(i) -> if i = k then typ else BoundTypeVar i
        | Forall(body) -> Forall(openRecType typ (k + 1u) body)
        | Existential(body) -> Existential(openRecType typ (k + 1u) body)
        | _ -> mapType (openRecType typ k) t

    let openType typ t =
        openRecType typ 0u t

    let openTypeWithVar alpha t =
        openType (FreeTypeVar alpha) t

    let rec openRecTypeInTerm typ k e =
        match e with
        | LambdaTerm(t, body) -> LambdaTerm(openRecType typ k t, openRecTypeInTerm typ k body)
        | LambdaType(body) -> LambdaType(openRecTypeInTerm typ (k + 1u) body)
        | ApplicationType(e1, t1) -> ApplicationType(openRecTypeInTerm typ k e1, openRecType typ k t1)
        | Pack(t1, e1, t2) -> Pack(openRecType typ k t1, openRecTypeInTerm typ k e1, openRecType typ (k + 1u) t2)
        | _ -> map (openRecTypeInTerm typ k) e

    let openTypeInTerm typ e =
        openRecTypeInTerm typ 0u e

    let rec closeRecTerm x i e =
        match e with
        | FreeVar(y) -> if x = y then BoundVar(i) else FreeVar(y)
        | LambdaTerm(t, body) -> LambdaTerm(t, closeRecTerm x (i + 1u) body)
        | Unpack(e1, e2) -> Unpack(closeRecTerm x i e1, closeRecTerm x (i + 1u) e2)
        | _ -> map (closeRecTerm x i) e

    /// abstract a free variable x, out of the term e
    let rec closeTerm x e =
        closeRecTerm x 0u e


    /// Find type varialbes in term type annotations and substitute them
//    let rec substituteTypeInTerm mapping e =
//        let incMapping = Util.incKeys 1 mapping
//        match e with 
//        | LambdaTerm(t, body) -> LambdaTerm(substituteType mapping t, substituteTypeInTerm mapping body)
//        | LambdaType(body) -> LambdaType(substituteTypeInTerm incMapping body)
//        | Pack(t1, e, t2) -> 
//            Pack(substituteType mapping t1, substituteTypeInTerm mapping e, substituteType incMapping t2)
//        | _ -> map (substituteTypeInTerm mapping) e

    /// Replace variables in e with corresponding indices
//    let rec substitute mapping e =
//        let incMapping = Map.map (fun _ -> liftTerms) <| Util.incKeys 1 mapping
//        let sub = substitute mapping
//        let sub' = substitute incMapping
//        match e with
//        | Variable id -> if Map.containsKey id mapping then
//                            Map.find id mapping else e
//        | LambdaTerm(t, body) ->
//            LambdaTerm(t, sub' body)
//        | LambdaType(body) ->
//            LambdaType(sub body)
//        | Unpack(e1, e2) ->
//            // e1 is bound to 0 in e2
//            Unpack(sub e1, sub' e2)
//        | _ ->
//            map sub e

    let rec subst e x trm =
        match e with
        | FreeVar(y) -> if x = y then trm else FreeVar(y)
        | _ -> map (fun e -> subst e x trm) e

    /// Get the type of a term in the given environment.
    /// D is the number of types in the current type environment.
    /// G is the current value:type environment
    let rec typeCheck D G e =
        System.Diagnostics.Debug.WriteLine(sprintf "typeCheck %A" <| formatExpr e)
        match e with
        | FreeVar id -> Map.find id G
        | True | False -> Bool
        | Tuple items -> Product(List.map (typeCheck D G) items)
        | LambdaTerm(t, body) -> 
            let x = genId ()
            let G' = Map.add x t G
            Function(t, typeCheck D G' (openTermWithVar x body))
        | LambdaType body ->
            Forall (typeCheck (D + 1) G body)
        | Pack(_, _, ex_type) -> Existential(ex_type)

        | Projection(i, e1) ->
            match typeCheck D G e1 with
            | Product(types) -> List.nth types i
        
        | If(e1, e2, e3) ->
            assert (typeCheck D G e1 = Bool)
            let t2 = typeCheck D G e2
//            assert (typeCheck D G e3 = t2)
            t2

        | Unpack(e1, e2) ->
            let ex_type = typeCheck D G e1
            match ex_type with
            | Existential(t) ->
                let x = genId ()
                let G' = Map.add x t G
                typeCheck (D + 1) G' (openTermWithVar x e2)

        | ApplicationTerm(e1, e2) ->
            let t = typeCheck D G e1
            match t with
            | Function(argType, returnType) ->
                // Make sure arguments have the correct types
                //assert (t = typeCheck D G e2)
                returnType

        | ApplicationType(e1, t) ->
            System.Diagnostics.Debug.WriteLine(formatExpr e, "application1")
            let tp = typeCheck D G e1
            System.Diagnostics.Debug.WriteLine(formatType tp, "application2")
            match tp with
            | Forall tbody ->
                openType t tbody

    let getType e = typeCheck 0 Map.empty e

    // apply a function to the next element in the list that isn't a value
    let rec applyToNextExpr f items =
        match items with
        | e::tail -> if isValue e then e::(applyToNextExpr f tail)
                     else (f e)::tail
        | [] -> []

    let rec step (e: Expression) =
        match e with
        // values step to themselves
        | True | False | LambdaTerm _ | LambdaType _ -> e

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

        | Unpack(Pack(tau, e1, _), body) ->
            openTerm e1 body
//            |> substituteTypeInTerm (Map.ofList [0, tau]) 
        | Unpack(e1, e2) -> 
            Unpack(step e1, e2)

        // Application is left-to-right, call-by-value
        | ApplicationTerm(e1, e2) ->
            // step the function or the first argument if either are not values
            if not (isValue e1) then ApplicationTerm(step e1, e2)
            else if not (isValue e2) then ApplicationTerm(e1, step e2)
            // if both are values, then substitute the first argument into the lambda
            else match e1 with
                    | LambdaTerm(t, body) ->
                        openTerm e2 body
        | ApplicationType(e1, t) ->
            // step the function if it isn't a value
            if not (isValue e1) then
                ApplicationType(step e1, t)
            else
                // ignore types at runtime
                match e1 with
                    | LambdaType body -> body

        | Projection(i, Tuple(items)) ->
            List.nth items i
        | Projection(i, e1) ->
            Projection(i, step e1)



    let rec eval e =
        let t = getType e
        System.Diagnostics.Debug.WriteLine(formatExpr e, "eval")
        if isValue e then e
        else 
            let e' = eval (step e)
            let t' = getType e'
            //assert (t = t')
            e'


        