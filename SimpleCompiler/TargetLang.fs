module TargetLang
    type Id = string

    type Type =
        | TypeVariable of Id
        | Bool
        | Product of list<Type>
        | Function of list<Id> * list<Type> * Type
        | Existential of Id * Type

    type Expression =
        | Variable of Id
        | True
        | False
        | Tuple of list<Expression>
        | If of Expression * Expression * Expression
        | Application of Expression * list<Type> * list<Expression>
        | Lambda of list<Id> * Map<Id, Type> * Expression
        | Projection of int * Expression
        (*pack   <t,     e> as       Ea.   t>*)
        | Pack of Type * Expression * Id * Type
        (*unpack   <a,   x> = e         in e*)
        | Unpack of Id * Id * Expression * Expression

    let rec isValue e =
        match e with
        | True -> true
        | False -> true
        | Tuple(items) -> List.forall isValue items
        | Lambda(_, _, _) -> true
        | Pack(_, e, _, _) -> isValue(e)
        | _ -> false

    let rec map f e =
        match e with
        | Tuple(items) -> Tuple (List.map f items)
        | If(e1, e2, e3) -> If(f e1, f e2, f e3)
        | Application(e1, typeArgs, args) ->
            Application(f e1, typeArgs, List.map f args)
        | Lambda(id, t, body) -> Lambda(id, t, f body)
        | Projection(i, e1) -> Projection(i, f e1)
        (*pack   <t,     e> as       Ea.   t>*)
        | Pack(t1, e1, id, t2) -> Pack(t1, f e1, id, t2)
        (*unpack   <a,   x> = e         in e*)
        | Unpack(tid, id, e1, e2) -> Unpack(tid, id, f e1, f e2)
        | _ -> e


    // e[target/replacement]
    let rec substitute mapping e =
        match e with
        | Variable id -> if Map.containsKey id mapping then
                            Map.find id mapping else e
        | _ -> map (substitute mapping) e