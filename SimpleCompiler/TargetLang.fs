module TargetLang
    type Id = int

    type Type =
        | TypeVariable of Id
        | Bool
        | Product of Type * Type
        | Function of Type * Type
        | Existential of Id * Type

    type Expression =
        | Variable of Id
        | True
        | False
        | Pair of Expression * Expression
        | If of Expression * Expression * Expression
        | Application of Expression * Expression
        | Lambda of Id * Type * Expression
        | Projection of int * Expression
        (*pack   <t,     e> as       Ea.   t>*)
        | Pack of Type * Expression * Id * Type
        (*unpack   <a,   x> = e         in e*)
        | Unpack of Id * Id * Expression * Expression

    let rec isValue e =
        match e with
        | True -> true
        | False -> true
        | Pair(e1, e2) -> (isValue e1) && (isValue e2)
        | Lambda(_, _, _) -> true
        | Pack(_, e, _, _) -> isValue(e)
        | _ -> false

