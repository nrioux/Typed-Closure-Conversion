module SourceLang
    type Id = int

    type Type =
        | Bool
        | Product of Type * Type
        | Function of Type * Type

    type Expression =
        | Variable of Id
        | True
        | False
        | Pair of Expression * Expression
        | If of Expression * Expression * Expression
        | Application of Expression * Expression
        | Lambda of Id * Type * Expression
        | Projection of int * Expression

    let rec isValue e =
        match e with
        | True -> true
        | False -> true
        | Pair(e1, e2) -> (isValue e1) && (isValue e2)
        | Lambda(_, _, _) -> true
        | _ -> false







