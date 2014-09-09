module Util
    /// Concatenate the strings in l with sep in between each one.
    let rec join sep l =
        match l with
        | [] -> ""
        | first :: [] -> first
        | first :: rest -> first + sep + (join sep rest)