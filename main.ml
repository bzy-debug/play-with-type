open Interp
open Infer

let print_type = fun x -> x |> inferType |> print_endline

let id = Letfun("f", "x", Var "x", Var "f")
let tw = Letfun("tw", "g", Letfun("app", "x", Call(Var "g", Call(Var "g", Var "x")), Var "app"), Var "tw")
let s x y z = (x z) (y z)
let se = Letfun("s", "x", Letfun("a1", "y", Letfun("a2", "z", Call(Call(Var "x", Var "z"), Call(Var"y", Var "z")), Var "a2"), Var "a1"), Var"s")

let exprs = [id; tw; se]
let () = List.iter print_type exprs
