type 'a env = (string * 'a) list

let rec lookup env x =
  match env with
  | [] -> failwith (x ^ "not found")
  | (y, v)::r -> if x = y then v else lookup r x

type expr =
  | CstI of int
  | CstB of bool
  | Var of string
  | Prim of string * expr * expr
  | Let of string * expr * expr
  | If of expr * expr * expr
  | Letfun of string * string * expr * expr
  | Call of expr * expr

type value =
  | Int of int
  | Closure of string * string * expr * value env

let rec eval exp env =
  match exp with
  | CstI i -> Int i
  | CstB b -> Int (if b then 1 else 0)
  | Var x -> lookup env x
  | Prim(ope, e1, e2) ->
      (let v1 = eval e1 env in
      let v2 = eval e2 env in
      match (ope, v1, v2) with
      | ("*", Int i1, Int i2) -> Int (i1 * i2)
      | ("-", Int i1, Int i2) -> Int (i1 - i2)
      | ("+", Int i1, Int i2) -> Int (i1 + i2)
      | ("=", Int i1, Int i2) -> Int (if i1 = i2 then 1 else 0)
      | ("<", Int i1, Int i2) -> Int (if i1 < i2 then 1 else 0)
      | _ -> failwith "unknown primitive or wrong type")
  | Let(x, eRhs, letBody) ->
      let xVal = eval eRhs env in
      let letEnv = (x, xVal) :: env in
      eval letBody letEnv
  | If(e1, e2, e3) ->
      (match eval e1 env with
      | Int 0 -> eval e2 env
      | Int _ -> eval e3 env
      | _ -> failwith "eval if")
  | Letfun(f, x, fBody, letBody) ->
      let bodyEnv = (f, Closure(f, x, fBody, env)) :: env in
      eval letBody bodyEnv
  | Call(eFun, eArg) ->
      let fClosure = eval eFun env in
      match fClosure with
      | Closure (f, x, fBody, fDeclEnv) ->
          let xVal = eval eArg env in
          let fBodyEnv = (x, xVal) :: (f, fClosure) :: fDeclEnv in
          eval fBody fBodyEnv
      | _ -> failwith "eval Call: not a function"

(* Evaluate in empty environment: program must have no free variables: *)

let run e = eval e []

(* Examples in abstract syntax *)

let ex1 = Letfun("f1", "x", Prim("+", Var "x", CstI 1), 
                 Call(Var "f1", CstI 12))

(* Factorial *)

let ex2 = Letfun("fac", "x", 
                 If(Prim("=", Var "x", CstI 0),
                    CstI 1,
                    Prim("*", Var "x", 
                              Call(Var "fac", 
                                   Prim("-", Var "x", CstI 1)))),
                 Call(Var "fac", CstI 10))

let ex3 = 
    Letfun("tw", "g", 
           Letfun("app", "x", Call(Var "g", Call(Var "g", Var "x")), 
                  Var "app"),
           Letfun("mul3", "y", Prim("*", CstI 3, Var "y"), 
                  Call(Call(Var "tw", Var "mul3"), CstI 11)))

let ex4 = 
    Letfun("tw", "g",
           Letfun("app", "x", Call(Var "g", Call(Var "g", Var "x")), 
                  Var "app"),
           Letfun("mul3", "y", Prim("*", CstI 3, Var "y"), 
                  Call(Var "tw", Var "mul3")))
