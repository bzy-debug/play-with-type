type expr =
    Name of string
  | Int of int
  | Bool of bool
  | If of expr * expr * expr
  | Fun of string * expr
  | App of expr * expr

type typ =
    TInt
  | TVar of string
  | TBool
  | TArr of typ * typ

let rec string_of_typ = function
  | TInt -> "int"
  | TVar x -> x
  | TBool -> "bool"
  | TArr(t1, t2) ->
      Printf.sprintf "(%s -> %s)" (string_of_typ t1) (string_of_typ t2)

let rec string_of_typ_typ_list = function
  | [] -> ""
  | (t1, t2)::rest ->
      Printf.sprintf "(%s, %s); %s" (string_of_typ t1) (string_of_typ t2) (string_of_typ_typ_list rest)

let init_env = [("+", TArr(TInt, TArr(TInt, TInt)));
                ("<=", TArr(TInt, TArr(TInt, TBool)))]

let type_var = ["'a"; "'b"; "'c"; "'d"; "'e"; "'f"]

let fresh =
  let x = ref 0 in
  fun () ->
    let var = TVar(List.nth type_var !x) in
    x := !x + 1;
    var

let rec infer exp env =
  match exp with
  | Int _ -> (TInt, [])
  | Bool _ -> (TBool, [])
  | Name s -> (List.assoc s env, [])
  | If(e1, e2, e3) ->
      let t' = fresh() in
      let (t1, c1) = infer e1 env in
      let (t2, c2) = infer e2 env in
      let (t3, c3) = infer e3 env in
      let c = [(t1, TBool); (t', t2); (t', t3)] in
      (t', c1 @ c2 @ c3 @ c)
  | Fun(x, e) ->
      let t1' = fresh() in
      let (t2, c) = infer e ((x, t1')::env) in
      (TArr(t1', t2), c)
  | App(e1, e2) ->
      let t' = fresh() in
      let (t1, c1) = infer e1 env in
      let (t2, c2) = infer e2 env in
      let c = [(t1, TArr(t2, t'))] in
      (t', c1 @ c2 @ c)

let rec occurs x t =
  match t with
  | TInt | TBool -> false
  | TVar y -> x = y
  | TArr(t1, t2) -> occurs x t1 || occurs x t2

let rec unify constraints =
  match constraints with
  | (TInt, TInt)::rest -> unify rest
  | (TBool, TBool)::rest -> unify rest
  | (TVar x, TVar y)::rest when x = y -> unify rest
  | (TArr(t1, t2), TArr(t3, t4))::rest ->
      unify ((t1, t3)::(t2, t4)::rest)
  | (TVar x , t)::rest when (not (occurs x t)) ->
      (TVar x, t)::unify rest
  | _ -> failwith "unify: not here"

let test = Fun("f", Fun("x", App(Name "f", App(App(Name "+", Name "x"), Int 1))))

let (aim, constraints) = infer test init_env
