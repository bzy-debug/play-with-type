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

let generate_fresh =
  fun () ->
    let x = ref 0 in
    fun () ->
      let var = TVar(List.nth type_var !x) in
      x := !x + 1;
      var

let rec get_cons exp env fresh =
  match exp with
  | Int _ -> (TInt, [])
  | Bool _ -> (TBool, [])
  | Name s -> (List.assoc s env, [])
  | If(e1, e2, e3) ->
      let t' = fresh() in
      let (t1, c1) = get_cons e1 env fresh in
      let (t2, c2) = get_cons e2 env fresh in
      let (t3, c3) = get_cons e3 env fresh in
      let c = [(t1, TBool); (t', t2); (t', t3)] in
      (t', c1 @ c2 @ c3 @ c)
  | Fun(x, e) ->
      let t1' = fresh() in
      let (t2, c) = get_cons e ((x, t1')::env) fresh in
      (TArr(t1', t2), c)
  | App(e1, e2) ->
      let t' = fresh() in
      let (t1, c1) = get_cons e1 env fresh in
      let (t2, c2) = get_cons e2 env fresh in
      let c = [(t1, TArr(t2, t'))] in
      (t', c1 @ c2 @ c)

let rec occurs x t =
  match t with
  | TInt | TBool -> false
  | TVar y -> x = y
  | TArr(t1, t2) -> occurs x t1 || occurs x t2

let rec subst t sbt =
  match t with
  | TVar _ when t = fst sbt -> snd sbt
  | TArr(t1, t2) -> TArr(subst t1 sbt, subst t2 sbt)
  | _ -> t

let rec solve t sbt_l =
  match sbt_l with
  | h::tl -> solve (subst t h) tl
  | [] -> t

let subst_pair tp ~sbt =
  (subst (fst tp) sbt, subst (snd tp) sbt)

let subst_all constraints sbt = List.map (subst_pair ~sbt) constraints

let rec unify constraints =
  match constraints with
  | (TInt, TInt)::rest -> unify rest
  | (TBool, TBool)::rest -> unify rest
  | (TVar x, TVar y)::rest when x = y -> unify rest
  | (TArr(t1, t2), TArr(t3, t4))::rest ->
      let rest = (t1, t3)::(t2, t4)::rest in
      unify ((t1, t3)::(t2, t4)::rest)
  | (TVar x , t)::rest when (not (occurs x t)) ->
      let sbt = (TVar x, t) in
      let rest = subst_all rest sbt in
      sbt::unify rest
  | (t, TVar x)::rest when (not (occurs x t)) ->
      let sbt = (TVar x, t) in
      let rest = subst_all rest sbt in
      sbt::unify rest
  | [] -> []
  | _ -> failwith (string_of_typ_typ_list constraints)

let infer exp =
  let (aim, constraints) = get_cons exp init_env (generate_fresh()) in
  let sbt = unify constraints in
  solve aim sbt
let test = Fun("f", Fun("x", App(Name "f", App(App(Name "+", Name "x"), Int 1))))
let id = Fun("x", Name "x")
let compose = Fun("g", Fun("f", Fun("x", App(Name "g", App(Name "f", Name "x")))))
let first = Fun("x", Fun("y", Name "x"))
let add = Fun("x", Fun("y", App(App(Name "+", Name "x"), Name "y")))
let succ = App(add, Int 1)
let le = Fun("x", Fun("y", App(App(Name "<=", Name "x"), Name "y")))
let le10 = App(le, Int 10)

let tests = [test; id; compose; first; add; succ; le; le10]

let _ = 
  List.map (fun x -> x |> infer |> string_of_typ |> print_endline) tests