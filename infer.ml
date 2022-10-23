open Interp

type 'a env = (string * 'a) list

let rec lookup env x =
  match env with
  | [] -> failwith ("lookup: " ^ x ^ " not found")
  | (y, v)::rest ->
      if x=y then v else lookup rest x

let rec mem x l =
  match l with
  | [] -> false
  | h :: t -> x = h || mem x t

let rec union (xs, ys) =
  match xs with
  | [] -> ys
  | hx::tx ->
      if mem hx ys then union(tx, ys)
      else hx :: union (tx, ys)

let rec unique l =
  match l with
  | [] -> []
  | h::t -> if mem h t then unique t
            else h::unique t

type typ =
  | TypI
  | TypB
  | TypF of typ * typ
  | TypV of typevar

and tyvarkind = 
  | NoLink of string
  | LinkTo of typ

and typevar = (tyvarkind * int) ref

type typescheme =
  TypeScheme of typevar list * typ

let setTvKind tyvar newKind =
  let (_, lvl) = !tyvar in
  tyvar := (newKind, lvl)

let setTvLevel tyvar newLevel =
  let (kind, _) = !tyvar in
  tyvar := (kind, newLevel)

let rec normType t =
  match t with
  | TypV tyvar ->
    (match !tyvar with
    | (LinkTo t1, _) ->
        let t2 = normType t1 in
        setTvKind tyvar (LinkTo t2); t2
    | _ -> t)
  | _ -> t

let rec freeTypeVars t: typevar list =
  match normType t with
  | TypI -> []
  | TypB -> []
  | TypV tv -> [tv]
  | TypF(t1, t2) -> union(freeTypeVars t1, freeTypeVars t2)

let occurCheck tyvar tyvars =
  if mem tyvar tyvars then failwith "type error: circularity"
  else ()

let pruneLevel maxLevel tvs =
  let reducelevel tyvar =
    let (_, level) = !tyvar in
    setTvLevel tyvar (min level maxLevel) in
  List.iter reducelevel tvs

(* Why do we need to prune level *)
let linkVarToType tyvar t =
  let (_, level) = !tyvar in
  let fvs = freeTypeVars t in
  occurCheck tyvar fvs;
  pruneLevel level fvs;
  setTvKind tyvar (LinkTo t)

let typeToString t =
  match t with
  | TypI -> "int"
  | TypB -> "bool"
  | TypV _ -> failwith "typeToString impossible"
  | TypF(_, _) -> "function"

let rec unify t1 t2 =
  let t1' = normType t1 in
  let t2' = normType t2 in
  match (t1', t2') with
  | (TypI, TypI) -> ()
  | (TypB, TypB) -> ()
  | (TypF(t1a, t1r), TypF(t2a, t2r)) ->
      unify t1a t2a;
      unify t1r t2r;
  | (TypV tv1, TypV tv2) ->
    let (_, tv1level) = !tv1 in
    let (_, tv2level) = !tv2 in
    if tv1 = tv2 then () 
    else if tv1level < tv2level
      then linkVarToType tv1 t2'
    else linkVarToType tv2 t1'
  | (TypV tv1, _) -> linkVarToType tv1 t2'
  | (_, TypV tv2) -> linkVarToType tv2 t1'
  | (TypI, t) -> failwith ("type error: int and " ^ typeToString t)
  | (TypB, t) -> failwith ("type error: bool and " ^ typeToString t)
  | (TypF _, t) -> failwith ("type error: function and " ^ typeToString t)

let typevarno = ref 0

let newTypeVar (level:int) =
  let rec mkname i res =
    if i < 26 then String.make 1 (char_of_int(97+i)) :: res
    else mkname (i/26-1) (String.make 1 (char_of_int(97+i mod 26)):: res) in
  let intToName i = List.fold_left (^) "" (mkname i []) in
  typevarno := !typevarno + 1;
  ref (NoLink (intToName !typevarno), level)

let generalize level t =
  let notFreeinContext tyvar =
    let (_, linkLevel) = !tyvar in
    linkLevel > level in
  let tvs = List.filter notFreeinContext (freeTypeVars t) in
  TypeScheme(unique tvs, t)

let rec copyType subst t : typ = 
  match t with
  | TypV tyvar ->
    (* Could this be rewritten so that loop does only the substitution *)
    let rec loop subst1 =          
      match subst1 with 
     | (tyvar1, type1) :: rest -> if tyvar1 = tyvar then type1 else loop rest
     | [] -> match !tyvar with
             | (NoLink _, _)  -> t
             | (LinkTo t1, _) -> copyType subst t1 in
    loop subst
  | TypF(t1, t2) -> TypF(copyType subst t1, copyType subst t2)
  | TypI -> TypI
  | TypB -> TypB

let specialize level (TypeScheme(tvs, t)) =
  let bindfresh tv = (tv, TypV(newTypeVar level)) in
  match tvs with
  | [] -> t
  | _ -> let subst = List.map bindfresh tvs in
         copyType subst t

let showtype t =
    let rec pr t = 
        match normType t with
        | TypI         -> "int"
        | TypB         -> "bool"
        | TypV tyvar   -> 
          (match !tyvar with
          | (NoLink name, _) -> name
          | _ -> failwith "showtype impossible")
        | TypF(t1, t2) -> "(" ^ pr t1 ^ " -> " ^ pr t2 ^ ")" in
    pr t 

type tenv = typescheme env

let rec typ (lvl: int) (env: tenv) (e: expr): typ =
  match e with
  | CstI _ -> TypI
  | CstB _ -> TypB
  | Var x -> specialize lvl (lookup env x)
  | Prim(ope, e1, e2) -> 
    (let t1 = typ lvl env e1 in
    let t2 = typ lvl env e2 in
    match ope with
    | "*" -> (unify TypI t1; unify TypI t2; TypI)
    | "+" -> (unify TypI t1; unify TypI t2; TypI)
    | "-" -> (unify TypI t1; unify TypI t2; TypI)
    | "=" -> (unify t1 t2; TypB)
    | "<" -> (unify TypI t1; unify TypI t2; TypB)
    | "&" -> (unify TypB t1; unify TypB t2; TypB)
    | _   -> failwith ("unknown primitive " ^ ope) )
  | Let(x, eRhs, letBody) -> 
    let lvl1 = lvl + 1 in
    let resTy = typ lvl1 env eRhs in
    let letEnv = (x, generalize lvl resTy) :: env in
    typ lvl letEnv letBody
  | If(e1, e2, e3) ->
    let t2 = typ lvl env e2 in
    let t3 = typ lvl env e3 in
    unify TypB (typ lvl env e1);
    unify t2 t3;
    t2
  | Letfun(f, x, fBody, letBody) -> 
    let lvl1 = lvl + 1 in
    let fTyp = TypV(newTypeVar lvl1) in
    let xTyp = TypV(newTypeVar lvl1) in
    let fBodyEnv = (x, TypeScheme([], xTyp)) 
                    :: (f, TypeScheme([], fTyp)) :: env in
    let rTyp = typ lvl1 fBodyEnv fBody in
    let _    = unify fTyp (TypF(xTyp, rTyp)) in
    let bodyEnv = (f, generalize lvl fTyp) :: env in
    typ lvl bodyEnv letBody
  | Call(eFun, eArg) -> 
    let tf = typ lvl env eFun in
    let tx = typ lvl env eArg in
    let tr = TypV(newTypeVar lvl) in
    unify tf (TypF(tx, tr));
    tr

let tyinf e0 = typ 0 [] e0

let inferType e =
  (typevarno := 0;
   showtype (tyinf e))
