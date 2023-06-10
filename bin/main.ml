type ast =
  | Var of string
  | App of ast * ast
  | Abs of string * ast
  | Let of string * ast * ast

type ty =
  | TCons of string * ty list
  | TFunc of ty * ty
  | TVar of int
  | TForall of int * ty

let rec string_of_ast a =
  match a with
  | Var v -> v
  | App (f, e) -> Printf.sprintf "(%s %s)" (string_of_ast f) (string_of_ast e)
  | Abs (x, e) -> Printf.sprintf "(\\%s. %s)" x (string_of_ast e)
  | Let (x, v, e) -> Printf.sprintf "(let %s = %s in %s)" x (string_of_ast v) (string_of_ast e)

let rec string_of_type t =
  match t with
  | TCons (c, ts) -> begin
    match ts with
    | [] -> c
    | ts -> List.fold_left (fun s t -> s ^ " " ^ string_of_type t) c ts
  end
  | TFunc (a, r) -> Printf.sprintf "(%s -> %s)" (string_of_type a) (string_of_type r)
  | TVar i -> Printf.sprintf "$%i" i
  | TForall (i, t) -> Printf.sprintf "(forall $%i. %s)" i (string_of_type t)

type env = { mutable gamma: (string * ty) list; mutable subs: (int * ty) list }

let empty_env () = { gamma = []; subs = [] }

let newvar e =
  match e.subs with
  | [] ->
    e.subs <- (0, TVar 0) :: e.subs;
    TVar 0
  | (i, _) :: _ ->
    e.subs <- (i + 1, TVar (i + 1)) :: e.subs;
    TVar (i + 1)

let rec replace i inst t =
  match t with
  | TCons (c, ts) -> TCons (c, List.map (replace i inst) ts)
  | TFunc (a, r) -> TFunc (replace i inst a, replace i inst r)
  | TVar j ->
    if i = j then
      inst
    else
      TVar j
  | TForall (j, t) -> TForall (j, replace i inst t)
  

let rec instantiate t e =
  match t with
  | TForall (i, t) ->
    let t = replace i (newvar e) t in
      instantiate t e
  | t -> t

let rec find e t =
  match t with
  | TVar i ->
    let t = List.assoc i e.subs in
    begin
      match t with
      | TVar j -> if i = j then t else find e (TVar j)
      | t -> t
    end
  | t -> t

let rec unify e ta tb =
  let ta = find e ta in
  let tb = find e tb in
  match (ta, tb) with
  | (TCons (c1, ts1), TCons (c2, ts2)) ->
    if c1 = c2 && List.length ts1 = List.length ts2 then
      let rec verify xs =
        match xs with
        | [] -> Ok ()
        | Ok _ :: xs -> verify xs
        | Error e :: _ -> Error e
      in verify (List.map2 (unify e) ts1 ts2)
    else Error (Printf.sprintf "could not unify %s and %s" (string_of_type ta) (string_of_type tb))
  | (TFunc (a1, r1), TFunc (a2, r2)) -> begin
    match unify e a1 a2 with
    | Ok _ -> unify e r1 r2
    | Error e -> Error e
  end
  | (TVar i, t) | (t, TVar i) ->
    let rec update subs i t =
      match subs with
      | [] -> []
      | (j, u) :: subs ->
        if i = j then
          (j, t) :: subs
        else (j, u) :: update subs i t
    in let () = e.subs <- update e.subs i t in
      Ok ()
  | _ -> Error (Printf.sprintf "could not unify %s and %s" (string_of_type ta) (string_of_type tb))

let polymorphise e t =
  let rec helper e t =
    let rec append_unique xs ys =
      match xs with
      | [] -> ys
      | x :: xs -> append_unique xs (x :: ys)
    in match t with
    | TCons (_, ts) -> List.fold_left append_unique [] (List.map (helper e) ts)
    | TFunc (a, r) ->
      let ats = helper e a in
      let rts = helper e r in
        append_unique ats rts
    | TVar i -> begin
      match find e (TVar i) with
      | TVar _ -> [i]
      | _ -> []
    end
    | TForall (_, _) -> raise Exit in
  let xs = helper e t in
    List.fold_left (fun t i -> TForall (i, t)) t xs

let rec infer a e =
  match a with
  | Var v -> begin
    match List.assoc_opt v e.gamma with
    | Some t -> Ok (instantiate t e)
    | None -> Error (Printf.sprintf "variable %s undefined" v)
  end
  | App (f, a) -> begin
    match infer f e with
    | Ok ft -> begin
      match infer a e with
      | Ok at -> begin
        let t_ret = newvar e in
        match unify e ft (TFunc (at, t_ret)) with
        | Ok _ -> Ok t_ret
        | Error e -> Error e
      end
      | Error e -> Error e
    end
    | Error e -> Error e
  end
  | Abs (x, v) -> begin
    let t = newvar e in
    let () = e.gamma <- (x, t) :: e.gamma in
    match infer v e with
    | Ok u -> 
      let () = e.gamma <- List.tl e.gamma in
        Ok (TFunc (t, u))
    | Error e -> Error e
  end
  | Let (x, v, u) -> begin
    match infer v e with
    | Ok vt -> begin
      let () = e.gamma <- (x, polymorphise e vt) :: e.gamma in
      match infer u e with
      | Ok ut ->
        let () = e.gamma <- List.tl e.gamma in
          Ok ut
      | Error e -> Error e
    end
    | Error e -> Error e
  end

let a = Let ("id", Abs ("x", Var "x"), App (App (Var "id", Var "id"), Var "2"))
let () =
  let e = empty_env () in
  let () = e.gamma <- [("2", TCons ("int", []))] in
    match infer a e with
    | Ok t -> Printf.printf "%s: %s\n" (string_of_ast a) (string_of_type (find e t))
    | Error err -> Printf.printf "error: %s\n" err
