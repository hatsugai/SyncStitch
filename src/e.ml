open Printf
open Error
open IdCol

type t =
  Bool of bool
| Int of int
| Var of Id.t
| Univ of T.t
| Tuple of t list
| Set of t list
| List of t list
| SetRange of t * t
| ListRange of t * t
| Chset of (t * T.t) list
| Chmap of ((t * T.t) * (t * T.t)) list
| And of t list
| Or of t list
| If of t * t * t
| Let of ((Id.t * T.t) list * t) list * t
| Case of t * Id.t * (Id.t * (Id.t list * t)) list
| Apply of t * T.t * (t * T.t) list
| Fun of (Id.t * T.t) list * t * T.t
| Pos of S.pos * t

let rec dig e =
  match e with
    Pos (_, e) -> dig e
  | _ -> e

let make_tuple es =
  match es with
    [e] -> e
  | _ -> Tuple es

let rec show e =
  match e with
    Bool b -> if b then "true" else "false"
  | Int k -> sprintf "%d" k
  | Var n -> Id.show n
  | Univ _ -> "univ"
  | Tuple es -> sprintf "(tuple %s)" (show_list es)
  | Set es -> sprintf "(set %s)" (show_list es)
  | List es -> sprintf "(list %s)" (show_list es)
  | SetRange (x, y) -> sprintf "(set-range %s %s)" (show x) (show y)
  | ListRange (x, y) -> sprintf "(list-range %s %s)" (show x) (show y)
  | Chset ps ->
     sprintf "(chset %s)"
       (Utils.cons_str_list (fun (x, rt) -> show x) ps)
  | Chmap m ->
     sprintf "(chmap %s)"
       (Utils.cons_str_list
          (fun ((a, _), (b, _)) ->
            sprintf "(%s,%s)" (show a) (show b))
          m)
  | And xs -> sprintf "(and %s)" (show_list xs)
  | Or xs -> sprintf "(or %s)" (show_list xs)
  | If (test, x, y) -> sprintf "(if %s %s %s)" (show test) (show x) (show y)
  | Let (bs, e) ->
     let s =
       List.fold_left
         (fun s (xs, e) ->
           sprintf "%s ((%s) %s)" s
             (Id.show_list (List.map (fun (x, t) -> x) xs))
             (show e))
       "" bs
     in
     sprintf "(let (%s) %s" s (show e)
  | Case (e, n, bs) ->
     let s =
       List.fold_left
         (fun s (ctor, (xs, e)) ->
           sprintf "%s ((%s %s) %s)"
             s (Id.show ctor) (Id.show_list xs) (show e))
         "" bs
     in
     sprintf "(case %s %s)" (show e) s
  | Apply (f, t_f, ets) ->
     sprintf "(%s %s)" (show f)
       (Utils.cons_str_list
          (fun (e, _) -> show e)
          ets)
  | Fun (xts, e, rt) ->
     sprintf "(fun (%s) %s)"
       (Utils.cons_str_list
          (fun (x, _) -> Id.show x)
          xts)
       (show e)
  | Pos (_, e) -> show e

and show_list es =
  List.fold_left
    (fun s e -> sprintf "%s %s" s (show e))
    "" es

let rec convert mdb e =
  let c = Utils.seq_count () in
  (if !Option.debug then
     Printf.printf "E.convert[%d] << %s\n" c (S.show e));
  let x = convert2 mdb e in
  (if !Option.debug then
     Printf.printf "E.convert[%d] >> %s\n" c (show x));
  x

and convert2 mdb e =
  let ft rt =
    match !rt with
      Some t -> t
    | None -> Error.corrupt_s "E.convert: type slot is not set:  " (S.show e)
  in
  match e with
  | S.Bool b -> Bool b
  | S.Int k -> Int k
  | S.Var n -> Var n
  | S.Univ rt -> Univ (ft rt)
  | S.Tuple xs -> Tuple (List.map (convert mdb) xs)
  | S.Set xs -> Set (List.map (convert mdb) xs)
  | S.List xs -> List (List.map (convert mdb) xs)
  | S.SetRange (x, y) -> SetRange (convert mdb x, convert mdb y)
  | S.ListRange (x, y) -> ListRange (convert mdb x, convert mdb y)
  | S.Chset ps ->
     let ps' =
       List.map
         (fun (e, rt) -> (convert mdb e, ft rt))
         ps
     in
     Chset ps'
  | S.Chmap m ->
     let m' =
       List.map
         (fun ((a, rt_a), (b, rt_b)) ->
           ((convert mdb a, ft rt_a), (convert mdb b, ft rt_b)))
         m
     in
     Chmap m'
  | S.And xs -> And (List.map (convert mdb) xs)
  | S.Or xs -> Or (List.map (convert mdb) xs)
  | S.If (test, e1, e2) ->
     If (convert mdb test, convert mdb e1, convert mdb e2)
  | S.Let (binding, e) ->
     let binding' =
       List.map
         (fun (xs, e) ->
           let xs' =
             List.map
               (fun (x, rt) -> (x, ft rt))
               xs
           in (xs', convert mdb e))
         binding
     in
     Let (binding', convert mdb e)
  | S.Case (e, rn, bs) ->
     let n =
       match !rn with
         Some n -> n
       | None -> Error.corrupt_s "E.convert " (S.show e)
     in
     let bs' =
       List.map (fun (ctor, (vs, e)) -> (ctor, (vs, convert mdb e))) bs
     in Case (convert mdb e, n, bs')
  | S.Stop        -> error_s "E.convert" (S.show e)
  | S.Skip        -> error_s "E.convert" (S.show e)
  | S.Spon _      -> error_s "E.convert" (S.show e)
  | S.Prefix _    -> error_s "E.convert" (S.show e)
  | S.Receive _   -> error_s "E.convert" (S.show e)
  | S.Branch _    -> error_s "E.convert" (S.show e)
  | S.Alt _       -> error_s "E.convert" (S.show e)
  | S.Amb _       -> error_s "E.convert" (S.show e)
  | S.Seq _       -> error_s "E.convert" (S.show e)
  | S.Par _       -> error_s "E.convert" (S.show e)
  | S.Hide _      -> error_s "E.convert" (S.show e)
  | S.Rename _    -> error_s "E.convert" (S.show e)
  | S.XAlt _      -> error_s "E.convert" (S.show e)
  | S.XAmb _      -> error_s "E.convert" (S.show e)
  | S.XSeq _      -> error_s "E.convert" (S.show e)
  | S.XPar _      -> error_s "E.convert" (S.show e)
  | S.Fun (xts, e, rt) ->
     let xts' =
       List.map
         (fun (x, rt, _) -> (x, ft rt))
         xts
     in Fun (xts', convert mdb e, ft rt)
  | S.Apply (f, rt_f, ets) ->
     let ets' =
       List.map
         (fun (e, rt) -> (convert mdb e, ft rt))
         ets
     in
     Apply (convert mdb f, ft rt_f, ets')
  | S.Pos (pos, e) ->
     with_pos pos
       (fun () -> Pos (pos, convert mdb e))

let rec collect_vars bs acc e =
  match e with
    Bool b -> acc
  | Int k -> acc
  | Var n ->
     if IdSet.mem n bs then
       IdSet.add n acc
     else
       acc
  | Univ t -> acc
  | Tuple es ->
     List.fold_left (collect_vars bs) acc es
  | Set es ->
     List.fold_left (collect_vars bs) acc es
  | List es ->
     List.fold_left (collect_vars bs) acc es
  | SetRange (x, y) ->
     collect_vars bs (collect_vars bs acc x) y
  | ListRange (x, y) ->
     collect_vars bs (collect_vars bs acc x) y
  | Chset ps ->
     List.fold_left
       (fun acc (e, t) -> collect_vars bs acc e)
       acc ps
  | Chmap m ->
     List.fold_left
       (fun acc ((a, _), (b, _)) ->
         collect_vars bs (collect_vars bs acc a) b)
       acc m
  | And es ->
     List.fold_left (collect_vars bs) acc es
  | Or es ->
     List.fold_left (collect_vars bs) acc es
  | If (test, x, y) ->
     let acc = collect_vars bs acc test in
     let acc = collect_vars bs acc x in
     collect_vars bs acc y
  | Let (bindings, e) ->
     let rec loop bs' acc bindings =
       match bindings with
         [] -> collect_vars bs' acc e
       | (xs, e)::bindings' ->
          let bs' =
            List.fold_left
              (fun bs' (x, t) -> IdSet.remove x bs')
              bs' xs
          in
          let acc = collect_vars bs acc e in
          loop bs' acc bindings'
     in loop bs acc bindings
  | Case (e, n, branches) ->
     let acc = collect_vars bs acc e in
     List.fold_left
       (fun acc (ctor, (xs, e)) ->
         let bs' = IdSet.remove_list xs bs in
         collect_vars bs' acc e)
       acc branches
  | Apply (f, t_f, ets) ->
     let acc = collect_vars bs acc f in
     List.fold_left
       (fun acc (e, t) -> collect_vars bs acc e)
       acc ets
  | Fun (xts, e, rt) ->
     let bs' =
       List.fold_left
         (fun bs' (x, t) ->
           IdSet.remove x bs')
         bs xts
     in collect_vars bs' acc e
  | Pos (_, e) -> collect_vars bs acc e

let op_precedence = [
    ("^",  50);
    ("*",  40); ("/",  40); ("%",  40);
    ("+",  30); ("-",  30);
    ("==",  20); ("!=", 20); ("<",  20); (">",  20); ("<=", 20); (">=", 20);
  ]

let rec desc e =
  match e with
    Bool b -> if b then "true" else "false"
  | Int k -> sprintf "%d" k
  | Var n -> Id.show n
  | Univ _ -> "univ"
  | Tuple es -> sprintf "(%s)" (desc_list desc es)
  | Set es -> sprintf "{%s}" (desc_list desc es)
  | List es -> sprintf "<%s>" (desc_list desc es)
  | SetRange (x, y) -> sprintf "{%s..%s}" (desc x) (desc y)
  | ListRange (x, y) -> sprintf "<%s..%s>" (desc x) (desc y)
  | Chset ps ->
     sprintf "{|%s|}"
       (Utils.cons_str_list (fun (e, t) -> desc e) ps)
  | Chmap m ->
     sprintf "{|%s|}"
       (Utils.cons_str_list
          (fun ((a, _), (b, _)) ->
            sprintf "(%s,%s)" (desc a) (desc b))
          m)
  | And xs ->
     (match xs with
        [] -> "true"
      | x::xs' ->
         List.fold_left
           (fun s x -> sprintf "%s and %s" s (desc x))
           (desc x) xs')
  | Or xs ->
     (match xs with
        [] -> "false"
      | x::xs' ->
         List.fold_left
           (fun s x -> sprintf "%s or %s" s (desc x))
           (desc x) xs')
  | If (test, x, y) ->
     sprintf "if %s then %s else %s" (show test) (show x) (show y)
  | Let (bs, e) ->
     let s =
       List.fold_left
         (fun s (nts, e) ->
           let t = sprintf "%s=%s" (desc_bound_vars nts) (desc e) in
           if s="" then t else sprintf "%s and %s" s t)
         "" bs
     in sprintf "let %s within %s" s (desc e)
  | Case (e, n, bs) ->
     let s =
       List.fold_left
         (fun s (ctor, (ps, e)) ->
           let t =
             sprintf "%s%s -> %s"
               (Id.show ctor) (desc_ctor_ps ps) (desc e)
           in
           if s="" then t else sprintf "%s | %s" s t)
         "" bs
     in
     sprintf "case %s of %s" (desc e) s
  | Apply (f, t_f, ets) -> desc_app f ets
  | Fun (xts, e, rt) -> "fun"
  | Pos (_, e) -> desc e

and desc_list f xs =
  Utils.cons_str_list f xs

and desc_bound_vars nts =
  match nts with
  | [(n, _)] -> Id.show n
  | _ ->
     sprintf "(%s)" (Utils.cons_str_list (fun (n, _) -> Id.show n) nts)

and desc_ctor_ps ps =
  match ps with
    [] -> ""
  | [n] -> " " ^ (Id.show n)
  | _ ->
     sprintf "(%s)" (Utils.cons_str_list Id.show ps)

and desc_app f ets =
  match f with
    Var n ->
    let s = Id.show n in
    (match List.assoc_opt s op_precedence with
       Some p ->
        infix p s
          (match ets with
             [(e, _); (e', _)] -> [e; e']
           | _ -> Error.corrupt_s "desc_app" (show f))
     | None ->
        sprintf "%s(%s)" s
          (Utils.cons_str_list
             (fun (e, t) -> desc e)
             ets))
  | _ ->
     sprintf "%s(%s)" (desc f)
       (Utils.cons_str_list
          (fun (e, t) -> desc e)
          ets)

and priority e =
  match e with
    Bool b -> 0
  | Int k -> 0
  | Var n -> 0
  | Univ _ -> 0
  | Tuple es -> 0
  | Set es -> 0
  | List es -> 0
  | SetRange _ -> 0
  | ListRange _ -> 0
  | Chset es -> 0
  | Chmap m -> 0
  | And _ -> 3
  | Or _ -> 2
  | If (test, x, y) -> 1
  | Let (bs, e) -> 1
  | Case (e, n, bs) -> 1
  | Apply (f, t_f, ets) ->
     (match f with
        Var n ->
         (match List.assoc_opt (Id.show n) op_precedence with
            Some p -> p
          | None -> 0)
      | _ -> 0)
  | Fun (xts, e, rt) -> 1
  | Pos (_, e) -> priority e

and infix p op es =
  match es with
    [] -> error "infix"
  | [e] ->
     let q = priority e in
     if q > 0 && p > q then
       sprintf "%s(%s)" op (desc e)
     else
       sprintf "%s%s" op (desc e)
  | e::es' ->
     List.fold_left
       (fun str e ->
         let q = priority e in
         if q > 0 && p > q then
           sprintf "%s%s(%s)" str op (desc e)
         else
           sprintf "%s%s%s" str op (desc e))
       (let q = priority e in
        if q > 0 && p > q then
          sprintf "(%s)" (desc e)
        else
          sprintf "%s" (desc e))
       es'
