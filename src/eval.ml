open Error
open Col
open IdCol
open VCol

let extend_env1 env x v =
  IdMap.add x v env

let extend_env env xs vs =
  List.fold_left2 extend_env1 env xs vs

let extend_env_ps env ps vs =
  List.fold_left2
    (fun env (x, t) v -> extend_env1 env x v)
    env ps vs

let rec eval mdb env expr =
  let c = Utils.seq_count () in
  (if !Option.debug then
     Printf.printf "eval[%d] << %s\n" c (E.show expr));
  let r = eval2 mdb env expr in
  (if !Option.debug then
     Printf.printf "eval[%d] >> %s\n" c (V.show r));
  r

and eval2 mdb env expr =
  match expr with
    E.Bool b               -> V.Bool b
  | E.Int k                -> V.Int k
  | E.Var n                -> lookup_var_val mdb env n
  | E.Univ t               -> V.Set (Univ.calc_univ mdb t)
  | E.Tuple xs             -> V.Tuple (List.map (eval mdb env) xs)
  | E.Set xs               -> V.Set (List.map (eval mdb env) xs)
  | E.List xs              -> V.List (List.map (eval mdb env) xs)
  | E.SetRange (x, y)      -> V.Set (eval_range mdb env x y)
  | E.ListRange (x, y)     -> V.List (eval_range mdb env x y)
  | E.Chset ps             -> eval_chset mdb env ps
  | E.Chmap m              -> eval_chmap mdb env m
  | E.And xs               -> eval_logical_and mdb env xs
  | E.Or xs                -> eval_logical_or mdb env xs
  | E.If (test, e1, e2)    -> eval_if mdb env test e1 e2
  | E.Let (bs, e)          -> eval_let mdb env bs e
  | E.Case (e, n, bs)      -> eval_case mdb env e bs
  | E.Apply (f, t_f, ets)  -> eval_apply mdb env f ets
  | E.Fun (xts, e, rt)     -> V.Fun (List.map fst xts, e, env)
  | E.Pos (pos, e)         -> with_pos pos (fun () -> eval mdb env e)

and lookup_var_val mdb env var =
  (* local env *)
  match IdMap.find_opt var env with
    Some value -> value
  | None ->
     (* global env *)
     (match Mdb.lookup_global_env_opt mdb var with
        Some x -> x
      | None -> error_s "unknown var: " (Id.show var))

and eval_range mdb env x y =
  match eval mdb env x with
    V.Int a ->
     (match eval mdb env y with
        V.Int b ->
         List.map (fun k -> V.Int k) (Utils.interval a (b+1)) (* inclusive *)
      | _ -> corrupt_s "range" (E.show y))
  |  _ -> corrupt_s "range" (E.show x)

and eval_chset mdb env ps =
  let s =
    List.fold_left
      (fun s (e, t) ->
        let v = eval mdb env e in
        match v with
          V.Event (ch, vs) -> VSet.add v s
        | V.Channel (ch, vs) ->
           Mdb.channel_event_fold mdb ch vs s
             (fun s us -> VSet.add (V.Event (ch, us)) s)
        | _ -> Error.corrupt_s "eval_chset " (E.show e))
      VSet.empty ps
  in
  let vs =
    VSet.fold
      (fun elem acc -> elem::acc)
    s []
  in
  V.Set vs

and eval_chmap mdb env m =
  let s =
    List.fold_left
      (fun s ((ea, _), (eb, _)) ->
        let a = eval mdb env ea in
        let b = eval mdb env eb in
        match a with
          V.Event (ch_a, vs_a) ->
           (match b with
              V.Event (ch_b, vs_b) ->
               VSet.add (V.Tuple [a; b]) s
            | V.Channel (ch_b, vs_b) ->
               Mdb.channel_event_fold mdb ch_b vs_b s
                 (fun s us ->
                   let e = V.Event (ch_b, us) in
                   VSet.add (V.Tuple [a; e]) s)
            | _ -> Error.corrupt "eval_chmap")
        | V.Channel (ch_a, vs_a) ->
           (match b with
              V.Event (ch_b, vs_b) ->
               Mdb.channel_event_fold mdb ch_a vs_a s
                 (fun s us ->
                   let e = V.Event (ch_a, us) in
                   VSet.add (V.Tuple [e; b]) s)
            | V.Channel (ch_b, vs_b) ->
               Mdb.channel_event_fold mdb ch_a vs_a s
                 (fun s us ->
                   match Utils.prefix_rest vs_a us with
                     Some xs ->
                     let ea = V.Event (ch_a, us) in
                     let eb = V.Event (ch_b, vs_b @ xs) in
                     VSet.add (V.Tuple [ea; eb]) s
                   | None -> Error.corrupt "eval_chmap")
            | _ -> Error.corrupt "eval_chmap")
        | _ -> Error.corrupt "eval_chmap")
      VSet.empty m
  in
  let vs =
    VSet.fold
      (fun elem acc -> elem::acc)
      s []
  in
  V.Set vs

and eval_logical_and mdb env xs =
  let rec loop xs =
    match xs with
      [] -> V.Bool true
    | x::xs' ->
       (match eval mdb env x with
          V.Bool b ->
           if b then
             loop xs'
           else
             V.Bool false
        | _ -> error "eval and")
  in loop xs

and eval_logical_or mdb env xs =
  let rec loop xs =
    match xs with
      [] -> V.Bool false
    | x::xs' ->
       (match eval mdb env x with
          V.Bool b ->
           if b then
             V.Bool true
           else
             loop xs'
        | _ -> error "eval and")
  in loop xs

and eval_if mdb env test e1 e2 =
  match eval mdb env test with
    V.Bool b ->
     if b then
       eval mdb env e1
     else
       eval mdb env e2
  | _ -> error "eval if"

and eval_let mdb env bs e =
  let envx =
    List.fold_left
      (fun envx (ps, e) ->
        let v = eval mdb env e in
        match ps with
          [] -> envx
        | p::ps' ->
           let (x, t) = p in
           (match ps' with
              [] -> extend_env1 envx x v
            | _ ->
               (match v with
                  V.Tuple vs -> extend_env_ps envx ps vs
                | _ -> error "eval let")))
      env bs
  in eval mdb envx e

and eval_case mdb env expr bs =
  match eval mdb env expr with
    Variant (ctor, vs) ->
     let (xs, e) = List.assoc ctor bs in
     let env' = extend_env env xs vs in
     eval mdb env' e
  | _ -> Undefined

(*
  function position:
  1. builtin
  2. user-defined
  3. ctor
  4. channel
 *)
and eval_apply mdb env f ets =
  let g = eval mdb env f in
  let xs = List.map (fun (e, t) -> eval mdb env e) ets in
  apply mdb env g xs

and apply mdb env f args =
  match f with
    V.BuiltinFun bf -> bf (apply mdb env) args
  | V.UserFun n ->
     let fun_spec = Mdb.lookup_fun_spec mdb n in
     let envx = extend_env V.env0 fun_spec.fun_param_list args in
     eval mdb envx fun_spec.fun_expr
  | V.Ctor n -> Variant (n, args)
  | V.Channel (n, vs) ->
     let chspec = Mdb.get_channel_spec mdb n in
     let vs' = vs @ args in
     if List.length vs' = List.length chspec.channel_type_list then
       V.Event (n, vs')
     else
       V.Channel (n, vs')
  | _ -> error_s "apply " (V.show f)
