open Printf
open Col
open IdCol
open TCol
open Spec

type typector_or_typename =
  ToTc of T.tcon
| ToTi of (S.t * S.t) option
| ToTn of Id.t

let alloc_tvar mdb =
  T.Var (Mdb.generate_tvar mdb)

let make_tuple_type ts =
  match ts with
    [] -> T.App (T.Tuple, [])
  | [t] -> t
  | _ -> T.App (T.Tuple, ts)

let show_tvar_map s =
  TVarMap.iter
    (fun v t -> printf "%d = %s\n" v (T.show t))
  s

let rec subst_tv s t =
  match t with
    T.Var v ->
     (match TVarMap.find_opt v s with
        None -> t
      | Some u ->
         (match u with
            T.Gen _ -> u
          | _ -> subst_tv s u))
  | T.App (tc, ts) ->
     T.App (tc, List.map (subst_tv s) ts)
  | T.Gen i -> Error.error "subst_tv: TGen"

let rec subst_tg s t =
  match t with
    T.Var v -> t
  | T.App (tc, ts) -> T.App (tc, List.map (subst_tg s) ts)
  | T.Gen i -> TGenMap.find i s

let resolve_tvar s_m t =
  let rec resolve t =
    match t with
      T.Var v ->
       (match TVarMap.find_opt v s_m with
          Some u -> resolve u
        | None -> t)
    | T.App (tc, ts) ->
       T.App (tc, List.map resolve ts)
    | T.Gen i -> t
  in resolve t

let show_s_m s_m =
  TVarMap.fold
    (fun v t s ->
      if s="" then
        sprintf "(%d, %s)" v (T.show t)
      else
        sprintf "%s (%d, %s)" s v (T.show t))
    s_m ""

let generalize s_m t =
  let rec resolve_n_collect_tvars tv_set t =
    match t with
      T.Var v ->
       (match TVarMap.find_opt v s_m with
          Some u -> resolve_n_collect_tvars tv_set u
        | None -> (TVarSet.add v tv_set, t))
    | T.App (tc, ts) ->
       let (tv_set, ts) =
         List.fold_left_map
           resolve_n_collect_tvars
           tv_set [] ts
       in (tv_set, T.App (tc, ts))
    | T.Gen i -> Error.error "generalize"
  in
  let (tv_set, t) = resolve_n_collect_tvars TVarSet.empty t in
  let subst =
    let vs = TVarSet.fold (fun v vs -> v::vs) tv_set [] in
    List.fold_lefti
      (fun s i v ->
        TVarMap.add v (T.Gen i) s)
      TVarMap.empty vs
  in
  subst_tv subst t

let subst_tv_with_check s_m t =
  generalize s_m t

let rec collect_tg s t =
  match t with
    T.Var _ -> s
  | T.App (tc, ts) ->
     List.fold_left collect_tg s ts
  | T.Gen i -> TGenSet.add i s

let instantiate mdb t =
  let s = collect_tg TGenSet.empty t in
  let subst =
    TGenSet.fold
      (fun tgen subst ->
        let v = alloc_tvar mdb in
        TGenMap.add tgen v subst)
      s TGenMap.empty
  in
  subst_tg subst t

let rec occurs s_m v t =
  match t with
    T.Var v' ->
     if v = v' then
       true
     else
       (match TVarMap.find_opt v' s_m with
          None -> false
        | Some t -> occurs s_m v t)
  | T.App (tc, ts) -> List.exists (occurs s_m v) ts
  | T.Gen i -> Error.error "occurs"

let extend_type_env s_v x t =
  IdMap.add x t s_v

type unification_result =
  UnificationOk of T.t TVarMap.t
| UnificationError of string

let rec unify0 s_m t1 t2 =
  match t2 with
    T.Var v2               -> unify1 s_m t2 t1
  | _                      -> unify1 s_m t1 t2

and unify1 s_m t1 t2 =
  match t1 with
    T.Var v1               ->
     (match TVarMap.find_opt v1 s_m with
        Some t             -> unify0 s_m t t2
      | None               ->
         (match t2 with
            T.Var v2       ->
             if v1 = v2 then
               UnificationOk s_m
             else
               (match TVarMap.find_opt v2 s_m with
                  Some t   -> unify0 s_m t1 t
                | None     -> UnificationOk (TVarMap.add v1 t2 s_m))
          | T.App (tc, ts) ->
             if occurs s_m v1 t2 then
               UnificationError
                 (sprintf "type mismatch: %s and %s"
                    (T.show t1) (T.show t2))
             else
               UnificationOk (TVarMap.add v1 t2 s_m)
          | T.Gen i -> Error.corrupt "unify0: TGen"))
  | T.App (tc1, ts1) ->
     (match t2 with
        T.App (tc2, ts2) ->
         if T.tycon_eq tc1 tc2 then
           let rec fold s_m ts1 ts2 =
             match ts1, ts2 with
               [], [] -> UnificationOk s_m
             | t1::ts1', t2::ts2' ->
                (match unify0 s_m t1 t2 with
                   UnificationOk s_m -> fold s_m ts1' ts2'
                 | UnificationError s -> UnificationError s)
             | _, _ ->
                UnificationError
                  (sprintf "type mismatch: %s and %s"
                     (T.show t1) (T.show t2))
           in fold s_m ts1 ts2
         else
           UnificationError
             (sprintf "type mismatch: %s and %s"
                (T.show t1) (T.show t2))
      | _ ->
         UnificationError
           (sprintf "type mismatch: %s and %s"
              (T.show t1) (T.show t2)))
  | T.Gen i -> Error.corrupt "unify: TGen"

let unify s_m t1 t2 =
  match unify0 s_m t1 t2 with
    UnificationOk s_m -> s_m
  | UnificationError s -> Error.error s

let counter = ref 0

let rec find_type mdb s_m s_v expr =
  let c = !counter in
  (if !Option.debug || !Option.debug_type then
     (counter := c + 1;
      printf "find_type[%d] << %s\n" c (S.show expr);
      flush stdout));
  let (s_m, t) = find_type2 mdb s_m s_v expr in
  (if !Option.debug || !Option.debug_type then
     (printf "find_type[%d] >> %s\n" c (T.show (subst_tv s_m t));
     flush stdout));
  (s_m, t)

and find_type2 mdb s_m s_v expr =
  match expr with
  | S.Bool _                -> (s_m, T.App (T.Bool, []))
  | S.Int _                 -> (s_m, T.App (T.Int None, []))
  | S.Var id                -> find_type_var mdb s_m s_v id
  | S.Univ rt               -> find_type_univ mdb s_m s_v rt
  | S.Tuple xs              -> find_type_tuple mdb s_m s_v xs
  | S.Set xs ->
     let (s_m, t) = find_type_homo mdb s_m s_v xs in
     (s_m, T.App (T.Set, [t]))
  | S.List xs ->
     let (s_m, t) = find_type_homo mdb s_m s_v xs in
     (s_m, T.App (T.List, [t]))
  | S.SetRange (x, y)            -> find_type_set_range mdb s_m s_v x y
  | S.ListRange (x, y)           -> find_type_list_range mdb s_m s_v x y
  | S.Chset ps                   -> find_type_chset mdb s_m s_v ps
  | S.Chmap m                    -> find_type_chmap mdb s_m s_v m
  | S.And xs                     -> find_type_logical_and mdb s_m s_v xs
  | S.Or xs                      -> find_type_logical_or mdb s_m s_v xs
  | S.If (test, e1, e2)          -> find_type_if mdb s_m s_v test e1 e2
  | S.Let (binding, e)           -> find_type_let mdb s_m s_v binding e
  | S.Case (e, rn, bs)           -> find_type_case mdb s_m s_v e rn bs
  | S.Stop                       -> (s_m, T.App (T.Process, []))
  | S.Skip                       -> (s_m, T.App (T.Process, []))
  | S.Spon p                     -> find_type_spon mdb s_m s_v p
  | S.Prefix (e, p)              -> find_type_prefix mdb s_m s_v e p
  | S.Receive (ch, rt, xs, g, p) -> find_type_receive mdb s_m s_v ch rt xs g p
  | S.Branch ps                  -> find_type_process_list mdb s_m s_v ps
  | S.Alt ps                     -> find_type_process_list mdb s_m s_v ps
  | S.Amb ps                     -> find_type_process_list mdb s_m s_v ps
  | S.Seq ps                     -> find_type_process_list mdb s_m s_v ps
  | S.Par (x, ps)                -> find_type_par mdb s_m s_v x ps
  | S.Hide (x, p)                -> find_type_hide mdb s_m s_v x p
  | S.Rename (m, p)              -> find_type_rename mdb s_m s_v m p
  | S.XAlt (x, r, rt, p)         -> find_type_xalt mdb s_m s_v x r rt p
  | S.XAmb (x, r, rt, p)         -> find_type_xalt mdb s_m s_v x r rt p
  | S.XSeq (x, r, rt, p)         -> find_type_xseq mdb s_m s_v x r rt p
  | S.XPar (x, r, rt, a, p)      -> find_type_xpar mdb s_m s_v x r rt a p
  | S.Fun (xts, e, rt)           -> find_type_fun mdb s_m s_v xts e rt
  | S.Apply (f, rt_f, ets)       -> find_type_apply mdb s_m s_v f rt_f ets
  | S.Pos (pos, e) ->
     Error.with_pos pos
       (fun () ->
         find_type mdb s_m s_v e)

and find_type_var mdb s_m s_v id =
  let t =
    match IdMap.find_opt id s_v with
      Some t -> t
    | None -> Mdb.lookup_type mdb id
  in (s_m, instantiate mdb t)

and find_type_univ mdb s_m s_v rt =
  match !rt with
    None ->
     let m = alloc_tvar mdb in
     rt := Some m;
     (s_m, T.App (T.Set, [m]))
  | Some t ->
     (s_m, T.App (T.Set, [t]))

and find_type_tuple mdb s_m s_v xs =
  let (s_m, ts) =
    List.fold_left_map
      (fun s_m x -> find_type mdb s_m s_v x)
      s_m [] xs
  in
  (s_m, make_tuple_type ts)

and find_type_homo mdb s_m s_v xs =
  let m = alloc_tvar mdb in
  let s_m =
    List.fold_left
      (fun s_m x ->
        let (s_m, t) = find_type mdb s_m s_v x in
        unify s_m m t)
      s_m xs
  in (s_m, m)

and dig_ch_type_list mdb s_m t =
  let rec dig s_m rs t =
    match unify0 s_m t T.event with
      UnificationOk s_m -> (s_m, List.rev rs)
    | UnificationError _ ->
       let u1 = alloc_tvar mdb in
       let u2 = alloc_tvar mdb in
       match unify0 s_m t (T.App (T.Fun, [u1; u2])) with
         UnificationOk s_m -> dig s_m (u1::rs) u2
       | UnificationError s -> Error.error s
  in dig s_m [] t

and check_channel mdb s_m s_v e rt =
  let (s_m, t) = find_type mdb s_m s_v e in
  rt := Some t;
  dig_ch_type_list mdb s_m t

and find_type_set_range mdb s_m s_v x y =
  let s_m = ensure_range_type mdb s_m s_v x y in
  (s_m, T.App (T.Set, [T.int]))

and find_type_list_range mdb s_m s_v x y =
  let s_m = ensure_range_type mdb s_m s_v x y in
  (s_m, T.App (T.List, [T.int]))

and ensure_range_type mdb s_m s_v x y =
  let (s_m, t) = find_type mdb s_m s_v x in
  let (s_m, u) = find_type mdb s_m s_v y in
  let s_m = unify s_m t T.int in
  let s_m = unify s_m u T.int in
  s_m

and find_type_chset mdb s_m s_v ps =
  let s_m =
    List.fold_left
      (fun s_m (e, rt) ->
        let (s_m, ts) = check_channel mdb s_m s_v e rt in
        s_m)
      s_m ps
  in
  (s_m, T.App (T.Set, [T.event]))

and ensure_equal_type_list s_m ts us =
  let rec loop s_m ts us =
    match ts with
      [] ->
      (match us with
         [] -> ()
       | _ -> Error.error "type mismatch in chmap")
    | t::ts' ->
       (match us with
          [] -> Error.error "type mismatch in chmap"
        | u::us' ->
           let s_m = unify s_m t u in
           loop s_m ts' us')
  in
  loop s_m ts us

and find_type_chmap mdb s_m s_v m =
  let s_m =
    List.fold_left
      (fun s_m ((a, rt_a), (b, rt_b)) ->
        let (s_m, ts_a) = check_channel mdb s_m s_v a rt_a in
        let (s_m, ts_b) = check_channel mdb s_m s_v b rt_b in
        (if ts_a <> [] && ts_b <> [] then
           ensure_equal_type_list s_m ts_a ts_b);
        s_m)
      s_m m
  in
  (s_m, T.event_map)

 and find_type_logical_and mdb s_m s_v xs =
   let (s_m, t) = find_type_homo mdb s_m s_v xs in
   let s_m = unify s_m t T.bool in
   (s_m, T.bool)

 and find_type_logical_or mdb s_m s_v xs =
   let (s_m, t) = find_type_homo mdb s_m s_v xs in
   let s_m = unify s_m t T.bool in
   (s_m, T.bool)

and find_type_if mdb s_m s_v test e1 e2 =
  let (s_m, t_test) = find_type mdb s_m s_v test in
  let s_m = unify s_m t_test T.bool in
  let (s_m, t_e1) = find_type mdb s_m s_v e1 in
  let (s_m, t_e2) = find_type mdb s_m s_v e2 in
  let s_m = unify s_m t_e1 t_e2 in
  (s_m, t_e1)

and find_type_let mdb s_m s_v bindings expr =
  let rec loop s_m s_vx bs =
    match bs with
      [] -> find_type mdb s_m s_vx expr
    | (ps, e)::bs' ->
       let (s_m, t) = find_type mdb s_m s_v e in
       match ps with
         [] -> loop s_m s_vx bs'
       | p::ps' ->
          let (x, rt) = p in
          (match ps' with
             [] ->
              let s_vx' = extend_type_env s_vx x t in
              rt := Some t;
              loop s_m s_vx' bs'
           | _ ->
              let ts = List.map (fun p -> alloc_tvar mdb) ps in
              let s_m = unify s_m t (T.App (T.Tuple, ts)) in
              let s_vx' =
                List.fold_left2
                  (fun s_vx p t ->
                    let (x, rt) = p in
                    rt := Some t;
                    extend_type_env s_vx x t)
                  s_vx ps ts
              in
              loop s_m s_vx' bs')
  in loop s_m s_v bindings

and find_type_case mdb s_m s_v expr rn branches =
  match branches with
    [] -> Error.error "no branches in case"
  | (ctor, (_, e))::bs ->
     let variant_spec = Mdb.get_variant_spec_from_ctor_name mdb ctor in
     rn := Some variant_spec.variant_name;
     let (s_m, t_expr) = find_type mdb s_m s_v expr in
     let s_m = unify s_m variant_spec.variant_type t_expr in
     let t_r = alloc_tvar mdb in
     let rec scan s_m cs bs =
       match bs with
         [] ->
          if cs = [] then
            s_m
          else
            Error.error "case patterns are not exhaustive"
       | (ctor, (vs, e))::bs ->
          (match List.assoc_opt ctor cs with
             None ->
              Error.error_s "unknown ctor in case: " (Id.show ctor)
           | Some ctor_spec ->
              let s_vx =
                List.fold_left2
                  extend_type_env
                  s_v vs ctor_spec.ctor_type_list
              in
              let (s_m, t_e) = find_type mdb s_m s_vx e in
              let s_m = unify s_m t_r t_e in
              scan s_m (List.remove_assoc ctor cs) bs)
     in
     let s_m = scan s_m variant_spec.ctor_spec_alist branches in
     (s_m, t_r)

and find_type_spon mdb s_m s_v p =
  let (s_m, t_p) = find_type mdb s_m s_v p in
  let s_m = unify s_m t_p T.process in
  (s_m, T.process)

and find_type_prefix mdb s_m s_v e p =
  let (s_m, t_e) = find_type mdb s_m s_v e in
  let s_m = unify s_m t_e T.event in
  let (s_m, t_p) = find_type mdb s_m s_v p in
  let s_m = unify s_m t_p T.process in
  (s_m, T.process)

and find_type_receive mdb s_m s_v ch rt_ch xs g p =
  let ts = List.map (fun v -> alloc_tvar mdb) xs in
  let s_vx = List.fold_left2 extend_type_env s_v xs ts in
  let (s_m, t_ch) = find_type mdb s_m s_v ch in
  rt_ch := Some t_ch;
  let s_m = unify s_m t_ch (T.make_channel_type ts) in
  let (s_m, t_g) = find_type mdb s_m s_vx g in
  let s_m = unify s_m t_g T.bool in
  let (s_m, t_p) = find_type mdb s_m s_vx p in
  let s_m = unify s_m t_p T.process in
  (s_m, T.process)

and find_type_xalt mdb s_m s_v x r rt_r p =
  let m = alloc_tvar mdb in
  let (s_m, t_r) = find_type mdb s_m s_v r in
  rt_r := Some t_r;
  let s_m = unify s_m t_r (T.App (T.Set, [m])) in
  let s_vx = extend_type_env s_v x m in
  let (s_m, t_p) = find_type mdb s_m s_vx p in
  let s_m = unify s_m t_p T.process in
  (s_m, T.process)

and find_type_xseq mdb s_m s_v x r rt_r p =
  let m = alloc_tvar mdb in
  let (s_m, t_r) = find_type mdb s_m s_v r in
  rt_r := Some t_r;
  let s_m = unify s_m t_r (T.App (T.List, [m])) in
  let s_vx = extend_type_env s_v x m in
  let (s_m, t_p) = find_type mdb s_m s_vx p in
  let s_m = unify s_m t_p T.process in
  (s_m, T.process)

and find_type_xpar mdb s_m s_v x r rt_r a p =
  let (s_m, t_a) = find_type mdb s_m s_v a in
  let s_m = unify s_m t_a T.event_set in
  let m = alloc_tvar mdb in
  let (s_m, t_r) = find_type mdb s_m s_v r in
  rt_r := Some t_r;
  let s_m = unify s_m t_r (T.App (T.Set, [m])) in
  let s_vx = extend_type_env s_v x m in
  let (s_m, t_p) = find_type mdb s_m s_vx p in
  let s_m = unify s_m t_p T.process in
  (s_m, T.process)

and find_type_process_list mdb s_m s_v ps =
  let s_m =
    List.fold_left
      (fun s_m p ->
        let (s_m, t_p) = find_type mdb s_m s_v p in
        unify s_m t_p T.process)
      s_m ps
  in (s_m, T.process)

and find_type_par mdb s_m s_v x ps =
  let (s_m, t_x) = find_type mdb s_m s_v x in
  let s_m = unify s_m t_x T.event_set in
  find_type_process_list mdb s_m s_v ps

and find_type_hide mdb s_m s_v x p =
  let (s_m, t_x) = find_type mdb s_m s_v x in
  let s_m = unify s_m t_x T.event_set in
  let (s_m, t_p) = find_type mdb s_m s_v p in
  let s_m = unify s_m t_p T.process in
  (s_m, T.process)

and find_type_rename mdb s_m s_v m p =
  let (s_m, t_m) = find_type mdb s_m s_v m in
  let s_m = unify s_m t_m T.event_map in
  let (s_m, t_p) = find_type mdb s_m s_v p in
  let s_m = unify s_m t_p T.process in
  (s_m, T.process)

and find_type_fun mdb s_m s_v xts e rt_r =
  let ts =
    List.map
      (fun (x, rt, tyspec_opt) ->
        let t =
          match tyspec_opt with
            None -> alloc_tvar mdb
          | Some tyspec -> tyspec_to_type mdb tyspec
        in
        rt := Some t; t)
      xts
  in
  let s_vx =
    List.fold_left2
      (fun s_v (x, rt, tyspec_opt) t ->
        extend_type_env s_v x t)
      s_v xts ts
  in
  let (s_m, t) = find_type mdb s_m s_vx e in
  rt_r := Some t;
  let t_f = List.fold_right T.make_fun_type ts t in
  (s_m, t_f)

and find_type_apply mdb s_m s_v f rt_f ets =
  let (s_m, ts) =
    List.fold_left_map
      (fun s_m (e, rt) ->
        let (s_m, t) = find_type mdb s_m s_v e in
        rt := Some t;
        (s_m, t))
    s_m [] ets
  in
  let (s_m, t_f) = find_type mdb s_m s_v f in
  rt_f := Some t_f;
  let t_r = alloc_tvar mdb in
  let t_f' = List.fold_right T.make_fun_type ts t_r in
  let s_m = unify s_m t_f t_f' in
  (s_m, t_r)

and ensure_event_type mdb s_m s_v x =
  let (s_m, t) = find_type mdb s_m s_v x in
  let _ = unify s_m t T.event in
  ()

and type_spec_tc_to_tc tstc =
  match tstc with
    S.TcBool     -> ToTc T.Bool
  | S.TcInt ropt -> ToTi ropt
  | S.TcTuple    -> ToTc T.Tuple
  | S.TcSet      -> ToTc T.Set
  | S.TcList     -> ToTc T.List
  | S.TcEvent    -> ToTc T.Event
  | S.TcFun      -> ToTc T.Fun
  | S.TcName n   -> ToTn n

and tyspec_to_type mdb tyspec =
  match tyspec with
    S.TApp (tstc, tyspec_list) ->
     let ts = List.map (tyspec_to_type mdb) tyspec_list in
     match type_spec_tc_to_tc tstc with
       ToTc tc -> T.App (tc, ts)
     | ToTi ropt ->
        (match ropt with
           None -> T.App (T.Int None, ts)
         | Some (a, b) ->
            let (s_m, t) = find_type mdb TVarMap.empty IdMap.empty a in
            let _ = unify s_m t T.int in
            let (s_m, t) = find_type mdb TVarMap.empty IdMap.empty b in
            let _ = unify s_m t T.int in
            let x = V.ensure_int (Eval.eval mdb V.env0 (E.convert mdb a)) in
            let y = V.ensure_int (Eval.eval mdb V.env0 (E.convert mdb b)) in
            if !Option.int_range_upper_bound_inclusive then
              T.App (T.Int (Some (x, y+1)), ts)
            else
              T.App (T.Int (Some (x, y)), ts))
     | ToTn n -> Mdb.get_type_def mdb n

let decompose_fun_type t =
  match t with
    T.App (T.Fun, [u; r]) ->
     (match u with
        T.App (T.Tuple, ts) -> (ts, r)
      | _ -> ([u], r))
  | _ -> ([], t)

let decompose_fun_expr expr t =
  match expr with
    S.Fun (xts, e, rt) ->
     let xs = List.map (fun (x, _, _) -> x) xts in
     let ts =
       List.map
         (fun (x, rt, _) ->
           match !rt with
             Some t -> t
           | None -> Error.corrupt_s "decompose_fun_expr" (S.show expr))
         xts
     in
     (match !rt with
        Some t_r -> (xs, ts, e, t_r)
      | None -> Error.corrupt_s "decompose_fun_expr" (S.show expr))
  | _ -> ([], [], expr, t)

let try_decompose_ch mdb e =
  let rec dig rs e =
    match e with
      S.Var n ->
       if Mdb.is_channel mdb n then
         Some (n, rs)
       else
         None
    | S.Apply (f, rt_f, ets) ->
       dig ((S.make_tuple (List.map fst ets))::rs) f
    | S.Pos (_, e) -> dig rs e
    | _ -> None
  in
  dig [] e

let is_fun_form e =
  match e with
    S.Fun _ -> true
  | _ -> false

let rec resolve_tv s_m expr =
  let g rt =
    match !rt with
      None -> Error.corrupt_s "resolve_tv" (S.show expr)
    | Some t ->
       rt := Some (subst_tv_with_check s_m t)
  in
  let rec f x =
    match x with
      S.Bool _ -> ()
    | S.Int _ -> ()
    | S.Var _ -> ()
    | S.Univ rt -> g rt
    | S.Tuple es -> List.iter f es
    | S.Set es -> List.iter f es
    | S.List es -> List.iter f es
    | S.SetRange (x, y) -> f x; f y
    | S.ListRange (x, y) -> f x; f y
    | S.Chset ps ->
       List.iter
         (fun (e, rt) -> g rt; f e)
         ps
    | S.Chmap m ->
       List.iter
         (fun ((a, rt_a), (b, rt_b)) ->
           g rt_a; g rt_b; f a; f b)
         m
    | S.And xs -> List.iter f xs
    | S.Or xs -> List.iter f xs
    | S.If (x, y, z) -> f x; f y; f z
    | S.Let (bs, e) ->
       List.iter
         (fun (ps, e) ->
           List.iter (fun p -> let (x, rt) = p in g rt) ps;
           f e)
         bs;
       f e
    | S.Case (e, rn, bs) ->
       f e; List.iter (fun (ctor, (xs, e)) -> f e) bs
    | S.Stop -> ()
    | S.Skip -> ()
    | S.Spon p -> f p
    | S.Prefix (e, p) -> f e; f p
    | S.Receive (ch, rt_ch, xs, guard, p) ->
       f ch; g rt_ch; f guard; f p
    | S.Branch ps -> List.iter f ps
    | S.Alt ps -> List.iter f ps
    | S.Amb ps -> List.iter f ps
    | S.Seq ps -> List.iter f ps
    | S.Par (a, ps) -> f a; List.iter f ps
    | S.Hide (a, p) -> f a; f p
    | S.Rename (m, p) -> f m; f p
    | S.XAlt (x, r, rt_r, p) -> f r; g rt_r; f p
    | S.XAmb (x, r, rt_r, p) -> f r; g rt_r; f p
    | S.XSeq (x, r, rt_r, p) -> f r; g rt_r; f p
    | S.XPar (x, r, rt_r, a, p) -> f r; g rt_r; f a; f p
    | S.Fun (xts, e, rt) ->
       List.iter (fun (x, rt, _) -> g rt) xts;
       f e; g rt
    | S.Apply (h, rt_f, ets) ->
       f h; g rt_f;
       List.iter
         (fun (e, rt) -> f e; g rt)
       ets
    | S.Pos (_, e) -> f e
  in f expr

let infer_type_defs mdb ds =
  Db.tr "infer_type_defs";
  let ts = List.map (fun (n, e) -> alloc_tvar mdb) ds in
  let s_v =
    List.fold_left2
      (fun s_v (n, e) t -> extend_type_env s_v n t)
      IdMap.empty ds ts
  in
  let s_m =
    List.fold_left2
      (fun s_m (n, e) t ->
        Error.with_context_name (Id.show n)
          (fun () ->
            let (s_m, u) = find_type mdb s_m s_v e in
            unify s_m t u))
      TVarMap.empty ds ts
  in
  Db.tr "  resolve";
  List.iter
    (fun (n, e) ->
      Error.with_context_name (Id.show n)
        (fun () -> resolve_tv s_m e))
    ds;
  Db.tr "  reg_type";
  IdMap.iter
    (fun n t ->
      let t' = subst_tv_with_check s_m t in
      Mdb.reg_type mdb n t')
    s_v;
  Db.tr "  classify into processes, functions, and values";
  List.iter2
    (fun (n, e) t ->
      Error.with_context_name (Id.show n)
        (fun () ->
          let t = subst_tv_with_check s_m t in
          if T.is_process_type t then
            let (xs, ts, e, t_r) = decompose_fun_expr e t in
            let process_spec = {
                process_name = n;
                process_param_list = xs;
                process_param_type_list = ts;
                process_expr = P.reduce (P.convert mdb e);
              }
            in Mdb.reg_process mdb n process_spec
          else if is_fun_form e then
            let (xs, ts, e, t_r) = decompose_fun_expr e t in
            let e = E.convert mdb e in
            let fun_spec = {
                fun_name = n;
                fun_param_list = xs;
                fun_param_type_list = ts;
                fun_return_type = t_r;
                fun_expr = e;
              }
            in
            Mdb.reg_fun mdb n fun_spec
          else
            let x = E.convert mdb e in
            let v = Eval.eval mdb V.env0 x in
            Mdb.reg_value mdb n v))
    ds ts

let handle_variant mdb n bs =
  Db.tr_s "handle_variant: " (Id.show n);
  let cs =
    List.map
      (fun (ctor, tyspec_list) ->
        let ts = List.map (tyspec_to_type mdb) tyspec_list in
        let ctor_spec = {
            ctor_name = ctor;
            ctor_type_list = ts;
          }
        in
        (ctor, ctor_spec))
      bs
  in
  Db.tr "=> done";
  Mdb.reg_variant mdb n cs

let handle_channels mdb ds =
  Db.tr "handle_channels";
  let alphabet =
    List.fold_left
      (fun alphabet (ns, tyspec_list) ->
        match ns with
          [] -> Error.corrupt "handle_channels: no channels"
        | n::_ ->
           Error.with_context_name (Id.show n)
             (fun () ->
               let ts = List.map (tyspec_to_type mdb) tyspec_list in
               let zss = List.map (Univ.calc_univ mdb) ts in
               let vss =
                 try
                   Utils.cartesian_product zss
                 with
                   Stack_overflow ->
                   Error.error "channel parameter is too big"
               in
               List.fold_left
                 (fun alphabet n ->
                   (if !Option.debug then
                      printf "handle_channel: %s\n" (Id.show n));
                   Mdb.reg_channel mdb n ts vss;
                   List.fold_left
                     (fun alphabet vs ->
                       (V.Event (n, vs))::alphabet)
                     alphabet vss)
                 alphabet ns))
      [] ds
  in
  Db.tr "  reg_alphabet";
  Mdb.reg_alphabet mdb alphabet

let infer_type_alias mdb n tyspec =
  Db.tr_s "nametype: " (Id.show n);
  Mdb.reg_type_alias mdb n (tyspec_to_type mdb tyspec)

let infer_type_scc mdb defs chdefs scc =
  Db.tr "infer_type_scc";
  let def =
    match scc with
      [] -> Error.error "infer_type_scc: no def"
    | n::ns -> IdMap.find n defs
  in
  match def with
    S.Def (n, e) ->
     let ds =
       List.map
         (fun n ->
           let def = IdMap.find n defs in
           match def with
             Def (n, e) -> (n, e)
           | _ -> Error.error_s "invalid dependency on " (Id.show n))
         scc
     in infer_type_defs mdb ds
  | S.DefChannel _ ->
     List.iter
       (fun n ->
         let def = IdMap.find n defs in
         match def with
           DefChannel _ -> ()
         | _ -> Error.error_s "invalid dependency on " (Id.show n))
       scc;
     handle_channels mdb chdefs
  | S.DefDatatype (n, bs) ->
     (match scc with
        [def] ->
         Error.with_context_name (Id.show n)
           (fun () -> handle_variant mdb n bs)
      | _ -> Error.error_s "invalid dependency on " (Id.show n))
  | S.DefNametype (n, tyspec) ->
     (match scc with
        [def] ->
         Error.with_context_name (Id.show n)
           (fun () -> infer_type_alias mdb n tyspec)
      | _ -> Error.error_s "invalid dependency on " (Id.show n))

let infer_type_scc_list mdb defs chdefs scc_list =
  List.iter (infer_type_scc mdb defs chdefs) scc_list
