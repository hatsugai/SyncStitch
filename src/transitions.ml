open Printf
open Error
open IdCol
open Spec
open Event
open EventCol

exception TransException of string

let evset_diff_list x ys =
  List.fold_left EventSet.diff x ys

let conv_evset s =
  match s with
    V.Set xs ->
     List.fold_left
       (fun evset x ->
         match x with
         | V.Event (n, vs) -> EventSet.add (Event (n, vs)) evset
         | _ -> error "Transitions.conv_evset")
       EventSet.empty xs
  | _ -> error "Transitions.conv_evset"

let conv_evmap v =
  match v with
    V.Set ps ->
     List.fold_left
       (fun evmap x ->
         match x with
           V.Tuple [a; b] ->
            (match a with
               V.Event (na, vs_a) ->
                (match b with
                   V.Event (nb, vs_b) ->
                    let ea = Event (na, vs_a) in
                    let eb = Event (nb, vs_b) in
                    let s =
                      match EventMap.find_opt ea evmap with
                        Some s -> s
                      | None -> EventSet.empty
                    in
                    EventMap.add ea (EventSet.add eb s) evmap
                 | _ -> corrupt "Transitions.conv_evmap")
             | _ -> corrupt "Transitions.conv_evmap")
         | _ ->  corrupt "Transitions.conv_evmap")
       EventMap.empty ps
  | _ -> error "Transitions.conv_evset"

let normalize mdb c =

  let rec norm c =
    match c with
      C.Omega             -> c
    | C.Process (env, p)  -> norm_proc env p
    | C.Alt cs            -> C.Alt (norm_cs cs)
    | C.Seq (c, ps)       -> C.Seq (norm c, ps)
    | C.Par (x, cs)       -> C.Par (x, norm_cs cs)
    | C.AlphaPar (xs, cs) -> C.AlphaPar (xs, List.map norm cs)
    | C.Hide (x, c')      -> C.Hide (x, norm c')
    | C.Rename (m, c')    -> C.Rename (m, norm c')

  and norm_cs cs =
    List.map norm cs

  and norm_env env p =
    let bs =
      IdMap.fold
        (fun n v bs -> IdSet.add n bs)
        env IdSet.empty
    in
    let fv = P.collect_vars bs IdSet.empty p in
    let env' =
      IdSet.fold
        (fun n env' -> IdMap.add n (IdMap.find n env) env')
        fv IdMap.empty
    in env'

  and norm_proc env p =
    match p with
      P.Stop                       -> C.Process (V.env0, p)
    | P.Skip                       -> C.Process (V.env0, p)
    | P.Omega                      -> C.Omega
    | P.Cont (n, es)               -> norm_cont env n es
    | P.Spon p'                    -> C.Process (norm_env env p, p)
    | P.Prefix (e, p')             -> C.Process (norm_env env p, p)
    | P.Receive (ch, _, xs, g, p') -> C.Process (norm_env env p, p)
    | P.Branch ps                  -> C.Process (norm_env env p, p)
    | P.Alt ps                     -> C.Alt (norm_ps env ps)
    | P.Amb ps                     -> C.Process (norm_env env p, p)
    | P.Seq ps                     -> norm_seq env ps
    | P.Par (x, ps)                -> norm_par env x ps
    | P.AlphaPar xs                -> norm_apar env xs
    | P.Hide (x, p)                -> norm_hide env x p
    | P.Rename (m, p)              -> norm_rename env m p
    | P.XAlt (x, r, _, p)          -> norm_xalt env x r p
    | P.XAmb (x, r, _, p')         -> C.Process (norm_env env p, p)
    | P.XSeq (x, r, _, p)          -> norm_xseq env x r p
    | P.XPar (x, r, _, a, p)       -> norm_xpar env x r a p
    | P.XAlphaPar (x, r, _, a, p)  -> norm_xapar env x r a p
    | P.If (test, p1, p2)          -> norm_if env test p1 p2
    | P.Let (bs, p)                -> norm_let env bs p
    | P.Case (e, n, bs)            -> norm_case env e bs
    | P.Pos (_, p)                 -> norm_proc env p

  and norm_cont env n es =
    let vs = List.map (fun e -> Eval.eval mdb env e) es in
    let process_spec = Mdb.lookup_process mdb n in
    let envx = Eval.extend_env env process_spec.process_param_list vs in
    norm (C.Process (envx, process_spec.process_expr))

  and norm_ps env ps =
    List.map (fun p -> norm (C.Process (env, p))) ps

  and norm_seq env ps =
    match ps with
      [] -> C.Process (V.env0, P.Skip)
    | [p] -> norm_proc env p
    | p::ps' ->
       let qs = List.map (fun p -> (norm_env env p, p)) ps' in
       C.Seq (norm_proc env p, qs)

  and norm_par env x ps =
    let v = Eval.eval mdb env x in
    let s = conv_evset v in
    C.Par (s, norm_ps env ps)

  and norm_apar env alpha_process_list =
    let alpha_config_list =
      List.map
        (fun (a, p) ->
          let v = Eval.eval mdb env a in
          let a = conv_evset v in
          let c = norm_proc env p in
          (a, c))
        alpha_process_list
    in
    make_apar_from_alpha_config_list alpha_config_list

  and make_apar_from_alpha_config_list alpha_config_list =
    (*
      xs: (alpha, config) list
      ys: (alpha, nosync) list (rev)
      rs: config list (rev)
      inv: rev vs @ us = us0  (alphabet list)
     *)
    let rec loop xs cs us acs =
      match acs with
        [] -> C.AlphaPar (List.rev xs, List.rev cs)
      | (a, c)::acs' ->
         (* b = u - (vs Un us') *)
         let b =
           List.fold_left
             (fun a (a', _) -> EventSet.diff a a')
             (List.fold_left EventSet.diff a us) acs'
         in
         loop ((a, b)::xs) (c::cs) (a::us) acs'
    in
    loop [] [] [] alpha_config_list

  and norm_hide env x p =
    let v = Eval.eval mdb env x in
    let s = conv_evset v in
    C.Hide (s, norm (C.Process (env, p)))

  and norm_rename env m p =
    let v = Eval.eval mdb env m in
    let evmap = conv_evmap v in
    C.Rename (evmap, norm (C.Process (env, p)))

  and norm_xalt env x r p =
    let v = Eval.eval mdb env r in
    let cs =
      match v with
        V.Set vs ->
         List.map
           (fun v ->
             let envx = Eval.extend_env1 env x v in
             norm (C.Process (envx, p)))
           vs
      | _ -> error "norm_xop_set"
    in
    C.Alt cs

  and norm_xseq env x r p =
    let env_list =
      let v = Eval.eval mdb env r in
      match v with
        V.List vs ->
         List.map
           (fun v -> Eval.extend_env1 env x v)
           vs
      | _ -> error "norm_xop_list"
    in
    match env_list with
      [] -> C.Process (V.env0, P.Skip)
    | [env] -> C.Process (env, p)
    | env::env_list' ->
       C.Seq (norm_proc env p, List.map (fun env -> (env, p)) env_list')

  and norm_xpar env x r a p =
    let v = Eval.eval mdb env a in
    let s = conv_evset v in
    let v = Eval.eval mdb env r in
    match v with
      V.Set vs ->
       (match vs with
          [] -> error "range is empty in xpar"
        | [v] ->
           let envx = Eval.extend_env1 env x v in
           norm (C.Process (envx, p))
        | _ ->
           let cs =
             List.map
               (fun v ->
                 let envx = Eval.extend_env1 env x v in
                 norm (C.Process (envx, p)))
               vs
           in
           C.Par (s, cs))
    | _ -> error "norm_xop_set"

  and norm_xapar env x r a p =
    let v = Eval.eval mdb env r in
    match v with
      V.Set vs ->
       (match vs with
          [] -> error "range is empty in xapar"
        | _ ->
           let alpha_config_list =
             List.map
               (fun v ->
                 let envx = Eval.extend_env1 env x v in
                 let v = Eval.eval mdb envx a in (* eval in x-env *)
                 let a = conv_evset v in
                 let c = norm (C.Process (envx, p)) in (* normalized in x-env *)
                 (a, c)) (* (alpha, config) *)
               vs
           in
           make_apar_from_alpha_config_list alpha_config_list)
    | _ -> error "norm_xop_set"

  and norm_if env test p1 p2 =
    match Eval.eval mdb env test with
      Bool true  -> norm (C.Process (env, p1))
    | Bool false -> norm (C.Process (env, p2))
    | _ -> error "norm_if"

  and norm_let env bs p =
    let envx =
      List.fold_left
        (fun envx (ps, e) ->
          let v = Eval.eval mdb env e in
          match ps with
            [] -> envx
          | p::ps' ->
             let (x, t) = p in
             (match ps' with
                [] -> Eval.extend_env1 envx x v
              | _ ->
                 (match v with
                    V.Tuple vs -> Eval.extend_env_ps envx ps vs
                  | _ -> error "norm_let")))
        env bs
    in norm (C.Process (envx, p))

  and norm_case env e bs =
    match Eval.eval mdb env e with
      Variant (ctor, vs) ->
       let (xs, p) = List.assoc ctor bs in
       let envx = Eval.extend_env env xs vs in
       norm (C.Process (envx, p))
    | _ -> error "trans_case"

  in norm c

let counter = ref 0

let rec trans mdb c =
  let i = !counter in
  (if !Option.debug then
     (counter := i + 1;
      printf "trans[%d] << %s\n" i (C.show c);
      flush stdout));
  let tr = trans2 mdb c in
  (if !Option.debug then
     (printf "trans[%d] >>" i;
      List.iter
        (fun (e, c) ->
          printf "    %s %s\n" (show e) (C.show c))
        tr;
      flush stdout));
  tr

 and trans2 mdb c =

  let rec trans c =
    match c with
      C.Omega             -> []
    | C.Process (env, p)  -> trans_process env p
    | C.Alt cs            -> trans_alt_config cs
    | C.Seq (c, ps)       -> trans_seq_config c ps
    | C.Par (x, cs)       -> trans_par_config x cs
    | C.AlphaPar (xs, cs) -> trans_apar_config xs cs
    | C.Hide (x, c)       -> trans_hide_config x c
    | C.Rename (m, c)     -> trans_rename_config m c

  and trans_process env p =
    match p with
      P.Stop                      -> []
    | P.Skip                      -> [(Tick, C.Omega)]
    | P.Omega                     -> []
    | P.Cont (n, es)              -> raise (TransException (P.show p))
    | P.Spon p                    -> trans_spon env p
    | P.Prefix (e, p)             -> trans_prefix env e p
    | P.Receive (ch, _, xs, g, p) -> trans_receive env ch xs g p
    | P.Branch ps                 -> trans_branch env ps
    | P.Alt ps                    -> raise (TransException (P.show p))
    | P.Amb ps                    -> trans_amb env ps
    | P.Seq ps                    -> raise (TransException (P.show p))
    | P.Par (x, ps)               -> raise (TransException (P.show p))
    | P.AlphaPar xs               -> raise (TransException (P.show p))
    | P.Hide (x, p)               -> raise (TransException (P.show p))
    | P.Rename (m, p)             -> raise (TransException (P.show p))
    | P.XAlt (x, r, _, p)         -> raise (TransException (P.show p))
    | P.XAmb (x, r, _, p)         -> trans_xamb env x r p
    | P.XSeq (x, r, _, p)         -> raise (TransException (P.show p))
    | P.XPar (x, r, _, a, p)      -> raise (TransException (P.show p))
    | P.XAlphaPar (x, r, _, a, p) -> raise (TransException (P.show p))
    | P.If (test, p1, p2)         -> raise (TransException (P.show p))
    | P.Let (bs, p)               -> raise (TransException (P.show p))
    | P.Case (e, n, bs)           -> raise (TransException (P.show p))
    | P.Pos (pos, p) ->
       with_pos pos
         (fun () ->
           trans_process env p)

  and trans_spon env p =
    [(Tau, C.Process (env, p))]

  and trans_prefix env e p =
    let v = Eval.eval mdb env e in
    match v with
      V.Event (n, es) -> [(Event (n, es), C.Process (env, p))]
    | _ -> Error.corrupt_s "trans_prefix" (V.show v)

  and trans_receive env ch params guard process =
    let v_ch = Eval.eval mdb env ch in
    let (ch_name, vs_partial) =
      match v_ch with
        V.Channel (n, vs) -> (n, vs)
      | _ -> Error.corrupt_s "trans_receive" (V.show v_ch)
    in
    let domain = Mdb.channel_domain mdb ch_name in
    List.fold_left
      (fun acc vs ->
        match Utils.prefix_rest vs_partial vs with
          None -> acc
        | Some vs_tail ->
        let envx = Eval.extend_env env params vs_tail in
        match Eval.eval mdb envx guard with
          V.Bool false -> acc
        | V.Bool true ->
           let event = Event (ch_name, vs) in
           (event, C.Process (envx, process))::acc
        | _ -> error "trans_receive")
      [] domain

  and trans_branch env ps =
    List.fold_left
      (fun acc p ->
        let c = normalize mdb (C.Process (env, p)) in
        (trans c) @ acc)
      [] ps

  and trans_amb env ps =
    List.map (fun p -> (Tau, C.Process (env, p))) ps

  and trans_xamb env x r p =
    let vs =
      let v = Eval.eval mdb env r in
      match v with
        V.Set vs -> vs
      | _ -> corrupt "trans_xamb"
    in
    if vs = [] then
      Error.error "range is empty in xamb"
    else
      List.map
        (fun v ->
          let envx = Eval.extend_env1 env x v in
          (Tau, C.Process (envx, p)))
        vs

  and trans_alt_config cs =
    let rec scan acc rs cs =
      match cs with
        [] -> acc
      | c::cs' ->
         let rec loop acc tr =
           match tr with
             [] -> scan acc (c::rs) cs'
           | (u, c')::tr' ->
              (match u with
                 Tau | HiddenEvent _ ->
                  let t = C.Alt (List.rev_append rs (c'::cs')) in
                  loop ((u, t)::acc) tr'
               | Tick | Event _ -> loop ((u, c')::acc) tr')
         in loop acc (trans c)
    in scan [] [] cs

  and trans_seq_config c ps =
    let rec loop acc tr =
      match tr with
        [] -> acc
      | (e, c')::tr' ->
         (match e with
          | Tick ->
             (match ps with
                [] -> corrupt "trans_seq_config"
              | [(env, p)] ->
                 loop ((Tau, C.Process (env, p))::acc) tr'
              | (env, p)::ps' ->
                 loop ((Tau, C.Seq (C.Process (env, p), ps'))::acc) tr')
          | Tau | Event _ | HiddenEvent _ ->
             loop ((e, C.Seq (c', ps))::acc) tr')
    in loop [] (trans c)

  and trans_par_config x cs =
    if List.for_all (fun c -> c = C.Omega) cs then
      [(Tick, C.Omega)]
    else
      let m = List.length cs in
      let ht = Hashtbl.create 0 in
      let reg k (n, vs) c =
        match Hashtbl.find_opt ht (n, vs) with
          Some v -> v.(k) <- c::v.(k)
        | None ->
           let v = Array.make m [] in
           v.(k) <- [c];
           Hashtbl.replace ht (n, vs) v
      in
      let sync acc =
        Hashtbl.fold
          (fun (n, vs) v acc ->
            List.fold_left
              (fun acc cs -> (Event (n, vs), C.Par (x, cs))::acc)
           acc (Utils.cartesian_product (Array.to_list v)))
        ht acc
      in
      let rec scan acc k rs cs =
        match cs with
          [] -> sync acc
        | c::cs' ->
           let rec loop acc tr =
             match tr with
               [] -> scan acc (k+1) (c::rs) cs'
             | (u, c')::tr' ->
                (match u with
                   Tau | HiddenEvent _ ->
                    let t = C.Par (x, List.rev_append rs (c'::cs')) in
                    loop ((u, t)::acc) tr'
                 | Tick ->
                    assert (c' = C.Omega);
                    let t = C.Par (x, List.rev_append rs (c'::cs')) in
                    loop ((Tau, t)::acc) tr'
                 | Event (n, vs) ->
                    if EventSet.mem u x then
                      (reg k (n, vs) c';
                       loop acc tr')
                    else
                      let t = C.Par (x, List.rev_append rs (c'::cs')) in
                      loop ((u, t)::acc) tr')
           in loop acc (trans c)
      in scan [] 0 [] cs

  and trans_apar_config xs cs =
    if List.for_all (fun c -> c = C.Omega) cs then
      [(Tick, C.Omega)]
    else
      trans_apar_config2 xs cs

  and trans_apar_config2 xs0 cs0 =
    let m = List.length cs0 in
    assert (m = List.length xs0);
    let ht = Hashtbl.create 0 in

    let makev e =
      let v = Array.make m [] in
      let rec loop k xs cs =
        match xs, cs with
        | (a, b)::xs', c::cs' ->
           (if EventSet.mem e a then
              v.(k) <- []       (* target states to be added *)
            else
              v.(k) <- [c]);    (* stay, not participate in sync *)
           loop (k+1) xs' cs'
        | _, _ -> v
      in
      loop 0 xs0 cs0
    in

    let reg k e c =
      match Hashtbl.find_opt ht e with
      | Some v -> v.(k) <- c::v.(k)
      | None ->
         let v = makev e in
         v.(k) <- [c];
         Hashtbl.replace ht e v
    in

    let sync acc =
      Hashtbl.fold
        (fun e v acc ->
          let css = Utils.cartesian_product (Array.to_list v) in
          List.fold_left
            (fun acc cs -> (e, C.AlphaPar (xs0, cs))::acc)
            acc css)
        ht acc
    in

    let rec scan acc k rs xs cs =
      match xs, cs with
      | (a, b)::xs', c::cs' ->
         let rec loop acc tr =
           match tr with
             [] -> scan acc (k+1) (c::rs) xs' cs'
           | (u, c')::tr' ->
              (match u with
               | Tau | HiddenEvent _ ->
                  Db.tr "apar tau";
                  let t = C.AlphaPar (xs0, List.rev_append rs (c'::cs')) in
                  loop ((u, t)::acc) tr'
               | Tick ->
                  Db.tr "apar tick";
                  assert (c' = C.Omega);
                  let t = C.AlphaPar (xs0, List.rev_append rs (c'::cs')) in
                  loop ((Tau, t)::acc) tr'
               | Event (n, vs) ->
                  if EventSet.mem u b then (* no sync *)
                    let t = C.AlphaPar (xs0, List.rev_append rs (c'::cs')) in
                    Db.tr_s "apar no sync:" (Event.show u);
                    loop ((u, t)::acc) tr'
                  else if EventSet.mem u a then (* sync *)
                    begin
                      Db.tr_s "apar sync:" (Event.show u);
                      reg k u c'; loop acc tr'
                    end
                  else
                    begin
                      Db.tr_s "apar inhibited:" (Event.show u);
                      loop acc tr'
                    end)
         in loop acc (trans c)
      | _, _ -> sync acc
    in scan [] 0 [] xs0 cs0

  and trans_hide_config x c =
    List.fold_left
      (fun acc (u, c') ->
        match u with
          Tau -> (Tau, C.Hide (x, c'))::acc
        | Tick -> (Tick, C.Omega)::acc
        | Event (n, vs) ->
           if EventSet.mem u x then
             (HiddenEvent (n, vs), C.Hide (x, c'))::acc
           else
             (u, C.Hide (x, c'))::acc
        | HiddenEvent (n, vs) ->
           (u, C.Hide (x, c'))::acc)
      [] (trans c)

  and trans_rename_config m c =
    List.fold_left
      (fun acc (u, c') ->
        match u with
          Tau -> (Tau, C.Rename (m, c'))::acc
        | Tick -> (Tick, C.Omega)::acc
        | Event (n, vs) ->
           (match EventMap.find_opt u m with
              None ->
               (u, C.Rename (m, c'))::acc
            | Some s ->
               EventSet.fold
                 (fun u acc -> (u, C.Rename (m, c'))::acc)
                 s acc)
        | HiddenEvent (n, vs) ->
           (u, C.Rename (m, c'))::acc)
      [] (trans c)

  in
  List.map
    (fun (e, p) -> (e, normalize mdb p))
    (trans c)
