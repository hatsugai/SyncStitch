open Printf
open Error
open Col
open IdCol
open CCol
open EventCol
open Lts
open Csp
open Guedra
open Ts

let open_process_explore mdb process_name tsi ts initial_state index_tree =
  let process_name = Id.show process_name in
  let width = int_of_float (o_o.ppi *. 9.0) in
  let height = int_of_float (o_o.ppi *. 5.3) in
  let window_title =
    sprintf "%s - %s - SyncStitch" process_name mdb.Mdb.model_filename
  in
  let (wch, pch) = create_toplevel_window window_title 0 0 width height in
  let cch = make_chan () in
  let nch = make_chan () in
  let prop =
    { Pe.process_name = process_name;
      wch_toplevel = wch;
      width = width; height = height }
  in
  Pe.init wch pch cch nch prop mdb tsi ts initial_state index_tree

let label_desc label = [Event.show label]
let label_line label = Event.show label
let label_dash label =
  match label with
    Event.Event _ -> false
  | Event.Tau | Event.Tick | Event.HiddenEvent _ -> true

let ts_interface_lts mdb process_name path =
  let initial_state =
    let c0 = C.Process (V.env0, P.Cont (process_name, [])) in
    Transitions.normalize mdb c0
  in
  let next = fun c -> Transitions.trans mdb c in
  let ht = ConfigHashtbl.create 0 in

  let calc_trans_and_reg s =
    match ConfigHashtbl.find_opt ht s with
      Some (id, trans) -> (id, trans)
    | None ->
       let trans =
         if !Option.debug then
           let rs = next s in
           let v = Array.of_list rs in
           Array.sort compare v;
           Transitions v
         else
           try
             let rs = next s in
             let v = Array.of_list rs in
             Array.sort compare v;
             Transitions v
           with
             _ -> TransitionsError "error state"
       in
       let id = ConfigHashtbl.length ht in
       ConfigHashtbl.replace ht s (id, trans);
       (id, trans)
  in

  let find_index source label target =
    let (id, trans) = calc_trans_and_reg source in
    match trans with
      Transitions v -> Utils.find_index v (label, target)
    | TransitionsError _ -> error "find_index"
  in

  let path_to_index_list initial_state path =
    let rec loop rs source path =
      match path with
        [] -> List.rev rs
      | (label, target)::path' ->
         let index = find_index source label target in
         loop (index::rs) target path'
    in loop [] initial_state path
  in

  let transitions s =
    let (id, trans) = calc_trans_and_reg s in
    trans
  in

  let state_id s =
    let (id, trans) = calc_trans_and_reg s in
    id
  in

  let state_desc s = C.desc s in
  let state_properties s = C.desc s in
  let tsi =
    { transitions = transitions;
      state_id = state_id;
      state_desc = state_desc;
      state_properties = state_properties;
      label_desc = label_desc;
      label_line = label_line;
      label_dash = label_dash }
  in
  let index_list = path_to_index_list initial_state path in
  (tsi, initial_state, index_list)

let ts_interface_dlts mdb process_name path =
  let dlts = Check.get_dlts process_name in

  let transitions0 s =
    let trans =
      EventMap.fold
        (fun u tt acc ->
          IntSet.fold
            (fun t acc -> (u, t)::acc)
         tt acc)
      dlts.v.(s).trans_map []
    in
    let v = Array.of_list trans in
    v
  in

  let find_index source label target =
    let v = transitions0 source in
    Utils.find_index v (label, target)
  in

  let path_to_index_list initial_state path =
    let rec loop rs source path =
      match path with
        [] -> List.rev rs
      | (label, target)::path' ->
         let index = find_index source label target in
         loop (index::rs) target path'
    in loop [] initial_state path
  in

  let transitions s = Transitions (transitions0 s) in
  let state_id s = s in
  let state_desc s =
    let rs =
      EventSetSet.fold
        (fun s rs -> (EventSet.show s)::rs)
        dlts.minacc_vec.(s) []
    in (sprintf "%d" s)::(List.rev rs)
  in
  let state_properties s = state_desc s in
  let tsi =
    { transitions = transitions;
      state_id = state_id;
      state_desc = state_desc;
      state_properties = state_properties;
      label_desc = label_desc;
      label_line = label_line;
      label_dash = label_dash }
  in
  let index_list = path_to_index_list 0 path in
  (tsi, 0, index_list)

let explore mdb process_name path =
  let process_spec =
    try
      Mdb.lookup_process mdb process_name
    with
      _ ->
      fprintf stderr "unknown process: %s\n" (Id.show process_name);
      exit 1
  in
  (if process_spec.process_param_list <> [] then
     (fprintf stderr "only processes with no args can be explored: %s\n"
        (Id.show process_name);
      exit 1));
  let (tsi, initial_state, index_list) =
    ts_interface_lts mdb process_name path
  in
  let index_tree = { index_tree_front = index_list; index_tree_tails = []; } in
  open_process_explore mdb process_name tsi () initial_state index_tree

let explore_dlts mdb process_name path =
  let (tsi, initial_state, index_list) =
    ts_interface_dlts mdb process_name path
  in
  let index_tree = { index_tree_front = index_list; index_tree_tails = []; } in
  open_process_explore mdb process_name tsi () initial_state index_tree

let split_simpath path =
  let rec loop ps qs path =
    match path with
      [] -> (ps, qs)
    | (u, (p, q))::path' ->
       match u with
         Event.Tau | HiddenEvent _ ->
           loop ps ((u, q)::qs) path'
         | Tick | Event _ ->
           loop ((u, p)::ps) ((u, q)::qs) path'
  in loop [] [] path

let convert_path mdb process_name path =
  let lts = Check.get_lts process_name in
  List.map
    (fun (u, i) -> (u, lts.v.(i).state))
    path

let start_protected () =
  let mdb =
    match !Mdb.g_mdb_opt with
      Some mdb -> mdb
    | None -> error "syncstitch init: no mdb"
  in

  match Check.get_check_result () with
    ResultExplore process_name ->
     explore mdb process_name []

  | ResultDeadlock (process_name, path) ->
     explore mdb process_name (List.tl path)

  | ResultDivergence (process_name, path, cycle) ->
     explore mdb process_name (path @ (List.tl cycle))

  | ResultTraceViolation (pn, qn, path, event) ->
     let (path_p, path_q) = split_simpath path in
     let path = convert_path mdb qn path_q in
     explore mdb qn path

  | ResultFailureViolation (pn, qn, path) ->
     let (path_p, path_q) = split_simpath path in
     let path = convert_path mdb qn path_q in
     par [
         (fun () -> explore_dlts mdb pn path_p);
         (fun () -> explore mdb qn path);
       ]

  | _ ->
     Error.corrupt "start_protected"

let start () =
  if !Option.debug then
    start_protected ()
  else
    try
      start_protected ()
    with
      _ ->
      fprintf stderr "something bad happend\n";
      exit 1
