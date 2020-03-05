open Printf
open Col
open CCol
open EventCol
open Lts

type deadlock_info = Id.t * (Event.t * C.t) list
type result_deadlock =
  DeadlockNone of C.t lts
| DeadlockFound of deadlock_info

exception Deadlock of C.t * ((Event.t * C.t) list)

let conv length iter find s0 ht =
  let dummy_state_prop = {
      state = s0;
      trans_map = EventMap.empty;
      b_tick = false;
      b_tau = false;
      tau_targets = IntSet.empty;
      initials = EventSet.empty;
    }
  in
  let n = length ht in
  let v = Array.make n dummy_state_prop in

  let trans_list_to_map trans =
    let rec loop map b_tick b_tau trans =
      match trans with
        [] -> (map, b_tick, b_tau)
      | (u, t)::trans' ->
         let s =
           match EventMap.find_opt u map with
             None -> IntSet.empty
           | Some s -> s
         in
         let (tid, _) = find ht t in
         let map = EventMap.add u (IntSet.add tid s) map in
         let (b_tick, b_tau) =
           match u with
             Tick -> (true, b_tau)
           | Tau | HiddenEvent _ -> (b_tick, true)
           | Event _ -> (b_tick, b_tau)
         in
         loop map b_tick b_tau trans'
    in loop EventMap.empty false false trans
  in

  iter
    (fun s (sid, trans) ->
      let (map, b_tick, b_tau) = trans_list_to_map trans in
      v.(sid) <- {
          state = s;
          trans_map = map;
          b_tick = b_tick;
          b_tau = b_tau;
          tau_targets = IntSet.empty;
          initials = EventSet.empty;
        })
    ht;
  v

let unfold_common mdb chk_dl process_name =
  let s0 = C.Process (V.env0, P.Cont (process_name, [])) in
  let s0 = Transitions.normalize mdb s0 in
  let next =
    if chk_dl then
      fun c _ path ->
      let trans = Transitions.trans mdb c in
      if trans = [] && c <> C.Omega then
        raise (Deadlock (s0, path))
      else
        trans
    else
      fun c _ _ -> Transitions.trans mdb c
  in
  let ht =
    Bfs.bfs
      (fun () -> ConfigHashtbl.create 0)
      ConfigHashtbl.replace
      ConfigHashtbl.mem
      ConfigHashtbl.length
      s0 next
  in
  let v =
    conv
      ConfigHashtbl.length
      ConfigHashtbl.iter
      ConfigHashtbl.find
      s0 ht
  in
  let print_state sep i =
    List.fold_left
      (fun s x ->
        if s="" then
          x
        else
          s ^ "\\l" ^ x)
      "" (C.desc v.(i).state)
  in
  {
    process_name = process_name;
    v = v;
    minacc_vec = [||];
    print_state = print_state;
    b_tau_targets = false;
    b_initials = false;
    b_minacc = false;
  }

let unfold mdb process_name =
  (if !Option.debug then
     printf "unfold %s\n" (Id.show process_name));
  unfold_common mdb false process_name

let check_deadlock mdb process_name =
  (if !Option.debug then
     printf "check_deadlock %s\n" (Id.show process_name));
  try
    let lts = unfold_common mdb true process_name in
    DeadlockNone lts
  with
    Deadlock (s0, path) ->
    DeadlockFound (process_name, ((Tau, s0)::(List.rev path)))
