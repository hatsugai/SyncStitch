open Printf
open Error
open Col
open Event
open EventCol
open Lts

type trace_violation_info = Id.t * Id.t * (int * int) path * Event.t
type failure_violation_info = Id.t * Id.t * (int * int) path
type result_refinement =
  NoViolation
| TraceViolation of trace_violation_info
| FailureViolation of failure_violation_info

exception ExnTraceViolation of (Event.t * (int * int)) list * Event.t
exception ExnFailureViolation of (Event.t * (int * int)) list

let make_next check_refusals lts_p lts_q =
  (fun (p, q) _ path ->
    (if check_refusals then (
       let minacc = lts_p.minacc_vec.(p) in
       let initials = lts_q.v.(q).initials in
       if lts_q.v.(q).b_tick then
         (if lts_p.v.(p).b_tick
             || (EventSetSet.cardinal minacc = 1
                 && EventSetSet.mem EventSet.empty minacc)
          then () else raise (ExnFailureViolation path))
       else if not lts_q.v.(q).b_tau then
         (if EventSetSet.exists
               (fun a -> EventSet.subset a initials)
               minacc
          then ()
          else raise (ExnFailureViolation path))));
    EventMap.fold
      (fun u qs acc ->
        IntSet.fold
          (fun q' acc ->
            match u with
              Tau | HiddenEvent _ -> (u, (p, q'))::acc
              | Tick | Event _ ->
                 (match EventMap.find_opt u lts_p.v.(p).trans_map with
                    Some ps ->
                     let p' = IntSet.choose ps in (* unique *)
                     (u, (p', q'))::acc
                  | None -> raise (ExnTraceViolation (path, u))))
          qs acc)
      lts_q.v.(q).trans_map [])

let check_refinement check_failures lts_p lts_q =
  (if !Option.debug then
     printf "check_refinement %s %s\n"
       (Id.show lts_p.process_name)
       (Id.show lts_q.process_name));
  calc_initials lts_q;
  let next = make_next check_failures lts_p lts_q in
  try
    let _ =
      Bfs.bfs
        (fun () -> Hashtbl.create 0)
        Hashtbl.replace
        Hashtbl.mem
        Hashtbl.length
        (0, 0) next
    in NoViolation
  with
    ExnTraceViolation (path, u) ->
     TraceViolation (lts_p.process_name, lts_q.process_name, path, u)
  | ExnFailureViolation path ->
     FailureViolation (lts_p.process_name, lts_q.process_name, path)
