open Printf
open EventCol
open Lts

let print_trace ch path =
  List.iteri
    (fun i (u, _) ->
      fprintf ch "%3d %-10s\n" i (Event.show u))
    path

let report mdb f =
  let filename = Mdb.get_model_filename mdb in
  let ch = open_out (filename ^ ".report") in
  f stdout;
  f ch;
  close_out ch

let report_deadlock mdb name path =
  report mdb
    (fun ch ->
      fprintf ch "deadlock: %s\n" (Id.show name);
      List.iteri
        (fun i (u, s) ->
          fprintf ch "%3d %-10s %s\n" i (Event.show u) (C.show s))
        path)

let report_divergence mdb name path cycle =
  report mdb
    (fun ch ->
      fprintf ch "divergence: %s\n" (Id.show name);
      List.iteri
        (fun i (u, s) ->
          fprintf ch "%3d %-10s %s\n" i (Event.show u) (C.show s))
        path;
      fprintf ch "--- cycle ---------\n";
      List.iteri
        (fun i (u, s) ->
          fprintf ch "%3d %-10s %s\n" i (Event.show u) (C.show s))
        cycle)

let violation_states_and_simpath path =
  let path' = (Event.Tau, (0, 0))::(List.rev path) in
  match path with
    [] -> (0, 0), path'
  | (u, (p, q))::_ -> (p, q), path'

let print_simpath ch lts_q path =
  List.iteri
    (fun i (u, (p, q)) ->
      let c = lts_q.v.(q).state in
      fprintf ch "%3d %-10s %4d %s\n" i (Event.show u) p (C.show c))
    path

let report_refinement_violation mdb lts_p dlts_p lts_q violation =
  report mdb
    (fun ch ->
      match violation with
        Refinement.TraceViolation (pn, qn, path, u) ->
         fprintf ch "trace violation: %s [T= %s\n" (Id.show pn) (Id.show qn);
         fprintf ch "event: %s\n" (Event.show u);
         let (p, q), path = violation_states_and_simpath path in
         calc_initials_for_state_prop lts_p.v.(p);
         let initials_p = lts_p.v.(p).initials in
         let initials_q = lts_q.v.(q).initials in
         fprintf ch "%s initials: %s\n" (Id.show pn) (EventSet.show initials_p);
         fprintf ch "%s initials: %s\n" (Id.show qn) (EventSet.show initials_q);
         print_simpath ch lts_q path
      | Refinement.FailureViolation (pn, qn, path) ->
         fprintf ch "failures violation: %s [F= %s\n" (Id.show pn) (Id.show qn);
         let (p, q), path = violation_states_and_simpath path in
         let minacc_p = dlts_p.minacc_vec.(p) in
         let initials_q = lts_q.v.(q).initials in
         fprintf ch "%s minaccs: %s\n" (Id.show pn) (EventSetSet.show minacc_p);
         fprintf ch "%s initials: %s\n" (Id.show qn) (EventSet.show initials_q);
         print_simpath ch lts_q path
      | Refinement.NoViolation -> ())
