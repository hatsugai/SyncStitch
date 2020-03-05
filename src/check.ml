open Printf
open Col
open IdCol
open TCol

type result =
  ResultOk
| ResultExplore of Id.t
| ResultError
| ResultDeadlock of Unfold.deadlock_info
| ResultDivergence of Divergence.divergence_info
| ResultTraceViolation of Refinement.trace_violation_info
| ResultFailureViolation of Refinement.failure_violation_info

let test_trace_opt : Event.t list option ref = ref None

let process_name_to_lts : (Id.t, C.t Lts.lts) Hashtbl.t = Hashtbl.create 0
let process_name_to_dlts : (Id.t, IntSet.t Lts.lts) Hashtbl.t = Hashtbl.create 0

let check_result : result ref = ref ResultOk

let get_check_result () =
  !check_result

let reg_check_result r =
  check_result := r

let get_lts_opt n =
  Hashtbl.find_opt process_name_to_lts n

let get_dlts_opt n =
  Hashtbl.find_opt process_name_to_dlts n

let get_lts n =
  match get_lts_opt n with
    Some lts -> lts
  | None -> Error.corrupt_s "get_lts: " (Id.show n)

let get_dlts n =
  match get_dlts_opt n with
    Some dlts -> dlts
  | None -> Error.corrupt_s "get_dlts: " (Id.show n)

let reg_lts n lts =
  Hashtbl.replace process_name_to_lts n lts

let reg_dlts n dlts =
  Hashtbl.replace process_name_to_dlts n dlts

let reg_test_trace trace =
  test_trace_opt := Some trace

let get_test_trace_opt () =
  !test_trace_opt

let check_test_trace mdb path0 =
  let trace_violation path =
    Printf.printf "* TEST TRACE VIOLATION\n";
    Report.print_trace stdout path0;
    exit 1
  in
  let rec loop tr path =
    match tr with
      [] ->
       (match path with
          [] -> ()
        | _ -> trace_violation path0)
    | e::tr' ->
       (match path with
          [] -> trace_violation path0
        | (u, _)::path' ->
           (match u with
              Event.Tau -> loop tr path'
            | Event.HiddenEvent _ -> loop tr path'
            | Event.Tick ->
               if e=u then
                 loop tr' path'
               else
                 trace_violation path0
            | Event.Event _ ->
               if e=u then
                 loop tr' path'
               else
                 trace_violation path0))
  in
  match get_test_trace_opt () with
    None -> ()
  | Some tr -> loop tr (List.tl path0)

let unfold mdb p =
  let lts = Unfold.unfold mdb p in
  reg_lts p lts;
  lts

let check_process_no_arg mdb n =
  let pspec = Mdb.lookup_process mdb n in
  if pspec.process_param_list <> [] then
    Error.error
      (sprintf "process taking no parameters must be specified for check: %s"
         (Id.show n))

let check_deadlock mdb p =
  check_process_no_arg mdb p;
  match Unfold.check_deadlock mdb p with
    DeadlockNone lts ->
     reg_lts p lts;
     ResultOk
  | DeadlockFound (process_name, path) ->
     Report.report_deadlock mdb p path;
     check_test_trace mdb path;
     ResultDeadlock (process_name, path)

let check_divergence mdb p =
  check_process_no_arg mdb p;
  let lts =
    match get_lts_opt p with
      None ->
       let lts = Unfold.unfold mdb p in
       reg_lts p lts;
       lts
    | Some lts -> lts
  in
  match Divergence.check_divergence mdb lts with
    NoDiv ->
     ResultOk
  | DivPathAndCycle (process_name, path, cycle) ->
     Report.report_divergence mdb p path cycle;
     check_test_trace mdb path;
     ResultDivergence (process_name, path, cycle)

let check_refinemet mdb check_refusals p q =
  check_process_no_arg mdb p;
  check_process_no_arg mdb q;
  let (lts_p, dlts_p) =
    match get_dlts_opt p with
      None ->
       let lts =
         match get_lts_opt p with
           None -> unfold mdb p
         | Some lts -> lts
       in
       let dlts = Det.determinize lts in
       (if check_refusals then Acceptances.calc_minacc lts dlts);
       reg_dlts p dlts;
       (lts, dlts)
    | Some dlts ->
       let lts = get_lts p in
       (if check_refusals && not dlts.b_minacc then
          Acceptances.calc_minacc lts dlts);
       (lts, dlts)
  in
  let lts_q =
    match get_lts_opt q with
      None -> unfold mdb q
    | Some lts -> lts
  in
  let r = Refinement.check_refinement check_refusals dlts_p lts_q in
  match r with
    NoViolation ->
     ResultOk
  | TraceViolation (pn, qn, path, u) ->
     Report.report_refinement_violation mdb lts_p dlts_p lts_q r;
     check_test_trace mdb path;
     ResultTraceViolation (pn, qn, path, u)
  | FailureViolation (pn, qn, path) ->
     Report.report_refinement_violation mdb lts_p dlts_p lts_q r;
     check_test_trace mdb path;
     ResultFailureViolation (pn, qn, path)

let check_traces mdb p q = check_refinemet mdb false p q
let check_failures mdb p q = check_refinemet mdb true p q

let check_assertion mdb assertion =
  match assertion with
    S.Deadlock p ->      check_deadlock mdb p
  | S.Divergence p ->    check_divergence mdb p
  | S.Traces (p, q) ->   check_traces mdb p q
  | S.Failures (p, q) -> check_failures mdb p q

let check_assertions mdb assertion_list =
  let rec loop assertion_list =
    match assertion_list with
      [] -> ResultOk
    | assertion::assertion_list' ->
       (match check_assertion mdb assertion with
          ResultOk -> loop assertion_list'
        | r -> r)
  in loop assertion_list

let reg_test_trace mdb test_trace_opt =
  match test_trace_opt with
    None -> ()
  | Some test_trace ->
     List.iter
       (Type.ensure_event_type mdb TVarMap.empty IdMap.empty)
       test_trace;
     let xs = List.map (E.convert mdb) test_trace in
     let ys = List.map (Eval.eval mdb V.env0) xs in
     let tr = List.map Event.convert ys in
     reg_test_trace tr
