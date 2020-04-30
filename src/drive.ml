open Printf
open Error
open IdCol
open CCol
open Spec

let explore_process : string option ref = ref None
let viz_process : string option ref = ref None
let ppi = ref 96.0
let font_name = ref "monospace"
let font_size = ref 10.0

let usage_msg = "syncstitch [option...] filename\n"
let version = "SyncStitch 4.2"

let option_spec =
  [
    ("-x", Arg.String (fun x -> explore_process := Some x),
	 "<process-name>             explore the process");
    ("-g", Arg.String (fun x -> viz_process := Some x),
	 "<process-name>             generate graph (dot)");
    ("-ppi", Arg.Float (fun x -> ppi := x),
	 "<ppi>                    pixels-per-inch");
    ("-font", Arg.String (fun x -> font_name := x),
	 "<face>                  font face");
    ("-font-size", Arg.Float (fun x -> font_size := x),
	 "<size>             font size in pt");
    ("-width", Arg.Float (fun x -> Option.window_width := x),
	 "<width>                window width in inch");
    ("-height", Arg.Float (fun x -> Option.window_height := x),
	 "<height>              window height in inch");
    ("--debug",
     Arg.Unit (fun () -> Option.debug := true), "");
    ("-version",
     Arg.Unit (fun () -> printf "%s\n" version; exit 0),
     "                     show version");
  ]

let g_args : string list ref = ref []

let anon_fun s = g_args := !g_args @ [s]

let make_dmap defs =
  let add n d map =
    if IdMap.mem n map then
      Error.error (sprintf "duplicate '%s'" (Id.show n))
    else
      IdMap.add n d map
  in
  let rec collect map chs defs =
    match defs with
      [] -> (map, List.rev chs)
    | def::defs' ->
       match def with
         S.Def (n, e) ->
          collect (add n def map) chs defs'
       | S.DefChannel (ns, tyspec_dom_opt) ->
          let map =
            List.fold_left
              (fun map n -> add n def map)
              map ns
          in collect map ((ns, tyspec_dom_opt)::chs) defs'
       | S.DefDatatype (n, bs) ->
          collect (add n def map) chs defs'
       | S.DefNametype (n, tyspec) ->
          collect (add n def map) chs defs'
  in collect IdMap.empty [] defs

let print_defs defs =
  List.iter
    (fun def ->
      match def with
        S.Def (n, e) ->
         printf "def %s %s\n" (Id.show n) (S.show e)
      | S.DefChannel (ns, tyspec_dom_opt) ->
         printf "defch %s\n" (Id.show_list ns)
      | S.DefDatatype (n, bs) ->
         printf "deftype %s\n" (Id.show n)
      | S.DefNametype (n, tyspec) ->
         printf "defalias %s\n" (Id.show n))
    defs

let reg_builtins mdb builtin_fun_spec_list =
  let reg (n, f, t) =
    let bf_spec = {
        bf_name = n;
        bf_fun = f;
        bf_type = t;
      }
    in
    Mdb.reg_bf_spec mdb bf_spec
  in
  List.iter reg builtin_fun_spec_list

let pickup_trace command_list =
  let rec loop command_list =
    match command_list with
      [] -> None
    | command::command_list' ->
       (match command with
          S.CheckTrace xs -> Some xs
        | _ ->
           loop command_list')
  in loop command_list

let phase filename =
  Error.filename := filename;
  (if !Option.debug then printf "phase parse\n");
  let parse_result = ParserCsp.parse filename in
  (if !Option.debug then print_defs parse_result.def_list);
  (if !Option.debug then printf "phase dependency\n");
  let scc_list = Dependency.group_defs parse_result.def_list in

  let mdb = Mdb.make_mdb filename parse_result.command_list in
  reg_builtins mdb BuiltinsCsp.builtin_fun_spec_list;

  (if !Option.debug then printf "phase type checking\n");
  let (dmap, chdefs) = make_dmap parse_result.def_list in
  Type.infer_type_scc_list mdb dmap chdefs scc_list;

  Check.reg_test_trace mdb (pickup_trace parse_result.command_list);

  (if !Option.debug then Mdb.show mdb);

  Command.command mdb parse_result.command_list;

  match !viz_process with
    None ->
     (match !explore_process with
        None ->
         let check_result =
           Check.check_assertions mdb parse_result.assertion_list
         in
         Check.reg_check_result check_result;
         check_result
      | Some process_name ->
         let check_result = Check.ResultExplore (Id.make process_name) in
         Check.reg_check_result check_result;
         check_result)
  | Some s ->
     (if !Option.debug then printf "phase unfold\n");
     let lts = Unfold.unfold mdb (Id.make s) in
     Lts.show lts;
     Viz.viz filename Event.show lts;
     Check.ResultOk

type run_mode = RunModeCommandLine | RunModeProcessExplorer

let drive run_mode =
  match !g_args with
    [filename] ->
     let check_result =
       try
         phase filename
       with
         Error.Error s ->
          Printf.printf "%s\n" s;
          Check.ResultError
       | Error.Corrupt s ->
          Printf.printf "CORRUPT: %s\n" s;
          exit 1
       | x ->
          raise x
     in
     (match run_mode with
        RunModeCommandLine ->
         (match check_result with
            Check.ResultOk -> exit 0
          | Check.ResultExplore p -> ()
          | Check.ResultError -> exit 2
          | Check.ResultDeadlock _ | Check.ResultDivergence _
          | Check.ResultTraceViolation _ | Check.ResultFailureViolation _ ->
             exit 1)
      | RunModeProcessExplorer ->
         (match check_result with
            Check.ResultOk -> exit 0
          | Check.ResultExplore p -> ()
          | Check.ResultError -> exit 2
          | Check.ResultDeadlock info -> ()
          | Check.ResultDivergence info -> ()
          | Check.ResultTraceViolation info -> ()
          | Check.ResultFailureViolation info -> ()))

  | _ ->
     Arg.usage option_spec usage_msg;
     exit 0

let () =
  Arg.parse option_spec anon_fun usage_msg
