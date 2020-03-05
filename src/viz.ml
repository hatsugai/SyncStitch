open Printf
open Col
open EventCol
open Lts

let viz name print_event lts =
  let n = Array.length lts.v in
  let emit_states ch lts =
    for id=0 to n-1 do
      let sprop = lts.v.(id) in
      fprintf ch "%d [label=\"%d\\n" id id;
      fprintf ch "%s" (lts.print_state "\\n" id);
      fprintf ch "\"";
      if EventMap.is_empty sprop.trans_map then
        fprintf ch ",style=filled,color=pink];\n"
      else if id=0 then
        fprintf ch ",style=filled,color=cyan];\n"
      else
        fprintf ch "];\n"
    done
  in
  let emit_transitions ch print_event lts =
    let emit_tr sid u tt =
      IntSet.iter
        (fun tid ->
          fprintf ch "%d -> %d [label=\"%s\"];\n" sid tid (print_event u))
      tt
    in
    for id=0 to n-1 do
      let sprop = lts.v.(id) in
      EventMap.iter (emit_tr id) sprop.trans_map
    done
  in
  let ch = open_out (name ^ ".dot") in
  fprintf ch "digraph {\n";
  fprintf ch "node [fontname = \"Consolas\",fontsize=12];\n";
  fprintf ch "edge [fontname = \"Concolas\",fontsize=12];\n";
  emit_states ch lts;
  emit_transitions ch print_event lts;
  fprintf ch "}\n";
  close_out ch;
  let command = sprintf "dot -Tsvg -o %s.svg %s.dot" name name in
  let _ = Unix.system command in
  let command = sprintf "dot -Tpdf -o %s.pdf %s.dot" name name in
  let _ = Unix.system command in
  ()
