open Printf

exception Error of string
exception Corrupt of string

let filename = ref ""
let context_name = ref ""
let context_pos = ref (0, 0)

let make_msg msg =
  let (lino, col) = !context_pos in
  if !context_name = "" then
    sprintf "%s:%d:%d: %s" !filename lino col msg
  else
    sprintf "%s:%d:%d: %s: %s" !filename lino col !context_name msg

let make_msg2 msg s =
  (make_msg msg) ^ s

let error msg       = raise (Error (make_msg msg))
let error_s msg s   = raise (Error (make_msg2 msg s))
let corrupt msg     = raise (Corrupt (make_msg msg))
let corrupt_s msg s = raise (Corrupt (make_msg2 msg s))

let with_context_name name f =
  let name_save = !context_name in
  context_name := name;
  let r = f () in
  context_name := name_save;
  r

let with_pos pos f =
  let pos_save = !context_pos in
  context_pos := pos;
  let r = f () in
  context_pos := pos_save;
  r

let with_context_name_pos name pos f =
  with_context_name name
    (fun () -> with_pos pos f)
