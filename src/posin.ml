type pos = {
    lino : int;
    col : int;
  }

type xch = {
    path : string;
    ch : in_channel;
    mutable pos : pos;
    mutable buf : char list;
    line_width : (int, int) Hashtbl.t;
  }

let eof = '\x00'

let is_eof c = (c = eof)

let open_in_opt path =
  match Stdio.open_in_opt path with
    None -> None
  | Some ch ->
     let xch = {
         path = path;
         ch = ch;
         pos = { lino = 1; col = 0; };
         buf = [];
         line_width = Hashtbl.create 0;
       }
     in Some xch

let close_in xch =
  close_in xch.ch

let rec input_char2 xch =
  match Stdio.input_char_opt xch.ch with
    None -> eof
  | Some c ->
     if c = '\n' then (
       Hashtbl.replace xch.line_width xch.pos.lino xch.pos.col;
       xch.pos <- { lino = xch.pos.lino + 1; col = 0; };
       c)
     else if c = eof then
       input_char2 xch
     else (
       xch.pos <- { xch.pos with col = xch.pos.col + 1; };
       c)

let input_char xch =
  match xch.buf with
    [] -> input_char2 xch
  | c::cs ->
     xch.buf <- cs;
     (if c = '\n' then
        xch.pos <- { lino = xch.pos.lino + 1; col = 0; }
      else
        xch.pos <- { xch.pos with col = xch.pos.col + 1; });
     c

let input_char_opt xch =
  let c = input_char xch in
  if c = eof then
    None
  else
    Some c

let pushback xch c =
  xch.buf <- c::xch.buf;
  (if xch.pos.col > 0 then
     xch.pos <- { xch.pos with col = xch.pos.col - 1; }
   else
     let lino = xch.pos.lino - 1 in
     let w = Hashtbl.find xch.line_width lino in
     xch.pos <- { lino = lino; col = w; })

let getpos xch = xch.pos
let get_filename xch = xch.path
