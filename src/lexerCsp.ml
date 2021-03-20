open Stdio
open Posin
open TokenCsp

type lex = {
    ch : Posin.xch;
    mutable pushback_buffer : t list;
}

let keyword_alist = [
    ("SKIP",        SKIP);
    ("STOP",        STOP);
    ("and",         AND);
    ("bool",        BOOL);
    ("case",        CASE);
    ("channel",     CHANNEL);
    ("check",       CHECK);
    ("datatype",    DATATYPE);
    ("deadlock",    DEADLOCK);
    ("divergence",  DIVERGENCE);
    ("else",        ELSE);
    ("event",       EVENT);
    ("false",       FALSE);
    ("if",          IF);
    ("int",         INT);
    ("let",         LET);
    ("list",        LIST);
    ("nametype",    NAMETYPE);
    ("not",         NOT);
    ("of",          OF);
    ("or",          OR);
    ("print",       PRINT);
    ("set",         SET);
    ("test",        TEST);
    ("then",        THEN);
    ("true",        TRUE);
    ("within",      WITHIN);
  ]

let is_space c = c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\x0c'
let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')
let is_id_char_first c = is_alpha c || c ='_'
let is_id_char c = is_id_char_first c || is_digit c || c = '\''

let rec get_token2 ch =
  let c = skip_space ch in
  if is_eof c then
    EOF
  else if c = '/' then
    SLASH
  else if c = '.' then
    let c = input_char ch in
    if c = '.' then
      RANGE
    else
      (pushback ch c; PERIOD)
  else if c = '!' then
    let c = input_char ch in
    if c = '=' then
      NE
    else
      (pushback ch c; EXCLAMATION)
  else if c = '?' then
    QUESTION
  else if c = '|' then
    let c = input_char ch in
    if c = '~' then
      let c = input_char ch in
      if c = '|' then
        INTCHOICE
      else
        (pushback ch c; pushback ch '~'; VERTICALBAR)
    else if c = '}' then
      RBRA_CHSET
    else if c = ']' then
      RBRA_PAR
    else if c = '|' then
      let c = input_char ch in
      if c = '|' then
        INTERLEAVE
      else
        (pushback ch c; pushback ch '|'; VERTICALBAR)
    else
      (pushback ch c; VERTICALBAR)
  else if c = '|' then
    VERTICALBAR
  else if c = ',' then
    COMMA
  else if c = ':' then
    let c = input_char ch in
    if c = ':' then
      TYPE_ANNON
    else
      (pushback ch c; COLON)
  else if c = ';' then
    SEMICOLON
  else if c = '\\' then
    BACKSLASH
  else if c = '(' then
    LPAR
  else if c = ')' then
    RPAR
  else if c = '{' then
    let c = input_char ch in
    if c = '-' then
      (block_comment ch; get_token2 ch)
    else if c = '|' then
      LBRA_CHSET
    else
      (pushback ch c; LCUR)
  else if c = '}' then
    RCUR
  else if c = '[' then
    let c = input_char ch in
    if c = ']' then
      EXTCHOICE
    else if c = '|' then
      LBRA_PAR
    else if c = '[' then
      LBRA_RENAME
    else if c = 'T' then
      let c = input_char ch in
      if c = '=' then
        IS_REFINED_BY_ON_TRACES
      else
        (pushback ch c; pushback ch 'T'; LBRA)
    else if c = 'F' then
      let c = input_char ch in
      if c = '=' then
        IS_REFINED_BY_ON_FAILURES
      else
        (pushback ch c; pushback ch 'T'; LBRA)
    else
      (pushback ch c; LBRA)
  else if c = ']' then
    let c = input_char ch in
    if c = ']' then
      RBRA_RENAME
    else
      (pushback ch c; RBRA)
  else if c = '+' then
    PLUS
  else if c = '-' then
    let c = input_char ch in
    if c = '-' then
      (line_comment ch; get_token2 ch)
    else if c = '>' then
      ARROW
    else
      (pushback ch c; MINUS)
  else if c = '*' then
    ASTERISK
  else if c = '/' then
    SLASH
  else if c = '%' then
    PERCENT
  else if c = '~' then
    TILDE
  else if c = '&' then
    AMPERSAND
  else if c = '=' then
    let c = input_char ch in
    if c = '=' then
      EQ
    else
      (pushback ch c; DEF)
  else if c = '<' then
    let c = input_char ch in
    if c = '=' then
      LE
    else if c = '-' then
      LARROW
    else
      (pushback ch c; LT)
  else if c = '>' then
    let c = input_char ch in
    if c = '=' then
      GE
    else
      (pushback ch c; GT)
  else if c = '^' then
    CIRCUMFLEX
  else if c = '@' then
    AT
  else if c = '#' then
    HASH
  else if is_id_char_first c then
    (pushback ch c; get_id ch)
  else if is_digit c then
    (pushback ch c; get_int ch false)
  else
    let x = Char.code c in
    if x >= 0x20 && x <= 0x7f then
      Error.error (Printf.sprintf "unknown char: '%c'" c)
    else
      Error.error (Printf.sprintf "unknown char: '0x%02x'" x)

and get_int ch minus =
  let rec loop n =
    let c = input_char ch in
    if is_digit c then
      let m = n * 10 + (Char.code c) - (Char.code '0') in
      if m >= n then
        loop m
      else
        Error.error "integer constant is too big"
    else
      (pushback ch c; LITERAL_INT (if minus then -n else n))
  in loop 0

and get_id ch =
  let rec loop cs =
    let c = input_char ch in
    if is_id_char c then
      loop (c::cs)
    else (
      pushback ch c;
      let s = Utils.char_list_to_string (List.rev cs) in
      match List.assoc_opt s keyword_alist with
        Some t -> t
      | None -> ID (Id.make s))
  in loop []

and skip_space ch =
  let c = input_char ch in
  if is_space c then
    skip_space ch
  else
    c

and line_comment ch =
  let c = input_char ch in
  if c = '\n' then
    ()
  else if is_eof c then
    Error.error "unexpected EOF"
  else
    line_comment ch

and block_comment ch =
  let c = input_char ch in
  if c = '-' then
    let c = input_char ch in
    if c = '}' then
      ()
    else
      (pushback ch c; block_comment ch)
  else if is_eof c then
    Error.error "unexpected EOF"
  else
    block_comment ch

let init ch = { ch = ch; pushback_buffer = [] }

let get_token lex =
  match lex.pushback_buffer with
    [] -> get_token2 lex.ch
  | t::ts ->
     (lex.pushback_buffer <- ts; t)

let pushback lex t =
  lex.pushback_buffer <- t::lex.pushback_buffer

let getpos lex =
  Posin.getpos lex.ch

let get_filename lex =
  Posin.get_filename lex.ch
