type t =
  EOF
| LITERAL_INT of int
| ID of Id.t
| AMPERSAND
| AND
| ARROW
| ASTERISK
| AT
| BACKSLASH
| BOOL
| CASE
| CHANNEL
| CHECK
| CIRCUMFLEX
| COLON
| COMMA
| DATATYPE
| DEADLOCK
| DEF
| DIVERGENCE
| ELSE
| EQ
| EVENT
| EXCLAMATION
| EXTCHOICE
| FALSE
| GE
| GT
| HASH
| IF
| INT
| INTCHOICE
| INTERLEAVE
| IS_REFINED_BY_ON_FAILURES
| IS_REFINED_BY_ON_TRACES
| LBRA
| LBRA_CHSET
| LBRA_PAR
| LCUR
| LE
| LET
| LIST
| LPAR
| LT
| MINUS
| NAMETYPE
| NE
| NOT
| OF
| OR
| PERCENT
| PERIOD
| PLUS
| PRINT
| QUESTION
| RANGE
| RBRA
| RBRA_CHSET
| RBRA_PAR
| RCUR
| RPAR
| SEMICOLON
| SET
| SKIP
| SLASH
| STOP
| TEST
| THEN
| TILDE
| TRUE
| TYPE
| TYPE_ANNON
| VERTICALBAR
| WITHIN

let show t =
  match t with
    EOF                       -> "EOF"
  | LITERAL_INT k             -> Printf.sprintf "%d" k
  | ID n                      -> Id.show n
  | AMPERSAND                 -> "&"
  | AND                       -> "and"
  | ARROW                     -> "->"
  | ASTERISK                  -> "*"
  | AT                        -> "@"
  | BACKSLASH                 -> "\\"
  | BOOL                      -> "bool"
  | CASE                      -> "case"
  | CHANNEL                   -> "channel"
  | CHECK                     -> "check"
  | CIRCUMFLEX                -> "^"
  | COLON                     -> ":"
  | COMMA                     -> ","
  | DATATYPE                  -> "datatype"
  | DEADLOCK                  -> "deadlock"
  | DEF                       -> "="
  | DIVERGENCE                -> "divergence"
  | ELSE                      -> "else"
  | EQ                        -> "=="
  | EVENT                     -> "event"
  | EXCLAMATION               -> "!"
  | EXTCHOICE                 -> "[]"
  | FALSE                     -> "false"
  | GE                        -> ">="
  | GT                        -> ">"
  | HASH                      -> "#"
  | IF                        -> "if"
  | INT                       -> "int"
  | INTCHOICE                 -> "|~|"
  | INTERLEAVE                -> "|||"
  | RANGE                     -> ".."
  | IS_REFINED_BY_ON_FAILURES -> "[F="
  | IS_REFINED_BY_ON_TRACES   -> "[T="
  | LBRA                      -> "["
  | LBRA_CHSET                -> "{|"
  | LBRA_PAR                  -> "[|"
  | LCUR                      -> "{"
  | LE                        -> "<="
  | LET                       -> "let"
  | LIST                      -> "list"
  | LPAR                      -> "("
  | LT                        -> "<"
  | MINUS                     -> "-"
  | NAMETYPE                  -> "nametype"
  | NE                        -> "!="
  | NOT                       -> "not"
  | OF                        -> "of"
  | OR                        -> "or"
  | PERCENT                   -> "%"
  | PERIOD                    -> "."
  | PLUS                      -> "+"
  | PRINT                     -> "print"
  | QUESTION                  -> "?"
  | RBRA                      -> "]"
  | RBRA_CHSET                -> "|}"
  | RBRA_PAR                  -> "|]"
  | RCUR                      -> "}"
  | RPAR                      -> ")"
  | SEMICOLON                 -> ";"
  | SET                       -> "set"
  | SKIP                      -> "SKIP"
  | SLASH                     -> "/"
  | STOP                      -> "STOP"
  | TEST                      -> "test"
  | THEN                      -> "then"
  | TILDE                     -> "~"
  | TRUE                      -> "true"
  | TYPE                      -> "type"
  | TYPE_ANNON                -> "::"
  | VERTICALBAR               -> "|"
  | WITHIN                    -> "within"
