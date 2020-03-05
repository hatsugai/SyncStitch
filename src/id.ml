open Printf

type t = Id of string

let make s = Id s

let id_event = make "event"

let rec show (Id s) = s
and show_list ns =
  List.fold_left
    (fun s n -> sprintf "%s %s" s (show n))
    "" ns

let c_name n = Utils.c_name (show n)
