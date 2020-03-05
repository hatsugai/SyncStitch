open Printf

type t =
  Tau
| Tick
| Event of Id.t * V.t list
| HiddenEvent of Id.t * V.t list

let convert v =
  match v with
    V.Event (ch, vs) -> Event (ch, vs)
  | _ -> Error.corrupt "Event.convert"


let show_args s vs =
  List.fold_left
    (fun s v -> s ^ "." ^ (V.show v))
    s vs

let show e =
  match e with
    Tau -> "tau"
  | Tick -> "tick"
  | Event (n, vs) ->
     (match vs with
        [] -> Id.show n
      | _ -> show_args (Id.show n) vs)
  | HiddenEvent (n, vs) ->
     (match vs with
        [] -> sprintf "%s*" (Id.show n)
      | _ -> show_args (sprintf "%s*" (Id.show n)) vs)
