open Printf

type tvar = int
type tgen = int

type t =
  Var of tvar
| App of tcon * t list
| Gen of tgen

and tcon =
  Bool
| Int of (int * int) option
| Fun
| Tuple
| Set
| List
| Event
| Process
| Name of Id.t

let bool      = App (Bool, [])
let int       = App (Int None, [])
let event     = App (Event, [])
let event_set = App (Set, [event])
let event_map = App (Set, [App (Tuple, [event; event])])
let process   = App (Process, [])

let tycon_eq tc1 tc2 =
  if tc1 = tc2 then
    true
  else
    match tc1, tc2 with
      Int _, Int _ -> true
    | _, _ -> false

let make_fun_type t u = App (Fun, [t; u])

let make_tuple_type ts =
  match ts with
    [t] -> t
  | _ -> App (Tuple, ts)

let make_curried_fun_type ts u =
  List.fold_right make_fun_type ts u

let make_channel_type ts =
  make_curried_fun_type ts event

let priority tc =
  match tc with
    Bool -> 0
  | Int range_opt -> 0
  | Fun -> 3
  | Tuple -> 2
  | Set -> 1
  | List -> 1
  | Event -> 0
  | Process -> 0
  | Name n -> 0

let rec show t =
  match t with
    Var k -> sprintf "'%d" k
  | App (tc, ts) ->
     (match tc with
        Bool -> "bool"
      | Int range_opt ->
         (match range_opt with
            None -> "int"
          | Some (a, b) -> sprintf "%d..%d" a b)
      | Fun -> 
         (match ts with
            [t; u] -> sprintf "%s -> %s" (enparen tc t) (enparen tc u)
          | _ -> Error.corrupt "T.show fun")
      | Tuple ->
         (match ts with
            [] -> "unit"
          | [t] -> show t
          | t::ts' ->
             List.fold_left
               (fun s t -> sprintf "%s * %s" s (enparen tc t))
               (enparen tc t) ts')
      | Set ->
         (match ts with
            [t] -> sprintf "%s set" (enparen tc t)
          | _ -> Error.corrupt "T.show set")
      | List ->
         (match ts with
            [t] -> sprintf "%s list" (enparen tc t)
          | _ -> Error.corrupt "T.show list")
      | Event -> "event"
      | Process -> "process"
      | Name n -> Id.show n)
  | Gen k -> sprintf "''%d" k

and enparen tc t =
  match t with
    Var k -> show t
  | App (tc2, ts) ->
     if priority tc > priority tc2 then
       show t
     else
       sprintf "(%s)" (show t)
  | Gen k -> show t

let is_int_type t =
  match t with
    App (Int range_opt, []) -> true
  | _ -> false

let is_process_type t =
  let rec dig t =
    match t with
      App (Process, []) -> true
    | App (Fun, [u; t]) -> dig t
    | _ -> false
  in dig t

let is_fun_type t =
  match t with
    App (Fun, [_; _]) -> true
  | _ -> false

let is_channel_type t =
  let rec dig t =
    match t with
      App (Event, []) -> true
    | App (Fun, [u; t]) -> dig t
    | _ -> false
  in dig t

let is_evset_type t =
  t = event_set

let element_type t =
  match t with
    App (tc, ts) ->
    (match tc with
       Set -> List.hd ts
     | List -> List.hd ts
     | _ -> Error.corrupt_s "element_type " (show t))
| _ -> Error.corrupt_s "element_type " (show t)

let tuple_type_list t =
  match t with
    App (tc, ts) ->
     (match tc with
        Tuple -> ts
      | _ -> Error.corrupt_s "tuple_type_list " (show t))
  | _ -> Error.corrupt_s "tuple_type_list " (show t)

let rec channel_parameter_type_list t =
  match t with
    App (Event, []) -> []
  | App (Fun, [t; u]) -> t::(channel_parameter_type_list u)
  | _ -> Error.corrupt_s "channel_parameter_type_list " (show t)

let rec is_polymorphic t =
  match t with
    Var v -> false
  | App (tc, ts) ->
     List.exists is_polymorphic ts
  | Gen i -> true
