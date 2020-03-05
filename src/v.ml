open Printf
open IdCol

type t =
  Undefined
| Bool of bool
| Int of int
| Set of t list
| List of t list
| Tuple of t list
| Variant of Id.t * t list
| BuiltinFun of ((t -> t list -> t) -> t list -> t)
| UserFun of Id.t
| Event of Id.t * t list
| Hidden of Id.t * t list
| Ctor of Id.t
| Channel of Id.t * t list
| Fun of Id.t list * E.t * t IdMap.t
| Tau
| Tick
| Tock

type env = t IdMap.t

let env0 : env = IdMap.empty

let equal_env env1 env2 = IdMap.equal (=) env1 env2

let hash_env env =
  IdMap.fold
    (fun n v acc -> acc + Hashtbl.hash n + Hashtbl.hash v)
  env 0

let rec show v =
  match v with
    Undefined -> "#undefined"
  | Bool b -> if b then "true" else "false"
  | Int k -> sprintf "%d" k
  | Set vs -> sprintf "{%s}" (show_list vs)
  | List vs -> sprintf "<%s>" (show_list vs)
  | Tuple vs -> sprintf "(%s)" (show_list vs)
  | Variant (n, vs) ->
     if vs=[] then
       Id.show n
     else
     sprintf "%s(%s)" (Id.show n) (show_list vs)
  | BuiltinFun f -> "#builtin"
  | UserFun n -> Id.show n
  | Event (n, vs) ->
     if vs = [] then
       Id.show n
     else
       sprintf "%s.%s" (Id.show n) (show_list_sep "." vs)
  | Hidden (n, vs) ->
     if vs = [] then
       sprintf "%s*" (Id.show n)
     else
     sprintf "%s(%s)*" (Id.show n) (show_list vs)
  | Ctor n -> Id.show n
  | Channel (n, vs) -> sprintf "%s.%s" (Id.show n) (show_list_sep "." vs)
  | Fun (xs, e, env) ->
     sprintf "(fun (%s) %s)" (Id.show_list xs) (E.show e)
  | Tau -> "tau"
  | Tick -> "tick"
  | Tock -> "tock"

and show_list vs = show_list_sep "," vs

and show_list_sep sep vs =
  match vs with
    [] -> ""
  | [v] -> show v
  | v::vs' ->
     List.fold_left
       (fun s v -> sprintf "%s%s%s" s sep (show v))
       (show v) vs'

let show_env env =
  if IdMap.is_empty env then
    ""
  else
    let s =
      IdMap.fold
        (fun n v s -> sprintf "%s %s=%s" s (Id.show n) (show v))
        env ""
    in sprintf "{%s}" s

let ensure_int v =
  match v with
    Int k -> k
  | _ -> Error.corrupt_s "V.ensure_int " (show v)
