open Printf
open IdCol
open EventCol

type evset = EventSet.t
type evmap = EventSet.t EventMap.t

type t =
  Omega
| Process of V.env * P.t
| Alt of t list
| Seq of t * (V.env * P.t) list
| Par of evset * t list
| Hide of evset * t
| Rename of evmap * t

let rec equal x y =
  match x with
    Omega ->
     (match y with
        Omega -> true
      | _ -> false)
  | Process (env1, p1) ->
    (match y with
       Process (env2, p2) ->
        V.equal_env env1 env2 && p1 = p2
     | _ -> false)
  | Alt cs1 ->
    (match y with
       Alt cs2 ->
        List.length cs1 = List.length cs2
        && List.for_all2 equal cs1 cs2
     | _ -> false)
  | Seq (c1, ps1) ->
    (match y with
       Seq (c2, ps2) ->
        equal c1 c2
        && List.for_all2
             (fun (env1, p1) (env2, p2) ->
               V.equal_env env1 env2 && p1 = p2)
             ps1 ps2
     | _ -> false)
  | Par (x1, cs1) ->
    (match y with
       Par (x2, cs2) ->
        EventSet.equal x1 x2
        && List.length cs1 = List.length cs2
        && List.for_all2 equal cs1 cs2
     | _ -> false)
  | Hide (x1, c1) ->
    (match y with
       Hide (x2, c2) ->
        EventSet.equal x1 x2 && equal c1 c2
     | _ -> false)
  | Rename (m1, c1) ->
    (match y with
       Rename (m2, c2) ->
       EventMap.equal EventSet.equal m1 m2 && equal c1 c2
     | _ -> false)

let rec hash x =
  match x with
    Omega -> Hashtbl.hash x
  | Process (env, p) ->
     9997 + V.hash_env env + Hashtbl.hash p
  | Alt cs ->
     List.fold_left
       (fun acc c -> acc + hash c)
       1 cs
  | Seq (c, ps) ->
     List.fold_left
       (fun acc (env, p) -> acc + V.hash_env env + Hashtbl.hash p)
       (hash c) ps
  | Par (x, cs) ->
     List.fold_left
       (fun acc c -> acc + hash c)
       (3 + EventSet.hash x) cs
  | Hide (x, c) ->
     4 + EventSet.hash x + hash c
  | Rename (m, c) ->
     5 + EventMap.hash m + hash c

let show_evset s =
  let str =
    EventSet.fold
      (fun u str ->
        sprintf "%s %s" str (Event.show u))
      s ""
  in
  if str = "" then
    "{}"
  else
    sprintf "{%s}" (String.sub str 1 (String.length str - 1))

let show_evmap m = "#evmap"

let rec show c =
  match c with
    Omega -> "OMEGA"
  | Process (env, p) ->
     sprintf "%s%s" (P.desc p) (V.show_env env)
  | Alt cs ->
     show_list " [] " cs
  | Seq (c, ps) ->
     sprintf "; %s %s"
       (show c) (P.show_list (List.map snd ps))
  | Par (x, cs) ->
     show_list " || " cs
  | Hide (x, c) ->
     sprintf "(%s)\\{*}" (show c)
  | Rename (m, c) ->
     sprintf "(%s)[[*]]" (show c)

and show_list sep cs =
  List.fold_left
    (fun s c ->
      if s="" then
        show c
      else
        s ^ sep ^ (show c))
    "" cs

let indent = 1

let desc c =
  let rec asm level acc c =
    match c with
      Omega ->
       (sprintf "%sOMEGA" (String.make level ' '))::acc
    | Process (env, p) ->
       let s = sprintf "%s%s" (String.make level ' ') (P.desc p) in
       IdMap.fold
         (fun x v acc ->
           let s = sprintf "%s%s=%s" (String.make (level + indent) ' ')
                     (Id.show x) (V.show v)
           in s::acc)
         env (s::acc)
    | Alt cs ->
       let acc = (sprintf "%s[]" (String.make level ' '))::acc in
       List.fold_left (asm (level + indent)) acc cs
    | Seq (c, ps) ->
       let acc = (sprintf "%s;" (String.make level ' '))::acc in
       let acc = asm (level + indent) acc c in
       List.fold_left
         (fun acc (env, p) ->
           let s =
             sprintf "%s%s"
               (String.make (level + indent) ' ')
               (P.desc p)
           in desc_env (level + indent * 2) (s::acc) env)
         acc ps
    | Par (x, cs) ->
       let s = sprintf "%s|| %s" (String.make level ' ') (EventSet.show x) in
       List.fold_left (asm (level + indent)) (s::acc) cs
    | Hide (x, c) ->
       let s = sprintf "%s\\ %s" (String.make level ' ') (EventSet.show x) in
       asm (level + indent) (s::acc) c
    | Rename (m, c) ->
       let s = sprintf "%srename" (String.make level ' ') in
       asm (level + indent) (s::acc) c

  and desc_env level acc env =
    IdMap.fold
      (fun x v acc ->
        let s = sprintf "%s%s=%s" (String.make level ' ')
                  (Id.show x) (V.show v)
        in s::acc)
      env acc

  in List.rev (asm 0 [] c)
