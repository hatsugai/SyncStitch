open Printf
open Col
open CCol
open EventCol
open Lts

type divergence_info = Id.t * C.t path * C.t path
type result_divergence =
  NoDiv
| DivPathAndCycle of divergence_info

let make_tau_trans_list trans_map =
  let set_to_list acc u s =
    IntSet.fold
      (fun i acc -> (u, i)::acc)
      s acc
  in
  EventMap.fold
    (fun u s acc ->
      match u with
        Tau | HiddenEvent _ -> set_to_list acc u s
        | Tick | Event _ -> acc)
    trans_map []

let find_tau_loop lts =
  let visited = Hashtbl.create 0 in
  let find p0 =
    let f = ref [(Event.Tau, p0)] in
    let fs = ref [] in
    let tr = ref [] in
    let on_path = Hashtbl.create 0 in
    let rec loop () =
      match !f with
        [] ->
         (match !fs with
            [] ->
             (match !tr with
                [] ->
                 assert (Hashtbl.length on_path = 0);
                 None
              | (u, p)::xs ->
                 assert (Hashtbl.mem on_path p);
                 assert (xs = []);
                 assert (Hashtbl.length on_path = 1);
                 None)
          | y::ys ->
             f := y;
             fs := ys;
             (match !tr with
                [] ->
                 Error.corrupt
                   (sprintf "find_tau_loop: len on_path %d"
                      (Hashtbl.length on_path))
              | (u, p)::xs ->
                 Hashtbl.replace visited p true;
                 Hashtbl.remove on_path p;
                 tr := xs;
                 loop ()))
      | (u, p)::xs ->
         if Hashtbl.mem on_path p then
           Some ((u, p)::!tr, on_path)
         else if Hashtbl.mem visited p then
           (f := xs; loop ())
         else
           let r = lts.v.(p).tau_targets in
           if IntSet.is_empty r then
             (Hashtbl.replace visited p true;
              f := xs;
              loop ())
           else
             (tr := (u, p)::!tr;
              Hashtbl.replace on_path p true;
              fs := xs::!fs;
              f := make_tau_trans_list lts.v.(p).trans_map;
              loop ())
    in loop ()
  in
  let n = Array.length lts.v in
  let rec loop p =
    if p = n then
      None
    else if Hashtbl.mem visited p then
      loop (p + 1)
    else
      match find p with
        Some x -> Some x
      | None -> loop (p+1)
  in
  loop 0

let trans_iter f trans =
  EventMap.iter
    (fun u s ->
      IntSet.iter
        (fun q -> f u q)
        s)
    trans

let find_initial_path lts on_path =
  let next = (fun p _ _ -> lts.v.(p).trans_map) in
  let goal p _ _ = Hashtbl.mem on_path p in
  let (r, ht) =
    Bfs.bfs_find
      (fun () -> Hashtbl.create 0)
      Hashtbl.replace
      Hashtbl.mem
      Hashtbl.length
      EventMap.empty
      trans_iter
      0 next goal
  in
  match r with
    None -> Error.corrupt "find_initial_path"
  | Some (state, id, path) -> path

let check_divergence mdb lts =
  (if !Option.debug then
     printf "check_divergence %s\n" (Id.show lts.process_name));
  calc_tau_targets lts;
  match find_tau_loop lts with
    None ->
     NoDiv
  | Some (ps, on_path) ->
     let qs = find_initial_path lts on_path in
     let xs =
       List.fold_left
         (fun acc (u, p) -> (u, lts.v.(p).state)::acc)
         [] qs
     in
     let ys =
       List.fold_left
         (fun acc (u, p) -> (u, lts.v.(p).state)::acc)
         [] ps
     in
     DivPathAndCycle (lts.process_name, xs, ys)
