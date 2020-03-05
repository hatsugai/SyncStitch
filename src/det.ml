open Printf
open Error
open Col
open Event
open EventCol
open Lts

module IntSetHashtbl =
  Hashtbl.Make (
      struct
        type t = IntSet.t
        let equal = IntSet.equal
        let hash = IntSet.hash
      end)

let tau_closure lts ss =
  let que = Queue.create () in
  let rec loop ss =
    if Queue.is_empty que then
      ss
    else
      let s = Queue.take que in
      let sprop = lts.v.(s) in
      let ss =
        IntSet.fold
          (fun t ss ->
            if IntSet.mem t ss then
              ss
            else
              (Queue.add t que; IntSet.add t ss))
          sprop.tau_targets ss
      in loop ss
  in
  IntSet.iter (fun s -> Queue.add s que) ss;
  loop ss

let update_evht ht u tt =
  if Hashtbl.mem ht u then
    Hashtbl.replace ht u (IntSet.union tt (Hashtbl.find ht u))
  else
    Hashtbl.add ht u tt

let make_next_ss lts =
  (fun ss _ _ ->
    let ht = Hashtbl.create 0 in
    IntSet.iter
      (fun s ->
        EventMap.iter
          (fun u tt ->
            match u with
              Tau | HiddenEvent _ -> ()
            | Tick | Event _ -> update_evht ht u tt)
          lts.v.(s).trans_map)
      ss;
    Hashtbl.fold
      (fun u tt trans ->
        let tc = tau_closure lts tt in
        (u, tc)::trans)
      ht [])

let determinize lts =
  (if !Option.debug then
     printf "determinize %s\n" (Id.show lts.process_name));
  calc_tau_targets lts;
  let s0 = tau_closure lts (IntSet.singleton 0) in
  let next = make_next_ss lts in
  let ht =
    Bfs.bfs
      (fun () -> IntSetHashtbl.create 0)
      IntSetHashtbl.replace
      IntSetHashtbl.mem
      IntSetHashtbl.length
      s0 next
  in
  let v =
    Unfold.conv
      IntSetHashtbl.length
      IntSetHashtbl.iter
      IntSetHashtbl.find
      s0 ht
  in
  {
    process_name = lts.process_name;
    v = v;
    minacc_vec = [||];
    print_state = (fun sep s -> sprintf "%d" s);
    b_tau_targets = false;
    b_initials = false;
    b_minacc = false;
  }
