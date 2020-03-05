open Printf
open Error
open Col
open Event
open EventCol
open Lts

let calc_minacc_of_state lts ss =
  let update acc sprop =
    match EventMap.find_opt Tick sprop.trans_map with
      Some _ ->
       if EventSetSet.mem EventSet.empty acc then
         acc
       else
         let acc =
           EventSetSet.filter
             (fun a -> not (EventSet.mem Tick a))
             acc
         in EventSetSet.add (EventSet.singleton Tick) acc
    | None ->
       if IntSet.is_empty sprop.tau_targets then (* stable *)
         if EventSetSet.exists
              (fun a -> EventSet.subset a sprop.initials)
              acc
         then
           acc
         else if EventSetSet.exists
                   (fun a -> EventSet.subset sprop.initials a)
                   acc
         then
           let acc =
             EventSetSet.filter
               (fun a -> not (EventSet.subset sprop.initials a))
               acc
           in EventSetSet.add sprop.initials acc
         else
           EventSetSet.add sprop.initials acc
       else
         acc
  in
  IntSet.fold
    (fun s acc -> update acc lts.v.(s))
    ss EventSetSet.empty

let calc_minacc lts dlts =
  if not dlts.b_minacc then (
    (if !Option.debug then
       printf "calc_minacc %s\n" (Id.show lts.process_name));
    calc_initials lts;
    let minacc_vec =
      Array.make (Array.length dlts.v) EventSetSet.empty
    in
    Lts.iter dlts
      (fun i tr ->
        let ss = dlts.v.(i).state in
        let acc = calc_minacc_of_state lts ss in
        minacc_vec.(i) <- acc);
    dlts.minacc_vec <- minacc_vec;
    dlts.b_minacc <- true)
