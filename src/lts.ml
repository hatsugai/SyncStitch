open Printf
open Col
open EventCol

type 's state_prop = {
    state : 's;
    trans_map : IntSet.t EventMap.t;
    b_tick : bool;
    b_tau : bool;
    mutable tau_targets : IntSet.t;
    mutable initials : EventSet.t;
}

type 's lts = {
    process_name : Id.t;
    v : 's state_prop array;
    mutable minacc_vec : EventSetSet.t array;
    mutable b_tau_targets : bool;
    mutable b_initials : bool;
    mutable b_minacc : bool;
    print_state : string -> int -> string;
}

type 's path = (Event.t * 's) list

let iter lts f =
  let n = Array.length lts.v in
  for i = 0 to n - 1 do
    f i lts.v.(i)
  done

let show lts =
  iter lts
    (fun i trans ->
      printf "%d %s\n" i (lts.print_state " " i);
      EventMap.iter
        (fun u s ->
          IntSet.iter
            (fun j ->
              printf "    %s %s\n" (Event.show u) (lts.print_state " " j))
            s)
        trans.trans_map)

let show_minacc lts =
  iter lts
    (fun i sprop ->
      printf "%d %s\n" i (lts.print_state " " i);
      EventSetSet.iter
        (fun s ->
          printf "    { ";
          EventSet.iter
            (fun u ->
              printf "%s " (Event.show u))
            s;
          printf "}\n")
        lts.minacc_vec.(i))

let calc_tau_targets_on_state_prop sprop =
  sprop.tau_targets <-
    EventMap.fold
      (fun u s targets ->
        match u with
          Tau | HiddenEvent _ -> IntSet.union targets s
          | Tick | Event _ -> targets)
      sprop.trans_map IntSet.empty

let calc_tau_targets lts =
  (if !Option.debug then
     printf "calc_tau_targets %s\n" (Id.show lts.process_name));
  if not lts.b_tau_targets then (
    iter lts (fun i sprop -> calc_tau_targets_on_state_prop sprop);
    lts.b_tau_targets <- true)

let calc_initials_for_state_prop sprop =
  sprop.initials <-
    EventMap.fold
      (fun u s initials ->
        match u with
          Tick | Event _ -> EventSet.add u initials
          | Tau | HiddenEvent _ -> initials)
      sprop.trans_map EventSet.empty

let calc_initials lts =
  (if !Option.debug then
     printf "calc_initials %s\n" (Id.show lts.process_name));
  if not lts.b_initials then (
    iter lts (fun i sprop -> calc_initials_for_state_prop sprop);
    lts.b_initials <- true)
