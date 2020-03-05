(* Abstract representation of Labelled-Transision-System (LTS) *)

type ('label, 'state) transition = 'label * 'state
type ('l, 's) transitions = ('l, 's) transition array
type ('l, 's) res_transitions =
  Transitions of ('l, 's) transitions
| TransitionsError of string

type state_desc = string list       (* state figure text on draw *)
type state_properties = string list (* property window *)
type label_desc = string list       (* transition line on draw *)
type label_line = string            (* path window item (one line) *)

(* abstract interface for LTS (and its viewer PE) *)
type ('l, 's) ts_interface = {
    transitions : 's -> ('l, 's) res_transitions;
    state_id : 's -> int;
    state_desc : 's -> state_desc;
    state_properties : 's -> state_properties;
    label_desc : 'l -> label_desc;
    label_line : 'l -> label_line;
    label_dash : 'l -> bool;    (* transition line: solid or dash  *)
  }

type index_tree = {
    index_tree_front : int list;
    index_tree_tails : index_tree list;
  }
