open DrawModel
open Ts

type 'l prop_trans = {
    fig_id_target : int;
    label : 'l;
    desc : label_desc;
  }

type ('l, 's) prop_state = {
    id : int;
    state : 's;
    trans : ('l, 's) transitions;
    outgoing : 'l prop_trans IntMap.t; (* index -> prop *)
    error : bool;
    path : (label_line * 's * int) array; (* fig_id *)
    desc : state_desc;
    properties : state_properties;
    x_ofs : float;
    y_ofs : float;
  }

(* Draw ext *)
type ('l, 's) pe_ext = {
    sfmap : IntSet.t IntMap.t;
    tsi : ('l, 's) ts_interface;
    sel_fig_id_state_on_path : int option;
}
