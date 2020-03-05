open Col
open IdCol

(* Tarjan *)
let decomposition vertices edges =
  let scc_list = ref [] in
  let index = ref 0 in
  let stack = ref [] in
  let vertex_index = Hashtbl.create 0 in
  let vertex_lowlink = Hashtbl.create 0 in
  let rec strongconnect v =
    Hashtbl.replace vertex_index v !index;
    Hashtbl.replace vertex_lowlink v !index;
    index := !index + 1;
    stack := v::!stack;
    IdSet.iter
      (fun w ->
        if not (Hashtbl.mem vertex_index w) then
          (strongconnect w;
           let v_lowlink = Hashtbl.find vertex_lowlink v in
           let w_lowlink = Hashtbl.find vertex_lowlink w in
           Hashtbl.replace vertex_lowlink v (min v_lowlink w_lowlink))
        else if List.mem w !stack then
          let v_lowlink = Hashtbl.find vertex_lowlink v in
          let w_index = Hashtbl.find vertex_index w in
          Hashtbl.replace vertex_lowlink v (min v_lowlink w_index)
        else ())
      (IdMap.find v edges);
    let v_lowlink = Hashtbl.find vertex_lowlink v in
    let v_index = Hashtbl.find vertex_index v in
    if v_lowlink = v_index then
      let scc = ref [] in
      let rec loop () =
        let w = List.hd !stack in
        stack := List.tl !stack;
        scc := w::!scc;
        if w = v then
          scc_list := !scc::!scc_list
        else
          loop ()
      in loop ()
  in
  IdSet.iter
    (fun v ->
      if not (Hashtbl.mem vertex_index v) then
        strongconnect v)
    vertices;
  !scc_list
