let bfs make reg mem length s0 next =
  let ht = make () in
  let que = Queue.create () in
  let rec loop () =
    if Queue.is_empty que then
      ht
    else
      let (state, id, path) = Queue.take que in
      let trans = next state id path in
      reg ht state (id, trans);
      List.iter
        (fun (label, target) ->
          if not (mem ht target) then
            let id = length ht in
            reg ht target (id, []);
            Queue.add (target, id, (label, target)::path) que)
        trans;
      loop ()
  in
  reg ht s0 (0, []);
  Queue.add (s0, 0, []) que;
  loop ()

let bfs_find make reg mem length dummy_trans iter s0 next goal =
  let ht = make () in
  let que = Queue.create () in
  let rec loop () =
    if Queue.is_empty que then
      (None, ht)
    else
      let (state, id, path) = Queue.take que in
      if goal state id path then
        (Some (state, id, path), ht)
      else
        let trans = next state id path in
        reg ht state (id, trans);
        iter
          (fun label target ->
            if not (mem ht target) then
              let id = length ht in
              reg ht target (id, dummy_trans);
              Queue.add (target, id, (label, target)::path) que)
          trans;
        loop ()
  in
  reg ht s0 (0, dummy_trans);
  Queue.add (s0, 0, []) que;
  loop ()
