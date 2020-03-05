open Spec

let rec calc_univ mdb t =

  let rec calc t =
    match t with
      T.App (tc, ts) -> calc2 tc ts
    | _ -> Error.corrupt_s "Univ.calc_univ" (T.show t)

  and calc2 tc ts =
    match tc with
      T.Bool -> [V.Bool false; V.Bool true]
    | T.Int range_opt ->
       let (a, b) =
         match range_opt with
           None -> Mdb.get_int_range mdb
         | Some (a, b) -> (a, b)
       in
       List.map (fun k -> V.Int k) (Utils.interval a b)
    | Fun -> Error.error "high-order function is not supported"
    | Tuple -> calc_tuple ts
    | Set ->
       (match ts with
          [t] -> calc_set t
        | _ -> Error.corrupt "Univ.calc_univ Set")
    | List ->
       let maxlen = Mdb.get_list_max_length mdb in
       (match ts with
          [t] -> calc_list maxlen t
        | _ -> Error.corrupt "Univ.calc_univ List")
    | Event -> Mdb.get_alphabet mdb
    | Process -> Error.error "process cannot be a value"
    | Name n ->
       (* calc univ on demand *)
       let vspec = Mdb.get_variant_spec mdb n in
       if vspec.variant_univ <> [] then
         vspec.variant_univ
       else
         let rec loop us cs =
           match cs with
              [] -> us
            | (ctor, ctor_spec)::cs ->
               let vss =
                 List.map (calc_univ mdb) ctor_spec.ctor_type_list
               in
               let us =
                 List.fold_left
                   (fun us vs -> (V.Variant (ctor, vs))::us)
                   us (Utils.cartesian_product vss)
               in
               loop us cs
         in
         let u = loop [] vspec.ctor_spec_alist in
         vspec.variant_univ <- u;
         u

  and calc_tuple ts =
    List.map
      (fun xs -> V.Tuple xs)
      (calc_univ_tuple mdb ts)

  and calc_set t =
    let vs = calc t in
    let vss = Utils.list_powerset vs in
    List.map (fun vs -> V.Set vs) vss

  and calc_list maxlen t =
    let vs = calc t in
    let rec loop acc prev k =
      if k = maxlen + 1 then
        List.map (fun vs -> V.List vs) acc
      else
        let xs = List.fold_left
                   (fun xs v ->
                     List.fold_left
                       (fun xs us -> (v::us)::xs)
                       xs prev)
                   [] vs in
        loop (List.append xs acc) xs (k+1)
    in loop [[]] [[]] 1

  in calc t

and calc_univ_tuple mdb ts =
  let vss = List.map (calc_univ mdb) ts in
  Utils.cartesian_product vss
