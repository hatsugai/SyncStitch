open Col
open IdCol
open S

(*
  collect free identifiers in the expr
  ns: IdSet.t: candidates
*)
let rec fv ns acc expr =
  match expr with
    Bool b -> acc
  | Int k -> acc
  | Var n ->
     if IdSet.mem n ns then
       IdSet.add n acc
     else
       acc
  | Univ _ -> acc
  | Tuple es -> fvs ns acc es
  | Set es -> fvs ns acc es
  | List es -> fvs ns acc es
  | SetRange (x, y) -> fv ns (fv ns acc x) y
  | ListRange (x, y) -> fv ns (fv ns acc x) y
  | Chset ps ->
     List.fold_left
       (fun acc (e, rt) ->
         assert (!rt = None);
         fv ns acc e)
       acc ps
  | Chmap m ->
     List.fold_left
       (fun acc ((a, _), (b, _)) ->
         fv ns (fv ns acc a) b)
       acc m
  | And es -> fvs ns acc es
  | Or es -> fvs ns acc es
  | If (x, y, z) ->
     fv ns (fv ns (fv ns acc x) y) z
  | Let (bs, e) ->
     let acc =
       List.fold_left
         (fun acc (vs, e) -> fv ns acc e)
         acc bs
     in
     let ns' =
       List.fold_left
         (fun ns (xs, e) ->
           List.fold_left
             (fun ns (x, rt) -> IdSet.remove x ns)
             ns xs)
         ns bs
     in
     fv ns' acc e
  | Case (e, n, bs) ->
     List.fold_left
       (fun acc (ctor, (vs, e)) ->
         let acc =
           if IdSet.mem ctor ns then
             IdSet.add ctor acc
           else
             acc
         in
         let ns' =
           List.fold_left
             (fun ns' v -> IdSet.remove v ns')
             ns vs
         in
         fv ns' acc e)
       (fv ns acc e) bs
  | Stop -> acc
  | Skip -> acc
  | Spon p -> fv ns acc p
  | Prefix (e, p) -> fv ns (fv ns acc e) p
  | Receive (ch, rt_ch, vs, g, p) ->
     let ns' =
       List.fold_left
         (fun ns' v -> IdSet.remove v ns')
         ns vs
     in fv ns' (fv ns' (fv ns acc ch) g) p
  | Branch ps -> List.fold_left (fv ns) acc ps
  | Alt ps -> List.fold_left (fv ns) acc ps
  | Amb ps -> List.fold_left (fv ns) acc ps
  | Seq ps -> List.fold_left (fv ns) acc ps
  | Par (a, ps) -> List.fold_left (fv ns) (fv ns acc a) ps
  | AlphaPar xs ->
     List.fold_left
       (fun acc (a, p) ->
         fv ns (fv ns acc a) p)
       acc xs
  | Hide (a, p) -> fv ns (fv ns acc a) p
  | Rename (m, p) -> fv ns (fv ns acc m) p
  | XAlt (x, r, rt_r, p) ->
     let ns' = IdSet.remove x ns in
     fv ns' (fv ns acc r) p
  | XAmb (x, r, rt_r, p) ->
     let ns' = IdSet.remove x ns in
     fv ns' (fv ns acc r) p
  | XSeq (x, r, rt_r, p) ->
     let ns' = IdSet.remove x ns in
     fv ns' (fv ns acc r) p
  | XPar (x, r, rt_r, a, p) ->
     let ns' = IdSet.remove x ns in
     fv ns' (fv ns (fv ns acc a) r) p
  | XAlphaPar (x, r, rt_r, a, p) ->
     let ns' = IdSet.remove x ns in
     fv ns' (fv ns' (fv ns acc r) a) p
  | Fun (xts, e, rt) ->
     let acc =
       List.fold_left
         (fun acc (x, rt, tyspec_opt) ->
           match tyspec_opt with
             None -> acc
           | Some tyspec -> fv_tyspec ns acc tyspec)
       acc xts
     in
     let ns' =
       List.fold_left
         (fun ns' (x, rt, tyspec) -> IdSet.remove x ns')
         ns xts
     in
     fv ns' acc e
  | Apply (f, rt_f, ets) ->
     List.fold_left
       (fun acc (e, t) -> fv ns acc e)
       (fv ns acc f) ets
  | Pos (_, e) -> fv ns acc e

and fvs ns acc es =
  List.fold_left (fv ns) acc es

and fv_tyspec ns acc t =
  match t with
    TApp (tc, ts) ->
     List.fold_left
       (fv_tyspec ns)
       (fv_tyctor ns acc tc) ts

and fv_tyspec_list ns acc ts =
  List.fold_left (fv_tyspec ns) acc ts

and fv_tyctor ns acc tc =
  match tc with
    TcBool -> acc
  | TcInt range_opt ->
     (match range_opt with
        None -> acc
      | Some (a, b) ->
         fv ns (fv ns acc a) b)
  | TcTuple -> acc
  | TcSet -> acc
  | TcList -> acc
  | TcEvent -> acc
  | TcFun -> acc
  | TcName n -> IdSet.add n acc

let add_def_deps ns deps def =
  match def with
    Def (n, e) ->
     let fs = fv ns IdSet.empty e in
     IdMap.add n fs deps

  | DefChannel (ns', tyspec_list) ->
     let fs =
       let fs = IdSet.singleton Id.id_event in
       fv_tyspec_list ns fs tyspec_list
     in
     List.fold_left
       (fun deps n -> IdMap.add n fs deps)
       deps ns'

  | DefDatatype (type_name, variant_defs) ->
     let rec collect deps ctors vs =
       match vs with
         [] -> IdMap.add type_name ctors deps
       | (ctor, tyspec_list)::vs' ->
          let fs = fv_tyspec_list ns IdSet.empty tyspec_list in
          let deps = IdMap.add ctor (IdSet.add type_name fs) deps in
          collect deps (IdSet.add ctor ctors) vs'
     in
     collect deps IdSet.empty variant_defs

  | DefNametype (n, t) ->
     let fs = fv_tyspec ns IdSet.empty t in
     IdMap.add n fs deps

let collect_def_ids defs =
  let rec collect ns chs ctors defs =
    match defs with
      [] -> (ns, chs, ctors)
    | def::defs' ->
       (match def with
          Def (n, e) ->
           collect (IdSet.add n ns) chs ctors defs'
        | DefChannel (ns', tyspec_dom_opt) ->
           let ns = IdSet.add_list ns' ns in
           let chs = IdSet.add_list ns' chs in
           collect ns chs ctors defs'
        | DefDatatype (type_name, variant_defs) ->
           let ctors' =
             List.fold_left
               (fun ctors' (ctor, _) ->
                 IdSet.add ctor ctors')
               ctors variant_defs
           in
           collect (IdSet.add type_name ns) chs ctors' defs'
        | DefNametype (n, tyspec) ->
           collect (IdSet.add n ns) chs ctors defs')
  in collect IdSet.empty IdSet.empty IdSet.empty defs

let calc_deps defs =
  let (ns, chs, ctors) = collect_def_ids defs in
  let ids = IdSet.union ns ctors in
  let deps =
    List.fold_left (add_def_deps ids) IdMap.empty defs
  in
  let deps = IdMap.add Id.id_event chs deps in
  (ids, ns, deps)

let make_def_map map def =
  match def with
    Def (n, e) ->
     IdMap.add n def map
  | DefChannel (ns, t) ->
     List.fold_left
       (fun map n -> IdMap.add n def map)
       map ns
  | DefDatatype (type_name, variant_defs) ->
     IdMap.add type_name def map
  | DefNametype (n, tyspec) ->
     IdMap.add n def map

let scc_edge_map edge_map scc_list =
  List.fold_lefti
    (fun scc_edge_map k scc ->
      let s =
        List.fold_left
          (fun s v ->
            IdSet.fold
              (fun w s ->
                let j =
                  List.find_index
                    (fun scc -> List.mem w scc)
                    scc_list
                in
                IntSet.add j s)
              (IdMap.find v edge_map) s)
          IntSet.empty scc
      in
      IntMap.add k s scc_edge_map)
    IntMap.empty scc_list

let topological_sort scc_list scc_deps =
  let rs = ref [] in
  let mark = Hashtbl.create 0 in
  let rec visit v =
    if not (Hashtbl.mem mark v) then
      (Hashtbl.replace mark v true;
       let v_deps = IntMap.find v scc_deps in
       IntSet.iter visit v_deps;
       rs := v::!rs)
  in
  List.iteri (fun k _ -> visit k) scc_list;
  List.map (List.nth scc_list) (List.rev !rs)
  
let prn_deps_map deps_map =
  Printf.printf "--------------------\n";
  IdMap.iter
    (fun n ns ->
      Printf.printf "%s -> " (Id.show n);
      IdSet.iter (fun n -> Printf.printf "%s " (Id.show n)) ns;
      print_newline ())
    deps_map;
  Printf.printf "--------------------\n"

let group_defs defs =
  let (handle_ids, defined_ids, deps_map) = calc_deps defs in
  (if !Option.debug then
     prn_deps_map deps_map);
  let scc_list = Scc.decomposition handle_ids deps_map in
  let scc_deps_map = scc_edge_map deps_map scc_list in
  let scc_list = topological_sort scc_list scc_deps_map in
  List.map
    (fun ns ->
      List.filter
        (fun n -> IdSet.mem n defined_ids)
        ns)
    scc_list
