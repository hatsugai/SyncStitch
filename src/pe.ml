open Error
open Csp
open Guedra
open DrawModel
open Ts
open PeFig

type prop = {
    process_name : string;
    wch_toplevel : win_msg chan;
    width : int;
    height : int;
  }

type ('a, 'b, 'c, 's) context = {
    (* selected state and figure id *)
    mutable cur_state : 's;
    mutable cur_state_fig_id : int;

    (* undo/redo *)
    mutable undo : ('s * int * ('a, 'b, 'c) model) list;
    mutable redo : ('s * int * ('a, 'b, 'c) model) list;

    (* layout of state figures *)
    hspace : float;
    vspace : float;

    (* sequence number for diagram filename *)
    mutable diagram_no : int;
  }

type ('t, 'l, 's) pe_checklist_draw_context = {
    mdb : Mdb.t;
    tsi : ('l, 's) ts_interface;
    ts : 't;
  }


let prn msg id = Printf.printf "%s %d\n" msg id; flush stdout

let sfmap_add itoken id sfmap =
  IntMap.add itoken
    (IntSet.add
       id
       (IntMap.find_with_default itoken sfmap IntSet.empty))
    sfmap

let sfmap_remove itoken id sfmap =
  IntMap.add itoken
    (IntSet.remove id (IntMap.find itoken sfmap))
    sfmap

let draw_item_trans_cl x y width height cs i sel ud dc act b_check =
  (if i = sel then
     (set_color o_o.color_fore;
      fill_rect (flo x) (flo y) (flo width) (flo height);
      set_color o_o.color_back)
   else
     set_color o_o.color_fore);
  let (label, target) = Array.get cs i in
  let s = dc.tsi.label_line label in
  draw_text (flo x) (flo y) s

let draw_item_path_lb x y width height cs i sel ud dc act =
  (if i = sel then
     (set_color o_o.color_fore;
      fill_rect (flo x) (flo y) (flo width) (flo height);
      set_color o_o.color_back)
   else
     set_color o_o.color_fore);
  let (label_line, _, _) = Array.get cs i in
  draw_text (flo x) (flo y) label_line

let init wch pch cch nch pe_prop mdb tsi ts initial_state index_tree =
  let rch_hsp = make_chan () in
  let rch_vsp = make_chan () in
  let wch_vsp = make_chan () in
  let wch_cl = make_chan () in
  let wch_path = make_chan () in
  let wch_draw = make_chan () in
  let cch_hsp = make_chan () in
  let cch_vsp = make_chan () in
  let cch_cl = make_chan () in
  let cch_path = make_chan () in
  let cch_draw = make_chan () in
  let nch_hsp = make_chan () in
  let nch_vsp = make_chan () in
  let nch_cl = make_chan () in
  let nch_path = make_chan () in
  let nch_draw = make_chan () in
  let pque = Queue.create () in
  let nque = Queue.create () in
  let dc_trans_cl = {                    (* draw context for Checklist *)
      mdb = mdb;
      tsi = tsi;
      ts = ts;
    }
  in
  let ud_trans_cl = {                    (* for Checklist *)
      Checklist.item_height = int_of_float (ceil o_o.funit);
      draw = draw_item_trans_cl;
      item_string = (fun dc (label, target) ->
        dc.tsi.label_line label);
    }
  in
  let dc_path_lb = {
      mdb = mdb;
      tsi = tsi;
      ts = ts;
    }
  in
  let ud_path_lb = {
      Listbox.item_height = int_of_float (ceil o_o.funit);
      draw = draw_item_path_lb;
      item_string = (fun (s, _, _) -> s);
    }
  in
  let ext = {                   (* Draw ext *)
      sfmap = IntMap.empty;
      tsi = tsi;
      sel_fig_id_state_on_path = None;
    }
  in
  let state_width = o_o.funit *. 4.0 in
  let state_height = o_o.funit *. 3.0 in

  let cc = {
      cur_state = initial_state;
      cur_state_fig_id = -1;    (* set later *)
      undo = [];
      redo = [];
      hspace = o_o.funit *. 6.0;
      vspace = o_o.funit *. 1.0;
      diagram_no = 0;
    }
  in

  let get_trans ts state =
    match tsi.transitions state with
      Transitions trans -> (trans, false)
    | TransitionsError s -> ([||], true)
  in

  let make_chkmap outgoing =
    IntMap.fold
      (fun index _ m -> Checklist.IntMap.add index true m)
      outgoing Checklist.IntMap.empty
  in

  let get_trans_n_chkmap ts state outgoing cont =
    let (trans, error) = get_trans ts state in
    if error then
      cont [||] Checklist.IntMap.empty
    else
      let chkmap = make_chkmap outgoing in
      cont trans chkmap
  in

  (* remove subtree under id
     NOTE: outgoing of the parent of id is not changed *)
  let rec remove_fig_recur fz fm sfmap id cont =
    let fig = IntMap.find id fm in
    Draw.remove_figure fz fm id
      (fun fz fm ->
        fig
          (GetProp
             (fun prop ->
               let itoken = tsi.state_id prop.state in
               let sfmap = sfmap_remove itoken id sfmap in
               remove_fig_recur_set fz fm sfmap prop.outgoing cont)))

  and remove_fig_recur_set fz fm sfmap outgoing cont =
    IntMap.enum_lnr (fz, fm, sfmap) outgoing
      (fun (fz, fm, sfmap) o next ->
        match o with
          None -> cont (fz, fm, sfmap)
        | Some (index, prop_trans) ->
           remove_fig_recur fz fm sfmap prop_trans.fig_id_target
             (fun (fz, fm, sfmap) -> next (fz, fm, sfmap)))
  in

  let rec process () =
    let event_list =
      [ recvEvt nch_cl always handle_cl;
        recvEvt nch_path always handle_path;
        recvEvt nch_draw always handle_draw ]
    in
    select_que2 event_list pque nque

  and handle_cl (ch, msg) =
    match msg with
      Checklist.OnCheck (cs, index, check) ->
       trans_check cs index check
    | Checklist.OnAction (cs, index, check) ->
       trans_action cs index check
    | Checklist.OnSelect (cs, sel) ->
       set_property_pane cs sel
    | _ -> process ()

  and handle_path (ch, msg) =
    match msg with
      Listbox.OnSelect (cs, sel) ->
       let (state, fig_id_opt) =
         if sel = -1 then
           (cc.cur_state, None)
         else
           let (_, target, fig_id) = Array.get cs sel in
           (target, Some fig_id)
       in
       (* update draw model for selected item *)
       set_sel_fig_id_state_on_path fig_id_opt
         (fun () ->
           (* unselect checklist if selected on path *)
           if sel = -1 then
             process ()
           else
             send cch_cl (Checklist.Select (-1))
               (fun () ->
                 match fig_id_opt with
                   None -> process ()
                 | Some fig_id ->
                    send cch_draw
                      (AdjustOriginFor (IntSet.singleton fig_id))
                      process))

    | Listbox.OnAction (cs, index) ->
       let (_, _, fig_id) = Array.get cs index in
       get_draw_model
         (fun model ->
           record_model model;
           let sel = IntSet.singleton fig_id in
           let model = { model with sel = sel; } in
           set_draw_model model
             (fun () ->
               send cch_draw AdjustOrigin
                 (fun () -> fig_sel model)))
    | _ -> process ()

  and set_sel_fig_id_state_on_path fig_id_opt k =
    get_draw_model
      (fun model ->
        set_sel_fig_id_state_on_path_with_model model fig_id_opt
          (fun _ -> k ()))

  and set_sel_fig_id_state_on_path_with_model model fig_id_opt k =
    let ext =
      { model.ext with
        sel_fig_id_state_on_path = fig_id_opt; }
    in
    let model = { model with ext=ext; } in
    set_draw_model model (fun () -> k model)

  and set_property_pane cs sel =
    send cch_path (Listbox.Select (-1))
      (fun () ->
        set_sel_fig_id_state_on_path None process)

  and trans_action cs index check =
    if check then
      process ()
    else
      realize_trans_on_checked cs index
        (fun id ->
          get_draw_model
            (fun model ->
              let sel = IntSet.singleton id in
              let model = { model with sel = sel } in
              set_draw_model model
                (fun () ->
                  send cch_draw AdjustOrigin
                    (fun () -> fig_sel model))))

  and get_draw_model k =
    send cch_draw Edit
      (fun () ->
        recv nch_draw always
          (fun (cch, msg) ->
            match msg with
              DrawModel model -> k model
            | _ -> error "get_draw_model"))

  and set_draw_model model k =
    send cch_draw (Update model) k

  and update_draw_model model k =
    get_draw_model (fun _ -> set_draw_model model k)

  and cancel_draw_model k =
    send cch_draw Cancel k

  and ref_draw_model k =
    get_draw_model
      (fun model ->
        cancel_draw_model
          (fun () -> k model))

  and trans_check cs index b_check =
    if b_check then
      realize_trans_on_checked cs index (fun _ -> process ())
    else
      remove_subtree_on_unchecked cs index

  and realize_trans_on_checked cs index k =
    get_draw_model
      (fun model ->
        record_model model;
        let fig_src = IntMap.find cc.cur_state_fig_id model.fm in
        get_prop_n_boundary fig_src
          (fun prop x y w h ->
            let n = IntMap.cardinal prop.outgoing in
            let (x, y) = layout_state x y w h n in
            let (label, state) = Array.get cs index in
            make_trans model.fz model.fm model.ext.sfmap fig_src prop
              index label state x y w h
              (fun fz fm sfmap _ _ _ prop ->
                let ext = { model.ext with sfmap=sfmap; } in
                let model = { model with fz=fz;fm=fm;ext=ext;} in
                set_draw_model model
                  (fun () -> k prop.id))))

  and remove_subtree_on_unchecked cs index =
    get_draw_model
      (fun model ->
        record_model model;
        let fig_src = IntMap.find cc.cur_state_fig_id model.fm in
        fig_src
          (GetProp
             (fun prop ->
               remove_trans_from_src_outgoing model.fm fig_src index
                 (fun fm fig_src prop_src trans_prop_removed ->
                   remove_fig_recur model.fz fm model.ext.sfmap
                     trans_prop_removed.fig_id_target
                     (fun (fz, fm, sfmap) ->
                       let ext = { model.ext with sfmap=sfmap; } in
                       let model =
                         { model with fz=fz; fm=fm; ext=ext; }
                       in
                       set_draw_model model process)))))

  and remove_trans_from_src_outgoing fm fig_src index k =
    fig_src
      (GetProp
         (fun prop ->
           let trans_prop = IntMap.find index prop.outgoing in
           let prop =
             { prop with
               outgoing = IntMap.remove index prop.outgoing }
           in
           fig_src
             (SetProp
                (prop,
                 (fun _ fig ->
                   let fm = IntMap.add prop.id fig fm in
                   k fm fig prop trans_prop)))))

  and get_prop_n_boundary fig k =
    fig
      (GetProp
         (fun prop ->
           fig
             (Boundary
                (fun x y w h -> k prop x y w h))))

  and layout_state x y w h n =
    let x_ofs = x +. w +. cc.hspace in
    let y_ofs =
      if n = 0 then
        y
      else if n mod 2 = 0 then
        y -. (flo (n / 2)) *. (h +. cc.vspace)
      else
        y +. (flo ((n+1) / 2)) *. (h +. cc.vspace)
    in (x_ofs, y_ofs)

  and handle_draw (ch, msg) =
    match msg with
      DrawModel.OnChanged (model, model') ->
       record_model model;
       if model.sel <> model'.sel then
         fig_sel model'
       else
         process ();
    | OnSelected model ->
       fig_sel model
    | OnKeyDown (code, state) ->
       handle_key code state
    | OnScroll (model, id, state, dx, dy) ->
       scroll_state_text model id state dx dy
    | _ -> process ()

  and scroll_state_text model id state dx dy =
    let fig = IntMap.find id model.fm in
    fig
      (GetProp
         (fun prop ->
           let prop = { prop with x_ofs = prop.x_ofs +. dx;
                                  y_ofs = prop.y_ofs +. dy; }
           in
           fig
             (SetProp
                (prop,
                 (fun _ fig ->
                   let fm = IntMap.add id fig model.fm in
                   let model = { model with fm=fm; } in
                   get_draw_model
                     (fun _ ->
                       set_draw_model model process))))))

  and record_model model =
    cc.undo <- (cc.cur_state, cc.cur_state_fig_id, model)::cc.undo;
    cc.redo <- []

  and handle_key code state =
    if code = 101 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+E: expand all *)
      expand_all ()
    else if (code = keyDelete || code = keyBackSpace)
            && (state land keyStateMask) = 0 then
      (* DEL or BACKSPACE: remove selected *)
      remove_selected ()
    else if code = 122 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+Z: undo *)
      undo ()
    else if code = 121 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+Y: redo *)
      redo ()
    else if code = 106 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+J: fit state size *)
      fit_state_size_selected ()
    else if code = 117 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+U: bring to front *)
      change_zo true
    else if code = 100 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+D: push back *)
      change_zo false
    else if code = 108 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+L: adjust view pos *)
      adjust_view_pos ()
    else if code = 114 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+R: right most position *)
      right_most_pos ()
    else if code = 112 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+P: save diagram as PDF and SVG *)
      snapshot_computation_tree ()
    else if code = 113 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+Q *)
      (guedra_quit (); process ())
    else if code = 119 && (state land keyStateMask) = keyStateControl then
      (* Ctrl+W *)
      (guedra_quit (); process ())
    else if code = keyF4 && (state land keyStateMask) = keyStateAlt then
      (* ALt+F4 *)
      (guedra_quit (); process ())
    else if code = 48 && (state land keyStateMask) = keyStateControl then
      reset_view ()
    else
      process ()

  and snapshot_computation_tree () =
    let scale = o_o.font_size /. o_o.funit in (* pixel -> point *)
    ref_draw_model
      (fun model ->
        Draw.boundary_fig_all model.fm
          (fun x y w h ->
            let margin = o_o.funit *. 3.0 in
            let w = (w +. margin *. 2.0) *. scale in
            let h = (h +. margin *. 2.0) *. scale in
            let (fn_pdf, i) =
              Utils.make_filename mdb.model_filename "pdf" cc.diagram_no
            in
            let fn_svg = Printf.sprintf "%s_%d.svg" mdb.model_filename i in
            cc.diagram_no <- i + 1;
            create_pdf_surface fn_pdf w h;
            snapshot_computation_tree_helper model x y w h scale margin
              (fun () ->
                create_svg_surface fn_svg w h;
                snapshot_computation_tree_helper
                  model x y w h scale margin process)))

  and snapshot_computation_tree_helper model x y w h scale margin k =
    set_color o_o.color_back;
    fill_rect 0.0 0.0 w h;
    push_translate_scale
      ((margin -. x) *. scale) ((margin -. y) *. scale)
      scale;
    send cch_draw (PaintCommand (model, margin -. x, margin -. y))
      (fun () ->
        recv nch_draw always
          (fun _ ->
            pop_translate_scale ();
            delete_surface ();
            k ()))

  and reset_view () =
    send cch_draw ResetOz process

  and right_most_pos () =
    send cch_draw RightMost process

  and adjust_view_pos () =
    send cch_draw AdjustOrigin process

  and change_zo b_up =
    get_draw_model
      (fun model ->
        record_model model;
        if IntSet.is_single model.sel then
          let id = IntSet.choose model.sel in
          Draw.get_zo model.fz id
            (fun zo ->
              let fz = IntMap.remove zo model.fz in
              let zo =
                if b_up then
                  Draw.new_zo_front fz
                else
                  Draw.new_zo_back fz
              in
              let fz = IntMap.add zo id fz in
              let model = { model with fz=fz; } in
              set_draw_model model process)
        else
          cancel_draw_model process)

  and fit_state_size_selected () =
    get_draw_model
      (fun model ->
        record_model model;
        IntSet.enum_lnr model.fm model.sel
          (fun fm o next ->
            match o with
              None ->
               let model = { model with fm=fm; } in
               set_draw_model model process
            | Some id ->
               fit_state_size fm id next))

  and fit_state_size fm id k =
    let fig = IntMap.find id fm in
    get_prop_n_boundary fig
      (fun prop _ _ w h ->
        let prop = { prop with x_ofs = 0.0; y_ofs = 0.0; } in
        fig
          (SetProp
             (prop,
              (fun _ fig ->
                let (w', h') = FigState.calc_text_size prop.desc in
                let w' = w' +. o_o.left_margin +. o_o.right_margin in
                let h' = h' +. o_o.top_margin +. o_o.bottom_margin in
                fig
                  (Move
                     (0.0, (h -. h') *. 0.5,
                      (fun fig ->
                        fig
                          (Resize
                             (w', h',
                              (fun fig ->
                                let fm = IntMap.add id fig fm in
                                k fm))))))))))

  and undo () =
    match cc.undo with
      [] -> process ()
    | (state, fig_id, model)::undo ->
       get_draw_model
         (fun model' ->
           cc.undo <- undo;
           cc.redo <- (cc.cur_state, cc.cur_state_fig_id, model')::cc.redo;
           cc.cur_state <- state;
           cc.cur_state_fig_id <- fig_id;
           set_draw_model model
             (fun () ->
               send cch_draw AdjustOrigin
                 (fun () -> fig_sel model)))

  and redo () =
    match cc.redo with
      [] -> process ()
    | (state, fig_id, model)::redo ->
       get_draw_model
         (fun model' ->
           cc.undo <- (cc.cur_state, cc.cur_state_fig_id, model')::cc.undo;
           cc.redo <- redo;
           cc.cur_state <- state;
           cc.cur_state_fig_id <- fig_id;
           set_draw_model model
             (fun () ->
               send cch_draw AdjustOrigin
                 (fun () -> fig_sel model)))

  and remove_selected () =
    get_draw_model
      (fun model ->
        record_model model;
        IntSet.enum_lnr
          (model.fz, model.fm, model.ext.sfmap)
          (IntSet.remove 0 model.sel)
          (fun (fz, fm, sfmap) o next ->
            match o with
              None ->
               let ext = { model.ext with sfmap=sfmap; } in
               let model' =
                 { fz=fz; fm=fm; sel=IntSet.empty; ext=ext; }
               in
               set_draw_model model'
                 (fun () -> make_list_empty process)
            | Some id ->
               if IntMap.mem id fm then
                 remove_fig fz fm sfmap id
                   (fun (fz, fm, sfmap) -> next (fz, fm, sfmap))
               else
                 next (fz, fm, sfmap)))

  and find_parent_opt fm id k =
    IntMap.enum_lnr () fm
      (fun () o next ->
        match o with
          None -> k None
        | Some (id', fig) ->
           (* find id in outgoing of fig *)
           fig
             (GetProp
                (fun prop ->
                  if IntMap.exists
                       (fun index prop_trans ->
                         prop_trans.fig_id_target = id)
                       prop.outgoing
                  then
                    k (Some (id', fig))
                  else
                    next ())))

  and remove_fig fz fm sfmap id k =
    find_parent_opt fm id
      (fun o ->
        match o with
          None -> k (fz, fm, sfmap)       (* root *)
        | Some (id_parent, fig) ->
           (* remove id from parent's outgoing *)
           fig
             (GetProp
                (fun prop ->
                  let outgoing =
                    IntMap.filter
                      (fun index prop_trans ->
                        prop_trans.fig_id_target <> id)
                      prop.outgoing
                  in
                  let prop = { prop with outgoing = outgoing } in
                  fig
                    (SetProp
                       (prop,
                        (fun _ fig ->
                          let fm = IntMap.add id_parent fig fm in
                          remove_fig_recur fz fm sfmap id k))))))

  and expand_all () =
    get_draw_model
      (fun model ->
        record_model model;
        if IntSet.is_single model.sel then
          let id = IntSet.choose model.sel in
          let fig_source = IntMap.find id model.fm in
          get_prop_n_boundary fig_source
            (fun prop x y w h ->
              expand_all2 model id fig_source prop x y w h)
        else
          cancel_draw_model process)

  and expand_all2 model id fig_source prop x y w h =
    let n = Array.length prop.trans in
    let rec loop index fz fm sfmap fig_source prop =
      if index = n then
        let ext = { model.ext with sfmap=sfmap; } in
        let model' = { model with fz=fz; fm=fm; ext=ext; } in
        set_draw_model model'
          (fun () ->
            let chkmap = make_chkmap prop.outgoing in
            send cch_cl
              (Checklist.SetList (prop.trans, chkmap, -1))
              process)
      else
        match IntMap.find_opt index prop.outgoing with
          Some _ -> loop (index+1) fz fm sfmap fig_source prop
        | None ->
           let (label, target) = Array.get prop.trans index in
           make_trans fz fm sfmap fig_source prop index label target
             (x +. w +. cc.hspace)
             (y +. (flo (index - n / 2)) *. (h +. cc.vspace))
             w h
             (fun fz fm sfmap fig_src prop_src _ _ ->
               loop (index+1) fz fm sfmap fig_src prop_src)
    in
    loop 0 model.fz model.fm model.ext.sfmap fig_source prop

  and fig_sel model =
    get_draw_model
      (fun _ ->
        set_sel_fig_id_state_on_path_with_model model None
          (fun model ->
            if IntSet.is_single model.sel then
              let id = IntSet.choose model.sel in
              let fig = IntMap.find id model.fm in
              fig
                (GetProp
                   (fun prop ->
                     cc.cur_state <- prop.state;
                     cc.cur_state_fig_id <- id;
                     get_trans_n_chkmap ts cc.cur_state prop.outgoing
                       (fun trans chkmap ->
                         send cch_cl (Checklist.SetList (trans, chkmap, -1))
                           (fun () ->
                             send cch_path (Listbox.SetList (prop.path, -1))
                               process))))
            else
              make_list_empty process))

  and make_list_empty k =
    send cch_cl (Checklist.SetList ([||], Checklist.IntMap.empty, -1))
      (fun () ->
        send cch_path (Listbox.SetList ([||], -1)) k)

  (*
    construct figs recursively along with 'index_tree'

    make_model_index_tree
      make_model_index_tree_branch
      make_model_index_list
        make_trans
          make_state_fig
   *)
  and make_model_index_tree fz fm sfmap fig prop x y index_tree cont =
    (* front *)
    make_model_index_list fz fm sfmap fig prop x y index_tree.index_tree_front
      (fun fz fm sfmap fig prop x y ->
        (* 'fig' and 'prop' are for the state at the end of the front *)
        make_model_index_tree_branch fz fm sfmap fig prop x y index_tree.index_tree_tails cont)

  and make_model_index_tree_branch fz fm sfmap fig prop x y branches cont =
    match branches with
      [] -> cont fz fm sfmap
    | index_tree::branches ->
       make_model_index_tree fz fm sfmap fig prop x y index_tree
         (fun fz fm sfmap ->
           (* update 'fig' and 'prop' because it has changed since child is added *)
           let fig = IntMap.find prop.id fm in
           fig
             (GetProp
                (fun prop ->
                  let y = y +. state_height +. cc.vspace in
                  make_model_index_tree_branch fz fm sfmap fig prop x y branches cont)))

  and make_model_index_list fz fm sfmap fig_src prop_src x y index_list cont =
    match index_list with
      [] -> cont fz fm sfmap fig_src prop_src x y
    | index::index_list ->
       let (label, state) = Array.get prop_src.trans index in
       make_trans fz fm sfmap fig_src prop_src
         index label state x y state_width state_height
         (fun fz fm sfmap _ _ fig prop ->
           make_model_index_list fz fm sfmap fig prop
             (x +. state_width +. cc.hspace) y index_list cont)

  and make_trans fz fm sfmap fig_src prop_src index label target x y w h cont =
    (* make state fig *)
    let label_line = tsi.label_line label in
    let s = Printf.sprintf "%2d %s" (Array.length prop_src.path) label_line in    (* number item *)
    let path = Array.append prop_src.path [|(s, target, prop_src.id)|] in
    make_state_fig fz fm sfmap path target x y w h
      prop_src.x_ofs prop_src.y_ofs 
      (fun fz fm sfmap fig prop ->
        (* make trans between fig_src and fig *)
        let prop_trans = {
            fig_id_target = prop.id;
            label = label;
            desc = tsi.label_desc label;
          }
        in
        let prop_src =
          { prop_src with
            outgoing = IntMap.add index prop_trans prop_src.outgoing }
        in
        fig_src
          (SetProp
             (prop_src,
              (fun _ fig_src ->
                let fm = IntMap.add prop_src.id fig_src fm in
                cont fz fm sfmap fig_src prop_src fig prop))))

  and make_state_fig fz fm sfmap path state x y w h dx dy cont =
    let zo = Draw.new_zo_front fz in
    let id = Draw.new_id fm in
    let desc = tsi.state_desc state in
    let properties = tsi.state_properties state in
    let (trans, error) = get_trans ts state in
    let prop = {
        id = id;
        state = state;
        trans = trans;
        outgoing = IntMap.empty;
        error = error;
        path = path;
        desc = desc;
        properties = properties;
        x_ofs = dx;
        y_ofs = dy;
      }
    in
    let fig = FigState.make_figure prop x y w h in
    let fz = IntMap.add zo id fz in
    let fm = IntMap.add id fig fm in
    let sfmap = sfmap_add (tsi.state_id state) id sfmap in
    cont fz fm sfmap fig prop

  in

  let start ()  =
    let fz = IntMap.empty in
    let fm = IntMap.empty in
    let sfmap = IntMap.empty in
    let path = [||] in
    (* initial state *)
    make_state_fig fz fm sfmap path initial_state
      0.0 0.0 state_width state_height 0.0 0.0
      (fun fz fm sfmap fig prop ->
        (* focus on the intial state *)
        cc.cur_state <- prop.state;
        cc.cur_state_fig_id <- prop.id;
        (* tree *)
        make_model_index_tree fz fm sfmap fig prop
          (state_width +. cc.hspace) 0.0 index_tree
          (fun fz fm sfmap ->
            (* retrieve the latest fig and prop *)
            let fig = IntMap.find prop.id fm in
            fig
              (GetProp
                 (fun prop ->
                   let chkmap = make_chkmap prop.outgoing in
                   (* set children *)
                   send cch_cl
                     (Checklist.SetList (prop.trans, chkmap, -1))
                     (fun () ->
                       let sel = IntSet.singleton prop.id in
                       let ext = {
                           tsi=tsi;
                           sfmap=sfmap;
                           sel_fig_id_state_on_path = None;
                         }
                       in
                       let model = { fz=fz; fm=fm; sel=sel; ext=ext; } in
                       update_draw_model model
                         (fun () ->
                           send cch_path (Listbox.SetList (prop.path, -1))
                             process))))))
  in
  register_shortcut_control pe_prop.wch_toplevel wch_draw 48;  (* 0 *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 100; (* d *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 101; (* e *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 106; (* j *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 108; (* l *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 112; (* p *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 114; (* r *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 117; (* u *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 121; (* y *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 122; (* z *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 113; (* q *)
  register_shortcut_control pe_prop.wch_toplevel wch_draw 119; (* w *)
  register_shortcut_alt pe_prop.wch_toplevel wch_draw keyF4;

  par
    [ (fun () -> Hsplitter.init Splitter.Movable wch pch cch_hsp nch_hsp rch_hsp
                   wch_vsp wch_draw
                   (int_of_float (o_o.funit *. 8.0))
                   1            (* border width *)
                   (int_of_float (o_o.funit *. 0.25))); (* mouse grab play *)
      (fun () -> Vsplitter.init Splitter.Movable wch_vsp rch_hsp cch_vsp nch_vsp rch_vsp
                   wch_cl wch_path
                   (int_of_float (o_o.funit *. 10.0))
                   1
                   (int_of_float (o_o.funit *. 0.25)));
      (fun () -> Checklistvs.init wch_cl rch_vsp cch_cl nch_cl
                   ud_trans_cl dc_trans_cl);
      (fun () -> Listboxvs.init wch_path rch_vsp cch_path nch_path
                   ud_path_lb dc_path_lb);
      (fun () -> Draw.init wch_draw rch_hsp cch_draw nch_draw ext);
      start]
