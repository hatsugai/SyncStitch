open Guedra
open DrawModel
open Draw
open PeFig

let color_state = color 1.0 1.0 1.0
let color_state_clone = color 1.0 1.0 1.0
let color_focus_on_path_fill = color 0.0 1.0 0.2
let color_focus_on_path_text = color_black

type handle = LT | MT | RT | LM | RM | LB | MB | RB

type transform_context =
  Idle
| Resizing of handle * float * float * float * float
| Scroll of float * float * float * float

let handles = [LT; MT; RT; LM; RM; LB; MB; RB]

let calc_text_size text =
  let rec loop w h text =
    match text with
      [] -> (w, h)
    | s::text ->
       let extents = text_extents s in
       loop (max w extents.width) (h +. extents.height) text
  in
  set_font o_o.font;
  loop 0.0 0.0 text

let handle_point handle x y w h =
  match handle with
    LT -> (x, y)
  | MT -> (x +. w *. 0.5, y)
  | RT -> (x +. w, y)
  | LM -> (x, y +. h *. 0.5)
  | RM -> (x +. w, y +. h *. 0.5)
  | LB -> (x, y +. h)
  | MB -> (x +. w *. 0.5, y +. h)
  | RB -> (x +. w, y +. h)

let in_handle x y xp yp =
  xp >= x -. o_o.handle_size && xp < x +. o_o.handle_size *. 2.0 &&
    yp >= y -. o_o.handle_size && yp < y +. o_o.handle_size *. 2.0

let hittest_handle x y w h xp yp =
  List.find_opt
    (fun handle ->
      let (xh, yh) = handle_point handle x y w h in
      in_handle xh yh xp yp)
  handles

let transform_by_handle handle x y w h dx dy =
  match handle with
    LT -> (x +. dx, y +. dy, w -. dx, h -. dy)
  | MT -> (x, y +. dy, w, h -. dy)
  | RT -> (x, y +. dy, w +. dx, h -. dy)
  | LM -> (x +. dx, y, w -. dx, h)
  | RM -> (x, y, w +. dx, h)
  | LB -> (x +. dx, y, w -. dx, h +. dy)
  | MB -> (x, y, w, h +. dy)
  | RB -> (x, y, w +. dx, h +. dy)

let select_subtree id fm cont =
  let rec collect s id k =
    let s = IntSet.add id s in
    let fig = IntMap.find id fm in
    fig
      (GetProp
         (fun prop ->
           IntMap.enum_lnr s prop.outgoing
             (fun s o next ->
               match o with
                 None -> k s
               | Some (index, prop_trans) ->
                  collect s prop_trans.fig_id_target next)))
  in
  collect IntSet.empty id cont

let rec make_figure prop x y w h =

  let rec make_fig x y w h tc0 =

    let rec make tc =
      fun cmd ->
      match cmd with
        HitTest (xp, yp, k) ->
         k (hittest xp yp)
      | Draw (model, cap, oz, k) ->
         draw tc (model, cap, oz, k)
      | MouseDown (xp, yp, state, button, model, cap, zo, k) ->
         mouse_down (xp, yp, state, button, model, cap, zo, k)
      | MouseMove (xp, yp, state, k) ->
         mouse_move tc (xp, yp, state, k)
      | MouseUp (xp, yp, state, button, k) ->
         mouse_up tc (xp, yp, state, button, k)
      | ConnectPoint (connect, k) ->
         connect_point tc connect k
    | Boundary k -> k x y w h
    | GetProp k -> k prop
    | SetProp (prop, k) ->
       k prop (make_figure prop x y w h)
    | Move (dx, dy, k) ->
       k (make_figure prop (x +. dx) (y +. dy) w h)
    | Resize (w, h, k) ->
       k (make_figure prop x y w h)

    and transform tc =
      let (x, y, w, h) =
        match tc with
          Resizing (handle, x0, y0, x1, y1) ->
           transform_by_handle handle x y w h (x1 -. x0) (y1 -. y0)
        | _ -> (x, y, w, h)
      in
      let (x, w) = if w >= 0.0 then (x, w) else (x +. w, -. w) in
      let (y, h) = if h >= 0.0 then (y, h) else (y +. h, -. h) in
      (x, y, w, h)

    and connect_point state connect_type k =
      let (x, y, w, h) = transform state in
      k connect_type x (y +. h *. 0.5)

    and hittest xp yp =
      match hittest_handle x y w h xp yp with
        None ->
         xp >= x && xp < x +. w && yp >= y && yp < y +. h
      | Some handle -> true

    and mouse_down (xp, yp, state, button, model, cap, zo, k) =
      if button = mouseButtonLeft
         && (state land keyStateMask) = 0 then
        (* move or transform *)
        match hittest_handle x y w h xp yp with
          None ->
           let cap = CapMove ((xp, yp), (xp, yp)) in
           let sel = IntSet.singleton prop.id in
           let model' = { model with sel = sel } in
           k model' cap [OnSelected model']
        | Some handle ->
           let tc = Resizing (handle, xp, yp, xp, yp) in
           let fig = make tc in
           let cap = CapFigure (prop.id, fig) in
           let sel = IntSet.singleton prop.id in
           let model' = { model with sel = sel } in
           k model' cap [OnSelected model']
      else if button = mouseButtonLeft
              && (state land keyStateMask) = keyStateShift then
        (* select or unselect *)
        (if IntSet.mem prop.id model.sel then
           let model' = { model with sel = IntSet.remove prop.id model.sel } in
           k model' CapNone [OnSelected model']
         else
           let model' = { model with sel = IntSet.add prop.id model.sel } in
           k model' CapNone [OnSelected model'])
      else if button = mouseButtonLeft
              && (state land keyStateMask) = keyStateAlt then
        (* select subtree *)
        select_subtree prop.id model.fm
          (fun sel ->
           let model' = { model with sel = sel } in
            k model' (CapMove ((xp, yp), (xp, yp))) [OnSelected model'])
      else if button = mouseButtonRight
              && (state land keyStateMask) = keyStateShift then
        (* scroll text *)
        let tc = Scroll (xp, yp, xp, yp) in
        let fig = make tc in
        let cap = CapFigure (prop.id, fig) in
        let sel = IntSet.singleton prop.id in
        let model' = { model with sel = sel } in
        k model' cap [OnSelected model']
      else
        k model CapNone []

    and mouse_move tc (xp, yp, state, k) =
      let tc =
        match tc with
          Idle -> Idle
        | Resizing (handle, x0, y0, x1, y1) ->
           (Resizing (handle, x0, y0, xp, yp))
        | Scroll (x0, y0, x1, y1) ->
           (Scroll (x0, y0, xp, yp))
      in
      k (make tc)

    and mouse_up tc (xp, yp, state, button, k) =
      let (x, y, w, h) = transform tc in
      match tc with
        Scroll (x0, y0, x1, y1) ->
         let prop' =
           { prop with
             x_ofs = prop.x_ofs +. x1 -. x0;
             y_ofs = prop.y_ofs +. y1 -. y0 }
         in
         k (make_figure prop' x y w h)
      | _ ->
         k (make_fig x y w h Idle)

    and draw tc (model, cap, oz, k) =
      let fm = model.fm in
      let sel = model.sel in
      let sfmap = model.ext.sfmap in
      let clones = IntMap.find (model.ext.tsi.state_id prop.state) sfmap in
      let b_alone = IntSet.is_single clones in
      let b_sel = IntSet.mem prop.id sel in
      let b_single = IntSet.is_single sel in
      let b_clone = if b_single then
                    let id = IntSet.choose sel in
                    IntSet.mem id clones
                  else false
      in
      let b_focus_on_path =
        match model.ext.sel_fig_id_state_on_path with
          None -> false
        | Some id -> id = prop.id
      in
      let (x, y, w, h) = transform tc in
      let (x, y) =
        match cap with
          CapMove ((x0, y0), (x1, y1)) ->
           if IntSet.mem prop.id sel then
             (x +. x1 -. x0, y +. y1 -. y0)
           else (x, y)
        | _ -> (x, y)
      in
      let (x_ofs, y_ofs) =
        match tc with
          Scroll (x0, y0, x1, y1) ->
           (prop.x_ofs +. x1 -. x0, prop.y_ofs +. y1 -. y0)
        | _ -> (prop.x_ofs, prop.y_ofs)
      in
      let xp = x +. w in
      let yp = y +. h *. 0.5 in
      draw_outgoing model.ext.tsi fm sel cap xp yp prop.outgoing
        (fun () ->
          (*
          (if b_alone then
             set_color o_o.color_state
           else if b_clone then
             set_color o_o.color_state_clone_sel
           else
             set_color o_o.color_state_clone);
           *)
          (if b_focus_on_path then
             (set_color color_focus_on_path_fill;
              fill_rect x y w h;
              set_color o_o.color_fore;
              set_line_width o_o.line_width;
              draw_rect x y w h;
             set_color color_focus_on_path_text)
           else if b_alone then
             (set_color o_o.color_back;
              fill_rect x y w h;
              set_color o_o.color_fore;
              set_line_width o_o.line_width;
              draw_rect x y w h)
           else if b_clone then
             (set_color color_state_clone;
              fill_rect x y w h;
              set_color o_o.color_back)
           else
             (set_color o_o.color_back;
              fill_rect x y w h;
              set_color o_o.color_fore;
              set_line_width o_o.line_width;
              set_dash_symmetric o_o.dash 0.0;
              draw_rect x y w h;
              set_dash_solid ()));
          set_font o_o.font;
          push_clip_f x y w h;
          List.iteri
            (fun i s ->
              draw_text
                (o_o.left_margin +. x +. x_ofs)
                (o_o.top_margin +. y +. y_ofs +. (flo i) *. o_o.funit)
                s)
            prop.desc;
          pop_clip ();
          (match cap with
             CapNone ->
              (if b_sel then
                 (if b_single then
                    draw_handles x y w h
                  else
                    draw_sel_handles x y w h))
           | CapFigure (id, fig) -> ()
           | CapScroll _ -> ()
           | CapSelect ((x0, y0), (x1, y1), tsel) ->
              if b_sel || IntSet.mem prop.id tsel then
                draw_sel_handles x y w h
              else ()
           | CapMove ((x0, y0), (x1, y1)) -> ());
          k ())

      and draw_outgoing tsi fm sel cap x y outgoing k =
        IntMap.enum_lnr () outgoing
          (fun () o next ->
            match o with
              None -> k ()
            | Some (_, prop_trans) ->
               draw_trans tsi fm sel cap x y prop_trans next)

      and text_size text =
        match text with
          [] -> (0.0, 0.0, 0.0)
        | s::text ->
           let extents = text_extents s in
           let rec loop w h text =
             match text with
               [] -> (w, h, extents.height)
             | s::text ->
                let extents = text_extents s in
                loop (max w extents.width) (h +. extents.height) text
           in
           loop extents.width extents.height text

      and draw_trans tsi fm sel cap x y prop_trans k =
        let fig_target = get_act_fig fm cap prop_trans.fig_id_target in
        fig_target
          (ConnectPoint
             ((),
              (fun () xc yc ->
                let (xc, yc) =
                  offset_fig sel cap prop_trans.fig_id_target xc yc
                in
                set_color o_o.color_fore;
                set_line_width o_o.line_width;
                (if tsi.label_dash prop_trans.label then
                   (set_dash_symmetric o_o.dash 0.0;
                    draw_line x y xc yc;
                    set_dash_solid ())
                 else
                   draw_line x y xc yc);
                set_font o_o.font;
                let (tw, th, lh) = text_size prop_trans.desc in
                let x = (x +. xc) *. 0.5 in
                let y = (y +. yc) *. 0.5 in
                set_color o_o.color_back;
                fill_rect
                  (x -. tw *. 0.5 -. o_o.left_margin)
                  (y -. th *. 0.5 -. o_o.top_margin)
                  (tw +. o_o.left_margin +. o_o.right_margin)
                  (th +. o_o.top_margin +. o_o.bottom_margin);
                set_color o_o.color_fore;
                List.iteri
                  (fun i s ->
                    draw_text (x -. tw *. 0.5) (y -. th *. 0.5 +. lh *. (float_of_int i)) s)
                  prop_trans.desc;
                k ())))

    in make tc0

  in make_fig x y w h Idle
