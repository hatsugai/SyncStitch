open S
open OpCsp
open TokenCsp
open LexerCsp
open Printf

type receive_term = Send of S.t | Receive of Id.t
type list_or_interval = XList of S.t list | XRange of S.t * S.t

let alloc_id =
  let c = ref 0 in
  (fun () ->
    let r = !c in
    c := !c + 1;
    Id.make (Printf.sprintf "_%d" r))

let error l msg =
  let pos = LexerCsp.getpos l in
  Error.with_pos (pos.lino, pos.col)
    (fun () -> Error.error msg)

let get_id l =
  match get_token l with
    ID id -> id
  | _ -> error l "missing identifier"

let ensure_token l t =
  let t' = get_token l in
  if t=t' then
    ()
  else
    error l (sprintf "missing '%s'" (show t))

let rec id_list l =
  match get_token l with
    ID n ->
    let t = get_token l in
    (match t with
       COMMA ->
        let ns = id_list l in n::ns
     | _ ->
         pushback l t; [n])
  | _ -> error l "missing identifier"

let rec binding l =
  match get_token l with
    ID n -> [(n, ref None)]
  | LPAR ->
     let ns = id_list l in
     ensure_token l RPAR;
     List.map (fun n -> (n, ref None)) ns
  | _ -> error l "missing identifier or '('"

let pattern l =
  let t = get_token l in
  match t with
    ID n ->
     let t = get_token l in
     (match t with
        ID p -> (n, [p])
      | LPAR ->
         let ns = id_list l in
         ensure_token l RPAR;
         (n, ns)
      | _ ->
         pushback l t; (n, []))
  | _ -> error l "illeal pattern in case"

let rec expr l =
  let pos = getpos l in
  let x = process l in
  Pos ((pos.lino, pos.col), x)

and expr_if l =
  let test = expr l in
  ensure_token l THEN;
  let x = expr l in
  ensure_token l ELSE;
  let y = expr l in
  S.If (test, x, y)

and expr_let l =
  let b = binding l in
  ensure_token l DEF;
  let x = expr l in
  ensure_token l WITHIN;
  let y = expr l in
  S.Let ([(b, x)], y)

and expr_case l =
  let e = expr l in
  ensure_token l OF;
  let bs = case_branch_list l in
  S.Case (e, ref None, bs)

and case_branch_list l =
  let b = case_branch l in
  let t = get_token l in
  match t with
    VERTICALBAR ->
     let bs = case_branch_list l in b::bs
  | _ ->
     pushback l t; [b]

and case_branch l =
  let pat = pattern l in
  ensure_token l ARROW;
  let e = expr l in
  let (ctor, xs) = pat in
  (ctor, (xs, e))

and process l =
  process_hide l

and process_hide l =
  let p = process_par l in
  let t = get_token l in
  match t with
    BACKSLASH ->
     let x = expr_value l in
     S.Hide (x, p)
  | _ ->
     pushback l t; p

and process_par l =
  let p = process_intchoice l in
  let t = get_token l in
  match t with
    LBRA_PAR ->
     let x = expr l in
     ensure_token l RBRA_PAR;
     let q = process_par l in
     S.Par (x, [p; q])
  | INTERLEAVE ->
     let q = process_par l in
     S.Par (S.Set [], [p; q])
  | _ ->
     pushback l t; p

and process_intchoice l =
  let rec loop ps =
    let t = get_token l in
    match t with
      INTCHOICE ->
       let p = process_extchoice l in
       loop (p::ps)
    | _ ->
       pushback l t;
       (match ps with
          [p] -> p
        | _ -> S.Amb (List.rev ps))
  in
  let p = process_extchoice l in
  loop [p]

and process_extchoice l =
  let rec loop ps =
    let t = get_token l in
    match t with
      LBRA ->
       ensure_token l RBRA;
       let p = process_seq l in
       loop (p::ps)
    | _ ->
       pushback l t;
       (match ps with
          [p] -> p
        | _ -> S.Alt (List.rev ps))
  in
  let p = process_seq l in
  loop [p]

and process_seq l =
  let rec loop ps =
    let t = get_token l in
    match t with
      SEMICOLON ->
       let p = process_term l in
       loop (p::ps)
  | _ ->
     pushback l t;
     (match ps with
        [p] -> p
      | _ -> S.Seq (List.rev ps))
  in
  let p = process_term l in
  loop [p]

and process_term l =
  let t = get_token l in
  match t with
    STOP -> S.Stop
  | SKIP -> S.Skip
  | _ ->
     pushback l t;
     let x = expr_value l in
     let t = get_token l in
     match t with
       ARROW ->
        let p = process_term l in S.Prefix (x, p)
     | PERIOD | EXCLAMATION | QUESTION ->
        (* send, receive, or channel application *)
        pushback l t;
        channel_term l x
     | _ ->
        pushback l t; x

(* { .e | !e | ?x }+['[' g ']'] -> p *)
and channel_term l ch =
  (* { .e | !e | ?x }+ *)
  let rec collect cs b_all_send =
    let t = get_token l in
    match t with
      QUESTION ->
       let x = get_id l in
       collect (Receive x::cs) false
    | PERIOD | EXCLAMATION ->
       let x = expr_value l in
       collect (Send x::cs) b_all_send
    | _ ->
       pushback l t;
       (List.rev cs, b_all_send)
  in
  (*
    1. classify sends and receives
    2. assign dummy parameters to sends
   *)
  let parse_receive_term cs =
    let rec loop ps xs es cs =
      match cs with
        [] -> (List.rev ps, List.rev xs, List.rev es)
      | c::cs' ->
         (match c with
            Send e ->
             let n = alloc_id () in
             loop (n::ps) (n::xs) (e::es) cs'
          | Receive x ->
             loop (x::ps) xs es cs')
    in
    loop [] [] [] cs
  in
  (* g ∧ x1=e1 ∧ x2=e1 ∧ ... *)
  let combine_guard g xs es =
    match xs with
      [] -> g
    | _ ->
       List.fold_left2
         (fun g x e ->
           let a =
             S.Apply (op_eq, ref None,
                      [(S.Var x, ref None); (e, ref None)])
           in
           if g = S.Bool true then
             a
           else
             S.And [g; a])
      g xs es
  in
  let (cs, b_all_send) = collect [] true in
  if b_all_send then
    (* prefix (send) or channel application *)
    let x =
      List.fold_left
        (fun f c ->
          match c with
            Send e -> S.Apply (f, ref None, [(e, ref None)])
          | Receive _ -> Error.corrupt "channel_term all send")
        ch cs
    in
    let t = get_token l in
    match t with
      ARROW ->
      let p = process_term l in
      S.Prefix (x, p)
    | _ ->
       pushback l t; x
  else
    let (ps, xs, es) = parse_receive_term cs in
    let g = (* ε | [g] *)
      let t = get_token l in
      (match t with
         LBRA ->
          let g = expr l in
          ensure_token l RBRA;
          g
       | _ ->
          pushback l t;
          Bool true)
    in
    ensure_token l ARROW;
    let p = process_term l in
    let g = combine_guard g xs es in
    S.Receive (ch, ref None, ps, g, p)

and expr_value l =
  let pos = getpos l in
  let x = expr_value2 l in
  Pos ((pos.lino, pos.col), x)

and expr_value2 l =
  expr_logical l

and expr_logical l =
  expr_or l

and expr_or l =
  let rec collect xs =
    let t = get_token l in
    match t with
      OR ->
       let x = expr_and l in
       collect (x::xs)
    | _ ->
       pushback l t;
       (match xs with
          [x] -> x
        | _ -> S.Or (List.rev xs))
  in
  collect [expr_and l]

and expr_and l =
  let rec collect xs =
    let t = get_token l in
    match t with
      AND ->
       let x = expr_not l in
       collect (x::xs)
    | _ ->
       pushback l t;
       (match xs with
          [x] -> x
        | _ -> S.And (List.rev xs))
  in
  collect [expr_not l]

and expr_not l =
  let t = get_token l in
  match t with
    NOT ->
    let e = expr_rel l in
    S.Apply (op_not, ref None, [(e, ref None)])
  | _ ->
     pushback l t;
     expr_rel l

and expr_rel l =
  let x = expr_cat l in
  let t = get_token l in
  match t with
    EQ -> let y = expr_cat l in
          S.Apply (op_eq, ref None, [(x, ref None); (y, ref None)])
  | GE -> let y = expr_cat l in
          S.Apply (op_ge, ref None, [(x, ref None); (y, ref None)])
  | GT -> let y = expr_cat l in
          S.Apply (op_gt, ref None, [(x, ref None); (y, ref None)])
  | LE -> let y = expr_cat l in
          S.Apply (op_le, ref None, [(x, ref None); (y, ref None)])
  | LT -> let y = expr_cat l in
          S.Apply (op_lt, ref None, [(x, ref None); (y, ref None)])
  | NE -> let y = expr_cat l in
          S.Apply (op_ne, ref None, [(x, ref None); (y, ref None)])
  | _ -> pushback l t; x

and expr_cat l =
  let x = expr_sum l in
  let t = get_token l in
  match t with
    CIRCUMFLEX ->
     let y = expr_cat l in
     S.Apply (op_concat, ref None, [(x, ref None); (y, ref None)])
  | _ -> pushback l t; x

and expr_sum l =
  let x = expr_prod l in
  let t = get_token l in
  match t with
    PLUS  -> let y = expr_sum l in
             S.Apply (op_add, ref None, [(x, ref None); (y, ref None)])
  | MINUS -> let y = expr_sum l in
             S.Apply (op_sub, ref None, [(x, ref None); (y, ref None)])
  | _ -> pushback l t; x

and expr_prod l =
  let x = expr_unary l in
  let t = get_token l in
  match t with
    ASTERISK -> let y = expr_prod l in
                S.Apply (op_mul, ref None, [(x, ref None); (y, ref None)])
  | SLASH    -> let y = expr_prod l in
                S.Apply (op_div, ref None, [(x, ref None); (y, ref None)])
  | PERCENT  -> let y = expr_prod l in
                S.Apply (op_mod, ref None, [(x, ref None); (y, ref None)])
  | _ -> pushback l t; x

and expr_unary l =
  expr_prim l

and expr_prim l =
  let t = get_token l in
  match t with
    FALSE -> S.Bool false
  | TRUE -> S.Bool true
  | LITERAL_INT k -> S.Int k
  | MINUS ->
     let x = expr l in
     S.Apply (op_neg, ref None, [(x, ref None)])
  | LPAR ->
     let xs = expr_list1 l in
     ensure_token l RPAR;
     (match xs with
        [x] -> x
      | _ -> S.Tuple xs)
  | LBRA ->
     let t = get_token l in
     (match t with
        RBRA ->
         let t = get_token l in
         (match t with
            ID x ->
             let t = get_token l in
             if t = COLON then      (* xalt *)
               let r = expr l in
               ensure_token l AT;
               let p = process l in
               S.XAlt (x, r, ref None, p)
             else
               error l "unexpected ']'"
          | _ ->
             error l "unexpected ']'")
      | _ ->
         error l "unexpected '['")
  | LT ->
     let t = get_token l in
     (match t with
        GT -> S.List []
      | _ ->
         pushback l t;
         match expr_list1_or_range l with
           XList xs ->
            ensure_token l GT;
            S.List xs
         | XRange (x, y) ->
            ensure_token l GT;
            S.ListRange (x, y))
  | LCUR ->
     let t = get_token l in
     (match t with
        RCUR -> S.Set []
      | _ ->
         pushback l t;
         match expr_list1_or_range l with
           XList xs ->
            ensure_token l RCUR;
            S.Set xs
         | XRange (x, y) ->
            ensure_token l RCUR;
            S.SetRange (x, y))
  | LBRA_CHSET ->
     let t = get_token l in
     (match t with
        RBRA_CHSET -> S.Set []
      | _ ->
         pushback l t;
         let x = expr_list1 l in
         ensure_token l RBRA_CHSET;
         S.Chset (List.map (fun e -> (e, ref None)) x))
  | ID n ->
     let t = get_token l in
     (match t with
        LPAR ->
         let xs = expr_list1 l in
         ensure_token l RPAR;
         let ets = List.map (fun x -> (x, ref None)) xs in
         S.Apply (Var n, ref None, ets)
      | _ ->
         pushback l t; S.Var n)
  | SET ->
     let t = get_token l in
     (match t with
        LPAR ->
         let xs = expr_list1 l in
         ensure_token l RPAR;
         let ets = List.map (fun x -> (x, ref None)) xs in
         S.Apply (Var (Id.make "set"), ref None, ets)
      | _ ->
         error l "missing '('")
  | INTCHOICE ->
     let x = get_id l in
     ensure_token l COLON;
     let r = expr l in
     ensure_token l AT;
     let p = process l in
     S.XAmb (x, r, ref None, p)
  | SEMICOLON ->
     let x = get_id l in
     ensure_token l COLON;
     let r = expr l in
     ensure_token l AT;
     let p = process l in
     S.XSeq (x, r, ref None, p)
  | LBRA_PAR ->
     let a = expr l in
     ensure_token l RBRA_PAR;
     let x = get_id l in
     ensure_token l COLON;
     let r = expr l in
     ensure_token l AT;
     let p = process l in
     S.XPar (x, r, ref None, a, p)
  | INTERLEAVE ->
     let x = get_id l in
     ensure_token l COLON;
     let r = expr l in
     ensure_token l AT;
     let p = process l in
     S.XPar (x, r, ref None, S.Set [], p)
  | IF -> expr_if l
  | LET -> expr_let l
  | CASE -> expr_case l
  | _ ->
     (if !Option.debug then
        Printf.printf "token: %s\n" (TokenCsp.show t));
     error l "missing expression"

and expr_list1_or_range l =
  let x = expr_sum l in
  let t = get_token l in
  match t with
    COMMA ->
     let xs = expr_list1 l in XList (x::xs)
  | RANGE ->
     let y = expr_sum l in      (* from sum level *)
     XRange (x, y)
  | _ ->
     pushback l t; XList [x]

and expr_list1 l =
  let x = expr l in
  let t = get_token l in
  match t with
    COMMA ->
     let xs = expr_list1 l in x::xs
  | _ ->
     pushback l t; [x]

and type_spec l =
  let rec loop rs =
    let t = get_token l in
    match t with
      ASTERISK ->
       let t = type_spec_prim l in
       loop (t::rs)
    | _ ->
       pushback l t;
       let ts = List.rev rs in
       (match ts with
          [t] -> t
        | _ -> TApp (TcTuple, ts))
  in
  let t = type_spec_prim l in
  loop [t]

and type_spec_prim l =
  let t = get_token l in
  match t with
    BOOL  -> TApp (TcBool, [])
  | INT   -> TApp (TcInt None, [])
  | EVENT -> TApp (TcEvent, [])
  | LPAR ->
     let t = get_token l in
     (match t with
        MINUS ->
         pushback l MINUS;
         pushback l LPAR;
         type_spec_int_range l
      | _ ->
         pushback l t;
         let ts = type_spec_list l in
         ensure_token l RPAR;
         (match ts with
            [t] -> t
          | ts  -> TApp (TcTuple, ts)))
  | LCUR ->
     let t = type_spec l in
     ensure_token l RCUR;
     TApp (TcSet, [t])
  | LT ->
     let t = type_spec l in
     ensure_token l GT;
     TApp (TcList, [t])
  | ID n ->                     (* interval or typename (variant) *)
     let t = get_token l in
     (match t with
        RANGE ->
         let t = expr l in
         TApp (TcInt (Some (S.Var n, t)), [])
      | _ ->
         pushback l t;
         TApp (TcName n, []))
  | LITERAL_INT a ->            (* interval *)
     let t = get_token l in
     (match t with
        RANGE ->
         let t = expr l in
         TApp (TcInt (Some (S.Int a, t)), [])
      | _ -> Error.error "missing type specifier")
  | _ ->
     pushback l t;
     type_spec_int_range l

and type_spec_int_range l =
  let x = expr l in
  let t = get_token l in
  (match t with
     RANGE ->
      let y = expr l in
      TApp (TcInt (Some (x, y)), [])
   | _ -> Error.error "missing type specifier")

and type_spec_list l =
  let rec loop ts =
    let x = get_token l in
    if x = COMMA then
      let t = type_spec l in loop (t::ts)
    else
      (pushback l x; List.rev ts)
  in
  let t = type_spec l in loop [t]

let ctor_spec l =
  let t = get_token l in
  match t with
    ID n ->
     let rec loop rs =
       let t = get_token l in
       if t = PERIOD then
         let t = type_spec l in loop (t::rs)
       else
         (pushback l t; (n, List.rev rs))
     in loop []
  | _ -> error l "missing constructor specifier"

let ctor_spec_list l =
  let rec loop cs =
    let t = get_token l in
    if t = VERTICALBAR then
      let c = ctor_spec l in
      loop (c::cs)
    else
      (pushback l t; List.rev cs)
  in
  let c = ctor_spec l in
  loop [c]

let datatype_def l =
  let id = get_id l in
  ensure_token l DEF;
  let cs = ctor_spec_list l in
  S.DefDatatype (id, cs)

let nametype_def l =
  let id = get_id l in
  ensure_token l DEF;
  let t = type_spec l in
  S.DefNametype (id, t)

let id_list l =
  let rec loop xs =
    let t = get_token l in
    if t = COMMA then
      let t = get_token l in
      match t with
        ID n -> loop (n::xs)
      | _ -> error l ""
    else
      (pushback l t; List.rev xs)
  in
  let t = get_token l in
  match t with
    ID n -> loop [n]
  | _ -> []

let event_def l =
  let xs = id_list l in
  S.DefChannel (xs, [])

let type_spec_dot_list l =
  let rec loop ts =
    let x = get_token l in
    if x = PERIOD then
      let t = type_spec l in loop (t::ts)
    else
      (pushback l x; List.rev ts)
  in
  let t = type_spec l in
  loop [t]

(*
  channel <name>+ : <type>{.<type>}*
*)
let channel_def l =
  let xs = id_list l in
  ensure_token l COLON;
  let ts = type_spec_dot_list l in
  DefChannel (xs, ts)

let rec parameter_decl_list l =
  let t = get_token l in
  match t with
    ID n ->
     let t = get_token l in
     (match t with
        COMMA ->
         let ps = parameter_decl_list l in n::ps
      | _ ->
         pushback l t; [n])
  | _ -> error l "missing identifier"

let const_def l =
  match get_token l with
    ID n ->
     (match get_token l with
        DEF ->
         let x = expr l in
         S.Def (n, x)
      | LPAR ->
         let xs = parameter_decl_list l in
         let xts = List.map (fun x -> (x, ref None, None)) xs in
         ensure_token l RPAR;
         ensure_token l DEF;
         let e = expr l in
         S.Def (n, S.Fun (xts, e, ref None))
      | _ -> error l "missing '=' or '('")
  | _ -> error l "missing identifier"

let assertion_decl l =
  match get_token l with
    DEADLOCK ->
     let id = get_id l in
     Deadlock id
  | DIVERGENCE ->
     let id = get_id l in
     Divergence id
  | ID p ->
     let t = get_token l in
     let q = get_id l in
     if t=IS_REFINED_BY_ON_TRACES then
       Traces (p, q)
     else if t=IS_REFINED_BY_ON_FAILURES then
       Failures (p, q)
     else
       error l "assertion"
  | _ -> error l "assertion"

let get_parameter l =
  let key = Id.show (get_id l) in
  ensure_token l DEF;
  let value =
    let v = get_token l in
    match v with
      LITERAL_INT k -> k
    | _ -> error l "get_option"
  in
  (key, value)

let parse_toplevel l =
  let rec loop ds bs cs =
    let pos = LexerCsp.getpos l in
    let t = get_token l in
    if t = EOF then
      {
        def_list = List.rev ds;
        assertion_list = List.rev bs;
        command_list = List.rev cs;
      }
    else if t = HASH then
      let (k, v) = get_parameter l in
      loop ds bs ((SetProp ((pos.lino, pos.col), k, v))::cs)
    else if t = CHECK then
      let c = assertion_decl l in
      loop ds (c::bs) cs
    else if t = PRINT then
      let e = expr l in
      loop ds bs ((Print ((pos.lino, pos.col), e))::cs)
    else if t = TEST then
      let e = expr l in
      loop ds bs ((Test ((pos.lino, pos.col), e))::cs)
    else
      let d =
        if t = DATATYPE then
          datatype_def l
        else if t = NAMETYPE then
          nametype_def l
        else if t = EVENT then
          event_def l
        else if t = CHANNEL then
          channel_def l
        else
          (pushback l t; const_def l)
      in
      loop (d::ds) bs cs
  in loop [] [] []

let parse filename =
  match Posin.open_in_opt filename with
    Some ch ->
     let lexer = LexerCsp.init ch in
     parse_toplevel lexer
  | None ->
     Error.error_s "cannot open " filename
