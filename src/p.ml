open Printf
open Error
open IdCol

type t =
  Stop
| Skip
| Omega
| Cont of Id.t * E.t list
| Spon of t
| Prefix of E.t * t
| Receive of E.t * T.t * Id.t list * E.t * t
| Branch of t list
| Alt of t list
| Amb of t list
| Seq of t list
| Par of E.t * t list
| AlphaPar of (E.t * t) list
| Hide of E.t * t
| Rename of E.t * t
| XAlt of Id.t * E.t * T.t * t
| XAmb of Id.t * E.t * T.t * t
| XSeq of Id.t * E.t * T.t * t
| XPar of Id.t * E.t * T.t * E.t * t
| XAlphaPar of Id.t * E.t * T.t * E.t * t
| If of E.t * t * t
| Let of ((Id.t * T.t) list * E.t) list * t
| Case of E.t * Id.t * (Id.t * (Id.t list * t)) list
| Pos of S.pos * t

let rec dig p =
  match p with
    Pos (_, p) -> dig p
  | _ -> p

let rec convert mdb expr =
  let ft rt =
    match !rt with
      Some t -> t
    | None -> Error.corrupt_s "E.convert " (S.show expr)
  in
  match expr with
  | S.Bool b      -> error "P.convert"
  | S.Int k       -> error "P.convert"
  | S.Var n       -> Cont (n, [])
  | S.Univ _      -> error "P.convert"
  | S.Tuple _     -> error "P.convert"
  | S.Set _       -> error "P.convert"
  | S.List _      -> error "P.convert"
  | S.SetRange _  -> error "P.convert"
  | S.ListRange _ -> error "P.convert"
  | S.Chset _     -> error "P.convert"
  | S.Chmap _     -> error "P.convert"
  | S.And _       -> error "P.convert"
  | S.Or _        -> error "P.convert"
  | S.If (test, e1, e2) ->
     If (E.convert mdb test, convert mdb e1, convert mdb e2)
  | S.Let (binding, e) ->
     let binding' =
       List.map
         (fun (xs, e) ->
           let xs' = List.map (fun (x, rt) -> (x, ft rt)) xs in
           (xs', E.convert mdb e))
         binding
     in
     Let (binding', convert mdb e)
  | S.Case (e, rn, bs) ->
     let n =
       match !rn with
         Some n -> n
       | None -> Error.corrupt_s "P.convert" (S.show expr)
     in
     let bs' =
       List.map (fun (ctor, (vs, e)) -> (ctor, (vs, convert mdb e))) bs
     in Case (E.convert mdb e, n, bs')
  | S.Stop -> Stop
  | S.Skip -> Skip
  | S.Spon p -> Spon (convert mdb p)
  | S.Prefix (e, p) ->
     Prefix (E.convert mdb e, convert mdb p)
  | S.Receive (ch, rt, vs, g, p) ->
     Receive (E.convert mdb ch, ft rt, vs, E.convert mdb g, convert mdb p)
  | S.Branch ps ->
     Branch (List.map (convert mdb) ps)
  | S.Alt ps ->
     Alt (List.map (convert mdb) ps)
  | S.Amb ps -> 
     Amb (List.map (convert mdb) ps)
  | S.Seq ps -> 
     Seq (List.map (convert mdb) ps)
  | S.Par (x, ps) -> 
     Par (E.convert mdb x, List.map (convert mdb) ps)
  | S.AlphaPar xs ->
     AlphaPar (List.map (fun (a, p) -> (E.convert mdb a, convert mdb p)) xs)
  | S.Hide (a, p) ->
     Hide (E.convert mdb a, convert mdb p)
  | S.Rename (m, p) ->
     Rename (E.convert mdb m, convert mdb p)
  | S.XAlt (x, r, rt, p) ->
     XAlt (x, E.convert mdb r, ft rt, convert mdb p)
  | S.XAmb (x, r, rt, p) ->
     XAmb (x, E.convert mdb r, ft rt, convert mdb p)
  | S.XSeq (x, r, rt, p) ->
     XSeq (x, E.convert mdb r, ft rt, convert mdb p)
  | S.XPar (x, r, rt, a, p) ->
     XPar (x, E.convert mdb r, ft rt, E.convert mdb a, convert mdb p)
  | S.XAlphaPar (x, r, rt, a, p) ->
     XAlphaPar (x, E.convert mdb r, ft rt, E.convert mdb a, convert mdb p)
  | S.Fun (xts, e, rt) -> error "P.convert"
  | S.Apply (f, t_f, ets) ->
     (match f with
        Var n ->
         let es' =
           List.map
             (fun (e, rt) -> E.convert mdb e)
             ets
         in
         Cont (n, es')
      | _ -> error "P.convert")
  | S.Pos (pos, e) ->
     with_pos pos
       (fun () -> Pos (pos, convert mdb e))

let rec collect_vars bs acc p =
  match p with
    Stop -> acc
  | Skip -> acc
  | Omega -> acc
  | Cont (n, es) ->
     List.fold_left (E.collect_vars bs) acc es
  | Spon p ->
     collect_vars bs acc p
  | Prefix (e, p) ->
     let acc = E.collect_vars bs acc e in
     collect_vars bs acc p
  | Receive (ch, t_ch, xs, g, p) ->
     let acc = E.collect_vars bs acc ch in
     let bs' = IdSet.remove_list xs bs in
     let acc = E.collect_vars bs' acc g in
     collect_vars bs' acc p
  | Branch ps ->
     List.fold_left (collect_vars bs) acc ps
  | Alt ps ->
     List.fold_left (collect_vars bs) acc ps
  | Amb ps ->
     List.fold_left (collect_vars bs) acc ps
  | Seq ps ->
     List.fold_left (collect_vars bs) acc ps
  | Par (x, ps) ->
     let acc = E.collect_vars bs acc x in
     List.fold_left (collect_vars bs) acc ps
  | AlphaPar xs ->
     List.fold_left
       (fun acc (a, p) ->
         let acc = E.collect_vars bs acc a in
         collect_vars bs acc p)
       acc xs
  | Hide (x, p) ->
     let acc = E.collect_vars bs acc x in
     collect_vars bs acc p
  | Rename (m, p) ->
     let acc = E.collect_vars bs acc m in
     collect_vars bs acc p
  | XAlt (x, r, t_r, p) ->
     let acc = E.collect_vars bs acc r in
     let bs' = IdSet.remove x bs in
     collect_vars bs' acc p
  | XAmb (x, r, t_r, p) ->
     let acc = E.collect_vars bs acc r in
     let bs' = IdSet.remove x bs in
     collect_vars bs' acc p
  | XSeq (x, r, t_r, p) ->
     let acc = E.collect_vars bs acc r in
     let bs' = IdSet.remove x bs in
     collect_vars bs' acc p
  | XPar (x, r, t_r, a, p) ->
     let acc = E.collect_vars bs acc a in
     let acc = E.collect_vars bs acc r in
     let bs' = IdSet.remove x bs in
     collect_vars bs' acc p
  | XAlphaPar (x, r, t_r, a, p) ->
     let acc = E.collect_vars bs acc r in
     let bs' = IdSet.remove x bs in
     let acc = E.collect_vars bs' acc a in
     collect_vars bs' acc p
  | If (test, p1, p2) ->
     let acc = E.collect_vars bs acc test in
     let acc = collect_vars bs acc p1 in
     collect_vars bs acc p2
  | Let (bindings, p) ->
     let rec loop bs' acc bindings =
       match bindings with
         [] -> collect_vars bs' acc p
       | (xs, e)::bindings' ->
          let bs' =
            List.fold_left
              (fun bs' (x, t) -> IdSet.remove x bs')
              bs' xs
          in
          let acc = E.collect_vars bs acc e in
          loop bs' acc bindings'
     in loop bs acc bindings
  | Case (e, n, branches) ->
     let acc = E.collect_vars bs acc e in
     List.fold_left
       (fun acc (ctor, (xs, p)) ->
         let bs' = IdSet.remove_list xs bs in
         collect_vars bs' acc p)
       acc branches
  | Pos (_, p) -> collect_vars bs acc p

let rec show p =
  match p with
    Stop -> "STOP"
  | Skip -> "SKIP"
  | Omega -> "OMEGA"
  | Cont (n, es) ->
     if es=[] then
       Id.show n
     else
       sprintf "(%s %s)" (Id.show n) (E.show_list es)
  | Spon p -> sprintf "(tau %s)" (show p)
  | Prefix (e, p) -> sprintf "(! %s %s)" (E.show e) (show p)
  | Receive (ch, t_ch, xs, g, p) ->
     sprintf "(? %s (%s) %s %s)"
       (E.show ch) (Id.show_list xs) (E.show g) (show p)
  | Branch ps -> sprintf "(branch %s)" (show_list ps)
  | Alt ps -> sprintf "(alt %s)" (show_list ps)
  | Amb ps -> sprintf "(amb %s)" (show_list ps)
  | Seq ps -> sprintf "(seq %s)" (show_list ps)
  | Par (x, ps) -> sprintf "(par %s %s)" (E.show x) (show_list ps)
  | AlphaPar xs -> sprintf "(apar %s)" (show_alpha_proc_list xs)
  | Hide (x, p) -> sprintf "(hide %s %s)" (E.show x) (show p)
  | Rename (m, p) -> sprintf "(rename %s %s)" (E.show m) (show p)
  | XAlt (x, r, t_r, p) ->
     sprintf "(xalt %s %s %s)" (Id.show x) (E.show r) (show p)
  | XAmb (x, r, t_r, p) ->
     sprintf "(xamb %s %s %s)" (Id.show x) (E.show r) (show p)
  | XSeq (x, r, t_r, p) ->
     sprintf "(xseq %s %s %s)" (Id.show x) (E.show r) (show p)
  | XPar (x, r, t_r, a, p) ->
     sprintf "(xpar %s %s %s %s)" (Id.show x) (E.show r) (E.show a) (show p)
  | XAlphaPar (x, r, t_r, a, p) ->
     sprintf "(xapar %s %s %s %s)" (Id.show x) (E.show r) (E.show a) (show p)
  | If (test, p1, p2) ->
     sprintf "(if %s %s %s)" (E.show test) (show p1) (show p2)
  | Let (bs, p) ->
     let s =
       List.fold_left
         (fun s (xs, e) ->
           sprintf "%s ((%s) %s)" s
             (Id.show_list (List.map (fun (x, t) -> x) xs))
             (E.show e))
       "" bs
     in
     sprintf "(let (%s) %s)" s (show p)
  | Case (e, n, bs) ->
     let s =
       List.fold_left
         (fun s (ctor, (xs, p)) ->
           sprintf "%s ((%s %s) %s)"
             s (Id.show ctor) (Id.show_list xs) (show p))
         "" bs
     in
     sprintf "(case %s %s)" (E.show e) s
  | Pos (_, p) -> show p

and show_list ps =
  List.fold_left
    (fun s p -> sprintf "%s %s" s (show p))
    "" ps

and show_alpha_proc_list xs =
  List.fold_left
    (fun s (a, p) -> sprintf "%s (%s %s)" s (E.show a) (show p))
    "" xs

let rec reduce p =
  match p with
    Stop -> p
  | Skip -> p
  | Omega -> p
  | Cont (n, es) -> p
  | Spon p -> Spon (reduce p)
  | Prefix (e, p) -> Prefix (e, reduce p)
  | Receive (ch, t_ch, xs, g, p) -> Receive (ch, t_ch, xs, g, reduce p)
  | Branch ps ->
     let ps = List.map reduce ps in
     (match ps with
        [Branch ps; r] -> reduce (Alt (ps @ [r]))
      | _ -> Branch ps)
  | Alt ps ->
     let ps = List.map reduce ps in
     (match ps with
        [Alt ps; r] -> reduce (Alt (ps @ [r]))
      | _ -> Alt ps)
  | Amb ps ->
     let ps = List.map reduce ps in
     (match ps with
        [Amb ps; r] -> reduce (Amb (ps @ [r]))
      | _ -> Amb ps)
  | Seq ps ->
     let ps = List.map reduce ps in
     (match ps with
        [Seq ps; r] -> reduce (Seq (ps @ [r]))
      | _ -> Seq ps)
  | Par (x, ps) ->
     let ps = List.map reduce ps in
     Par (x, ps)
  | AlphaPar xs -> AlphaPar (List.map (fun (a, p) -> (a, reduce p)) xs)
  | Hide (x, p) -> Hide (x, reduce p)
  | Rename (m, p) -> Rename (m, reduce p)
  | XAlt (x, r, t_r, p) -> XAlt (x, r, t_r, reduce p)
  | XAmb (x, r, t_r, p) -> XAmb (x, r, t_r, reduce p)
  | XSeq (x, r, t_r, p) -> XSeq (x, r, t_r, reduce p)
  | XPar (x, r, t_r, a, p) -> XPar (x, r, t_r, a, reduce p)
  | XAlphaPar (x, r, t_r, a, p) -> XAlphaPar (x, r, t_r, a, reduce p)
  | If (test, p1, p2) -> If (test, reduce p1, reduce p2)
  | Let (bs, p) -> Let (bs, reduce p)
  | Case (e, n, bs) ->
     let bs' = List.map (fun (ctor, (xs, p)) -> (ctor, (xs, reduce p))) bs in
     Case (e, n, bs')
  | Pos (_, p) -> reduce p

let rec priority p =
  match p with
    Stop -> 0
  | Skip -> 0
  | Omega -> 0
  | Cont (n, es) -> 1
  | Spon p -> 2
  | Prefix (e, p) -> 2
  | Receive (ch, t_ch, xs, g, p) -> 2
  | Branch ps -> 4
  | Alt ps -> 4
  | Amb ps -> 4
  | Seq ps -> 3
  | Par (x, ps) -> 4
  | AlphaPar _ -> 4
  | Hide (x, p) -> 5
  | Rename (m, p) -> 1
  | XAlt (x, r, t_r, p) -> 6
  | XAmb (x, r, t_r, p) -> 6
  | XSeq (x, r, t_r, p) ->  6
  | XPar (x, r, t_r, a, p) -> 6
  | XAlphaPar (x, r, t_r, a, p) -> 6
  | If (test, p1, p2) -> 7
  | Let (bs, p) -> 7
  | Case (e, n, bs) -> 7
  | Pos (_, p) -> priority p

let rec desc p0 =
  match p0 with
    Stop -> "STOP"
  | Skip -> "SKIP"
  | Omega -> "OMEGA"
  | Cont (n, es) ->
     if es=[] then
       Id.show n
     else
       sprintf "%s(%s)" (Id.show n) (E.desc_list E.desc es)
  | Spon p ->
     sprintf "tau->%s" (enparen p0 p)
  | Prefix (e, p) ->
     sprintf "%s->%s" (E.desc e) (enparen p0 p)
  | Receive (ch, t_ch, xs, g, p) ->
     let s =
       List.fold_left
         (fun s x -> sprintf "%s?%s" s (Id.show x))
         "" xs
     in
     (match g with
        E.Bool true ->
         sprintf "%s%s->%s" (E.desc ch) s (enparen p0 p)
      | _ ->
         sprintf "%s%s[%s]->%s" (E.desc ch) s (E.desc g) (enparen p0 p))
  | Branch ps ->
     let s =
       List.fold_left
         (fun s p -> sprintf "%s %s" s (enparen p0 p))
         "" ps
     in sprintf "(branch %s)" s
  | Alt ps ->
     (match ps with
        [] -> "STOP"
      | [p] -> desc p
      | p::ps' ->
         List.fold_left
           (fun str p -> sprintf "%s [] %s" str (enparen p0 p))
           (sprintf "%s" (enparen p0 p)) ps')
  | Amb ps ->
     (match ps with
        [] -> error "desc amb"
      | [p] -> desc p
      | p::ps' ->
         List.fold_left
           (fun str p -> sprintf "%s |~| %s" str (enparen p0 p))
           (sprintf "%s" (enparen p0 p)) ps')
  | Seq ps ->
     (match ps with
        [] -> error "desc amb"
      | [p] -> desc p
      | p::ps' ->
         List.fold_left
           (fun str p -> sprintf "%s; %s" str (enparen p0 p))
           (sprintf "%s" (enparen p0 p)) ps')
  | Par (x, ps) ->
     (match ps with
        [] -> error "desc par"
      | [p] -> desc p
      | p::ps' ->
         List.fold_left
           (fun str p -> sprintf "%s||%s" str (enparen p0 p))
           (sprintf "%s" (enparen p0 p)) ps')
  | AlphaPar xs -> "||"
  | Hide (x, p) ->
     sprintf "(%s)\\%s" (enparen p0 p) (E.desc x)
  | Rename (m, p) ->
     sprintf "%s[[...]]" (enparen p0 p)
  | XAlt (x, r, t_r, p) ->
     sprintf "[]%s:%s@%s" (Id.show x) (E.desc r) (enparen p0 p)
  | XAmb (x, r, t_r, p) ->
     sprintf "|~|%s:%s@%s" (Id.show x) (E.desc r) (enparen p0 p)
  | XSeq (x, r, t_r, p) ->
     sprintf ";%s:%s@%s" (Id.show x) (E.desc r) (enparen p0 p)
  | XPar (x, r, t_r, a, p) ->
     sprintf "||%s:%s@%s" (Id.show x) (E.desc r) (enparen p0 p)
  | XAlphaPar (x, r, t_r, a, p) ->
     sprintf "||%s:%s@%s" (Id.show x) (E.desc r) (enparen p0 p)
  | If (test, p1, p2) ->
     sprintf "if %s then %s else %s"
       (E.desc test) (enparen p0 p1) (enparen p0 p2)
  | Let (bs, p) ->
     sprintf "let ... within %s" (enparen p0 p)
  | Case (e, n, bs) ->
     sprintf "case %s of ..." (E.desc e)
  | Pos (_, p) -> desc p

and enparen p q =
  if priority p >= priority q then
    desc q
  else
    sprintf "(%s)" (desc q)
