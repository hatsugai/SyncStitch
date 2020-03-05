open Printf

type pos = int * int

type t =
  Bool of bool
| Int of int
| Var of Id.t
| Univ of T.t option ref
| Tuple of t list
| Set of t list
| List of t list
| SetRange of t * t
| ListRange of t * t
| Chset of (t * T.t option ref) list
| Chmap of ((t * T.t option ref) * (t * T.t option ref)) list
| And of t list
| Or of t list
| If of t * t * t
| Let of ((Id.t * T.t option ref) list * t) list * t
| Case of t * Id.t option ref * (Id.t * (Id.t list * t)) list
| Stop
| Skip
| Spon of t
| Prefix of t * t
| Receive of t * T.t option ref * Id.t list * t * t
| Branch of t list
| Alt of t list
| Amb of t list
| Seq of t list
| Par of t * t list
| Hide of t * t
| Rename of t * t
| XAlt of Id.t * t * T.t option ref * t
| XAmb of Id.t * t * T.t option ref * t
| XSeq of Id.t * t * T.t option ref * t
| XPar of Id.t * t * T.t option ref * t * t
| Fun of (Id.t * T.t option ref * tyspec option) list * t * T.t option ref
| Apply of t * T.t option ref * (t * T.t option ref) list
| Pos of pos * t

and tyspec =
  TApp of tyctor * tyspec list

and tyctor =
  TcBool
| TcInt of (t * t) option
| TcTuple
| TcSet
| TcList
| TcEvent
| TcFun
| TcName of Id.t

type assertion =
  Deadlock of Id.t
| Divergence of Id.t
| Traces of Id.t * Id.t
| Failures of Id.t * Id.t

type definition =
  Def of Id.t * t
| DefChannel of Id.t list * tyspec list
| DefDatatype of Id.t * (Id.t * tyspec list) list
| DefNametype of Id.t * tyspec

type command =
  SetProp of pos * string * int
| Print of pos * t
| Test of pos * t
| CheckTrace of t list

type parse_result = {
    def_list : definition list;
    assertion_list : assertion list;
    command_list : command list;
  }

let rec show e =
  match e with
    Bool b -> if b then "true" else "false"
  | Int k -> sprintf "%d" k
  | Var n -> Id.show n
  | Univ _ -> "univ"
  | Tuple xs -> sprintf "(tuple %s)" (show_list xs)
  | Set xs -> sprintf "(set %s)" (show_list xs)
  | List xs -> sprintf "(list %s)" (show_list xs)
  | SetRange (x, y) -> sprintf "(set-range %s %s)" (show x) (show y)
  | ListRange (x, y) -> sprintf "(list-range %s %s)" (show x) (show y)
  | Chset xs ->
     sprintf "(chset %s)"
       (Utils.cons_str_list (fun (x, rt) -> show x) xs)
  | Chmap m ->
     sprintf "(chmap %s)"
       (Utils.cons_str_list
          (fun ((a, _), (b, _)) -> sprintf "(%s, %s)" (show a) (show b))
          m)
  | And xs -> sprintf "(and %s)" (show_list xs)
  | Or xs -> sprintf "(or %s)" (show_list xs)
  | If (test, x, y) -> sprintf "(if %s %s %s)" (show test) (show x) (show y)
  | Let (bs, e) ->
     let s =
       List.fold_left
         (fun s (xs, e) ->
           sprintf "%s ((%s) %s)"
             s
             (Id.show_list (List.map (fun (x, t) -> x) xs))
             (show e))
         "" bs
     in
     sprintf "(let (%s) %s" s (show e)
  | Case (e, rn, bs) ->
     let s =
       List.fold_left
         (fun s (ctor, (xs, e)) ->
           sprintf "%s ((%s %s) %s)"
             s (Id.show ctor) (Id.show_list xs) (show e))
         "" bs
     in
     sprintf "(case %s %s)" (show e) s
  | Stop -> "STOP"
  | Skip -> "SKIP"
  | Spon p -> sprintf "(tau %s)" (show p)
  | Prefix (e, p) -> sprintf "(! %s %s)" (show e) (show p)
  | Receive (ch, rt, xs, g, p) ->
     sprintf "(? %s (%s) %s %s)" (show ch) (Id.show_list xs) (show g) (show p)
  | Branch ps -> sprintf "(branch %s)" (show_list ps)
  | Alt ps -> sprintf "(alt %s)" (show_list ps)
  | Amb ps -> sprintf "(amb %s)" (show_list ps)
  | Seq ps -> sprintf "(seq %s)" (show_list ps)
  | Par (a, ps) ->
     sprintf "(par %s %s)" (show a) (show_list ps)
  | Hide (a, p) ->
     sprintf "(hide %s %s)" (show a) (show p)
  | Rename (m, p) ->
     sprintf "(rename %s %s)" (show m) (show p)
  | XAlt (x, r, rt, p) ->
     sprintf "(xalt %s %s %s)" (Id.show x) (show r) (show p)
  | XAmb (x, r, rt, p) ->
     sprintf "(xamb %s %s %s)" (Id.show x) (show r) (show p)
  | XSeq (x, r, rt, p) ->
     sprintf "(xseq %s %s %s)" (Id.show x) (show r) (show p)
  | XPar (x, r, rt, a, p) ->
     sprintf "(xpar %s %s %s %s)" (Id.show x) (show r) (show a) (show p)
  | Apply (f, rt_f, ets) ->
     sprintf "(%s %s)" (show f)
       (Utils.cons_str_list
          (fun (e, t) -> show e)
          ets)
  | Fun (xts, e, rt) ->
     sprintf "(fun (%s) %s)"
       (Utils.cons_str_list
          (fun (x, _, _) -> Id.show x)
          xts)
       (show e)
  | Pos (_, e) -> show e

and show_list xs =
  List.fold_left
    (fun s x -> sprintf "%s %s" s (show x))
    "" xs

and show_tyspec t =
  match t with
    TApp (tc, ts) ->
    sprintf "TApp (%s, %s)" (show_tyctor tc) (show_tyspec_list ts)

and show_tyctor tc =
  match tc with
    TcBool -> "bool"
  | TcInt ropt ->
     (match ropt with
        None -> "int"
      | Some (a, b) ->
         sprintf "(%s)..(%s)" (show a) (show b))
  | TcTuple -> "tuple"
  | TcSet -> "set"
  | TcList -> "list"
  | TcEvent -> "event"
  | TcFun -> "fun"
  | TcName n -> Id.show n

and show_tyspec_list ts =
  List.fold_left
    (fun s t -> sprintf "%s %s" s (show_tyspec t))
  "" ts

and show_assertion a =
  match a with
    Deadlock p ->
     sprintf "deadlock %s" (Id.show p)
  | Divergence p ->
     sprintf "divergence %s" (Id.show p)
  | Traces (p, q) ->
     sprintf "traces %s %s" (Id.show p) (Id.show q)
  | Failures (p, q) ->
     sprintf "failures %s %s" (Id.show p) (Id.show q)

and show_elem e =
  match e with
    Def (n, e) ->
     sprintf "Def (%s, %s)" (Id.show n) (show e)
  | DefChannel (ns, ts) ->
     sprintf "DefChannel ([%s], [%s])"
       (Id.show_list ns) (show_tyspec_list ts)
  | DefDatatype (n, cs) ->
     let s =
       List.fold_left
         (fun s (ctor, tyspec_opt) ->
           sprintf "%s %s" s (Id.show ctor))
         "" cs
     in
     sprintf "DefDatatype (%s, %s)" (Id.show n) s
  | DefNametype (n, _) ->
     sprintf "DefNametype (%s, _)" (Id.show n)

let make_tuple es =
  match es with
    [e] -> e
  | _ -> Tuple es
