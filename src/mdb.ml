open Printf
open Error
open Col
open IdCol
open Spec

type t = {
    model_filename : string;
    id_to_type : (Id.t, T.t) Hashtbl.t;
    id_to_type_alias : (Id.t, T.t) Hashtbl.t;
    id_to_variant_spec : (Id.t, variant_spec) Hashtbl.t;
    ctor_to_variant_spec : (Id.t, variant_spec) Hashtbl.t;
    id_to_channel_spec : (Id.t, channel_spec) Hashtbl.t;
    id_to_process_spec : (Id.t, process_spec) Hashtbl.t;
    id_to_fun_spec : (Id.t, fun_spec) Hashtbl.t;
    id_to_builtin_fun_spec : (Id.t, builtin_fun_spec) Hashtbl.t;
    id_to_value : (Id.t, V.t) Hashtbl.t;

    int_inf : int;
    int_sup : int;
    list_max_length : int;

    mutable next_id : int;
    mutable alphabet : V.t list;
  }

let g_mdb_opt = ref (None : t option)

let show mdb =
  printf "* mdb\n";
  printf "model_filename = %s\n" mdb.model_filename;
  printf "** id_to_type_alias\n";
  Hashtbl.iter
    (fun n t -> printf "%s %s\n" (Id.show n) (T.show t))
    mdb.id_to_type_alias;
  printf "** id_to_variant_spec\n";
  Hashtbl.iter
    (fun n vspec -> printf "%s\n" (Id.show n))
    mdb.id_to_variant_spec;
  printf "--- id_to_type ------\n";
  Hashtbl.iter
    (fun n t -> printf "%s : %s\n" (Id.show n) (T.show t))
    mdb.id_to_type;
  printf "--- id_to_process_spec ------\n";
  Hashtbl.iter
    (fun n pspec ->
      printf "%s(%s)=%s\n" (Id.show n)
        (Id.show_list pspec.process_param_list)
        (P.show pspec.process_expr))
    mdb.id_to_process_spec;
  printf "--- id_to_fun_spec ------\n";
  Hashtbl.iter
    (fun n pspec ->
      printf "%s\n" (Id.show n))
    mdb.id_to_fun_spec;
  printf "--- id_to_value ------\n";
  Hashtbl.iter
    (fun n v ->
      printf "%s = %s\n" (Id.show n) (V.show v))
    mdb.id_to_value;
  printf "--- id_to_channel_spec ------\n";
  Hashtbl.iter
    (fun n ch_spec ->
      printf "%s @ {" (Id.show n);
      List.iter
        (fun vs -> printf " {%s}" (V.show_list vs))
        ch_spec.channel_domain;
      printf "}\n")
    mdb.id_to_channel_spec;
  printf "--- ctor_to_variant_spec ------\n";
  Hashtbl.iter
    (fun ctor vspec -> printf "%s\n" (Id.show ctor))
    mdb.ctor_to_variant_spec

let get_prop_with_default command_list key default =
  let rec loop command_list =
    match command_list with
      [] -> default
    | command::command_list' ->
       (match command with
          S.SetProp (_, k, v) ->
           if k = key then
             v
           else
             loop command_list'
        | _ ->
           loop command_list')
  in loop command_list

let make_mdb model_filename command_list =
  let a = get_prop_with_default command_list "int_inf" (-3) in
  let b = get_prop_with_default command_list "int_sup" 13 in
  let maxlen = get_prop_with_default command_list "list_max_length" 7 in
  let mdb = {
      model_filename = model_filename;
      id_to_type = Hashtbl.create 0;
      id_to_type_alias = Hashtbl.create 0;
      id_to_variant_spec = Hashtbl.create 0;
      id_to_process_spec = Hashtbl.create 0;
      id_to_fun_spec = Hashtbl.create 0;
      id_to_builtin_fun_spec = Hashtbl.create 0;
      id_to_value = Hashtbl.create 0;
      id_to_channel_spec = Hashtbl.create 0;
      ctor_to_variant_spec = Hashtbl.create 0;
      next_id = 0;
      int_inf = a;
      int_sup = b;
      list_max_length = maxlen;
      alphabet = [];
    }
  in
  g_mdb_opt := Some mdb;
  mdb

let reg_bf_spec mdb bf_spec =
  Hashtbl.replace mdb.id_to_builtin_fun_spec bf_spec.bf_name bf_spec;
  Hashtbl.replace mdb.id_to_value bf_spec.bf_name (V.BuiltinFun bf_spec.bf_fun);
  Hashtbl.replace mdb.id_to_type bf_spec.bf_name bf_spec.bf_type

let get_bf_spec mdb n =
  Hashtbl.find mdb.id_to_builtin_fun_spec n

let generate_tvar mdb =
  let id = mdb.next_id in
  mdb.next_id <- id + 1;
  id

let lookup_type mdb id =
  match Hashtbl.find_opt mdb.id_to_type id with
    Some t -> t
  | None ->
     error_s "unknown id: " (Id.show id)

let reg_type mdb id t =
  if Hashtbl.mem mdb.id_to_type id then
    error_s "duplicate type: " (Id.show id)
  else
    Hashtbl.replace mdb.id_to_type id t

let reg_variant mdb n cs =
  let u = T.App (T.Name n, []) in
  let variant_spec = {
      variant_name = n;
      variant_type = u;
      ctor_spec_alist = cs;
      variant_univ = [];
    }
  in
  Hashtbl.replace mdb.id_to_variant_spec n variant_spec;
  List.iter
    (fun (n, ctor_spec) ->
      match ctor_spec.ctor_type_list with
        [] ->
         reg_type mdb n u
      | ts ->
         let t = List.fold_right T.make_fun_type ts u in
         reg_type mdb n t)
    cs;
  List.iter
    (fun (ctor, _) ->
      if Hashtbl.mem mdb.ctor_to_variant_spec ctor then
        error_s "duplicate constructor: " (Id.show ctor)
      else
        Hashtbl.replace mdb.ctor_to_variant_spec ctor variant_spec)
    cs

let reg_channel mdb n ts vss =
  let ch_spec = {
      channel_name = n;
      channel_type_list = ts;
      channel_domain = vss;
    }
  in
  Hashtbl.replace mdb.id_to_channel_spec n ch_spec;
  reg_type mdb n (T.make_channel_type ts)

let get_variant_spec_from_ctor_name mdb ctor =
  match Hashtbl.find_opt mdb.ctor_to_variant_spec ctor with
    Some vspec -> vspec
  | None -> Error.corrupt_s "get_variant_spec_from_ctor_name" (Id.show ctor)

let reg_type_alias mdb n t =
  match Hashtbl.find_opt mdb.id_to_variant_spec n with
    None ->
     (match Hashtbl.find_opt mdb.id_to_type_alias n with
        None ->
         Hashtbl.replace mdb.id_to_type_alias n t
      | Some _ ->
         error_s "duplicate nametype: " (Id.show n))
  | Some _ ->
     error_s "duplicate nametype: " (Id.show n)

let get_type_def mdb n =
  match Hashtbl.find_opt mdb.id_to_variant_spec n with
    None ->
     (match Hashtbl.find_opt mdb.id_to_type_alias n with
        None ->
         error_s "unknown type name: " (Id.show n)
      | Some t -> t)
  | Some vspec -> vspec.variant_type

let reg_process mdb n process_spec =
  Hashtbl.replace mdb.id_to_process_spec n process_spec

let lookup_process mdb n =
  match Hashtbl.find_opt mdb.id_to_process_spec n with
    Some pspec -> pspec
  | None ->
     error_s "process not found: " (Id.show n)

let reg_fun mdb n fun_spec =
  Hashtbl.replace mdb.id_to_fun_spec n fun_spec

let lookup_fun_spec_opt mdb n =
  Hashtbl.find_opt mdb.id_to_fun_spec n

let lookup_fun_spec mdb n =
  Hashtbl.find mdb.id_to_fun_spec n

let reg_value mdb n v =
  Hashtbl.replace mdb.id_to_value n v

let lookup_global_env_opt mdb n =
  match Hashtbl.find_opt mdb.id_to_value n with
    Some v -> Some v
  | None ->
     match Hashtbl.find_opt mdb.id_to_fun_spec n with
       Some fun_spec -> Some (V.UserFun fun_spec.fun_name)
     | None ->
        match Hashtbl.find_opt mdb.ctor_to_variant_spec n with
          Some variant_spec ->
           let ctor_spec = List.assoc n variant_spec.ctor_spec_alist in
           (match ctor_spec.ctor_type_list with
              [] -> Some (V.Variant (n, []))
            | _ -> Some (V.Ctor n))
        | None ->
           match Hashtbl.find_opt mdb.id_to_channel_spec n with
             Some ch_spec ->
              (match ch_spec.channel_type_list with
                 [] -> Some (V.Event (n, []))
               | _ -> Some (V.Channel (n, [])))
           | None -> None

let get_channel_spec mdb ch =
  Hashtbl.find mdb.id_to_channel_spec ch

let channel_domain mdb ch =
  match Hashtbl.find_opt mdb.id_to_channel_spec ch with
    Some ch_spec -> ch_spec.channel_domain
  | None -> error_s "channel_domain: unknown channel: " (Id.show ch)

let channel_event_fold mdb ch vs acc f =
  let dom = channel_domain mdb ch in
  List.fold_left
    (fun acc us ->
      if Utils.is_prefix vs us then
        f acc us
      else
        acc)
    acc dom

let get_model_filename mdb =
  mdb.model_filename

let get_variant_spec mdb n =
  match Hashtbl.find_opt mdb.id_to_variant_spec n with
    Some variant_spec -> variant_spec
  | None -> error_s "unknown datatype: " (Id.show n)

let get_int_range mdb =
  (mdb.int_inf, mdb.int_sup)

let get_list_max_length mdb = mdb.list_max_length

let reg_alphabet mdb alphabet =
  mdb.alphabet <- alphabet

let get_alphabet mdb = mdb.alphabet

let is_channel mdb n =
  Hashtbl.mem mdb.id_to_channel_spec n

let iter_variant_spec mdb f =
  Hashtbl.iter
    (fun _ vspec -> f vspec)
    mdb.id_to_variant_spec

let lookup_user_defined_function_opt mdb f =
  Hashtbl.find_opt mdb.id_to_fun_spec f

let fold_channel_spec mdb acc f =
  Hashtbl.fold
    (fun n ch_spec acc -> f acc ch_spec)
    mdb.id_to_channel_spec acc

let iter_process_spec mdb f =
  Hashtbl.iter (fun _ spec -> f spec) mdb.id_to_process_spec

let iter_fun_spec mdb f =
  Hashtbl.iter
    (fun _ spec -> f spec)
    mdb.id_to_fun_spec