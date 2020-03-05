open IdCol
open TCol

let command mdb command_list =
  let rec do_command c =
    match c with
      S.Print (pos, x) ->
       Error.with_pos pos
         (fun () ->
           let (s_m, t) = Type.find_type mdb TVarMap.empty IdMap.empty x in
           Type.resolve_tv s_m x;
           let e = E.convert mdb x in
           let v = Eval.eval mdb V.env0 e in
           Printf.printf "print %s => %s\n" (E.desc e) (V.show v))
    | S.Test (pos, x) ->
       Error.with_pos pos
         (fun () ->
           let (s_m, t) = Type.find_type mdb TVarMap.empty IdMap.empty x in
           let s_m = Type.unify s_m t T.bool in
           Type.resolve_tv s_m x;
           let e = E.convert mdb x in
           let v = Eval.eval mdb V.env0 e in
           if v = V.Bool true then
             Printf.printf "test ok: %s\n" (E.desc e)
           else
             Error.error_s "test failed: " (E.desc e))
    | _ -> ()
  in
  List.iter do_command command_list
