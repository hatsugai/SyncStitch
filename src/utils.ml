open Printf
open Error

let char_list_to_string cs =
  let n = List.length cs in
  let buf = Buffer.create n in
  List.iteri (fun i c -> Buffer.add_char buf c) cs;
  Buffer.contents buf

let string_to_char_list s =
  let rec f k cs =
    if k = 0 then
      cs
    else
      f (k-1) ((String.get s (k-1))::cs)
  in
  f (String.length s) []

(* path => (dir, fname, ext) *)
let splitpath path =
  let rec f rs = function
      [] -> ("", char_list_to_string rs, "")
    | c::cs ->
       if c = '.' then
         if rs = [] then
           g "" [] cs
         else
           g (char_list_to_string (c::rs)) [] cs
       else if c = '/' || c = '\\' || c = ':' then
         (char_list_to_string (List.rev (c::cs)), char_list_to_string rs, "")
       else
         f (c::rs) cs
  and g ext rs = function
      [] -> ("", char_list_to_string rs, ext)
    | c::cs ->
       if c = '/' || c = '\\' || c = ':' then
         (char_list_to_string (List.rev (c::cs)), char_list_to_string rs, ext)
       else
         g ext (c::rs) cs
  in
  f [] (List.rev (string_to_char_list path))

let interval_fold a b acc f =
  let rec fold acc k =
    if k >= b then
      acc
    else
      fold (f acc k) (k+1)
  in fold acc a

let normalize_path path =
  let n = String.length path in
  if n = 0 then
    ""
  else
    let c = String.get path (n - 1) in
    if c = '/' || c = '\\' then
      path
    else
      path ^ "/"

let rec interval a b =
  if a >= b then
    []
  else
    a::(interval (a+1) b)

let make_list n x =
  let rec f n acc =
    if n = 0 then acc else f (n-1) (x::acc)
  in
  if n < 0 then
    error "list_repeat: length < 0"
  else
    f n []

let rec cartesian_product = function
    [] -> [[]]
  | xs::xss ->
     let yss = cartesian_product xss in
     List.flatten
       (List.map
          (fun ys ->
            List.map
              (fun x -> x::ys)
              xs)
          yss)

let rec make_filename basename extension index =
  let fn = Printf.sprintf "%s_%d.%s" basename index extension in
  if Sys.file_exists fn then
    make_filename basename extension (index+1)
  else
    (fn, index)

let find_index v x =
  let n = Array.length v in
  let rec loop i =
    if i=n then
      error "find_index"
    else if v.(i) = x then
      i
    else
      loop (i+1)
  in loop 0

let make_comma_string f xs =
  match xs with
    [] -> ""
  | [x] -> f x
  | x::xs' ->
     List.fold_left
       (fun s x -> sprintf "%s,%s" s (f x))
       (f x) xs'

let list_sum xs =
  List.fold_left
    (fun acc x -> acc + x)
    0 xs

let expt x y =
  let rec f z x y =
    if y = 0 then
      z
    else if y mod 2 = 0 then
      f z (x * x) (y / 2)
    else
      f (z * x) x (y - 1)
  in
  f 1 x y

let take xs n =
  let rec f k xs rs =
    if k = n then
      List.rev rs
    else
      match xs with
        [] -> Error.error "take: out of range"
      | x::xs' -> f (k+1) xs' (x::rs)
  in
  if n < 0 then
    Error.error "take: out of range"
  else
    f 0 xs []

let rec drop xs n =
  let rec f xs n =
    if n = 0 then
      xs
    else
      match xs with
        [] -> Error.error "drop: out of range"
      | x::xs' -> drop xs' (n-1)
  in
  if n < 0 then
    Error.error "drop: out of range"
  else
    f xs n

let interval_map a b f =
  let rec g rs k =
    if k >= b then
      List.rev rs
    else
      g ((f k)::rs) (k + 1)
  in g [] a

let rec list_powerset = function
    [] -> [[]]
  | x::xs ->
     let s = list_powerset xs in
     List.append
       s
       (List.map (fun xs -> x::xs) s)

let cons_str_list show xs =
  List.fold_left
    (fun s x ->
      if s="" then
        show x
      else
        s ^ "," ^ (show x))
    "" xs

let rec prefix_rest xs ys =
  match xs with
    [] -> Some ys
  | x::xs' ->
     (match ys with
        [] -> None
      | y::ys' ->
         if x = y then
           prefix_rest xs' ys'
         else
           None)

let is_prefix xs ys =
  match prefix_rest xs ys with
    None -> false
  | _ -> true

let is_alpha c = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')
let is_digit c = c >= '0' && c <= '9'
let hex = "0123456789ABCDEF"

let c_name s =
  let n = String.length s in
  let buf = Buffer.create 0 in
  let rec loop k =
    if k = n then
      Bytes.to_string (Buffer.to_bytes buf)
    else
      let c = s.[k] in
      if is_alpha c || is_digit c then
        (Buffer.add_char buf c; loop (k+1))
      else
        let x = Char.code c in
        Buffer.add_char buf '_';
        Buffer.add_char buf hex.[x / 16];
        Buffer.add_char buf hex.[x mod 16];
        loop (k+1)
  in loop 0

let seq_count =
  let c = ref 0 in
  fun () -> let r = !c in c := r + 1; r

let make_c_tmp =
  let count = ref 0 in
  fun () ->
  let c = !count in
  count := c + 1;
  sprintf "tmp_xxx_%d" c

let rec interval_iter a b f =
  if a < b then
    (f a; interval_iter (a+1) b f)

let interval_fold a b acc f =
  let rec fold acc k =
    if k >= b then
      acc
    else
      fold (f acc k) (k+1)
  in fold acc a

(* ~ log_2(x) *)
let bitwidth x =
  let rec f k y =
    if x <= y then
      k
    else
      f (k + 1) (y * 2)
  in f 1 2

let make_temp_file base ext =
  if !Option.debug then
    Printf.sprintf "./%s%s" base ext
  else
    let dir = Filename.get_temp_dir_name () in
    Filename.temp_file ~temp_dir:dir base ext
