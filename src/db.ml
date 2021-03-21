let tr msg =
  if !Option.debug then
    Printf.printf "%s\n" msg

let tr_s msg s =
  if !Option.debug then
    Printf.printf "%s %s\n" msg s

let tr_ss msg s s2 =
  if !Option.debug then
    Printf.printf "%s %s %s\n" msg s s2

let tr_d msg k =
  if !Option.debug then
    Printf.printf "%s %d\n" msg k

let str msg k =
  if !Option.debug then
    Printf.printf "%s[%d]\n" msg k

let str_s msg k s =
  if !Option.debug then
    Printf.printf "%s[%d] %s\n" msg k s

let pr msg =
  Printf.printf "%s\n" msg

let pr_s msg s =
  Printf.printf "%s %s\n" msg s

let pr_ss msg s s2 =
  Printf.printf "%s %s %s\n" msg s s2

let pr_d msg k =
  Printf.printf "%s %d\n" msg k

