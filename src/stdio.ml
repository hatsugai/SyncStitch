let standard_input () = stdin
let standard_output () = stdout
let standard_error () = stderr

let open_in_opt path =
  try
    Some (open_in path)
  with
    _ -> None

let open_out_opt path =
  try
    Some (open_out path)
  with
    _ -> None

let input_char_opt ch =
  try
    Some (input_char ch)
  with
    End_of_file -> None
