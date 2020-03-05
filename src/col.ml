open Printf

exception ColError of string

module List =
  struct
    include List

    let iteri2 f xs ys =
      let rec loop i xs ys =
        match xs, ys with
          x::xs', y::ys' ->
          f i x y; loop (i+1) xs' ys'
        | _, _ -> ()
      in loop 0 xs ys

    let fold_lefti f acc xs =
      let rec fold acc k xs =
        match xs with
          [] -> acc
        | x::xs -> fold (f acc k x) (k+1) xs
      in fold acc 0 xs

    let fold_left_map f acc tail xs =
      let rec g acc rs = function
          [] -> (acc, rev rs)
        | x::xs ->
           let (acc, y) = f acc x in
           g acc (y::rs) xs
      in g acc tail xs

    let find_index_opt pred xs =
      let rec loop i xs =
        match xs with
          [] -> None
        | x::xs' ->
           if pred x then Some i else loop (i+1) xs'
      in loop 0 xs

    let find_index pred xs =
      match find_index_opt pred xs with
        Some i -> i
      | None -> raise Not_found

    let assoc_index key alist =
      let rec loop i alist =
        match alist with
          [] -> raise Not_found
        | (k, v)::alist' ->
           if k=key then
             i
           else
             loop (i+1) alist'
      in loop 0 alist

    let rec member eq x xs =
      match xs with
        [] -> false
      | x'::xs' -> eq x x' || member eq x xs'

    let last xs =
      match xs with
        [] -> raise (ColError "last")
      | x::xs ->
         let rec f x = function
             [] -> x
           | x'::xs -> f x' xs
         in f x xs

    let butlast xs =
      match xs with
        [] -> raise (ColError "butlast")
      | x::xs ->
         let rec f rs x = function
             [] -> List.rev rs
           | x'::xs -> f (x::rs) x' xs
         in f [] x xs

    let take xs n =
      let rec f k xs rs =
        if k = n then
          List.rev rs
        else
          match xs with
            [] -> raise (ColError "take: out of range")
          | x::xs' -> f (k+1) xs' (x::rs)
      in
      if n < 0 then
        raise (ColError "take: out of range")
      else
        f 0 xs []

    let rec drop xs n =
      let rec f xs n =
        if n = 0 then
          xs
        else
          match xs with
            [] -> raise (ColError "drop: out of range")
          | x::xs' -> drop xs' (n-1)
      in
      if n < 0 then
        raise (ColError "drop: out of range")
      else
        f xs n

    let rec update xs k x =
      if xs=[] then
        raise (ColError "list_update: index out of range")
      else
        if k=0 then
          x::(List.tl xs)
        else
          (List.hd xs)::(update (List.tl xs) (k-1) x)

    let remove1 x xs =
      let rec f rs = function
          [] -> raise (ColError "list_remove1: not found")
        | y::ys -> if x = y then
                     List.rev_append rs ys
                   else
                     f (y::rs) ys
      in
      f [] xs

    let remove x xs =
      let rec loop rs xs =
        match xs with
          [] -> List.rev rs
        | y::ys' ->
           if x = y then
             loop rs ys'
           else
             loop (y::rs) ys'
      in
      loop [] xs

    let insert xs k x =
      let rec f k rs xs =
        if k = 0 then
          List.rev_append rs (x::xs)
        else
          match xs with
            [] -> raise (ColError "list_insert: index out of range")
          | y::ys -> f (k-1) (y::rs) ys
      in
      if k < 0 then
        raise (ColError "list_insert: index out of range")
      else
        f k [] xs

    let remove_index xs k =
      let rec f k rs = function
          [] -> raise (ColError "list_remove_index: index out of range")
        | x::xs ->
           if k = 0 then
             List.rev_append rs xs
           else
             f (k-1) (x::rs) xs
      in
      if k < 0 then
        raise (ColError "list_remove_index: index out of range")
      else
        f k [] xs

  end

module IntSet =
  struct
    module X =
      Set.Make
        (struct
          type t = int
          let compare = compare
        end)
    include X

    let hash s = fold (+) s 0
  end

module IntMap =
  struct
    module X =
      Map.Make
        (struct
          type t = int
          let compare = compare
        end)
    include X

    let find key map =
      match find_opt key map with
        Some v -> v
      | None -> Error.error (sprintf "IntMap: unknown key: %d" key)

    let find_with_default key map default =
      match find_opt key map with
        Some v -> v
      | None -> default
  end
