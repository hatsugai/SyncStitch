open Error
open Col
open V
open Spec

let lognot apply xs =
  match xs with
    [Bool b] -> Bool (not b)
  | _ -> Undefined

let rec eq x y =
  match x, y with
    Set xs, Set ys ->
     ListSet.subset eq xs ys && ListSet.subset eq ys xs
  | List xs, List ys ->
     List.length xs = List.length ys
     && List.for_all2 eq xs ys
  | Tuple xs, Tuple ys ->
     List.length xs = List.length ys
     && List.for_all2 eq xs ys
  | Variant (cx, xs), Variant (cy, ys) ->
     cx = cy && (List.for_all2 eq xs ys)
  | Event (cx, xs), Event (cy, ys) ->
     cx = cy && (List.for_all2 eq xs ys)
  | _, _ -> x = y

let equal apply xs =
  match xs with
    [x; y] -> Bool (eq x y)
  | _ -> Undefined

let noteq apply xs =
  match xs with
    [x; y] -> Bool (not (eq x y))
  | _ -> Undefined

let lt apply xs =
  match xs with
    [Int x; Int y] -> Bool (x < y)
  | _ -> Undefined

let gt apply xs =
  match xs with
    [Int x; Int y] -> Bool (x > y)
  | _ -> Undefined

let le apply xs =
  match xs with
    [Int x; Int y] -> Bool (x <= y)
  | _ -> Undefined

let ge apply xs =
  match xs with
    [Int x; Int y] -> Bool (x >= y)
  | _ -> Undefined

let neg apply xs =
  match xs with
    [Int k] -> Int (-k)
  | _ -> Undefined

let add apply xs =
  let rec f acc = function
      [] -> Int acc
    | x::xs ->
       (match x with
          Int k -> f (acc + k) xs
        | _ -> Undefined)
  in f 0 xs

let sub apply xs =
  let rec f n = function
      [] -> Int n
    | x::xs ->
       (match x with
          Int k -> f (n - k) xs
        | _ -> Undefined)
  in
  match xs with
    [] -> Undefined
  | [Int k] -> Int (-k)
  | (Int k)::xs -> f k xs
  | _ -> Undefined

let mul apply xs =
  let rec f n = function
      [] -> Int n
    | x::xs ->
       (match x with
          Int k ->
           let m = n * k in
           if m = 0 then
             Int 0
           else
             f m xs
        | _ -> Undefined)
  in f 1 xs

let div apply xs =
  match xs with
    [Int x; Int y] ->
     if y = 0 then
       error "division by 0"
     else
       Int (x / y)
  | _ -> Undefined

let modulo apply xs =
  match xs with
    [Int x; Int y] ->
     if y = 0 then
       error "division by 0"
     else
       Int (x mod y)
  | _ -> Undefined

let expt apply xs =
  let rec f z x y =
    if y = 0 then
      z
    else if y mod 2 = 0 then
      f z (x * x) (y / 2)
    else
      f (z * x) x (y - 1)
  in
  match xs with
    [Int x; Int y] ->
     if y < 0 then
       error "expr: y < 0"
     else
       Int (f 1 x y)
  | _ -> Undefined

let list_to_set apply xs =
  match xs with
    [List es] ->
     let ys =
       List.fold_left
         (fun s x ->
           if List.mem x s then
             s
           else
             x::s)
         [] es
     in Set (List.sort compare ys)
  | _ -> Undefined

let set_to_list apply xs =
  match xs with
    [Set es] -> List es
  | _ -> Undefined

let is_null apply xs =
  match xs with
    [List []] -> Bool true
  | [List _] -> Bool false
  | _ -> Undefined

let length apply xs =
  match xs with
    [List es] -> Int (List.length es)
  | _ -> Undefined

let car apply xs =
  match xs with
    [List []] -> error "car"
  | [List (e::es)] -> e
  | _ -> Undefined

let cdr apply xs =
  match xs with
    [List []] -> error "cdr"
  | [List (e::es)] -> List es
  | _ -> Undefined

let last apply xs =
  match xs with
    [List []] -> error "last"
  | [List es] -> List.last es
  | _ -> Undefined

let butlast apply xs =
  match xs with
    [List []] -> error "butlast"
  | [List es] -> List (List.butlast es)
  | _ -> Undefined

let list_ref apply xs =
  match xs with
    [List xs; Int k] ->
     if k >= 0 && k < List.length xs then
       List.nth xs k
     else
       error "ref: index out of range"
  | _ -> Undefined

let take apply xs =
  match xs with
    [List xs; Int k] ->
     if k >= 0 && k <= List.length xs then
       List (List.take xs k)
     else
       error "take: index out of range"
  | _ -> Undefined

let drop apply xs =
  match xs with
    [List xs; Int k] ->
     if k >= 0 && k <= List.length xs then
       List (List.drop xs k)
     else
       error "drop: index out of range"
  | _ -> Undefined

let cons apply xs =
  match xs with
    [x; List xs] -> List (x::xs)
  | _ -> Undefined

let append1 apply xs =
  match xs with
    [List xs; x] -> List (List.append xs [x])
  | _ -> Undefined

let append apply xs =
  match xs with
    [List xs; List ys] -> List (List.append xs ys)
  | _ -> Undefined

let update apply xs =
  match xs with
    [List xs; Int k; x] ->
     if k >= 0 && k <= List.length xs then
       List (List.update xs k x)
     else
       error "update: index out of range"
  | _ -> Undefined

let remove1 apply xs =
  match xs with
    [List xs; x] ->
     if List.mem x xs then
       List (List.remove1 x xs)
     else
       error "remove1: not found"
  | _ -> Undefined

let find_index apply xs =
  match xs with
    [List xs; x] ->
     (match List.find_index_opt (fun y -> x=y) xs with
        Some i -> Int i
      | None -> Int (-1))
  | _ -> Undefined

let insert apply xs =
  match xs with
    [List xs; Int k; x] ->
     if k >= 0 && k <= List.length xs then
       List (List.insert xs k x)
     else
       error "update: index out of range"
  | _ -> Undefined

let remove_index apply xs =
  match xs with
    [List xs; Int k] ->
     if k >= 0 && k <= List.length xs then
       List (List.remove_index xs k)
     else
       error "remove_index: index out of range"
  | _ -> Undefined

let reverse apply xs =
  match xs with
    [List xs] -> List (List.rev xs)
  | _ -> Undefined

let interval apply xs =
  match xs with
    [Int a; Int b] ->
     List (List.map (fun x -> Int x) (Utils.interval a b))
  | _ -> Undefined

let make_list apply xs =
  match xs with
    [Int n; x] ->
     if n < 0 then
       error "make_list: length < 0"
     else
       List (Utils.make_list n x)
  | _ -> Undefined

let is_empty apply xs =
  match xs with
    [Set xs] -> Bool (xs = [])
  | _ -> Undefined

let is_subset apply xs =
  match xs with
    [Set xs; Set ys] -> Bool (ListSet.subset eq xs ys)
  | _ -> Undefined

let card apply xs =
  match xs with
    [Set xs] -> Int (List.length xs)
  | _ -> Undefined

let adjoin apply xs =
  match xs with
    [Set xs; x] ->
     if List.member eq x xs then
       Set xs
     else
       Set (List.sort compare (x::xs))
  | _ -> Undefined

let union apply xs =
  match xs with
    [Set xs; Set ys] ->
     Set (List.sort compare (ListSet.union eq xs ys))
  | _ -> Undefined

let inter apply xs =
  match xs with
    [Set xs; Set ys] ->
     Set (List.sort compare (ListSet.inter eq xs ys))
  | _ -> Undefined

let diff apply xs =
  match xs with
    [Set xs; Set ys] ->
     Set (List.sort compare (ListSet.diff eq xs ys))
  | _ -> Undefined

let choice apply xs =
  match xs with
    [Set []] -> error "choice: empty set"
  | [Set (x::xs)] -> x     
  | _ -> Undefined

let list_mem apply xs =
  match xs with
    [x; List xs] -> Bool (List.mem x xs)
  | _ -> Undefined

let set_mem apply xs =
  match xs with
    [x; Set xs] -> Bool (List.mem x xs)
  | _ -> Undefined

let list_remove apply xs =
  match xs with
    [List xs; x] -> List (List.remove x xs)
  | _ -> Undefined

let set_remove apply xs =
  match xs with
    [Set xs; x] ->
     Set (List.sort compare (List.remove x xs))
  | _ -> Undefined

let set_interval apply xs =
  match xs with
    [Int a; Int b] ->
     Set (List.map (fun x -> Int x) (Utils.interval a b))
  | _ -> Undefined

let map apply xs =
  match xs with
    [f; List xs] ->
     let r = List.map (fun x -> apply f [x]) xs in
     List r
  | _ -> Undefined

let fold apply xs =
  match xs with
    [f; acc; List xs] ->
     List.fold_left
       (fun acc x -> apply f [acc; x])
       acc xs
  | _ -> Undefined
