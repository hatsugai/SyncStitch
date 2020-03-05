open Col

let subset eq xs ys =
  List.for_all (fun x -> List.member eq x ys) xs

let union eq xs ys =
  List.fold_left
    (fun zs x -> if List.member eq x zs then zs else x::zs)
    ys xs

let inter eq xs ys =
  List.fold_left
    (fun zs x -> if List.member eq x ys then x::zs else zs)
    [] xs

let diff eq xs ys =
  List.fold_left
    (fun zs x -> if List.member eq x ys then zs else x::zs)
    [] xs
