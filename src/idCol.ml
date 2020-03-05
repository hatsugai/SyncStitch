open Printf

module IdSet =
  struct
    module X =
      Set.Make (
          struct
            type t = Id.t
            let compare = compare
          end)
    include X

    let add_list xs s =
      List.fold_left
        (fun s x -> add x s)
        s xs

    let remove_list xs s =
      List.fold_left
        (fun s x -> remove x s)
        s xs

end

module IdMap =
  struct
    module X =
      Map.Make (
          struct
            type t = Id.t
            let compare = compare
          end)
    include X

    let find key map =
      match find_opt key map with
        Some v -> v
      | None -> Error.error_s "IdMap: unknown key: " (Id.show key)

    let find_with_default key map default =
      match find_opt key map with
        Some v -> v
      | None -> default
  end
