open Printf

module TVarSet =
   Set.Make (
       struct
         type t = T.tvar
         let compare = compare
       end)

module TVarMap =
  struct
    module X =
      Map.Make (
          struct
            type t = T.tvar
            let compare = compare
          end)
    include X

    let find key map =
      match find_opt key map with
        Some v -> v
      | None ->
         Error.error (sprintf "TVarMap: unknown key: %d" key)

    let find_with_default key map default =
      match find_opt key map with
        Some v -> v
      | None -> default
  end

module TGenSet =
   Set.Make (
       struct
         type t = T.tgen
         let compare = compare
       end)

module TGenMap =
  struct
    module X =
      Map.Make (
          struct
            type t = T.tgen
            let compare = compare
          end)
    include X

    let find key map =
      match find_opt key map with
        Some v -> v
      | None ->
         Error.error (sprintf "TGenMap: unknown key: %d" key)

    let find_with_default key map default =
      match find_opt key map with
        Some v -> v
      | None -> default
  end
