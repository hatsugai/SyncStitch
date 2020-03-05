module ConfigHashtbl =
  Hashtbl.Make (
      struct
        type t = C.t
        let equal = C.equal
        let hash = C.hash
      end)
