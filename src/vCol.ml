module VSet =
  struct
    module X =
      Set.Make
        (struct
          type t = V.t
          let compare = compare
        end)
    include X
  end
