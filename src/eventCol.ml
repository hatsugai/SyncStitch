open Printf

module EventSet =
  struct
    module X =
      Set.Make (
          struct
            type t = Event.t
            let compare = compare
          end)
    include X

    let hash s = fold (fun x acc -> acc + Hashtbl.hash x) s 0

    let show s =
      let str =
        fold
          (fun u str ->
            if str="" then
              Event.show u
            else
              sprintf "%s,%s" str (Event.show u))
          s ""
      in "{" ^ str ^ "}"
  end

module EventMap =
  struct
    module X =
      Map.Make (
          struct
            type t = Event.t
            let compare = compare
          end)
    include X

    let hash m =
      fold
        (fun e s acc ->
          acc + Hashtbl.hash e + Hashtbl.hash s)
        m 0

  end

module EventSetSet =
  struct
    module X =
      Set.Make
        (struct
          type t = EventSet.t
          let compare = compare
        end)
    include X

    let show ss =
      let str =
        fold
          (fun s str ->
            if str="" then
              EventSet.show s
            else
              sprintf "%s, %s" str (EventSet.show s))
          ss ""
      in "{ " ^ str ^ " }"

  end

module EventPairSet =
  struct
    module X =
      Set.Make (
          struct
            type t = Event.t * Event.t
            let compare = compare
          end)
    include X

    let show s =
      let str =
        fold
          (fun (a, b) str ->
            if str="" then
              sprintf "(%s, %s)" (Event.show a) (Event.show b)
            else
              sprintf "%s, (%s, %s)" str (Event.show a) (Event.show b))
          s ""
      in "{" ^ str ^ "}"
  end
