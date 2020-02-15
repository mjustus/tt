open Cmdliner

module Config = struct
  type print = {
    raw    : bool;
    term   : bool;
    normal : bool
  }

  type config = {
    print  : print;
    check  : bool;
    normal : bool;
  }

  type t = {
    config : config;
    files  : string list
  }

  type print_soup = Raw | Term | Normal
  let to_print : print_soup list -> print = fun xs -> {
    raw    = List.mem Raw    xs;
    term   = List.mem Term   xs;
    normal = List.mem Normal xs
  }

  let to_data print check normal files : t =
    {config = {print; check; normal}; files}
end
   
let print =
  let doc = "Pretty-print internal representation of the input program." in
  Arg.(value & opt (list (enum ["raw", Config.Raw; "term", Config.Term; "normal", Config.Normal])) [] & info ["p"; "print"] ~doc)

let normal =
  let enable =
    let doc = "Fully normalise." in
    true, Arg.info ["n"; "normal"] ~doc
  in
  Arg.(last & vflag_all [false] [enable])

let check =
  let disable =
    let doc = "Skip type checking." in
    false, Arg.info ["no-check"] ~doc
  in
  Arg.(last & vflag_all [true] [disable])

let files = Arg.(non_empty & pos_all file [] & info [] ~docv:"FILE")

let term =
  let doc = "A dependently typed language with name abstraction." in
  Term.(
    pure Config.to_data
    $ (pure Config.to_print $ print)
    $ check
    $ normal
    $ files
  ),
  Term.info "freshtt" ~version:"0.0.1" ~doc
