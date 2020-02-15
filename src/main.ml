open Function

let tee : 'a. ('a -> unit) -> 'a -> 'a = fun f a ->
  f a; a

let guard : 'a. bool -> ('a -> unit) -> 'a -> 'a = function
  | true  -> tee
  | false -> fun _ a -> a

let print d =
  PPrint.ToChannel.pretty 1. 78 stdout d;
  print_newline ()

let to_term : Raw.file -> Term.file = fun t ->
  Error.String.catch (Term.from_raw_file t Term.Env.init) failwith

let pipeline : Cmd.Config.config -> string -> unit = fun c f ->
  let open Cmd.Config in
  Read.from_file f
  |> guard c.print.raw  (snd %> Raw.Print.print_file  %> print)
  |> Product.map2 to_term
  |> guard c.print.term (snd %> Term.Print.print_file %> print)
  |> guard c.check (Product.fold Test.validate)
  |> guard c.normal (fun (_, t) ->
    let r = Readback.norm_file (Eval.eval_file t File.Done) File.Done in
    if c.print.normal then
      print (Normal.Print.print_file r)
  )
  |> fun _ -> ()

let iter : Cmd.Config.t -> unit = fun t ->
  let open Cmd.Config in
  List.iter (pipeline t.config) t.files

let () : unit =
  match Cmdliner.Term.eval Cmd.term with
  | `Ok t ->
      let () = iter t in
      exit 0
  | _     ->
      exit 1
        
