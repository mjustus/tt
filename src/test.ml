type flag = Success | Failure of Failure_code.t

let validate : flag -> Term.file -> unit = fun f t ->
  let success =
    match f with
    | Success   -> fun () -> print_endline "Success!"
    | Failure _ -> fun () -> failwith "Expected failure but type checking was successful."
  in
  let failure =
    match f with
    | Success   -> fun e -> failwith ("Type checking failed: " ^ Failure.to_string e)
    | Failure c -> fun e -> if c = Failure.to_code e then
                                   print_endline "Failure as expected"
                                 else
                                   failwith ("Type checking failed for the wrong reason. Expected " ^ Failure_code.to_string c ^ " but got " ^ Failure.to_string e ^ " instead.")
  in 
  Check.E.catch_map (Check.check_file t Check.Env.init)
    success
    failure
