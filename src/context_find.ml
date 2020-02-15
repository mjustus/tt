module Make (F : Heq.S) (C : Context_base.S with type 'a value = 'a F.t) = struct
  let rec find : type a b. b F.t -> a C.t -> (a Var.t) Option.t = fun x t ->
    match t with
    | C.Empty                          -> Option.fail
    | C.Comma (_, y) when F.hequal x y -> Option.pure Var.Z
    | C.Comma (t, _)                   -> Option.map  Var.v (find x t)
end

module Make_option (F : Heq.S) (C : Context_base.S with type 'a value = 'a F.t option) = struct
  let rec find_option : type a b. b F.t -> a C.t -> (a Var.t) Option.t = fun x t ->
    match t with
    | C.Empty                               -> Option.fail
    | C.Comma (_, Some y) when F.hequal x y -> Option.pure Var.Z
    | C.Comma (t, _     )                   -> Option.map  Var.v (find_option x t)
end
