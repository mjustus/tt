module Make (F : Presheaf.S) (Base : Context_base.S with type 'a value = 'a F.t) = struct
  module P1 = Presheaf.P1 (F) (Base)
            
  let rec lookup : type a. a Var.t -> a Base.t -> a F.t = fun v t ->
    match v, t with
    | _      , Base.Empty        -> .
    | Var.Z  , Base.Comma (t, a) -> P1.p1 t a
    | Var.V v, Base.Comma (t, _) -> P1.p1 t (lookup v t)
end
