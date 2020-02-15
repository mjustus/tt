module Make (C : Context_base.S) = struct
  module Id = Weaken_id.Make (struct type 'a t = 'a C.value end) (C)

  let p1 : type a. a C.t -> (a Tag.v, a) Weaken.t = fun c -> Weaken.W (Id.id c)
end
