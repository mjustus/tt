open Weaken

module Make (A : Type.TYPE1) (C : Context_base.S with type 'a value = 'a A.t) = struct
  let rec id : type a. a C.t -> (a, a) t = function
    | C.Empty        -> I
    | C.Comma (c, _) -> V (id c)
end
