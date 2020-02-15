module type S = sig
  include Type.TYPE1

  val wk : ('a, 'b) Weaken.t -> 'b t -> 'a t
end

module Const (A : Type.TYPE0) = struct
  type 'a t = A.t
  let wk _ = Function.id
end

module Option (F : S) = struct
  type 'a t = 'a F.t option
  let wk w = Option.map (F.wk w)
end

let r : 'a Option (Const (Type.String)).t = Some "ad"
                      
module P1 (F : S) (C : Context_base.S) = struct
  module P1 = Weaken_p1.Make (C)
  
  let p1 : 'a. 'a C.t -> 'a F.t -> ('a Tag.v) F.t = fun c -> F.wk (P1.p1 c)
end
