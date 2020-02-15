module type S = sig
  type 'a value
  type _ t =
    | Empty : Tag.z t
    | Comma : 'a t * 'a value -> ('a Tag.v) t

  val empty : Tag.z t
  val comma : 'a t -> 'a value -> ('a Tag.v) t
end
   
module Make (A : Type.TYPE1) : S with type 'a value = 'a A.t = struct
  type 'a value = 'a A.t
  
  type _ t =
    | Empty : Tag.z t
    | Comma : 'a t * 'a A.t -> ('a Tag.v) t

  let empty : Tag.z t = Empty
  let comma : 'a. 'a t -> 'a A.t -> ('a Tag.v) t = fun t x -> Comma (t, x)
end
