type _ t =
  | Z : ('a Tag.v) t
  | V : 'a t -> ('a Tag.v) t
