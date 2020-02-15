type    z = Z
type 'a v = V of 'a

module Addition = struct
  type ('a, 'b, 'c) t =
    | Z : ('a, z, 'a) t
    | V : ('a, 'b, 'c) t -> ('a, 'b v, 'c v) t
end

