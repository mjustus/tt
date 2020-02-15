type (_, _) t =
  (*
  | E : (Tag.z, Tag.z) t
  *)  
  | I : ('a, 'a) t
  | V : ('a, 'b) t -> ('a Tag.v, 'b Tag.v) t
  | W : ('a, 'b) t -> ('a Tag.v, 'b      ) t

let rec compose : type a b c. (b, c) t -> (a, b) t -> (a, c) t = fun w w' ->
  match w,  w' with
  (*
  | E  , _    -> w'
  *)
  | I  , _    -> w'
  | _  , I    -> w
  | V w, V w' -> V (compose w w')
  | W w, V w' -> W (compose w w')
  | _  , W w' -> W (compose w w')

let p1 : 'a. ('a Tag.v, 'a) t = W I
                   
(*
let rec shift : type a b. (a, b) t -> (a Tag.v, b) t = function
  | V w -> W w
  | W w -> W (shift w)
*)

(*
let rec id : type a. (a, 'a) Context_base.t -> (a, a) t = function
  | Context_base.Empty        -> E
  | Context_base.Comma (c, _) -> V (id c)

*)
