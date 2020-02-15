include Var_base

let v : type a. a t -> (a Tag.v) t = fun t -> V t

let rec count : type a. a t -> int = function
  | Z   -> 0
  | V t -> count t + 1

let rec wk : type a b. (a, b) Weaken.t -> b t -> a t = fun w v ->
  match w, v with
  (*
  | Weaken.E  , _   -> .
  *)
  | Weaken.I  , _   -> v
  | Weaken.V _, Z   -> Z
  | Weaken.V w, V v -> V (wk w v)
  | Weaken.W w, _   -> V (wk w v)

let rec lift : type a b c. (a, b, c) Tag.Addition.t -> b t -> c t = fun a t ->
  match t, a with
  | Z  , Tag.Addition.V _ -> Z
  | V t, Tag.Addition.V a -> V (lift a t)
