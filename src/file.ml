type 'a t =
  | Defn of 'a t * Binder.t_opt * 'a * 'a
  | Done

let mk_defn : 'a. Binder.t_opt -> 'a -> 'a -> 'a t -> 'a t = fun x t t' f ->
  Defn (f, x, t, t')

let rec lookup : 'a. Binder.t -> 'a t -> ('a * 'a) Option.t = fun x f ->
  match f with
  | Defn (_, Some y, t, t') when x = y -> Option.pure @@ (t , t')
  | Defn (f, _     , _, _ )            -> lookup x f
  | Done                               -> Option.fail

let rec bound : 'a. ('a -> Set_string.t) -> 'a t -> Set_string.t = fun b f ->
  match f with
  | Defn (f, o, t, t') ->
      Option.fold
        Set_string.add
        (fun () -> Function.id) o
        (Set_string.union (b t) (Set_string.union (b t') (bound b f)))
  | Done -> Set_string.empty

let unit : 'a t = Done

let rec mult : 'a. 'a t -> 'a t -> 'a t = fun f f' ->
  match f with
  | Defn (f, x, t, t') -> Defn (mult f f', x, t, t')
  | Done -> f'
