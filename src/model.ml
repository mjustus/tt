type level = int

type _ t_nf =
  | Dwn : 'a t * 'a t -> 'a t_nf
and _ t =
  | Unv : level -> 'a t
  | Fun : 'a t * 'a t_cl -> 'a t
  | Val : 'a t_vl -> 'a t
and _ t_vl =
  | Lam : 'a t_cl -> 'a t_vl
  | Up  : 'a t * 'a t_ne -> 'a t_vl
and _ t_ne =
  | Var : 'a Var.t -> 'a t_ne
  | App : 'a t_ne * 'a t_nf -> 'a t_ne
and ('a, 'b) s =
  | Empty : (Tag.z, 'b) s
  | Comma : ('a, 'b) s * 'b t -> ('a Tag.v, 'b) s
and _ t_cl = Cls : ('a, 'b) s * Binder.t_opt * ('a Tag.v) Term.t -> 'b t_cl

module Bidirectional = struct
  type _ t_nf =
    | Chk : 'a t * 'a t -> 'a t_nf
  and _ t_infer =
    | Unv : level -> 'a t_infer
    | Fun : 'a t_infer * 'a t_cl -> 'a t_infer
    | Neu : 'a t_ne -> 'a t_infer
  and _ t_check =
    | Lam : 'a t_cl -> 'a t_check
    | Inf : 'a t_infer -> 'a t_check
  and _ t_ne =
    | Var : 'a Var.t -> 'a t_ne
    | App : 'a t_ne * 'a t_check -> 'a t_ne
  and ('a, 'b) s =
    | Empty : (Tag.z, 'b) s
    | Comma : ('a, 'b) s * 'b t -> ('a Tag.v, 'b) s
  and _ t_cl = Cls : ('a, 'b) s * Binder.t_opt * ('a Tag.v) Term.t -> 'b t_cl
end
           
let rec lookup : type a b. a Var.t -> (a, b) s -> b t = fun v s ->
  match v, s with
  | _      , Empty        -> .
  | Var.Z  , Comma (_, t) -> t
  | Var.V v, Comma (s, _) -> lookup v s

type file = Tag.z t File.t

let comma : type a b. (a, b) s -> b t -> (a Tag.v, b) s = fun s t -> Comma (s, t)
      
let mk_dwn : type a. a t -> a t -> a t_nf = fun t t' -> Dwn (t, t')
let mk_val : type a. a t_vl -> a t = fun t -> Val t
let mk_unv : type a. level -> a t = fun l -> Unv l
let mk_pi  : type a. a t -> a t_cl -> a t = fun t t' -> Fun (t, t')
let mk_lam : type a. a t_cl -> a t_vl = fun t -> Lam t
let mk_cls : type a b. (a, b) s -> Binder.t_opt -> (a Tag.v) Term.t -> b t_cl = fun s x t -> Cls (s, x, t)
let mk_up  : type a. a t -> a t_ne -> a t_vl = fun t t' -> Up (t, t')
let mk_var : type a. a Var.t -> a t_ne = fun v -> Var v
let mk_app : type a. a t_ne -> a t_nf -> a t_ne = fun t t' -> App (t, t')

let unv_syn : type a. a t = Unv (-1)
                          
let rec wk : type a b. (a, b) Weaken.t -> b t -> a t = fun w t ->
  match t with
  | Unv l       -> Unv l
  | Fun (t, t') -> Fun (wk w t, wk_cl w t')
  | Val t       -> Val (wk_vl w t)
and wk_vl : type a b. (a, b) Weaken.t -> b t_vl -> a t_vl = fun w t ->
  match t with
  | Lam t       -> Lam (wk_cl w t)
  | Up  (t, t') -> Up (wk w t, wk_ne w t')
and wk_ne : type a b. (a, b) Weaken.t -> b t_ne -> a t_ne = fun w t ->
  match t with
  | Var v       -> Var (Var.wk w v)
  | App (t, t') -> App (wk_ne w t, wk_nf w t')
and wk_nf : type a b. (a, b) Weaken.t -> b t_nf -> a t_nf = fun w t ->
  match t with
  | Dwn (t, t') -> Dwn (wk w t, wk w t')
and wk_s : type a b c. (a, b) Weaken.t -> (c, b) s -> (c, a) s = fun w t ->
  match t with
  | Empty        -> Empty
  | Comma (s, t) -> Comma (wk_s w s, wk w t)
and wk_cl : type a b. (a, b) Weaken.t -> b t_cl -> a t_cl = fun w (Cls (s, x, t)) ->
  Cls (wk_s w s, x, t)
                  
(*
let rec wkv_s : Var.t -> s -> s = fun v ->
  Context.map (wkv v)
and wkv_nf : Var.t -> t_nf -> t_nf = fun n t ->
  match t with
  | Dwn (t, t') -> Dwn (wkv n t, wkv n t')
and wkv_ne : Var.t -> t_ne -> t_ne = fun v t ->
  match t with
  | Var v'                    -> Var (Var.wkv v v')
  | App (t, t')               -> App (wkv_ne v t, wkv_nf v t')
and wkv : Var.t -> t -> t = fun v t ->
  match t with
  | Unv _       -> t
  | Fun (t, t') -> Fun (wkv v t, wkv v t')
  | Val t       -> Val (wkv_vl v t)
and wkv_vl : Var.t -> t_vl -> t_vl = fun v t ->
  match t with
  | Cls (x, t, s )        -> Cls (x, t, wkv_s v s)
  | Up  (t, t')           -> Up  (wkv v t, wkv_ne v t')
*)

let rec lift : type a b c. (a, b, c) Tag.Addition.t -> b t -> c t = fun a t ->
  match t with
  | Unv l       -> Unv l
  | Fun (t, t') -> Fun (lift a t, lift_cl a t')
  | Val t       -> Val (lift_vl a t)
and lift_vl : type a b c. (a, b, c) Tag.Addition.t -> b t_vl -> c t_vl = fun a t ->
  match t with
  | Lam t       -> Lam (lift_cl a t)
  | Up  (t, t') -> Up (lift a t, lift_ne a t')
and lift_ne : type a b c. (a, b, c) Tag.Addition.t -> b t_ne -> c t_ne = fun a t ->
  match t with
  | Var v       -> Var (Var.lift a v)
  | App (t, t') -> App (lift_ne a t, lift_nf a t')
and lift_nf : type a b c. (a, b, c) Tag.Addition.t -> b t_nf -> c t_nf = fun a t ->
  match t with
  | Dwn (t, t') -> Dwn (lift a t, lift a t')
and lift_s : type a b b' c. (a, b, c) Tag.Addition.t -> (b', b) s -> (b', c) s = fun a s ->
  match s with
  | Empty        -> Empty
  | Comma (s, t) -> Comma (lift_s a s, lift a t)
and lift_cl : type a b c. (a, b, c) Tag.Addition.t -> b t_cl -> c t_cl = fun a (Cls (r, x, t)) ->
  Cls (lift_s a r, x, t)
  
let lift_z : type a. Tag.z t -> a t = fun t ->
  lift Tag.Addition.Z t


let bound : type a. a t -> Binder.t_opt = function
  | Val (Lam (Cls (_, x, _))) -> x
  | _ -> None
