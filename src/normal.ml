open Function

type level = int

type _ nf =
  | Unv : level -> 'a nf
  | Fun : 'a nf * 'a bnd -> 'a nf
  | Val : 'a vl -> 'a nf
and _ vl =
  | Lam : 'a bnd -> 'a vl
  | Neu : 'a ne -> 'a vl
and _ ne =
  | Var : 'a Var.t -> 'a ne
  | App : 'a ne * 'a nf -> 'a ne
and _ bnd =
  | Bnd : Binder.t_opt * ('a Tag.v) nf -> 'a bnd

type file = Tag.z nf File.t

let mk_fun : type a. a nf -> a bnd -> a nf = fun t t' -> Fun (t, t')
let mk_val : type a. a vl -> a nf = fun t -> Val t
let mk_neu : type a. a ne -> a vl = fun t -> Neu t
let mk_lam : type a. a bnd -> a vl = fun t -> Lam t
let mk_var : type a. a Var.t -> a ne = fun v -> Var v
let mk_app : type a. a ne -> a nf -> a ne = fun t t' -> App (t, t')

let rec wk_ne : type a b. (a, b) Weaken.t -> b ne -> a ne = fun w t ->
  match t with
  | Var v       -> Var (Var.wk w v)
  | App (t, t') -> App (wk_ne w t, wk_nf w t')
and wk_vl : type a b. (a, b) Weaken.t -> b vl -> a vl = fun w t ->
  match t with
  | Lam t -> Lam (wk_bnd w t)
  | Neu t -> Neu (wk_ne w t)
and wk_nf : type a b. (a, b) Weaken.t -> b nf -> a nf = fun w t ->
  match t with
  | Unv l       -> Unv l
  | Fun (t, t') -> Fun (wk_nf w t, wk_bnd w t')
  | Val t       -> Val (wk_vl w t)
and wk_bnd : type a b. (a, b) Weaken.t -> b bnd -> a bnd = fun w (Bnd (x, t)) ->
  Bnd (x, wk_nf (Weaken.V w) t)

let rec to_term_nf : type a. a nf -> a Term.t = function
  | Unv l       -> Term.Unv l
  | Fun (t, t') -> Term.Fun  (to_term_nf t, to_term_bnd t')
  | Val t       -> to_term_vl t
and to_term_vl : type a. a vl -> a Term.t = function
  | Lam t -> Term.Lam (to_term_bnd t)
  | Neu t -> to_term_ne t
and to_term_ne : type a. a ne -> a Term.t = function
  | Var v       -> Term.Var v
  | App (t, t') -> Term.App (to_term_ne t, to_term_nf t')
and to_term_bnd : type a. a bnd -> a Term.t_bnd = function
  | Bnd (x, t) -> Term.Bnd (x, to_term_nf t)
  
let rec to_term_file : file -> Term.file = fun f ->
  match f with
  | File.Defn (f, x, t, t') -> File.Defn (to_term_file f, x, to_term_nf t, to_term_nf t')
  | File.Done               -> File.Done

module Print = struct  
  let print : Tag.z nf -> PPrint.document =
    Term.Print.print % to_term_nf
  let print_file : file -> PPrint.document =
    Term.Print.print_file % to_term_file
end
