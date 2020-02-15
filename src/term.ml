open Function

type level = int

type _ t =
  | Unv : level -> 'a t
  | Fun : 'a t * 'a t_bnd -> 'a t
  | Lam : 'a t_bnd -> 'a t
  | App : 'a t * 'a t -> 'a t
  | Var : 'a Var.t -> 'a t
  | Let : 'a t * 'a t * 'a t_bnd -> 'a t
  (* reference to a file-wide definition *)
  | Ref : Binder.t -> 'a t
  | Chk : 'a t * 'a t -> 'a t
and _ t_bnd = Bnd : Binder.t_opt * ('a Tag.v) t -> 'a t_bnd

(* Bidirectional:
type _ t_check =
  | Lam : 'a t_check_bnd -> 'a t_check
  | Let : 'a t_infer * 'a t_check_bnd -> 'a t_check
  (* reference to a file-wide definition *)
and _ t_infer =
  | Unv : level -> 'a t_infer
  | Fun : 'a t_infer * 'a t_infer_bnd -> 'a t_infer
  | Var : 'a Var.t -> 'a t_infer
  | App : 'a t_infer * 'a t_check -> 'a t_infer
  | Ref : Binder.t -> 'a t_infer
  | Chk : 'a t_infer * 'a t_check -> 'a t_infer
and _ t_check_bnd = CheckBnd : Binder.t_opt * ('a Tag.v) t_check -> 'a t_check_bnd
and _ t_infer_bnd = InferBnd : Binder.t_opt * ('a Tag.v) t_infer -> 'a t_infer_bnd
*)

(*
type file = Tag.z t File.t
*)

type file = Tag.z t File.t

let mk_let : type a. Binder.t_opt -> a t -> a t -> (a Tag.v) t -> a t = fun x t1 t1' t2 -> Let (t1, t1', Bnd (x, t2))
let mk_unv : type a. int -> a t = fun i -> Unv i
let mk_fun : type a. Binder.t_opt -> a t -> (a Tag.v) t -> a t = fun x t t' -> Fun (t, Bnd (x, t'))
let mk_lam : type a. Binder.t_opt -> (a Tag.v) t -> a t = fun x t -> Lam (Bnd (x, t))
let mk_app : type a. a t -> a t -> a t = fun t t' -> App (t, t')
let mk_var : type a. a Var.t -> a t = fun v -> Var v
let mk_chk : type a. a t -> a t -> a t = fun t t' -> Chk (t, t')

let rec lift : type a b c. (a, b, c) Tag.Addition.t -> b t -> c t = fun a t ->
  match t with
  | Unv l -> Unv l
  | Fun (t, t') -> Fun (lift a t, lift_bnd a t')
  | Lam t -> Lam (lift_bnd a t)
  | App (t, t') ->  App (lift a t, lift a t')
  | Var v -> Var (Var.lift a v)
  | Let (t1, t2, t) -> Let (lift a t1, lift a t2, lift_bnd a t)
  | Ref x -> Ref x
  | Chk (t, t') -> Chk (lift a t, lift a t')
and lift_bnd : type a b c. (a, b, c) Tag.Addition.t -> b t_bnd -> c t_bnd = fun a t ->
  match t with
  | Bnd (x, t) -> Bnd (x, lift (Tag.Addition.V a) t)
                 
let lift_z : type a. Tag.z t -> a t = fun t ->
  lift Tag.Addition.Z t

let rec occurs : type a. a Var.t -> a t -> bool = fun v t ->
  match t with
  | Unv _
  | Ref _       -> false
  | Lam t       -> occurs_bnd v t
  | Fun (t, t') -> occurs v t || occurs_bnd v t'
  | Chk (t, t')
  | App (t, t') -> occurs v t || occurs v t'
  | Var w       -> v = w
  | Let (t1, t1', t2) -> occurs v t1 || occurs v t1' || occurs_bnd v t2
and occurs_bnd : type a. a Var.t -> a t_bnd -> bool = fun v (Bnd (_, t)) ->
  occurs (Var.v v) t

let rec bound : type a. a t -> Set_string.t = fun t ->
  match t with
  | Lam t -> bound_bnd t
  | Fun (t, t') -> Set_string.union (bound t) (bound_bnd t')
  | Chk (t, t')
  | App (t, t') -> Set_string.union (bound t) (bound t')
  | Unv _
  | Var _ -> Set_string.empty
  | Let (t1, t1', t2) -> Set_string.union (Set_string.union (bound t1) (bound t1')) (bound_bnd t2)
  | Ref x -> Set_string.singleton x
and bound_bnd : type a. a t_bnd -> Set_string.t = fun (Bnd (x, t)) ->
  match x with
  | Some x -> Set_string.add x (bound t)
  | None   -> bound t

let bound_file : file -> Set_string.t = File.bound bound

module Print = struct
  module C = Context.Make (Presheaf.Const (Type.String))

  module Env = struct
    type 'a t = {
      gen   : string Brook.t;
      gamma : 'a C.t
    }
  end

  module M = Reader_t.Make1 (Env) (Error.String)
  (*  module Op = Monad.Op (M)*)


  let rec prime_close : string list -> string Brook.t = fun xs ->
    lazy (prime_close_data xs)
  and prime_close_data : string list -> string Brook.t_data = fun xs ->
    Brook.prepend_tail xs (prime_close (List.map (fun x -> x ^ "'") xs))

    
(*
  let rec prime_close : string list -> string Brook.t = fun xs ->
    lazy (prime_close_data xs)
  and prime_close_data : string list -> string Brook.t_data = fun xs ->
    Brook.prepend_tail xs (prime_close (List.map (fun x -> x ^ "'") xs))
*)    

  let generate : string list -> Set_string.t -> string Brook.t = fun base exclude ->
    let extend   = ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] in
    let combined = List.fold_left (fun l x -> l @ List.map (fun s -> s ^ x) base) [] extend in
    let prime    = List.map (fun s -> s ^ "'") in
    let pred     = fun s -> not (Set_string.mem s exclude) in
    Brook.filter
      pred
      (Brook.prepend (base @ prime base @ combined) (prime_close (prime (prime (base @ combined)))))

  let init : Set_string.t -> Tag.z Env.t = fun exclude ->
    let names = ["x"; "y"; "z"; "u"; "v"; "w"; "r"; "s"; "t"; "p"; "q"] in
    { Env.gen   = generate names exclude
    ; Env.gamma = C.Empty
    }

  let lookup : type a. a Var.t -> (string, a) M.t = fun v {Env.gamma;_} ->
    Error.String.pure (C.lookup v gamma)

  let register : type a. string option -> ('c, a) M.t -> ('c, a) M.t = function
    | Some v ->
        M.local (fun s ->
          {s with Env.gen = Brook.swap Eq.String.equal (Brook.head s.gen) v s.gen}
        )
    | None ->
       Function.id

  let read : (string, 'a) M.t = fun {Env.gen;_} ->
    Error.String.pure (Brook.head gen)

  let fresh : type c. string option -> (string -> ('a, c Tag.v) M.t) -> ('a, c) M.t = fun x f ->
    let open M in
    match x with
    | Some v ->
        M.local (fun s ->
          Env.{s with
            gamma = C.Comma (s.gamma, v)
          }
        ) @@
        f v
    | None   ->
        read >>= fun v ->
        M.local (fun s ->
          Env.{
            gen     = Brook.tail s.gen;
            gamma   = C.Comma (s.gamma, v)
          }
        ) @@
        f v

  let rec to_raw : type a. a t -> (Raw.t, a) M.t = fun t ->
    let open M in
    match t with
    | Unv l             -> M.pure (Raw.Unv l)
    | Fun _             -> Raw.mk_abs <$> to_raw_abs t
    | Lam t             -> Raw.mk_lam <$> to_raw_mult t
    | App (t, t')       -> Raw.mk_app <$> to_raw t <*> to_raw t'
    | Var v             -> Raw.mk_idt <$> lookup v
    | Chk (t, t')       -> Raw.mk_chk <$> to_raw t <*> to_raw t'
    | Let (t1, t1', t2) -> Raw.mk_let <$> to_raw t1 <*> to_raw t1' <*> to_raw_opt t2
    | Ref x             -> M.pure (Raw.Idt x)
  and to_raw_abs : type a. a t -> ((Raw.t, Raw.t) Raw.telescope, a) M.t = fun t ->
    let open M in
    match t with
    | Fun (t, Bnd (x, t')) ->
        to_raw t >>= fun t ->
        fresh x @@ fun n ->
        if occurs Var.Z t' then
          Raw.mk_pi t (N_list.Last (Some n)) <$> to_raw_abs t'
        else
          Raw.mk_up % Raw.mk_abs <$> (Raw.mk_pi t (N_list.Last None) <$> (Raw.mk_up <$> to_raw t'))
    | _          ->
        Raw.mk_up <$> to_raw t
  and to_raw_mult : type a. a t_bnd -> (Raw.t Named.Mult_opt.t, a) M.t = fun (Bnd (x, t)) ->
    let open M in
    fresh x @@ fun v ->
    if occurs Var.Z t then
      Named.Mult_opt.bind (N_list.Last (Some v)) <$> to_raw t
    else
      Named.Mult_opt.bind (N_list.Last  None)    <$> to_raw t
  and to_raw_opt : type a. a t_bnd -> (Raw.t Named.Opt.t, a) M.t = fun (Bnd (x, t)) ->
    let open M in
    fresh x @@ fun v ->
    if occurs Var.Z t then
      Named.Opt.bind (Some v) <$> to_raw t
    else
      Named.Opt.bind None     <$> to_raw t

  let rec to_raw_file : file -> (Raw.file, Tag.z) M.t = fun f ->
    let open M in
    match f with
    | File.Defn (f, x, t, t') -> File.mk_defn x <$> to_raw t <*> to_raw t' <*> to_raw_file f
    | File.Done               -> M.pure File.Done

  let print : Tag.z t -> PPrint.document = fun t ->
    Error.String.catch_map (to_raw t (init (bound t))) (Raw.Print.print % Raw.compress) failwith

  let print_file : file -> PPrint.document = fun t ->
    Error.String.catch_map (to_raw_file t (init (bound_file t)))
      (Raw.Print.print_file % Raw.compress_file)
      failwith
end

module Gamma = Context.Make (Presheaf.Option (Presheaf.Const (Type.String)))

module Env = struct
  type _ result =
    | R_var  : 'a Var.t -> 'a result
    | R_defn : 'a result

  type 'a t = {
    delta : file
  ; gamma : 'a Gamma.t
  }

  let init : Tag.z t = {
    delta = File.Done
  ; gamma = Gamma.Empty
  }

  let lookup_delta : 'a. Binder.t -> file -> 'a result Option.t = fun x d ->
    Option.map (fun _ -> R_defn) (File.lookup x d)

  module Find = Context_find.Make_option (Heq.Const (Eq.String)) (Gamma.Base)

  let lookup_gamma : type a. string -> a Gamma.t -> a result Option.t = fun n g ->
    Option.map (fun v -> R_var v) (Find.find_option n g)

  let lookup : type a. string -> a t -> a result Option.t = fun n {delta; gamma} ->
    Option.fold
      Option.pure
      (fun () -> lookup_delta n delta)
      (lookup_gamma n gamma)
end

module M = Reader_t.Make1 (Env) (Error.String)
module Op = struct
  let (let*) = M.bind
  
  let fail : string -> ('a, 'r) M.t = fun s ->
    M.cast (Error.String.fail s)

  let fresh : type c. Binder.t_opt -> (c Tag.v t, c Tag.v) M.t -> (c Tag.v t, c) M.t = fun x ->
    M.local (fun e -> Env.{e with gamma = Gamma.Comma (e.gamma, x)})

  let fresh_defn : Binder.t_opt -> Tag.z t -> Tag.z t -> ('a, Tag.z) M.t -> ('a, Tag.z) M.t = fun x t t' ->
    M.local (fun e -> Env.{e with delta = File.Defn (e.delta, x, t, t')})

  let t (type c) (x : Binder.t_opt) (m : (c Tag.v t, c Tag.v) M.t) =
    let open M in
    let f m = mk_lam x <$> fresh x m in
    f m
  let lookup : type c. Binder.t -> (c Env.result Option.t, c) M.t = fun x e ->
    Error.String.pure (Env.lookup x e)
end
open Op


let from_raw_idt : type c. Binder.t -> c Env.result option -> (c t, c) M.t = fun x r ->
  match r with
  | Some (Env.R_var  v)         -> M.pure (Var v)
  | Some (Env.R_defn  )         -> M.pure (Ref x)                                   
  | None                        -> fail ("Unbound identifier '" ^ x ^ "'.")

let rec from_raw : type c. Raw.t -> (c t, c) M.t = fun t ->
  let open M in
  match t with
  | Raw.Let (t1, t1', Named.Opt.Bound (x, t2)) ->
     mk_let x <$> from_raw t1 <*> from_raw t1' <*> fresh x (from_raw t2)
  | Raw.Unv i ->
     M.pure (mk_unv i)
  | Raw.Abs t ->
      from_raw_abs t
  | Raw.Lam (Named.Mult_opt.Bound (N_list.Last x, t)) ->
     mk_lam x <$> fresh x (from_raw t)
  | Raw.Lam (Named.Mult_opt.Bound (N_list.More (x, xs), t)) ->
     mk_lam x <$> fresh x (from_raw (Raw.Lam (Named.Mult_opt.Bound (xs, t))))
  | Raw.App (t, t') ->
      mk_app
      <$> from_raw t
      <*> from_raw t'
  | Raw.Idt x ->
      lookup x >>= from_raw_idt x
  | Raw.Chk (t, t') ->
      mk_chk <$> from_raw t <*> from_raw t'
and from_raw_abs : type c. (Raw.t, Raw.t) Raw.telescope -> (c t, c) M.t = fun t ->
  let open M in
  match t with
  | Raw.Pi (t, Named.Mult_opt.Bound (N_list.Last x, t')) ->
      mk_fun x <$> from_raw t <*> fresh x (from_raw_abs t')
  | Raw.Pi (t, Named.Mult_opt.Bound (N_list.More (x, xs), t')) ->
      mk_fun x <$> from_raw t <*> fresh x (from_raw_abs (Raw.Pi (t, Named.Mult_opt.Bound (xs, t'))))
  | Raw.Up t ->
      from_raw t
(* TODO: optional annotation
   and from_raw_opt : Raw.t Option.t -> t Option.t M.t = fun t ->
   let module A = Monad.ToApplicative (M) in
   let module T = Traversable.Option  (A) in
   T.traverse from_raw t
*)

let rec from_raw_file : Raw.file -> (file, Tag.z) M.t = fun f ->
  let open M in
  match f with
  | File.Defn (f, x, t, t') ->
     let* t  = from_raw t in
     let* t' = from_raw t' in
     let* f  = fresh_defn x t t' (from_raw_file f) in
     pure (File.mk_defn x t t' f)
  | File.Done ->
      M.pure File.Done
