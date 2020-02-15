open Function


module Env = struct
  type ('a, 'b) t =
    { delta : Model.file
    ; gamma : ('a, 'b) Model.s
    ; rho   : ('a, 'b) Model.s
    }

  let init : (Tag.z, 'b) t = {delta = File.Done; gamma = Model.Empty; rho = Model.Empty}
end
module E = Error.Make (Failure)
module M = Reader_t.Make2 (Env) (E)
open M.Op
(*
module Op = Monad.Op (M)
open Op
 *)

let fail : type a b c. Failure.t -> (a, b, c) M.t = fun m _ ->
  E.fail m  

let delta : type a b. (Model.file, a, b) M.t = fun e ->
  E.pure e.Env.delta

let gamma : type a b. ((a, b) Model.s, a, b) M.t = fun e ->
  E.pure e.Env.gamma

let rho : type a b. ((a, b) Model.s, a, b) M.t = fun e ->
  E.pure e.Env.rho
   
let extend_var : type a b c. b Model.t -> b Model.t -> (c, a Tag.v, b) M.t -> (c, a, b) M.t = fun d d' ->
  M.local (fun e ->
    let gamma = Model.Comma (e.Env.gamma, d ) in
    let rho   = Model.Comma (e.Env.rho  , d') in
    Env.{e with gamma; rho}
  )

let extend_defn : 'a 'b 'c. Binder.t_opt -> Tag.z Model.t -> Tag.z Model.t -> ('c, 'a, 'b) M.t -> ('c, 'a, 'b) M.t = fun x d d' ->
  M.local (fun e ->
    Env.{e with delta = File.mk_defn x d d' e.Env.delta}
  )

let shift : type a b c. b Model.t -> (c, a Tag.v, b Tag.v) M.t -> (c, a, b) M.t = fun d ->
  M.local (fun e ->
  let gamma = Model.Comma (
    Model.wk_s Weaken.p1 e.Env.gamma,
    Model.wk   Weaken.p1 d
  ) in
  let rho = Model.Comma (
    Model.wk_s Weaken.p1 e.Env.rho,
    Model.Val (Model.Up (Model.wk Weaken.p1 d, Model.Var Var.Z))
  ) in
  Env.{e with gamma; rho})

let m_shift : type a b c. (b Model.t, a, b) M.t -> (c, a Tag.v, b Tag.v) M.t -> (c, a, b) M.t = fun m m' ->
  m >>= fun d -> shift d m'

let gen : type a b c. b Model.t -> (b Tag.v Model.t -> (c, a Tag.v, b Tag.v) M.t) -> (c, a, b) M.t = fun d f ->
  shift d (
    rho >>= fun r ->
    f @@ Model.lookup Var.Z r
  )

let eval : type a b. a Term.t -> (b Model.t, a, b) M.t = fun t ->
  Eval.eval t <$> rho <*> delta

let lookup_var : type a. a Var.t -> ('b Model.t, a, 'b) M.t = fun v ->
  Model.lookup v <$> gamma

let lookup_def : type a b. Binder.t -> (b Model.t, a, b) M.t = fun x ->
  M.ask >>= fun {Env.delta; _} ->
  Option.fold
    (M.pure % Model.lift_z % snd)
    (fun () -> fail (Failure.UnboundDefn (delta, x)))
    (File.lookup x delta)

let equiv : type a b. b Model.t -> b Model.t -> b Model.t -> (unit, a, b) M.t = fun dt d d' ->
  Readback.rb dt d  <$> delta >>= fun n  ->
  Readback.rb dt d' <$> delta >>= fun n' ->
  if n = n' then
    M.pure ()
  else
    fail (Failure.NotEquiv (d, d'))

let equiv_type : type a b. b Model.t -> b Model.t -> (unit, a, b) M.t = fun d d' ->
  Readback.rb_type d  <$> delta >>= fun n  ->
  Readback.rb_type d' <$> delta >>= fun n' ->
  if n = n' then
    M.pure ()
  else
    fail (Failure.NotEquiv (d, d'))

let unv_neg : type a b. Model.level -> (unit, a, b) M.t = fun l ->
  if l < 0 then
    fail (Failure.UnvNegative l)
  else
    M.pure ()

let app : type c. c Model.t -> c Model.t -> (c Model.t, 'a, 'b) M.t = fun d d' ->
  Eval.app d d' <$> delta

let app_cl : type c. c Model.t_cl -> c Model.t -> (c Model.t, 'a, 'b) M.t = fun d d' ->
  Eval.app_cl d d' <$> delta
  
let rec sub_type : type a b. b Model.t -> b Model.t -> (unit, a, b) M.t = fun d d' ->
  match d, d' with
  | Model.Unv l, Model.Unv l' ->
      unv_neg l  >>
      unv_neg l' >>
      if (l <= l') then
        M.pure ()
      else
        fail (Failure.NotSubUnv (l, l'))
  | Model.Fun (d1, d1'), Model.Fun (d2, d2') ->
      equiv_type d1 d2 >> (* TODO make covariant? *)
      gen d1 @@ fun v ->
      sub_type <$> (app_cl (Model.wk_cl Weaken.p1 d1') v) <**> (app_cl (Model.wk_cl Weaken.p1 d2') v)
  | _ ->
      equiv_type d d'

let super_type : type a b. b Model.t -> b Model.t -> (unit, a, b) M.t = fun d d' ->
  sub_type d' d

let super_unv : type a b. Model.level -> b Model.t -> (unit, a, b) M.t = fun l d' ->
  sub_type d' (Model.Unv l)

let is_fun : type a b. b Model.t -> (b Model.t * b Model.t_cl, a, b) M.t = function
  | Model.Fun (d, d') -> M.pure (d, d')
  | d                 -> fail (Failure.NotFun d)

let is_unv : type a b. b Model.t -> (Model.level, a, b) M.t = function
  | Model.Unv l -> unv_neg l >> M.pure l 
  | d           -> fail (Failure.NotUnv d)
                              
let is_kind : type a b. b Model.t -> (unit, a, b) M.t = function
  | Model.Unv l -> unv_neg l
  | d           -> fail (Failure.NotUnv d)

let lub : type b. Model.level -> Model.level -> b Model.t = fun l l' ->
  Model.Unv (max l l')
                 
let rec check : type a b. a Term.t -> b Model.t -> (unit, a, b) M.t = fun t dt ->
  match t, dt with
  | Term.Lam (Term.Bnd (_, t)), Model.Fun (dt, dt') ->
      gen dt @@ fun v ->
      app_cl (Model.wk_cl Weaken.p1 dt') v >>=
      check t
  | Term.Lam _, _ ->
      fail (Failure.NotFun dt)
  | Term.Let (tt', t', Term.Bnd (_, t)), _ ->
      check_type tt' >>
      eval tt'      >>= fun dt' ->
      check t' dt'  >>
      eval t'       >>= fun d'  ->
      extend_var dt' d' @@
      check t dt
  | _ ->
      infer t >>= super_type dt
(*
and infer_s : Term.s -> S.t M.t = function
  | Term.Ident          -> M.ask
  | Term.Cmpse (s1, s2) -> infer_s s1 >>
                           infer_s s2
  | Term.WkVal s        -> infer_s s >>=
                           wkv
  | Term.Comma (s, t)   -> infer_s s    >>= fun g ->
                           infer_type t >>= fun d ->
                           M.pure (Context.Comma (g, TODO undo substitution? d))
 *)
    
and infer : type a b. a Term.t -> (b Model.t, a, b) M.t = fun t ->
  match t with
  | Term.Chk (tt, t) ->
      let* () = check_type tt in
      let* dt = eval tt in
      let* () = check t dt in
      M.pure dt
  | Term.Unv k ->
      M.pure (Model.Unv (k + 1))
  | Term.Fun (t, Term.Bnd (_, t')) ->
      let* dt  = infer_type t in
      let* dt' = m_shift (eval t) (infer_type t') in
      M.pure (lub dt dt')
  | Term.App (t, t') ->
      let* (dt, dt') = infer t >>= is_fun in
      let* () = check t' dt in
      let* d' = eval t' in
      app_cl dt' d'
  | Term.Var v ->
      lookup_var v
  | Term.Ref x ->
      lookup_def x
  | Term.Lam _ ->
      failwith "Lambda abstraction not inferrable."
  | Term.Let _ ->
      failwith "Can't infer type of local definition."
and check_type : type a b. a Term.t -> (unit, a, b) M.t = fun t ->
  infer t >>= is_kind
and infer_type : type a b. a Term.t -> (Model.level, a, b) M.t = fun t ->
  infer t >>= is_unv
  
let rec check_file : Term.file -> (unit, Tag.z, Tag.z) M.t = function
  | File.Defn (f, x, tt, t) ->
      let* () = check_type tt in
      let* dt = eval tt in
      let* () = check t dt in
      let* d  = eval t in
      extend_defn x dt d (check_file f)
  | File.Done ->
      M.pure ()
