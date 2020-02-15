open Function

type exn_app = Exn_app_witness : 'a Model.t_vl * 'a Model.t -> exn_app
exception Exn_app of exn_app

let lookup_def : type a. Binder.t -> Model.file -> a Model.t = fun x f ->
  Option.fold
    (Model.lift_z % snd)
    (fun () -> failwith @@ "Definition '" ^ x ^ "' not found in environment")
    (File.lookup x f)

let rec app_cl : type a. a Model.t_cl -> a Model.t -> Model.file -> a Model.t = fun (Model.Cls (r, _, t)) d' f ->
  eval t (Model.Comma (r, d')) f

and app_vl : type a. a Model.t_vl -> a Model.t -> Model.file -> a Model.t = fun d d' f ->
  match d with
  | Model.Lam d ->
     app_cl d d' f
  | Model.Up (Model.Fun (d1, d2), d) ->
     Model.Val (Model.Up (app_cl d2 d' f, Model.App (d, Model.Dwn (d1, d'))))
  | _ -> raise (Exn_app (Exn_app_witness (d, d')))

and app : type a. a Model.t -> a Model.t -> Model.file -> a Model.t = fun d d' ->
  match d with
  | Model.Val d -> app_vl d d'
  | _           -> failwith "Not a function abstraction."

and eval : type a b. a Term.t -> (a, b) Model.s -> Model.file -> b Model.t = fun t r f ->
  match t with
  (*  | Term.Sub (t,s)      -> eval t (eval_s s r) *)
  | Term.Unv l           -> Model.Unv l
  | Term.Fun (t, t')     -> Model.Fun (eval t r f, eval_cl t' r)
  | Term.Lam t           -> Model.Val (Model.Lam (eval_cl t r))
  | Term.App (t, t')     -> app (eval t r f) (eval t' r f) f
  | Term.Var v           -> Model.lookup v r
  | Term.Let (_, t1, t2) -> app_cl (eval_cl t2 r) (eval t1 r f) f
  | Term.Ref x           -> lookup_def x f
  | Term.Chk (_, t')     -> eval t' r f
and eval_cl : type a b. a Term.t_bnd -> (a, b) Model.s ->  b Model.t_cl = fun (Term.Bnd (x, t)) r ->
  Model.Cls (r, x, t)

let rec eval_file : Term.file -> Model.file -> Model.file = fun t f ->
  match t with
  | File.Defn (tf, x, tt, t) ->
      let dt = eval      tt Model.Empty f in
      let d  = eval      t  Model.Empty f in
      let df = eval_file tf (File.mk_defn x dt d f) in
      File.mk_defn x dt d df
  | File.Done ->
      File.Done
