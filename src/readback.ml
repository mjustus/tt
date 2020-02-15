type exn_rb = Exn_rb_witness : 'a Model.t * 'a Model.t -> exn_rb
exception Exn_rb of exn_rb

let fresh : type a. a Model.t -> (a Tag.v) Model.t = fun d ->
  Model.Val (Model.Up (Model.wk Weaken.p1 d, Model.Var Var.Z))

let rec rb_ne : type a. a Model.t_ne -> Model.file -> a Normal.ne = fun d f ->
  match d with
  | Model.Var v                     -> Normal.Var v
  | Model.App (d, d')               -> Normal.App (rb_ne d f, rb_nf d' f)

and rb_vl : type a. a Model.t_vl -> Model.file -> a Normal.vl = fun d f ->
  match d with
  | Model.Up  (_, d) -> Normal.Neu (rb_ne d f)
  | Model.Lam _      -> failwith "Encountered ill-typed value during readback."

and rb : type a. a Model.t -> a Model.t -> Model.file -> a Normal.nf = fun dt d f ->
  match dt with
  | Model.Unv _         ->
      rb_type d f
  | Model.Fun (dt, dt') ->
      let v = fresh dt in
      Normal.(Val (Lam (Bnd (Model.bound d, rb (Eval.app_cl (Model.wk_cl Weaken.p1 dt') v f) (Eval.app (Model.wk Weaken.p1 d) v f) f))))
  | Model.Val _        ->
     begin match d with
     | Model.Val d -> Normal.Val (rb_vl d f)
     | _           -> raise (Exn_rb (Exn_rb_witness (dt, d)))
     end

and rb_type : type a. a Model.t -> Model.file -> a Normal.nf = fun d f ->
  match d with
  | Model.Unv l       ->
      Normal.Unv l
  | Model.Fun (d, (Model.Cls (_, x, _) as d')) ->
      let v = fresh d in
      Normal.Fun (rb_type d f, Normal.Bnd (x, rb_type (Eval.app_cl (Model.wk_cl Weaken.p1 d') v f) f))
  | Model.Val d       ->
      Normal.Val (rb_vl d f)       
       
and rb_nf : type a. a Model.t_nf -> Model.file -> a Normal.nf = function
  | Model.Dwn (dt, d) -> rb dt d

let rec norm_file : Model.file -> Model.file -> Normal.file = fun t f ->
  match t with
  | File.Defn (t, x , dt, d) ->
     let nt = rb_type dt f in
     let n  = rb dt   d  f in
     File.mk_defn x nt n (norm_file t (File.mk_defn x dt d f))
  | File.Done ->
     File.Done
