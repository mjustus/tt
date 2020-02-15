type t =
(*
  | NotSubType   of Model.t * Model.t
  | UnboundVar   of Model.t Context.t * Var.t
 *)
  | UnboundDefn : Model.file * Binder.t -> t
  | UnvNegative : Model.level -> t
  | NotUnv      : 'b Model.t -> t
  | NotFun      : 'b Model.t -> t
  | NotSubUnv   : Model.level * Model.level -> t
  | NotEquiv    : 'b Model.t * 'b Model.t -> t

let to_code : t -> Failure_code.t = fun t ->
  let open Failure_code in
  match t with
  | UnboundDefn  _ -> UNBOUND_DEFN
  | UnvNegative  _ -> UNV_NEGATIVE
  | NotUnv       _ -> NOT_UNV
  | NotFun       _ -> NOT_FUN
  | NotSubUnv    _ -> NOT_SUB_UNV
  | NotEquiv     _ -> NOT_EQUIV
(*
  | NotSubType   _ -> NOT_SUB_TYPE

  | NotUnv       _ -> NOT_UNV
  | UnboundVar   _ -> UNBOUND_VAR
*)

let to_string : t -> string = fun t ->
  Failure_code.to_string (to_code t)
