type t =
  | UNBOUND_DEFN
  | UNV_NEGATIVE
  | NOT_UNV
  | NOT_FUN
  | NOT_SUB_TYPE
  | NOT_SUB_UNV
  | NOT_EQUIV

let to_string : t -> string = fun t ->
  match t with
  | UNBOUND_DEFN -> "UNBOUND_DEFN"
  | UNV_NEGATIVE -> "UNV_NEGATIVE"
  | NOT_UNV      -> "NOT_UNV"
  | NOT_FUN      -> "NOT_FUN"
  | NOT_SUB_TYPE -> "NOT_SUB_TYPE"
  | NOT_SUB_UNV  -> "NOT_SUB_UNV"
  | NOT_EQUIV    -> "NOT_EQUIV"
