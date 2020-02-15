type ('a, 'b) telescope =
  | Pi of 'a * (('a, 'b) telescope) Named.Mult_opt.t
  | Up of 'b
type t =
  (* telescope of type abstractions *)
  | Abs of (t, t) telescope
  | Unv of int
  | Lam of t Named.Mult_opt.t
  | App of t * t
  (* variable or file-wide definition *)
  | Idt of string
  (* let binding *)
  | Let of t * t * t Named.Opt.t
  (* type annotation: first argument is the type, second the term *)
  | Chk of t * t
                                      
(*
type file =
  | Defn of t * t * file Named.Opt.t
  | Done
*)

type file = t File.t

let mk_let : t -> t -> t Named.Opt.t -> t = fun t t' t'' -> Let (t, t', t'')
let mk_unv : int -> t = fun l -> Unv l
let mk_pi : 'a -> Binder.t_nlist_opt -> ('a, 'b) telescope -> ('a, 'b) telescope = fun t xs t' -> Pi (t, Named.Mult_opt.Bound (xs, t'))
let mk_up : 'b -> ('a, 'b) telescope = fun t -> Up t
let mk_abs : ('a, 'b) telescope -> t = fun t -> Abs t
let mk_lam : t Named.Mult_opt.t -> t = fun t -> Lam t
let mk_app : t -> t -> t = fun t t' -> App (t, t')
let mk_idt : string -> t = fun x -> Idt x
let mk_chk : t -> t -> t = fun t t' -> Chk (t, t')

let rec compress : t -> t = fun t ->
  match t with
  | Abs t -> Abs (compress_abs t)
  | Unv _ | Idt _ -> t
  | Lam t -> Lam (compress_lam t)
  | App (t, t') -> App (compress t, compress t')
  | Let (t1, t1', Named.Opt.Bound (x, t2)) -> Let (compress t1, compress t1', Named.Opt.Bound (x, compress t2))
  | Chk (t, t') -> Chk (compress t, compress t')
and compress_lam : t Named.Mult_opt.t  -> t Named.Mult_opt.t = function
  | Named.Mult_opt.Bound (xs, Lam t) ->
      begin match compress_lam t with
      | Named.Mult_opt.Bound (ys, t) ->
          Named.Mult_opt.Bound (N_list.concat xs ys, t)
      end
  | t -> compress_binder t
and compress_binder : t Named.Mult_opt.t -> t Named.Mult_opt.t = function
  | Named.Mult_opt.Bound (xs, t) ->
      Named.Mult_opt.Bound (xs, compress t)
and compress_abs : (t, t) telescope -> (t, t) telescope = function
  | Pi (t, t') -> Pi (compress t, compress_abs_binder t')
  | Up (Abs t) -> compress_abs t
  | Up t       -> Up (compress t)
and compress_abs_binder : (t, t) telescope Named.Mult_opt.t -> (t, t) telescope Named.Mult_opt.t = function
  | Named.Mult_opt.Bound (xs, t) ->
      Named.Mult_opt.Bound (xs, compress_abs t)

let rec compress_file : file -> file = function
  | File.Defn (f, x, t, t') ->
      File.Defn (compress_file f, x, compress t, compress t')
  | File.Done  -> Done
  
module Print = struct
  let (^^) = PPrint.(^^)
  let (^/^) = PPrint.(^/^)
  let (^//^) = PPrint.(^//^)
  let (!^) = PPrint.(!^)

  let infix_colon_paren x y =
    ((PPrint.lparen ^^ x) ^//^ (PPrint.colon ^^ PPrint.space ^^ y)) ^^ PPrint.rparen

  let infix_colon_bracket x y =
    ((PPrint.lbracket ^^ x) ^//^ (PPrint.colon ^^ PPrint.space ^^ y)) ^^ PPrint.rbracket

  type context =
    | None
    | AppLeft | AppRight
    | ChkLeft | ChkRight
    | AtLeft
    | Swp
    | SPiLeft | SPiRight
    | SNaLeft | SNaRight
    | CmpTest
    | Other

  let rec need_parens : context -> t -> bool = fun c t ->
    match t with
    | Chk _ ->
        begin match c with
        | None -> false
        | _ -> true
        end
    | Idt _ -> false
    | Unv   _ ->
        begin match c with
        | AppRight -> true
        |  _ -> false
        end
    | Abs (Pi _) ->
        begin match c with
        | AppLeft | AppRight | AtLeft | SPiLeft | SNaRight -> true
        | _ -> false
        end
    | Abs (Up t) ->
        need_parens c t
    | App _ ->
        begin match c with
        | AppRight -> true
        |  _ -> false
        end
    | Lam   _ ->
        begin match c with
        | AppLeft | AppRight -> true
        | _ -> false
        end
    | Let _ ->
       begin match c with
       | AppLeft | AppRight | ChkLeft | AtLeft | SPiLeft | CmpTest -> true
       | _ -> false
       end

  let arrow : PPrint.document = !^ "→"

  let print_idt = function Some x -> !^ x | None -> PPrint.underscore

  let print_bound : Binder.t_nlist_opt -> PPrint.document = fun b ->
    PPrint.group (N_list.fold_map print_idt (^/^) b)

  let print_bound_comma : Binder.t_nlist_opt -> PPrint.document =
    N_list.fold_map print_idt (fun d d' -> d ^/^ PPrint.comma ^//^ d')

  let rec print : t -> PPrint.document = fun t ->
    match t with
    | Unv i ->
        !^ "U" ^^ PPrint.space ^^ !^ (string_of_int i)
    | Abs (Pi (t, Named.Mult_opt.Bound (N_list.Last None, Up t'))) ->
        PPrint.group (print_ctx SPiLeft t ^//^ arrow)
        ^//^ print_ctx SPiRight t'
    | Abs t -> print_telescope (print_ctx Other) t PPrint.group
    | Lam (Named.Mult_opt.Bound (xs, t')) ->
        PPrint.group (
          !^ "λ"
          ^^  print_bound xs
          ^^  PPrint.dot
        )
        ^//^ print_ctx Other t'
    | App (t, t') -> (print_ctx AppLeft t) ^//^ (print_ctx AppRight t')
    | Idt s -> !^ s
    | Let (t1, t1', Named.Opt.Bound (x, t2)) ->
       (PPrint.group (
           !^ "let" ^//^ print_idt x
           ^//^ PPrint.colon ^//^ print_ctx Other t1
           ^//^ PPrint.equals
         )
         ^//^ print_ctx Other t1'
         ^//^ !^ "in"
       )
       ^/^ print_ctx Other t2
    | Chk (t,t') ->
        let infix_wrap x y = x ^//^ ((!^ "::") ^^ PPrint.space ^^ y) in
        infix_wrap (print_ctx ChkLeft t') (print_ctx ChkRight t)

  and print_ctx : context -> t -> PPrint.document = fun c t ->
    if need_parens c t then
      PPrint.parens (print t)
    else
      print t
  and print_telescope : 'a. ('a -> PPrint.document) -> (t, 'a) telescope -> (PPrint.document -> PPrint.document) -> PPrint.document = fun f t acc ->
    match t with
    | Pi (t, Named.Mult_opt.Bound (xs, Up t')) ->
        PPrint.group (acc (infix_colon_paren (print_bound_comma xs) (print_ctx Other t) ^//^ arrow))
        ^//^ f t'
    | Pi (t, Named.Mult_opt.Bound (xs, t')) ->
        print_telescope f t' (fun d -> acc (infix_colon_paren (print_bound_comma xs) (print_ctx Other t) ^/^ d))
    | Up t -> f t

  let print_decl : Binder.t_opt -> t -> t -> PPrint.document = fun x t t' ->
    PPrint.group ((print_idt x ^//^ PPrint.colon) ^//^ print t)
    ^//^ PPrint.equals ^//^ print t'

  let rec print_file : file -> PPrint.document = fun t ->
    match t with
    | File.Defn (Done, x, t, t') ->
        print_decl x t t'
    | File.Defn (f, x, t, t') ->
        print_decl x t t' ^/^ PPrint.semi
        ^/^ print_file f
    | File.Done -> PPrint.empty
end
