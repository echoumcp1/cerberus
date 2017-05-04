(* Created by Victor Gomes 2017-03-10 *)

open Util
module M = Mem
module T = AilTypes
module C = Core_ctype

(* Undefined Behaviour *)
exception Undefined of string
exception Error of string

(* Keep track of the last memory operation, for error display *)
type memop = Store | Load | Create | Alloc | None
let last_memop = ref None

let show_memop = function
  | Store -> "store"
  | Load -> "load"
  | Create -> "create"
  | Alloc -> "alloc"
  | None -> raise (Error "unknown last memop")

let (>>=) = M.bind0
let return = M.return0

(* Runtime flags *)
let batch =
  try ignore (Sys.getenv "CERB_BATCH"); true
  with _ -> false

let stdout = ref ""

(* init/set globals before calling main *)

let set_global (f, x) =
  f return () >>= fun y -> x := y; return ()

let init_globals glbs =
  List.fold_left
    (fun acc (f, x) -> acc >>= fun _ -> set_global (f, x))
    (return ()) glbs

let null_ptr = M.null_ptrval C.Void0

(* Non deterministic choice *)

let nd n xs =
  Random.self_init ();
  Random.int n |> List.nth xs

(* IV min/max wraps *)

let ivctor memf errmsg = function
  | C.Basic0 (T.Integer it) -> memf it
  | _ -> raise (Error errmsg)

let ivmin = ivctor M.min_ival "ivmin"

let ivmax = ivctor M.max_ival "ivmax"

(* Ail types *)

let ail_qualifier (c, r, v, a) =
  { AilTypes.const = c;
    AilTypes.restrict = r;
    AilTypes.volatile = v;
    AilTypes.atomic = a;
  }

let is_scalar ty =
  AilTypesAux.is_scalar (Core_aux.unproj_ctype ty)

let is_integer ty =
  AilTypesAux.is_integer (Core_aux.unproj_ctype ty)

let is_signed ty =
  AilTypesAux.is_signed_integer_type (Core_aux.unproj_ctype ty)

let is_unsigned ty =
  AilTypesAux.is_unsigned_integer_type (Core_aux.unproj_ctype ty)

(* Loaded - Specified and unspecified values *)

type 'a loaded =
  | Specified of 'a
  | Unspecified of C.ctype0

let specified x = Specified x
let unspecified x = Unspecified x

exception Label of string * (M.integer_value) loaded

(* Cast from memory values *)

let get_integer m =
  let terr _ _ = raise (Error "Type mismatch, expecting integer values.") in
  M.case_mem_value m unspecified terr (fun _ -> specified) terr terr (terr()) terr terr

let get_pointer m =
  let terr _ _ = raise (Error "Type mismatch, expecting pointer values.") in
  M.case_mem_value m unspecified terr terr terr (fun _ p -> specified p)
    (terr()) terr terr

(* Cast to memory values *)

let mk_int s = M.integer_ival (Nat_big_num.of_string s)

(* Binary operations wrap *)

let add = M.op_ival M.IntAdd
let sub = M.op_ival M.IntSub
let mul = M.op_ival M.IntMul
let div = M.op_ival M.IntDiv
let remt = M.op_ival M.IntRem_t
let remf = M.op_ival M.IntRem_f
let exp = M.op_ival M.IntExp

let eq n m = Option.get (M.eq_ival (Some M.initial_mem_state) n m)
let lt n m = Option.get (M.lt_ival (Some M.initial_mem_state) n m)
let gt n m = Option.get (M.lt_ival (Some M.initial_mem_state) m n)
let le n m = Option.get (M.le_ival (Some M.initial_mem_state) n m)
let ge n m = Option.get (M.le_ival (Some M.initial_mem_state) m n)

let eq_ptrval p q = M.eq_ptrval p q
let ne_ptrval p q = M.ne_ptrval p q
let ge_ptrval p q = M.ge_ptrval p q
let lt_ptrval p q = M.lt_ptrval p q
let gt_ptrval p q = M.gt_ptrval p q
let le_ptrval p q = M.le_ptrval p q
let diff_ptrval p q = M.diff_ptrval p q
let valid_for_deref_ptrval p = return $ M.validForDeref_ptrval p

(* Memory actions wrap *)

let create pre al ty =
  last_memop := Create;
  M.allocate_static 0 pre al ty

let alloc pre al n =
  last_memop := Alloc;
  M.allocate_dynamic 0 pre al n

let load_integer ity e =
  last_memop := Load;
  M.load (C.Basic0 (T.Integer ity)) e >>= return % get_integer % snd

let load_pointer q cty e =
  last_memop := Load;
  M.load (C.Pointer0 (q, cty)) e >>= return % get_pointer % snd

let store f ty e1 e2 =
  last_memop := Store;
  let e = match e2 with
    | Specified e -> f e
    | Unspecified ty -> M.unspecified_mval ty
  in M.store ty e1 e

let store_integer ity =
  store (M.integer_value_mval ity) (C.Basic0 (T.Integer ity))

let store_pointer q cty =
  store (M.pointer_mval cty) (C.Pointer0 (q, cty))

(* TODO: it only support array of int *)

(*
let store_array cty size =
  let mk_array = match cty with
    | C.Void0 -> raise (Error "store array: not expecting void type")
    | C.Basic0 (T.Integer ity) -> List.map (M.integer_value_mval ity)
    | C.Basic0 (T.Floating fty) -> List.map (M.floating_value_mval fty)
                                    (*
    | C.Array0 of C.ctype0 * Nat_big_num.num option
    | C.Function0 of C.ctype0 * (AilTypes.qualifiers * C.ctype0) list * bool
    | C.Pointer0 of AilTypes.qualifiers * C.ctype0
    | C.Atomic0 of C.ctype0
    | C.Struct0 of C.struct_tag
    | C.Union0 of C.union_tag
    | C.Builtin0 of string *)
  in
  store (fun e -> M.array_mval (mk_array e)) (C.Array0 (cty, size))
*)
let store_array q cty size e1 le2 =
  last_memop := Store;
  M.store (C.Array0 (q, cty, size)) e1 (
    match le2 with
    | Specified e2 ->
      begin match cty with
        | C.Basic0 (T.Integer ity) ->
          M.array_mval (List.map (function
              | Specified i -> M.integer_value_mval ity i
              | Unspecified ty -> M.unspecified_mval ty
          ) e2)
        | _ -> raise (Error "excepting an array of integers")
      end
    | Unspecified ty -> M.unspecified_mval ty
  )

(* Printf wrap *)

let printf (conv : C.ctype0 -> M.integer_value -> M.integer_value)
    (xs:M.integer_value list)
    (args:(C.ctype0 * M.pointer_value) list) =
  let encode ival = match Mem_aux.integerFromIntegerValue ival with
    | Some n -> Decode_ocaml.encode_character_constant n
    | None -> Debug_ocaml.error
                "Printf: one of the element of the format array was invalid"
  in
  let eval_conv cty x =
    let throw_error _ = raise (Error "Rt_ocaml.printf: expecting an integer") in
    let n = M.case_mem_value x
        throw_error
        (fun _ -> throw_error)
        (fun _ v -> conv cty v)
        (fun _ -> throw_error)
        (fun _ -> throw_error)
        throw_error
        (fun _ -> throw_error)
        (fun _ -> throw_error)
    in Either.Right (Undefined.Defined0 (Core.Vloaded (Core.LVspecified (Core.OVinteger n))))
  in
  Output.printf eval_conv (List.rev (List.map encode xs)) args
  >>= begin function
    | Either.Right (Undefined.Defined0 xs) ->
      let n = List.length xs in
      let output = String.init n (List.nth xs) in
      if batch then stdout := !stdout ^ String.escaped output
      else print_string output;
      return (M.integer_ival (Nat_big_num.of_int n))
    | Either.Right (Undefined.Undef (_, xs) ) ->
      raise (Error (String.concat "," 
                      (List.map Undefined.stringFromUndefined_behaviour xs)))
    | Either.Right (Undefined.Error (_, m) ) -> raise (Error m)
    | Either.Left z -> raise (Error (Pp_errors.to_string z))
  end

(* Exit continuation *)

exception Exit of (M.integer_value loaded)

let constraints = "CONSTRS ==> []\nLog[0]\n\nEnd[0]\n"

let print_batch res =
  Printf.printf
    "Defined {value: \"%s\", stdout: \"%s\", blocked: \"false\"}\n%s"
    res !stdout constraints

let print_err_batch e =
  let err = match e with
    | Mem_common.MerrUnitialised str ->
        "MerrUnitialised \"" ^  (str ^ "\"")
    | Mem_common.MerrInternal str ->
        "MerrInternal \"" ^  (str ^ "\"")
    | Mem_common.MerrOther str ->
        "MerrOther \"" ^  (str ^ "\"")
    | Mem_common.MerrReadFromDead ->
        "MerrReadFromDead"
    | Mem_common.MerrWIP str ->
        "Memory WIP: " ^ str
  in Printf.printf
    "Killed {msg: memory layout error (%s seq) ==> %s}\n%s"
    (show_memop !last_memop) err constraints

let string_of_specified n =
  Printf.sprintf "Specified(%s)" (Nat_big_num.to_string n)

let string_of_unspec cty =
  Printf.sprintf "Unspecified(\"%s\")" (String_core_ctype.string_of_ctype cty)

let quit f =
  try
    match M.runMem (f (fun x -> raise (Exit x)) ()) M.initial_mem_state with
    | [] -> raise (Error "continuation not raised: no result from runMem")
    | [Either.Left e] -> if batch then print_err_batch e
    | [Either.Right _] ->
      raise (Error "continuation not raised: one result from runMem")
    | _ -> raise (Error "continuation not raised: multiple results from runMem")
  with
  | Exit x ->
    (match x with
     | Specified x ->
       let n = M.eval_integer_value x |> Option.get in
       if batch then print_batch (string_of_specified n);
       exit (Nat_big_num.to_int n)
     | Unspecified cty ->
       if batch then print_batch (string_of_unspec cty);
       exit(-1)
    )

let create_tag_defs_map defs =
  List.fold_left
    (fun m (s, xs) -> Pmap.add s xs m)
    (Pmap.empty Core_fvs.sym_compare) defs

let run tags gls main =
  begin fun cont args ->
    Tags.set_tagDefs (create_tag_defs_map tags);
    init_globals gls
    >>= fun _ -> main cont args
  end |> quit
