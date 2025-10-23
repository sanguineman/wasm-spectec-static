open Xl
open Il.Ast
open Util.Source

(* dec $rev_<X>(X* ) : X* *)

let rev_ ~(at : region) (targs : targ list) (values_input : value list) : value
    =
  let typ = Extract.one at targs in
  let values = Extract.one at values_input |> Value.get_list in
  List.rev values |> Value.list typ.it

let rev_impl ~at (typ : targ) (vs : Value.t list) : (Value.t, Err.t) result =
  at |> ignore;
  (* Use the Value.list constructor, passing the *element type* (typ.it) *)
  Ok (Value.list typ.it (List.rev vs))

(* dec $concat_<X>((X* )* ) : X* *)

let concat_ ~(at : region) (targs : targ list) (values_input : value list) :
    value =
  let typ = Extract.one at targs in
  let values =
    Extract.one at values_input
    |> Value.get_list
    |> List.concat_map Value.get_list
  in
  values |> Value.list typ.it

let concat_impl ~at (typ : targ) (vss : Value.t list list) :
    (Value.t, Err.t) result =
  at |> ignore;
  (* vss is already a 'value list list', just List.concat and re-wrap *)
  Ok (Value.list typ.it (List.concat vss))

(* dec $distinct_<K>(K* ) : bool *)

let distinct_ ~(at : region) (targs : targ list) (values_input : value list) :
    value =
  let _typ = Extract.one at targs in
  let values = Extract.one at values_input |> Value.get_list in
  let set = Sets.VSet.of_list values in
  Sets.VSet.cardinal set = List.length values |> Value.bool

let distinct_impl ~at (_typ : targ) (vs : Value.t list) :
    (Value.t, Err.t) result =
  at |> ignore;
  let set = Sets.VSet.of_list vs in
  let is_distinct = Sets.VSet.cardinal set = List.length vs in
  Ok (Value.bool is_distinct)

(* dec $partition_<X>(X*, nat) : (X*, X* ) *)

let partition_ ~(at : region) (targs : targ list) (values_input : value list) :
    value =
  let typ = Extract.one at targs in
  let value_list, value_len = Extract.two at values_input in
  let values = Value.get_list value_list in
  let len = value_len |> Value.get_num |> Num.to_int |> Bigint.to_int_exn in
  let values_left, values_right =
    values
    |> List.mapi (fun idx value -> (idx, value))
    |> List.partition (fun (idx, _) -> idx < len)
  in
  let value_left = List.map snd values_left |> Value.list typ.it in
  let value_right = List.map snd values_right |> Value.list typ.it in
  Value.tuple [ value_left; value_right ]

let partition_impl ~at (typ : targ) (vs : Value.t list) (n : Bigint.t) :
    (Value.t, Err.t) result =
  try
    (* Safely handle the int conversion *)
    let len = Bigint.to_int_exn n in
    let left, right =
      vs
      |> List.mapi (fun idx v -> (idx, v))
      |> List.partition (fun (idx, _) -> idx < len)
    in
    let v_left = Value.list typ.it (List.map snd left) in
    let v_right = Value.list typ.it (List.map snd right) in
    Ok (Value.tuple [ v_left; v_right ])
  with _ ->
    Error (Err.runtime at "partition: index is too large to be an integer")

(* dec $assoc_<X, Y>(X, (X, Y)* ) : Y? *)

let assoc_ ~(at : region) (targs : targ list) (values_input : value list) :
    value =
  let _typ_key, typ_value = Extract.two at targs in
  let value, value_list = Extract.two at values_input in
  let values =
    Value.get_list value_list
    |> List.map (fun value ->
           match value.it with
           | TupleV [ value_key; value_value ] -> (value_key, value_value)
           | _ -> assert false)
  in
  let value_opt =
    List.fold_left
      (fun value_found (value_key, value_value) ->
        match value_found with
        | Some _ -> value_found
        | None when Value.compare value value_key = 0 -> Some value_value
        | None -> None)
      None values
  in
  value_opt |> Value.opt typ_value.it

let assoc_impl ~at (_typ_x : targ) (typ_y : targ) (key : Value.t)
    (pairs : (Value.t * Value.t) list) : (Value.t, Err.t) result =
  at |> ignore;
  (* Use List.assoc_opt which is safe and returns an option *)
  let result_opt = List.assoc_opt key pairs in
  (* Use the Value.opt constructor, passing the *value type* (typ_y.it) *)
  Ok (Value.opt typ_y.it result_opt)

let builtins =
  [
    ("rev_", Define.make_one_targ_one_arg (Parse.list_of Parse.value) rev_impl);
    ( "concat_",
      Define.make_one_targ_one_arg
        (Parse.list_of (Parse.list_of Parse.value))
        concat_impl );
    ( "distinct_",
      Define.make_one_targ_one_arg (Parse.list_of Parse.value) distinct_impl );
    ( "partition_",
      Define.make_one_targ_two_args
        (Parse.list_of Parse.value)
        Parse.nat partition_impl );
    ( "assoc_",
      Define.make_two_targs_two_args Parse.value (Parse.list_of Parse.pair)
        assoc_impl );
  ]
