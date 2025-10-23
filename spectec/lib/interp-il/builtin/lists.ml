open Il.Ast
open Util.Source

(* dec $rev_<X>(X* ) : X* *)

let rev_ ~at (typ : targ) (vs : Value.t list) : (Value.t, Err.t) result =
  at |> ignore;
  Ok (Value.list typ.it (List.rev vs))

(* dec $concat_<X>((X* )* ) : X* *)

let concat_ ~at (typ : targ) (vss : Value.t list list) : (Value.t, Err.t) result
    =
  at |> ignore;
  Ok (Value.list typ.it (List.concat vss))

(* dec $distinct_<K>(K* ) : bool *)

let distinct_ ~at (_typ : targ) (vs : Value.t list) : (Value.t, Err.t) result =
  at |> ignore;
  let set = Sets.VSet.of_list vs in
  let is_distinct = Sets.VSet.cardinal set = List.length vs in
  Ok (Value.bool is_distinct)

(* dec $partition_<X>(X*, nat) : (X*, X* ) *)

let partition_ ~at (typ : targ) (vs : Value.t list) (n : Bigint.t) :
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

let assoc_ ~at (_typ_x : targ) (typ_y : targ) (key_query : Value.t)
    (pairs : (Value.t * Value.t) list) : (Value.t, Err.t) result =
  at |> ignore;
  let value_opt =
    List.fold_left
      (fun value_found (key, value) ->
        match value_found with
        | Some _ -> value_found
        | None when Value.eq key_query key -> Some value
        | None -> None)
      None pairs
  in
  Ok (Value.opt typ_y.it value_opt)

let builtins =
  [
    ("rev_", Define.make_one_targ_one_arg (Parse.list_of Parse.value) rev_);
    ( "concat_",
      Define.make_one_targ_one_arg
        (Parse.list_of (Parse.list_of Parse.value))
        concat_ );
    ( "distinct_",
      Define.make_one_targ_one_arg (Parse.list_of Parse.value) distinct_ );
    ( "partition_",
      Define.make_one_targ_two_args
        (Parse.list_of Parse.value)
        Parse.nat partition_ );
    ( "assoc_",
      Define.make_two_targs_two_args Parse.value (Parse.list_of Parse.pair)
        assoc_ );
  ]
