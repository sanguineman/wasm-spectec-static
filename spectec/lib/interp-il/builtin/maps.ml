open Xl
open Il.Ast
open Error
open Util.Source

(* Value map *)

module VMap = Map.Make (Value)

type map = Value.t VMap.t

(* Conversion between meta-maps and OCaml assoc lists *)

let map_of_value (value : value) : map =
  let tuple_of_value (value : value) : value * value =
    match value.it with
    | CaseV ([ []; [ { it = Atom.Colon; _ } ]; [] ], [ value_key; value_value ])
      ->
        (value_key, value_value)
    | _ ->
        error no_region
          (Format.asprintf "expected a pair, but got %s" (Value.to_string value))
  in
  match value.it with
  | CaseV
      ( [ [ { it = Atom.LBrace; _ } ]; [ { it = Atom.RBrace; _ } ] ],
        [ value_pairs ] ) ->
      Value.get_list value_pairs |> List.map tuple_of_value
      |> List.fold_left
           (fun map (value_key, value_value) ->
             VMap.add value_key value_value map)
           VMap.empty
  | _ ->
      error no_region
        (Format.asprintf "expected a map, but got %s" (Value.to_string value))

let value_of_map (typ_key : typ) (typ_value : typ) (map : map) : value =
  let value_of_tuple ((value_key, value_value) : value * value) : value =
    let value =
      let vid = Value.fresh () in
      let typ = Il.Ast.VarT ("pair" $ no_region, [ typ_key; typ_value ]) in
      CaseV ([ []; [ Atom.Colon $ no_region ]; [] ], [ value_key; value_value ])
      $$$ { vid; typ }
    in
    value
  in
  let value_pairs =
    let vid = Value.fresh () in
    let typ =
      Il.Ast.IterT
        ( Il.Ast.VarT ("pair" $ no_region, [ typ_key; typ_value ]) $ no_region,
          Il.Ast.List )
    in
    ListV (VMap.bindings map |> List.map value_of_tuple) $$$ { vid; typ }
  in
  let value =
    let vid = Value.fresh () in
    let typ = Il.Ast.VarT ("map" $ no_region, [ typ_key; typ_value ]) in
    CaseV
      ( [ [ Atom.LBrace $ no_region ]; [ Atom.RBrace $ no_region ] ],
        [ value_pairs ] )
    $$$ { vid; typ }
  in
  value

(* Built-in implementations *)

(* dec $find_map<K, V>(map<K, V>, K) : V? *)

let find_map ~at (_typ_key : targ) (typ_val : targ) (map : map) (key : Value.t)
    =
  at |> ignore;
  let result_opt = VMap.find_opt key map in
  Ok (Value.opt typ_val.it result_opt)

(* dec $find_maps<K, V>(map<K, V>*, K) : V? *)

let find_maps ~at (_typ_key : targ) (typ_val : targ) (maps : map list)
    (key : Value.t) =
  at |> ignore;
  let result_opt =
    List.fold_left
      (fun value_opt map ->
        match value_opt with
        | Some _ -> value_opt
        | None -> VMap.find_opt key map)
      None maps
  in
  Ok (Value.opt typ_val.it result_opt)

(* dec $add_map<K, V>(map<K, V>, K, V) : map<K, V> *)

let add_map ~at (typ_key : targ) (typ_val : targ) (map : map) (key : Value.t)
    (v : Value.t) =
  at |> ignore;
  let map = VMap.add key v map in
  Ok (value_of_map typ_key typ_val map)

(* dec $adds_map<K, V>(map<K, V>, K*, V* ) : map<K, V> *)

let adds_map ~at (typ_key : targ) (typ_val : targ) (map : map)
    (keys : Value.t list) (vals : Value.t list) =
  try
    let map = List.fold_left2 (fun m k v -> VMap.add k v m) map keys vals in
    Ok (value_of_map typ_key typ_val map)
  with Invalid_argument _ ->
    let msg =
      Printf.sprintf
        "adds_map: key list length (%d) does not match value list length (%d)"
        (List.length keys) (List.length vals)
    in
    Error (Err.RuntimeError (at, msg))

(* dec $update_map<K, V>(map<K, V>, K, V) : map<K, V> *)

let update_map = add_map

let builtins : (string * Define.t) list =
  [
    ("find_map", Define.make_two_targs_two_args Parse.map Parse.value find_map);
    ( "find_maps",
      Define.make_two_targs_two_args (Parse.list_of Parse.map)
        Parse.value (* K *)
        find_maps );
    ( "add_map",
      Define.make_two_targs_three_args Parse.map Parse.value Parse.value add_map
    );
    ( "adds_map",
      Define.make_two_targs_three_args Parse.map
        (Parse.list_of Parse.value)
        (Parse.list_of Parse.value)
        adds_map );
    ( "update_map",
      Define.make_two_targs_three_args Parse.map Parse.value Parse.value
        update_map );
  ]
