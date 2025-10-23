open Xl
open Il.Ast
open Error
open Util.Source

(* Value set *)

module VSet = Set.Make (Value)

type set = VSet.t

(* Conversion between meta-sets and OCaml lists *)

let set_of_value (value : value) : set =
  match value.it with
  | CaseV
      ( [ [ { it = Atom.LBrace; _ } ]; [ { it = Atom.RBrace; _ } ] ],
        [ value_elements ] ) ->
      let values_element = Value.get_list value_elements in
      VSet.of_list values_element
  | _ ->
      error no_region
        (Format.asprintf "expected a set, but got %s" (Value.to_string value))

let value_of_set (typ_key : typ) (set : set) : value =
  let values_element = VSet.elements set in
  let value_elements =
    let vid = Value.fresh () in
    let typ = Il.Ast.IterT (typ_key, Il.Ast.List) in
    ListV values_element $$$ { vid; typ }
  in
  let value =
    let vid = Value.fresh () in
    let typ = Il.Ast.VarT ("set" $ no_region, [ typ_key ]) in
    CaseV
      ( [ [ Atom.LBrace $ no_region ]; [ Atom.RBrace $ no_region ] ],
        [ value_elements ] )
    $$$ { vid; typ }
  in
  value

(* dec $intersect_set<K>(set<K>, set<K>) : set<K> *)

let intersect_set ~at (key_typ : targ) (set_a : VSet.t) (set_b : VSet.t) =
  at |> ignore;
  let result_set = VSet.inter set_a set_b in
  Ok (value_of_set key_typ result_set)

(* dec $union_set<K>(set<K>, set<K>) : set<K> *)

let union_set ~at (key_typ : targ) (set_a : VSet.t) (set_b : VSet.t) =
  at |> ignore;
  let result_set = VSet.union set_a set_b in
  Ok (value_of_set key_typ result_set)

(* dec $unions_set<K>(set<K>* ) : set<K> *)

let unions_set ~at (key_typ : targ) (sets : VSet.t list) =
  at |> ignore;
  let result_set = List.fold_left VSet.union VSet.empty sets in
  Ok (value_of_set key_typ result_set)

(* dec $diff_set<K>(set<K>, set<K>) : set<K> *)

let diff_set ~at (key_typ : targ) (set_a : VSet.t) (set_b : VSet.t) =
  at |> ignore;
  let result_set = VSet.diff set_a set_b in
  Ok (value_of_set key_typ result_set)

(* dec $sub_set<K>(set<K>, set<K>) : bool *)

let sub_set ~at (_key_typ : targ) (set_a : VSet.t) (set_b : VSet.t) =
  at |> ignore;
  Ok (Value.bool (VSet.subset set_a set_b))

(* dec $eq_set<K>(set<K>, set<K>) : bool *)

let eq_set ~at (_key_typ : targ) (set_a : VSet.t) (set_b : VSet.t) =
  at |> ignore;
  Ok (Value.bool (VSet.equal set_a set_b))

let builtins : (string * Define.t) list =
  [
    ("intersect_set", Define.T1.a2 Arg.set Arg.set intersect_set);
    ("union_set", Define.T1.a2 Arg.set Arg.set union_set);
    ("unions_set", Define.T1.a1 (Arg.list_of Arg.set) unions_set);
    ("diff_set", Define.T1.a2 Arg.set Arg.set diff_set);
    ("sub_set", Define.T1.a2 Arg.set Arg.set sub_set);
    ("eq_set", Define.T1.a2 Arg.set Arg.set eq_set);
  ]
