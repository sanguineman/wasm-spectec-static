open Xl
open Il.Ast
open Util.Source

(* Conversion between meta-numerics and OCaml numerics *)

let bigint_of_value (value : value) : Bigint.t =
  value |> Value.get_num |> Num.to_int

(* dec $sum(nat* ) : nat *)

let sum ~(at : region) (targs : targ list) (values_input : value list) : value =
  Extract.zero at targs;
  let values =
    Extract.one at values_input |> Value.get_list |> List.map bigint_of_value
  in
  let sum = List.fold_left Bigint.( + ) Bigint.zero values in
  Value.nat sum

let sum_impl ~at (nums : Bigint.t list) : (Value.t, Err.t) result =
  at |> ignore;
  let total = List.fold_left Bigint.( + ) Bigint.zero nums in
  Ok (Value.nat total)

(* dec $max(nat* ) : nat *)

let max ~(at : region) (targs : targ list) (values_input : value list) : value =
  Extract.zero at targs;
  let values =
    Extract.one at values_input |> Value.get_list |> List.map bigint_of_value
  in
  let max = List.fold_left Bigint.max Bigint.zero values in
  Value.nat max

let max_impl ~at (nums : Bigint.t list) : (Value.t, Err.t) result =
  match nums with
  | [] -> Error.error at "max requires at least one argument"
  | h :: t ->
      let max_value = List.fold_left Bigint.max h t in
      Ok (Value.nat max_value)

(* dec $min(nat* ) : nat *)

let min ~(at : region) (targs : targ list) (values_input : value list) : value =
  Extract.zero at targs;
  let values =
    Extract.one at values_input |> Value.get_list |> List.map bigint_of_value
  in
  let min = List.fold_left Bigint.min Bigint.zero values in
  Value.nat min

let min_impl ~at (nums : Bigint.t list) : (Value.t, Err.t) result =
  match nums with
  | [] -> Error.error at "max requires at least one argument"
  | h :: t ->
      let min_value = List.fold_left Bigint.min h t in
      Ok (Value.nat min_value)

let builtins =
  [
    ("sum", Define.make_one_arg (Parse.list_of Parse.nat) sum_impl);
    ("max", Define.make_one_arg (Parse.list_of Parse.nat) max_impl);
    ("min", Define.make_one_arg (Parse.list_of Parse.nat) min_impl);
  ]
