open Xl
open Il.Ast
open Util.Source

(* Conversion between meta-numerics and OCaml numerics *)

let bigint_of_value (value : value) : Bigint.t =
  value |> Value.get_num |> Num.to_int

(* dec $sum(nat* ) : nat *)

let sum (at : region) (targs : targ list) (values_input : value list) : value =
  Extract.zero at targs;
  let values =
    Extract.one at values_input |> Value.get_list |> List.map bigint_of_value
  in
  let sum = List.fold_left Bigint.( + ) Bigint.zero values in
  Value.nat sum

(* dec $max(nat* ) : nat *)

let max (at : region) (targs : targ list) (values_input : value list) : value =
  Extract.zero at targs;
  let values =
    Extract.one at values_input |> Value.get_list |> List.map bigint_of_value
  in
  let max = List.fold_left Bigint.max Bigint.zero values in
  Value.nat max

(* dec $min(nat* ) : nat *)

let min (at : region) (targs : targ list) (values_input : value list) : value =
  Extract.zero at targs;
  let values =
    Extract.one at values_input |> Value.get_list |> List.map bigint_of_value
  in
  let min = List.fold_left Bigint.min Bigint.zero values in
  Value.nat min
