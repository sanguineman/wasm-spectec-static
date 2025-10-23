open Xl
open Il.Ast
open Util.Source

(* dec $int_to_text(int) : text *)

let int_to_text (at : region) (targs : targ list) (values_input : value list) :
    value =
  Extract.zero at targs;
  let num = Extract.one at values_input |> Value.get_num in
  Num.string_of_num num |> Value.text

let int_to_text_impl ~at (num : Bigint.t) : (Value.t, Err.t) result =
  at |> ignore;
  Ok (Value.text (Bigint.to_string num))

(* dec $strip_prefix(text, text) : text *)

let strip_prefix (at : region) (targs : targ list) (values_input : value list) :
    value =
  Extract.zero at targs;
  let value_text, value_prefix = Extract.two at values_input in
  let text = Value.get_text value_text in
  let prefix = Value.get_text value_prefix in
  assert (String.starts_with ~prefix text);
  let text =
    String.sub text (String.length prefix)
      (String.length text - String.length prefix)
  in
  Value.text text

let strip_prefix_impl ~at (text : string) (prefix : string) :
    (Value.t, Err.t) result =
  if String.starts_with ~prefix text then
    let new_text =
      String.sub text (String.length prefix)
        (String.length text - String.length prefix)
    in
    Ok (Value.text new_text)
  else
    (* Return a safe, explicit error *)
    let msg =
      Printf.sprintf "strip_prefix: text %S does not start with prefix %S" text
        prefix
    in
    Error (Err.runtime at msg)

(* dec $strip_suffix(text, text) : text *)

let strip_suffix (at : region) (targs : targ list) (values_input : value list) :
    value =
  Extract.zero at targs;
  let value_text, value_suffix = Extract.two at values_input in
  let text = Value.get_text value_text in
  let suffix = Value.get_text value_suffix in
  assert (String.ends_with ~suffix text);
  let text = String.sub text 0 (String.length text - String.length suffix) in
  Value.text text

let strip_suffix_impl ~at (text : string) (suffix : string) :
    (Value.t, Err.t) result =
  if String.ends_with ~suffix text then
    let new_text =
      String.sub text 0 (String.length text - String.length suffix)
    in
    Ok (Value.text new_text)
  else
    (* Return a safe, explicit error *)
    let msg =
      Printf.sprintf "strip_suffix: text %S does not end with suffix %S" text
        suffix
    in
    Error (Err.runtime at msg)

let builtins =
  [
    ("int_to_text", Define.make_one_arg Parse.int int_to_text_impl);
    ( "strip_prefix",
      Define.make_two_args Parse.text Parse.text strip_prefix_impl );
    ( "strip_suffix",
      Define.make_two_args Parse.text Parse.text strip_suffix_impl );
  ]
