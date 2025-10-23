open Util.Source
open Il.Ast

type t = at:region -> targ list -> value list -> (Value.t, Err.t) result

let ( let* ) = Result.bind

module Extract = struct
  let extract_targs (n : int) (at : region) (targs : targ list) :
      (unit, Err.t) result =
    if List.length targs = n then Ok ()
    else
      Error
        (Err.arity at
           (Printf.sprintf "Expected %d type arguments, got %d" n
              (List.length targs)))

  let extract_values (n : int) (at : region) (values : value list) :
      (value list, Err.t) result =
    if List.length values = n then Ok values
    else
      Error
        (Err.arity at
           (Printf.sprintf "Expected %d value arguments, got %d" n
              (List.length values)))

  let extract ~(targs_num : int) ~(args_num : int) (at : region)
      (targs : targ list) (values : value list) :
      (unit * value list, Err.t) result =
    let* () = extract_targs targs_num at targs in
    let* vs = extract_values args_num at values in
    Ok ((), vs)
end

let make_zero_arg (impl : at:region -> (Value.t, Err.t) result) : t =
 fun ~at targs values ->
  let* (), _ = Extract.extract ~targs_num:0 ~args_num:0 at targs values in
  impl ~at

let make_one_arg (p1 : 'a Parse.t)
    (impl : at:region -> 'a -> (Value.t, Err.t) result) : t =
 fun ~at targs values ->
  let* (), vs = Extract.extract ~targs_num:0 ~args_num:1 at targs values in
  match vs with
  | [ v1 ] ->
      let* arg1 = p1 at v1 in
      impl ~at arg1
  | _ ->
      Error
        (Err.arity at
           (Printf.sprintf "Expected 1 argument, got %d" (List.length vs)))

let make_two_args (p1 : 'a Parse.t) (p2 : 'b Parse.t)
    (impl : at:region -> 'a -> 'b -> (Value.t, Err.t) result) : t =
 fun ~at targs values ->
  let* (), vs = Extract.extract ~targs_num:0 ~args_num:2 at targs values in
  match vs with
  | [ v1; v2 ] ->
      let* arg1 = p1 at v1 in
      let* arg2 = p2 at v2 in
      impl ~at arg1 arg2
  | _ ->
      Error
        (Err.arity at
           (Printf.sprintf "Expected 2 arguments, got %d" (List.length vs)))

let make_three_args (p1 : 'a Parse.t) (p2 : 'b Parse.t) (p3 : 'c Parse.t)
    (impl : at:region -> 'a -> 'b -> 'c -> (Value.t, Err.t) result) : t =
 fun ~at targs values ->
  let* (), vs = Extract.extract ~targs_num:0 ~args_num:3 at targs values in
  match vs with
  | [ v1; v2; v3 ] ->
      let* arg1 = p1 at v1 in
      let* arg2 = p2 at v2 in
      let* arg3 = p3 at v3 in
      impl ~at arg1 arg2 arg3
  | _ ->
      Error
        (Err.arity at
           (Printf.sprintf "Expected 3 arguments, got %d" (List.length vs)))

let make_one_targ_one_arg (p1 : 'a Parse.t)
    (impl : at:region -> targ -> 'a -> (Value.t, Err.t) result) : t =
 fun ~at targs values ->
  let* (), vs = Extract.extract ~targs_num:1 ~args_num:1 at targs values in
  match (targs, vs) with
  | [ targ1 ], [ v1 ] ->
      let* arg1 = p1 at v1 in
      impl ~at targ1 arg1
  | _ ->
      Error
        (Err.arity at
           (Printf.sprintf
              "Expected 1 type argument and 1 value argument, got %d type \
               arguments and %d value arguments"
              (List.length targs) (List.length vs)))

let make_one_targ_two_args (p1 : 'a Parse.t) (p2 : 'b Parse.t)
    (impl : at:region -> targ -> 'a -> 'b -> (Value.t, Err.t) result) : t =
 fun ~at targs values ->
  let* (), vs = Extract.extract ~targs_num:1 ~args_num:2 at targs values in
  match (targs, vs) with
  | [ targ1 ], [ v1; v2 ] ->
      let* arg1 = p1 at v1 in
      let* arg2 = p2 at v2 in
      impl ~at targ1 arg1 arg2
  | _ ->
      Error
        (Err.arity at
           (Printf.sprintf
              "Expected 1 type argument and 2 value arguments, got %d type \
               arguments and %d value arguments"
              (List.length targs) (List.length vs)))

let make_two_targs_one_arg (p1 : 'a Parse.t)
    (impl : at:region -> targ -> targ -> 'a -> (Value.t, Err.t) result) : t =
 fun ~at targs values ->
  let* (), vs = Extract.extract ~targs_num:2 ~args_num:1 at targs values in
  match (targs, vs) with
  | [ targ1; targ2 ], [ v1 ] ->
      let* arg1 = p1 at v1 in
      impl ~at targ1 targ2 arg1
  | _ ->
      Error
        (Err.arity at
           (Printf.sprintf
              "Expected 2 type arguments and 1 value argument, got %d type \
               arguments and %d value arguments"
              (List.length targs) (List.length vs)))

let make_two_targs_two_args (p1 : 'a Parse.t) (p2 : 'b Parse.t)
    (impl : at:region -> targ -> targ -> 'a -> 'b -> (Value.t, Err.t) result) :
    t =
 fun ~at targs values ->
  let* (), vs = Extract.extract ~targs_num:2 ~args_num:2 at targs values in
  match (targs, vs) with
  | [ targ1; targ2 ], [ v1; v2 ] ->
      let* arg1 = p1 at v1 in
      let* arg2 = p2 at v2 in
      impl ~at targ1 targ2 arg1 arg2
  | _ ->
      Error
        (Err.arity at
           (Printf.sprintf
              "Expected 2 type arguments and 2 value arguments, got %d type \
               arguments and %d value arguments"
              (List.length targs) (List.length vs)))

let make_two_targs_three_args (p1 : 'a Parse.t) (p2 : 'b Parse.t)
    (p3 : 'c Parse.t)
    (impl :
      at:region -> targ -> targ -> 'a -> 'b -> 'c -> (Value.t, Err.t) result) :
    t =
 fun ~at targs values ->
  let* (), vs = Extract.extract ~targs_num:2 ~args_num:3 at targs values in
  match (targs, vs) with
  | [ targ1; targ2 ], [ v1; v2; v3 ] ->
      let* arg1 = p1 at v1 in
      let* arg2 = p2 at v2 in
      let* arg3 = p3 at v3 in
      impl ~at targ1 targ2 arg1 arg2 arg3
  | _ ->
      Error
        (Err.arity at
           (Printf.sprintf
              "Expected 2 type arguments and 3 value arguments, got %d type \
               arguments and %d value arguments"
              (List.length targs) (List.length vs)))
