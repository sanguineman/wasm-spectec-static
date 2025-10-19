open Types
open Util.Source

type t = value

(* Ticker for node identifier tracking *)

let compare = compare
let to_string t = Print.string_of_value t
let eq (value_l : t) (value_r : t) : bool = compare value_l value_r = 0
let tick = ref 0
let refresh () = tick := 0
let fresh () =
  let id = !tick in
  tick := id + 1;
  id

let with_fresh_val (typ : typ') : vnote =
  let vid = fresh () in
  { vid; typ }

let with_typ (typ : typ') (v : value') : t = v $$$ with_fresh_val typ

let get_bool (value : t) =
  match value.it with BoolV b -> b | _ -> failwith "get_bool"

let get_num (value : t) =
  match value.it with NumV n -> n | _ -> failwith "get_num"

let get_text (value : t) =
  match value.it with TextV s -> s | _ -> failwith "get_text"

let get_list (value : t) =
  match value.it with ListV values -> values | _ -> failwith "unseq"

let get_opt (value : t) =
  match value.it with OptV value -> value | _ -> failwith "get_opt"

let get_struct (value : t) =
  match value.it with StructV fields -> fields | _ -> failwith "get_struct"

let bool (b : bool) : t = BoolV b |> with_typ BoolT
let nat (i : Bigint.t) : t = NumV (`Nat i) |> with_typ (NumT `NatT)
let int (i : Bigint.t) : t = NumV (`Int i) |> with_typ (NumT `IntT)
let text (s : string) : t = TextV s |> with_typ TextT

let tuple (vs : t list) : t =
  let typs = List.map (fun v -> v.note.typ $ no_region) vs in
  TupleV vs |> with_typ (TupleT typs)
let opt (typ : typ') (v : t option) : t =
  OptV v |> with_typ (IterT (typ $ no_region, Opt))
let list (typ : typ') (vs : t list) : t =
  ListV vs |> with_typ (IterT (typ $ no_region, List))
