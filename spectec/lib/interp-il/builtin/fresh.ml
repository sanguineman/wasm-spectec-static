open Il.Ast
open Util.Source

(* dec $fresh_tid() : tid *)

let fresh_tid_impl ~at : (Value.t, Err.t) result =
  at |> ignore;
  let tid = Effect.perform FreshTid () in
  let typ = Il.Ast.VarT ("tid" $ no_region, []) in
  Ok (Value.Make.text typ tid)

let builtins = [ ("fresh_tid", Define.make_zero_arg fresh_tid_impl) ]
