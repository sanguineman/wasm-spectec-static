(** The IL Abstract Syntax Tree and Core API. This module is the main entry
    point for IL. *)

include module type of Core.Types
include module type of Core.Effects
module Print : module type of Core.Print
module Eq : module type of Core.Eq
module Free : module type of Core.Free

(** Constructors and operations on IL Values. *)
module Value : sig
  include module type of Core.Value

  val to_string : value -> string
  val compare : value -> value -> int
end
