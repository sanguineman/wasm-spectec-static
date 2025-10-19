include Core.Types

include Core.Effects

module Print = Core.Print

module Eq = Core.Eq

module Free = Core.Free

module Value = struct
  include Core.Value (* Constructors from value.ml *)
  
  let compare = compare
end
