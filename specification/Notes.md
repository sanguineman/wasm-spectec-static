# WebAssembly static semantics in P4-SpecTec

## Notes
This section records several issues encountered and design decisions made accordingly while writing the static semantics of WebAssembly in P4-SpecTec.

1. syntax declaration with type parameters (dependent types declaration)
To the best of my knowledge, P4-SpecTec does not support dependent types. For example, the following kind of parameterized syntax declaration—possible in Wasm-SpecTec—is not supported:
```
syntax binop_(numtype)
syntax binop_(Inn) =
  | ADD | SUB | MUL | DIV sx | ...
syntax binop_(Fnn) =
  | ADD | SUB | MUL | DIV | ...
```

However, while inspecting spectec/lib/lang/el/types.ml, I found that there exists a syntax that appears to allow type parameters in syntax declaration, as shown below:
```spectec
(* Definitions *)

type def = def' phrase
and def' =
  (* `syntax` list(id `<` list(tparam, `,`) `>`, `,`) *)
  | SynD of (id * tparam list) list
  | ...
```

Motivated by the concrete syntax described in the comment above, I attempted to encode the binop syntax using type parameters in P4-SpecTec as follows:
```spectec
syntax binop_<numtype> ;; unexpected token error here
syntax binop_<numtype> =
  | ADD | SUB | MUL | DIV sx | ...
syntax binop_<numtype> =
  | ADD | SUB | MUL | DIV | ...
```

However, this fails to parse with an "unexpected token" error at the first line. This seems to occur because of the parser
bug in P4-SpecTec that does not recognize type parameters in syntax declaration.
However, this fails to parse, producing an “unexpected token” error at the first line. This suggests that the current P4-SpecTec parser does not properly recognize type parameters in syntax declarations, despite the apparent support in the AST definition.

To work around this issue, I defined separate syntax for integer and float binops as follows:
```spectec
syntax ibinop =
  | IADD | ISUB | IMUL | IDIV sx | ...
syntax fbinop =
  | FADD | FSUB | FMUL | FDIV | ...
```



