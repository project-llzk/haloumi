# haloumi-ir-gen

This crate defines types and traits for handling the IR generation step that transforms 
a circuit synthesis into a *computer program-like* representation of the circuit.

The IR is generated in two phases; unresolved IR and resolved IR. Unresolved IR uses the Halo2 `Expression` 
type for the gate polynomials. That type defines reads to cells as queries relative to the current row. That is the
reason is considered unresolved since it depends on the circuit synthesis region information for representing 
the whole semantic information of the circuit. Resolved IR uses an expression type that does not depend on the 
circuit synthesis and is decoupled from the lifetime of the synthesis.

The lowering pipeline at this point takes the circuit synthesis and generates the unresolved IR. At that point 
the user can inject additional IR that can be used for encoding information that helps backends that may not be 
directly represented by the IR generated from the circuit synthesis.

The unresolved IR is then resolved, untying it from the synthesis lifetime and it can be sent further down the pipeline.
