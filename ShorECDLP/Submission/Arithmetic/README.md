# Arithmetic

This directory contains the verified reversible field-arithmetic stack used by the
secp256k1 submission. Registers are `List Wire` values in least-significant-bit-first
order. Multi-register programs take those lists as separate arguments rather than packing
bit positions into tuples. The arithmetic circuits are deliberately textbook and generic
in the modulus; `Secp256k1Instance.lean` supplies their concrete 257-bit allocation at the
field prime `p`.

Every composite operation is proved against the classical basis-state semantics and
packages correctness, locality, T-count, H/P-freedom, and gate well-formedness for the
same circuit term.

Each Lean file starts with a self-contained module header in the same order: the program in
syntax-sugared pseudocode, its public specification, and then the implementation and proof
details. Interface-only files explicitly say that they introduce no concrete circuit.

## Readable circuit and assertion syntax

Concrete circuits use the `circuit!` term syntax from `Framework/InstructionSet.lean`.
Semicolon-separated lines execute from top to bottom, `gate!` embeds a primitive gate, and any
ordinary line may itself be a complete circuit. This makes certified subprograms nest without
exposing `List` append plumbing:

```lean
def modAdd ... : Circuit :=
  let compute := modAddCompute ...
  circuit! {
    compute;
    selectPoint flag sum candidate out;
    compute.reverse
  }
```

This is a pure term macro: it expands to the existing `Circuit = List Gate` constructors and
appends, with no second program AST or evaluator.

Correctness statements can open `ArithmeticNotation` and write `st⟦ᵣws⟧` for
`regValue ws st` and `clean(ws, st)` for `Clean ws st`. Together with the existing classical
execution notation `⟪program⟫ st`, a post-state register read is
`(⟪program⟫ st)⟦ᵣlayout.out⟧`. All three forms expand directly to the original terms, so the
stored propositions are unchanged.

For a bottom-up explanation of the construction and proofs, see
[Verified Reversible Arithmetic for Shor ECDLP](../../../docs/ARITHMETIC.md).

## Import dependency DAG

The graph below shows direct project-local Lean imports. An arrow `A --> B` means that
`B` imports `A`. Mathlib imports and the root `ShorECDLP.lean` aggregator are omitted.

```mermaid
flowchart LR
  Semantics["Framework/Classical/Semantics.lean"]
  CostModel["Framework/CostModel.lean"]
  Field["Submission/Field.lean"]

  Adder["Adder.lean"]
  Contracts["Contracts.lean"]
  Ripple["RippleAdder.lean"]
  Primitives["Primitives.lean"]
  InPlaceAdder["InPlaceAdder.lean"]
  InPlaceModular["InPlaceModular.lean"]
  LowSpaceModMul["LowSpaceModMul.lean"]
  Predicates["Predicates.lean"]
  ModAdd["ModAdd.lean"]
  ModSub["ModSub.lean"]
  ModMul["ModMul.lean"]
  ModExp["ModExp.lean"]
  FermatInv["FermatInv.lean"]
  Instance["Secp256k1Instance.lean"]

  Semantics --> Adder
  CostModel --> Adder
  Semantics --> Contracts
  CostModel --> Contracts
  Adder --> Ripple
  Contracts --> Primitives
  Ripple --> Primitives
  Primitives --> InPlaceAdder
  Primitives --> Predicates
  Contracts --> ModAdd
  Ripple --> ModAdd
  Primitives --> ModAdd
  ModAdd --> ModSub
  Primitives --> ModMul
  InPlaceAdder --> InPlaceModular
  ModSub --> InPlaceModular
  ModMul --> InPlaceModular
  InPlaceModular --> LowSpaceModMul
  Primitives --> ModExp
  Contracts --> FermatInv
  Field --> FermatInv
  ModAdd --> Instance
  LowSpaceModMul --> Instance
  ModExp --> Instance
  FermatInv --> Instance
```

The mathematical construction has an additional contract-composition DAG. These arrows
are values and proofs supplied to plans, not Lean imports: higher layers do not import a
lower layer's private carry or workspace implementation.

```mermaid
flowchart LR
  Add["modAdd_contract"]
  LegacyMul["ModMul.Plan.modMul_contract"]
  LowMul["LowSpaceModMul.modMul_contract"]
  Exp["ModExp.Plan.modExp_contract"]
  Inv["FermatInv.correct"]
  Instance["Secp256k1Instance.secpProgram"]

  Add -->|ModAddContract| LegacyMul
  LegacyMul -->|ModMulContract| Exp
  LowMul -->|ModMulContract| Exp
  Exp -->|ModExpContract at p, exponent p - 2| Inv
  Add -->|fixed 257-bit wiring| Instance
  LowMul -->|fixed 257-bit layout| Instance
  Exp -->|fixed 257-bit schedule| Instance
  Inv -->|same-program specialization| Instance
```

## Files and public boundaries

| File | Role | Main public boundary |
| --- | --- | --- |
| [`Contracts.lean`](Contracts.lean) | Defines LSB-first public register layouts and the clean out-of-place interface shared by modular operations. | `RegisterLayout`, `CleanBinaryContract`, `ModAddContract`, `ModSubContract`, `ModMulContract`, `ModExpContract` |
| [`Adder.lean`](Adder.lean) | One-bit reversible full-adder cell over `CX` and `CCX`. | `fullAdder`, `fullAdder_sum`, `fullAdder_carry`, `fullAdder_tCount` |
| [`RippleAdder.lean`](RippleAdder.lean) | Chains full-adder cells into an n-bit ripple-carry adder. | `ripple`, `ripple_correct`, `ripple_tCount`, `ripple_HPFree`, `ripple_wellFormed` |
| [`Primitives.lean`](Primitives.lean) | Reusable implementation-neutral leaves: constant loading, controlled selection, register copying, support lemmas, and reverse-circuit cancellation. | `loadConst`, `selectPoint`, `copyReg`, `Arithmetic.run_reverse_cancel` |
| [`InPlaceAdder.lean`](InPlaceAdder.lean) | Cuccaro majority/unmajority addition into an existing target with one reusable carry wire. | `inPlaceAddCarry`, `inPlaceAddCarry_correct`, `inPlaceAddCarry_tCount` |
| [`InPlaceModular.lean`](InPlaceModular.lean) | Reversible in-place subtraction, comparison, modular doubling, and controlled modular addition using one reusable width-sized mask. | `modularDouble`, `modularDouble_correct`, `controlledModAdd`, `controlledModAdd_correct` |
| [`LowSpaceModMul.lean`](LowSpaceModMul.lean) | MSB-first Horner modular multiplication using two reusable width-sized work registers and three flag bits. | `LowSpaceModMul.program`, `LowSpaceModMul.program_correct`, `LowSpaceModMul.program_tCount`, `LowSpaceModMul.modMul_contract`, `LowSpaceModMul.layout_allWires_length` |
| [`Predicates.lean`](Predicates.lean) | Bennett-clean reversible zero and equality flags over `X`, `CX`, and `CCX`. | `zeroFlag`, `zeroFlag_correct`, `equalFlag`, `equalFlag_correct` |
| [`ModAdd.lean`](ModAdd.lean) | Adds two registers modulo an arbitrary positive modulus using ripple addition, one conditional reduction, and uncomputation. | `modAdd`, `modAdd_program_correct`, `modAdd_tCount`, `modAdd_contract` |
| [`ModSub.lean`](ModSub.lean) | Subtracts two registers modulo an arbitrary positive modulus using two's-complement ripple subtraction, conditional correction, and uncomputation. | `modSub`, `modSub_program_correct`, `modSub_tCount`, `modSub_contract` |
| [`ModMul.lean`](ModMul.lean) | Generic Bennett-clean schoolbook multiplier retained as a compositional reference implementation. | `ModMul.Plan.program`, `ModMul.Plan.program_correct`, `ModMul.Plan.program_tCount`, `ModMul.Plan.modMul_contract` |
| [`ModExp.lean`](ModExp.lean) | Bennett-clean, LSB-first square-and-multiply built from certified modular-multiplication calls. | `ModExp.Plan.program`, `ModExp.Plan.program_correct`, `ModExp.Plan.program_tCount`, `ModExp.Plan.program_tCount_eq_of_uniform`, `ModExp.Plan.modExp_contract` |
| [`FermatInv.lean`](FermatInv.lean) | Thin field-specific correctness closure: exponentiation by `p - 2` computes inversion in `Fp`. It defines no second circuit. | `FermatInv.correct` |
| [`Secp256k1Instance.lean`](Secp256k1Instance.lean) | Concrete block allocation for the width-257 secp256k1 modular adder, 1,288-wire low-space multiplier, exponentiator, and Fermat inversion specialization. | `addProgram_correct`, `addProgram_tCount`, `mulProgram_correct`, `mulProgram_tCount`, `secpMulLayout_allWires_length`, `secpAddProgram_correct`, `secpAddProgram_tCount`, `secpMulProgram_correct`, `secpMulProgram_tCount`, `secpProgram_correct`, `secpProgram_tCount`, `secp_fermat_inverse` |

## Contract discipline

`CleanBinaryContract program layout modulus op cost` binds all obligations to the exact
same `program`:

- `layout.lhs` and `layout.rhs` have equal width, are preserved, and contain canonical
  inputs below `modulus`;
- `layout.out` starts clean and receives `op lhs rhs mod modulus`;
- private `layout.work` wires start and finish clean;
- every control and target belongs to `layout.allWires` (`CircuitUsesOnly`);
- `tCount program = cost`;
- `program` is H/P-free and physically well-formed.

`ModMul.Plan` and `ModExp.Plan` use a Bennett compute-copy-uncompute wrapper: build the
forward history, copy the result to a disjoint public output, and run the history in
reverse. The concrete secp256k1 instance instead supplies `LowSpaceModMul.program` to
`ModExp`: it updates a clean output by reversible Horner steps and restores one modulus
register, one mask, and three flag wires after every call.

## Suggested reading order

1. [`Contracts.lean`](Contracts.lean) for the interface and invariants.
2. [`Adder.lean`](Adder.lean) and [`RippleAdder.lean`](RippleAdder.lean) for the bit-level
   arithmetic base.
3. [`Primitives.lean`](Primitives.lean) for the shared reversible-circuit tools.
4. [`InPlaceAdder.lean`](InPlaceAdder.lean), [`InPlaceModular.lean`](InPlaceModular.lean), and
   [`LowSpaceModMul.lean`](LowSpaceModMul.lean) for the active low-space multiplication path.
5. [`Predicates.lean`](Predicates.lean) for clean reversible zero/equality flags.
6. [`ModAdd.lean`](ModAdd.lean), [`ModSub.lean`](ModSub.lean), [`ModMul.lean`](ModMul.lean), and
   [`ModExp.lean`](ModExp.lean) for the modular construction and reference-plan interfaces.
7. [`FermatInv.lean`](FermatInv.lean) for the generic secp256k1 field-inversion closure.
8. [`Secp256k1Instance.lean`](Secp256k1Instance.lean) for the concrete 257-bit plans, allocation,
   exact numeric costs, and same-program inversion specialization.

Run the complete repository proof gate from the repository root with:

```sh
./scripts/verify.sh
```
