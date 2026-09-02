# Verified Reversible Arithmetic for Shor ECDLP

## A bottom-up textbook for the `ShorECDLP` Lean development

**Audience.** This text assumes the background of a senior undergraduate in computer science: binary arithmetic, modular arithmetic, basic algorithms and data structures, and some exposure to mathematical proofs. Prior knowledge of Lean or quantum computing is helpful but not required.

**Source snapshot.** The technical statements in this book describe `VerifiedQC/ShorECDLP` at green `main` commit `83cac4fd9b757c6e790fa52346dc11c33d7aadde` (August 2026). Declaration names are included so that every important claim can be located in the source.

**Scope.** The center of the book is the completed M1 arithmetic stack:

```text
reversible gates
    -> one-bit full adder
    -> n-bit ripple-carry adder
    -> modular addition
    -> modular multiplication
    -> modular exponentiation
    -> Fermat inversion in the secp256k1 field
```

The final chapters explain the mathematical elliptic-curve boundary that has already landed—secp256k1 constants, its point type, verified doubling tables, and a conditional two-register order-finding theorem over an abstract oracle—and the still-unimplemented circuit layers: a concrete point encoding, point addition, scalar multiplication, and the concrete ECDLP oracle.

---

## Contents

1. [What is being verified?](#1-what-is-being-verified)
2. [The machine model: wires, gates, states, and costs](#2-the-machine-model-wires-gates-states-and-costs)
3. [The contract that makes arithmetic compositional](#3-the-contract-that-makes-arithmetic-compositional)
4. [The one-bit reversible full adder](#4-the-one-bit-reversible-full-adder)
5. [The ripple-carry adder](#5-the-ripple-carry-adder)
6. [Reusable reversible primitives and Bennett cleanup](#6-reusable-reversible-primitives-and-bennett-cleanup)
7. [Modular addition](#7-modular-addition)
8. [Modular multiplication](#8-modular-multiplication)
9. [Modular exponentiation](#9-modular-exponentiation)
10. [Fermat inversion over the Bitcoin field](#10-fermat-inversion-over-the-bitcoin-field)
11. [The elliptic-curve boundary](#11-the-elliptic-curve-boundary)
12. [How the proofs compose](#12-how-the-proofs-compose)
13. [Cost derivations and a secp256k1-sized illustration](#13-cost-derivations-and-a-secp256k1-sized-illustration)
14. [What is proved, assumed, and still missing](#14-what-is-proved-assumed-and-still-missing)
15. [Reading the Lean source](#15-reading-the-lean-source)
16. [Glossary and review questions](#16-glossary-and-review-questions)

---

# Part I — Foundations

## 1. What is being verified?

The eventual goal is a verified implementation of the arithmetic inside Shor's algorithm for the elliptic-curve discrete logarithm problem on secp256k1, the curve used by Bitcoin.

Given a base point `P` and a target point `Q = [k]P`, Shor's ECDLP algorithm needs an oracle that coherently computes

$$
R \longmapsto R + [a]P + [b]Q.
$$

The registers holding `a` and `b` may be in quantum superposition. Therefore the arithmetic underneath the oracle cannot be an ordinary destructive program. It must be implemented as a **well-formed, H/P-free** reversible arithmetic circuit: its classical gate action is a bijection on bit strings, and its quantum lift preserves inner products.

The repository follows a deliberately conservative strategy:

- use a very small primitive gate set;
- build textbook, unoptimized arithmetic from those gates;
- prove functional correctness and resource cost about the exact same circuit term;
- restore all private scratch bits so that higher layers can reuse them safely;
- keep mathematical assumptions visible in theorem signatures;
- refuse `sorry`, `admit`, `native_decide`, or new unreviewed axioms in delivered code.

This is not an optimization project yet. It is a proof-carrying baseline: a simple implementation whose meaning and cost can be audited from the bottom up.

### 1.1 Four different questions

It is useful to separate four questions that are often blurred together.

1. **Does the circuit compute the intended function?**

   Example: does the modular multiplier output `x * y mod p`?

2. **Does it restore its inputs and private workspace as promised?**

   A numerically correct output is not enough if garbage remains entangled with it.

3. **Is the circuit physically meaningful?**

   A malformed `CX q q` is not an invertible controlled-NOT. Control and target roles must use distinct wires.

4. **What does the exact circuit cost under the chosen metric?**

   The repository uses a simple T-count model. It does not infer cost from a prose algorithm.

The public arithmetic contracts answer all four questions about one concrete `program`.

### 1.2 What “verified” means here

For the M1 arithmetic modules, “verified” means that Lean checks proofs of:

- basis-state functional correctness;
- preservation of public inputs;
- cleanup of declared work registers;
- confinement to declared wires;
- exact T-count;
- absence of `H` and `P` gates, so the classical semantics is faithful;
- gate-level well-formedness, so the quantum semantics preserves inner products.

Later, the theorem `Quantum.run_ket_agrees_classical` transports the basis-state arithmetic result into the quantum semantics. The arithmetic is not re-proved with complex amplitudes.

### 1.3 A status warning

The arithmetic stack is parametric in register layouts and certified subcircuits. It proves that every valid plan has the advertised behavior and cost. The current `main` branch does **not** yet assemble a concrete, end-to-end secp256k1 point-addition or ECDLP-oracle circuit with a final wire allocation. Numerical examples in this book are therefore evaluations of proved symbolic formulas, not a claim that a complete oracle instance already exists.

---

## 2. The machine model: wires, gates, states, and costs

The relevant framework files are:

- `ShorECDLP/Framework/InstructionSet.lean`
- `ShorECDLP/Framework/CostModel.lean`
- `ShorECDLP/Framework/BasisState.lean`
- `ShorECDLP/Framework/Classical/Semantics.lean`
- `ShorECDLP/Framework/Quantum/Semantics.lean`
- `ShorECDLP/Framework/Quantum/InnerProduct.lean`

### 2.1 Wires and circuits

A wire is just a natural-number index:

```lean
abbrev Wire := Nat
```

A circuit is a straight-line list of primitive gates:

```lean
abbrev Circuit := List Gate
```

Composite definitions use `circuit! { ... }` as step-by-step syntax over that same list type:

```lean
def cleanedProgram (compute select : Circuit) : Circuit :=
  circuit! {
    compute;
    select;
    compute.reverse
  }
```

Lines execute from top to bottom. An ordinary line is a nested `Circuit`; a `gate!` line embeds
one primitive gate. The syntax is a term macro that emits only the existing list constructors
and appends—there is no separate statement language, interpreter, or cost semantics.

The primitive gate family is:

| Gate | Informal action | Arithmetic role |
| --- | --- | --- |
| `X t` | flip bit `t` | load constants, initialize `1` |
| `CX c t` | flip `t` if `c = 1` | XOR, copy into a clean target |
| `CCX a b t` | flip `t` if `a = b = 1` | AND-controlled updates; the nonlinear arithmetic primitive |
| `H t` | Hadamard | quantum superposition; not used by arithmetic |
| `P dir k t` | phase by `±2π/2^k` | QFT phase; not used by arithmetic |

All arithmetic circuits use only `X`, `CX`, and `CCX`.

### 2.2 Basis states

A computational basis state assigns one Boolean to every wire:

```lean
abbrev BasisState := Wire -> Bool
```

Only finitely many wires are touched by a finite circuit, but the total function makes it easy to discuss a circuit placed inside a larger machine.

The update notation

```lean
s[i ↦ b]
```

means: return the same state as `s`, except wire `i` now contains `b`.

### 2.3 Registers are little-endian wire lists

A register is represented by a list of wire indices. The first wire is the least-significant bit. Its value is:

```lean
def regValue : List Wire -> BasisState -> Nat
  | [],      _ => 0
  | w :: ws, s => (if s w then 1 else 0) + 2 * regValue ws s
```

After `open scoped ArithmeticNotation`, specifications write the same term as `st⟦ᵣws⟧`.
Clean-register assertions use `clean(ws, st)`, and classical execution already has the notation
`⟪c⟫ st`. Thus `(⟪c⟫ st)⟦ᵣout⟧` means the value of `out` after running `c`. These are parse-time
notations only; they do not wrap or alter the stored propositions.

For example, let `r = [10, 11, 12]`. If wires `10`, `11`, and `12` contain `true`, `false`, and `true`, then

$$
\operatorname{regValue}(r) = 1 + 2\cdot 0 + 4\cdot 1 = 5.
$$

This little-endian convention is used consistently by the ripple adder, schoolbook multiplication, square-and-multiply exponentiation, and doubling tables.

`writeReg ws n s` recursively writes the low `ws.length` bits of `n` into `ws`. For a duplicate-free register, this has the expected fixed-width behavior: reading back the low bits gives reduction modulo `2^width`. The duplicate-free qualification matters—a repeated wire can be overwritten later in the recursion. `ShorECDLP/Framework/BasisState.lean` deliberately keeps this primitive API small; the order-finding proof layer proves the fitting-value and restoration lemmas it needs. A concrete oracle will still need a circuit-specific whole-state bridge from its arithmetic contracts to the required `writeReg` equality.

### 2.4 Classical execution

`Classical.applyGate` gives a bit-string action to each primitive gate, and `Classical.run` folds a circuit from left to right.

For `X`, `CX`, and `CCX`, this is the genuine reversible action. For `H` and `P`, the classical semantics uses an identity placeholder merely to keep the function total. Consequently, a correctness proof against `Classical.run` is meaningful only when the circuit contains no `H` or `P`.

That restriction is recorded by:

```lean
def Classical.HPFree (c : Circuit) : Prop :=
  forall g in c, g is X, CX, or CCX
```

The actual definition is expressed through `Classical.IsClassicalGate`, but the idea is exactly “no Hadamard or phase gates.”

### 2.5 Well-formedness is a separate property

`CircuitWellFormed c` says every primitive gate assigns distinct wires to distinct logical roles:

- `CX c t` requires `c ≠ t`;
- `CCX a b t` requires `a ≠ b`, `a ≠ t`, and `b ≠ t`.

This is not redundant with `HPFree`.

Consider the malformed gate `CX q q`. It is H/P-free, but its classical formula sets

$$
q \leftarrow q \oplus q = 0,
$$

which loses information and is not invertible. Thus:

- **`HPFree`** says the cheap classical semantics agrees with the quantum basis action;
- **`CircuitWellFormed`** says the gate arrangement is physically reversible/unitary.

The two predicates are kept separate throughout the development.

### 2.6 The cost model

The framework's cost function is deliberately simple:

| Gate | `tCost` |
| --- | ---: |
| `X` | 0 |
| `H` | 0 |
| `CX` | 0 |
| `CCX` | 7 |
| `P forward k` or `P inverse k` | 1 |

The circuit cost is the sum:

```lean
def tCount (c : Circuit) : Nat := (c.map tCost).sum
```

For arithmetic, all nonzero cost comes from Toffoli gates. A circuit with `N` Toffolis and no phase gates has T-count `7N` in this model.

This is a baseline metric, not a claim that every hardware platform must synthesize gates this way. A different submission may prove a different resource theorem about the same or another circuit.

### 2.7 Lifting arithmetic to quantum states

The quantum state space is finite-support complex amplitudes over the same `BasisState`. The central bridge is:

```lean
theorem Quantum.run_ket_agrees_classical
    (c : Circuit) (s : BasisState)
    (hc : Classical.HPFree c) :
    Quantum.run c (Quantum.ket s) =
      Quantum.ket (Classical.run c s)
```

This theorem says that an H/P-free circuit acts on each computational-basis ket exactly as `Classical.run` transforms the underlying basis state. Linearity then determines its action on a superposition. H/P-freedom alone does not make that state transformer injective; the separate well-formedness theorem supplies reversibility and physical validity.

Physical norm preservation comes from a different theorem:

```lean
theorem Quantum.run_preservesInner
    (c : Circuit) (hc : CircuitWellFormed c) :
    Quantum.PreservesInner (Quantum.run c)
```

Remember the division of labor:

```text
HPFree             -> classical/quantum agreement
CircuitWellFormed  -> inner-product and norm preservation
```

---

## 3. The contract that makes arithmetic compositional

The key interface is in `ShorECDLP/Submission/Arithmetic/Contracts.lean`.

### 3.1 Public and private registers

A binary arithmetic component exposes four wire blocks:

```lean
structure RegisterLayout where
  lhs  : List Wire
  rhs  : List Wire
  out  : List Wire
  work : List Wire
```

`lhs` and `rhs` are public inputs. `out` is a fresh public output. `work` is private scratch owned by the component.

A valid layout requires:

- `lhs`, `rhs`, and `out` have equal lengths;
- every wire in `lhs ++ rhs ++ out ++ work` is distinct.

The private workspace may have any length. Higher-level algorithms do not need to know its internal shape.

### 3.2 Clean registers

```lean
def Clean (ws : List Wire) (st : BasisState) : Prop :=
  forall w in ws, st w = false
```

`Clean` lives in `ShorECDLP/Framework/BasisState.lean`, where both arithmetic contracts and the abstract oracle can use it without introducing a dependency between those layers.

An out-of-place arithmetic call assumes `out ++ work` starts clean. It must return `work` clean. This is the reversible analogue of a function call receiving zero-initialized scratch and returning it to the allocator.

The output is not required to be cleared afterward—it contains the answer.

### 3.3 The complete binary contract

The generic proposition is:

```lean
CleanBinaryContract program layout modulus op cost
```

Its fields require the following facts about the exact same `program`:

1. **Correctness.** For canonical inputs `lhs < modulus` and `rhs < modulus`, and clean `out ++ work`:

   - `lhs` is preserved;
   - `rhs` is preserved;
   - `out = op(lhs, rhs) mod modulus`;
   - `work` is clean afterward.

2. **Locality.** `CircuitUsesOnly layout.allWires program` records every control and every target used by every gate.

3. **Exact cost.** `tCount program = cost`.

4. **Classical faithfulness.** `Classical.HPFree program`.

5. **Physical validity.** Every valid layout makes `program` well-formed.

The specializations are only names for the mathematical operation:

```lean
ModAddContract  := CleanBinaryContract ... Nat.add
ModMulContract  := CleanBinaryContract ... Nat.mul
ModExpContract  := CleanBinaryContract ... Nat.pow
```

### 3.4 Why locality records controls as well as targets

It is tempting to say that a circuit “uses” only the wires it writes. That is too weak for safe uncomputation.

Suppose a forward computation reads an outside wire as a control. Between the forward pass and its reverse, another component changes that outside wire. The reverse no longer retraces the same path, so scratch may fail to clear.

`CircuitUsesOnly` therefore records all controls and targets. From it, the theorem `CircuitUsesOnly.preservesOutside` derives that every undeclared wire remains unchanged.

### 3.5 The same-program-term discipline

A common specification failure is to prove:

- circuit `A` computes the right function; and
- circuit `B` has the advertised cost;

without proving `A = B`.

`CleanBinaryContract program ...` prevents this drift structurally. Correctness, cleanup, locality, T-count, H/P-freedom, and well-formedness all mention the same `program` parameter.

This discipline is the backbone of the higher layers:

```text
ModAddContract value
    consumed by ModMul.Plan

ModMulContract value
    consumed by ModExp.Schedule

ModExpContract value
    consumed by FermatInv.correct
```

The consumer imports the public contract, not the producer's private carry wiring or proof internals.

### 3.6 What the contract deliberately does not say

The contract does not claim:

- that inputs outside `[0, modulus)` are handled canonically;
- that dirty scratch inputs are accepted;
- that the construction is in-place;
- that its workspace is small;
- that the cost model is hardware-optimal;
- that a concrete secp256k1 wire allocation has already been instantiated.

These omissions are intentional. A strong, honest contract is better than a broad statement whose implementation assumptions are hidden.

---

# Part II — From bits to clean modular addition

## 4. The one-bit reversible full adder

Source: `ShorECDLP/Submission/Arithmetic/Adder.lean`.

### 4.1 The classical full-adder equations

A one-bit full adder receives bits `a`, `b`, and carry-in `cin`. It produces:

$$
s = a \oplus b \oplus cin
$$

and

$$
co = \operatorname{majority}(a,b,cin).
$$

The majority bit can be written using XOR of pairwise conjunctions:

$$
co = (a \land b) \oplus (a \land cin) \oplus (b \land cin).
$$

Why does XOR work rather than OR? If exactly two input bits are `1`, exactly one pairwise conjunction is `1`. If all three are `1`, all three conjunctions are `1`, and `1 xor 1 xor 1 = 1`. In every other case they are all `0`.

The integer identity behind the circuit is:

$$
a+b+cin = s + 2co.
$$

This identity is what the multi-bit proof will sum across columns.

### 4.2 Why fresh output bits are necessary

An ordinary assignment such as `s := a xor b xor cin` destroys the old value of `s`; it is not reversible on all bit strings. The circuit instead XORs the answer into output wires known to start at `0`.

Thus the logical interface is:

```text
(a, b, cin, 0, 0) -> (a, b, cin, sum, carry)
```

The inputs remain available. The two output wires carry the new information required to make the mapping injective.

### 4.3 The exact circuit

The Lean definition is a list of six gates:

```text
fullAdder(a, b, cin; clean s, clean co):
  CCX a   b    co
  CCX a   cin  co
  CCX b   cin  co
  CX  a        s
  CX  b        s
  CX  cin      s
```

The first three gates toggle `co` by the three pairwise products. The last three toggle `s` by the three input bits.

Because `s` and `co` start at `0`, their final values are exactly the intended sum and carry. The input wires appear only as controls and are never modified.

### 4.4 What Lean proves

The public declarations are:

- `fullAdder`
- `fullAdder_sum`
- `fullAdder_carry`
- `fullAdder_tCount`

Under the relevant freshness and distinctness hypotheses:

```text
after[s]  = a XOR b XOR cin
after[co] = (a AND b) XOR (a AND cin) XOR (b AND cin)
```

The proofs reduce the six-gate execution and check the eight possible assignments to `(a,b,cin)`.

### 4.5 Cost

There are three `CCX` gates and three free `CX` gates:

$$
T_{FA} = 3\cdot 7 = 21.
$$

Lean proves the exact equality:

```lean
fullAdder_tCount : tCount (fullAdder a b cin s co) = 21
```

### 4.6 A concrete example

Take `a=1`, `b=0`, and `cin=1`.

- The sum gates toggle `s` twice, so `s=0`.
- Only `a AND cin` is true, so `co=1`.

The integer check is:

$$
1+0+1 = 0 + 2\cdot 1 = 2.
$$

---

## 5. The ripple-carry adder

Source: `ShorECDLP/Submission/Arithmetic/RippleAdder.lean`.

### 5.1 Lining up binary registers

For an `n`-bit addition, the source passes the three little-endian registers separately:

```text
a    = [a_0, a_1, ..., a_(n-1)]
b    = [b_0, b_1, ..., b_(n-1)]
sum  = [sum_0, sum_1, ..., sum_(n-1)]
```

A fourth list supplies fresh carry-out wires `co_i`. The carry-out of bit position `i` becomes the carry-in of bit position `i+1`. Keeping the roles as separate `List Wire` arguments makes the Lean program match the register-level pseudocode directly; no list of tuple-packed columns is constructed.

The circuit is defined recursively:

```text
ripple([], [], [], cin, []) = []

ripple(a_i :: as, b_i :: bs, sum_i :: sums, cin, co_i :: carries) =
  circuit! {
    fullAdder(a_i,b_i,cin; sum_i,co_i);
    ripple(as,bs,sums,co_i,carries)
  }
```

The list order is LSB-first, so the recursive execution follows the direction in which carry information flows.

### 5.2 The main invariant

Let:

- `A` be the register of all `a_i` wires;
- `B` be the register of all `b_i` wires;
- `S` be the register of all `sum_i` wires;
- `C` be the final carry bit;
- `c_0` be the initial carry-in bit.

The theorem `ripple_correct` proves:

$$
S + 2^n C = A + B + c_0.
$$

This statement is stronger and cleaner than only saying `S = (A+B) mod 2^n`. It records the overflow bit too. The modular corollary follows immediately:

$$
S = (A+B+c_0) \bmod 2^n.
$$

For ordinary addition, the initial carry wire is clean, so `c_0=0`.

### 5.3 Why the induction works

At the least-significant column, the full-adder identity is

$$
a_0+b_0+c_0 = s_0 + 2c_1.
$$

The remaining columns satisfy the induction hypothesis

$$
S_{high} + 2^{n-1}C = A_{high}+B_{high}+c_1.
$$

Multiply the second equation by `2` and add the first. The intermediate carry `c_1` appears once on each side and is absorbed into the binary place value. The result is the whole-register identity.

The Lean proof additionally tracks that the first cell leaves all later input and output wires unchanged. That is why `fullAdder_other` and `ripple_other` are important supporting lemmas.

### 5.4 Wire validity

`wiresOK a b sum cin couts` records alignment and the distinctness conditions required by the chain:

- the five roles in each full-adder cell are distinct;
- a cell's new sum/carry outputs do not alias later register positions;
- carry wires are placed consistently;
- later cells cannot overwrite earlier results.

This is more than bookkeeping. It closes two different proof obligations:

- arithmetic preservation facts used by the induction;
- `CircuitWellFormed`, needed for quantum unitarity.

### 5.5 Structural theorems

The public arithmetic and structural results include:

- `ripple_correct`
- `ripple_tCount`
- `ripple_HPFree`
- `ripple_wellFormed`

For `n = a.length` and matching `b`, `sum`, and carry lists:

$$
T_{ripple}(n) = 21n.
$$

The circuit is H/P-free because it is a concatenation of full adders containing only `CX` and `CCX`.

### 5.6 Example: `5 + 3` in four bits

Little-endian bit strings are:

```text
5 = [1,0,1,0]
3 = [1,1,0,0]
```

With initial carry `0`, the columns produce:

| Column | `a_i` | `b_i` | carry in | `s_i` | carry out |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 | 0 | 1 |
| 1 | 0 | 1 | 1 | 0 | 1 |
| 2 | 1 | 0 | 1 | 0 | 1 |
| 3 | 0 | 0 | 1 | 1 | 0 |

Thus `S = [0,0,0,1] = 8` and final carry `0`, so

$$
8 + 2^4\cdot 0 = 5+3.
$$

---

## 6. Reusable reversible primitives and Bennett cleanup

Source: `ShorECDLP/Submission/Arithmetic/Primitives.lean`.

The larger circuits repeatedly need four small ideas: loading a known constant, selecting between two candidates, copying a register, and reversing a computation.

### 6.1 Loading a classical constant

`loadConst ws c` applies `X` to precisely those wires whose corresponding bit of `c` is `1`.

```text
for i in 0 .. width-1:
  if bit(c,i) = 1:
    X ws[i]
```

If `ws` is duplicate-free, the register starts clean, and `c < 2^width`, `loadConst_correct` proves that it holds exactly `c` afterward.

The operation is self-inverse: applying the same X pattern again clears the register. Its T-count is zero because `X` is free in the framework metric.

### 6.2 Copying into a clean register

`copyReg src dst` applies aligned CNOTs:

```text
for (s,d) in zip(src,dst):
  CX s d
```

If `src` and `dst` have equal lengths, `(src ++ dst)` is duplicate-free, and `dst` starts at zero, `copyReg_correct` proves that `dst` ends with the value of `src`; the disjointness facts also give preservation of `src`. This is reversible copying of a computational-basis value, not an unrestricted quantum cloning operation: on a superposition it creates entanglement rather than two independent copies.

The T-count is zero.

### 6.3 Reversible selection

Under `selectOK flag xs ys outs` and a clean output register `outs`, the selector chooses `xs` or `ys` into that output without changing either input. The predicate also records register alignment, makes output wires duplicate-free, and separates the flag, both sources, and outputs in every gate role:

```text
selectBit(flag, x, y; clean out):
  CX  x out
  CX  x y
  CCX flag y out
  CX  x y
```

Trace the two cases.

- If `flag=0`, the `CCX` does nothing. The first `CX` leaves `out=x`, and the final `CX` restores `y`.
- If `flag=1`, the middle value is `y xor x`, so the Toffoli toggles `out` from `x` to `x xor (y xor x) = y`; the final CNOT again restores `y`.

`selectPoint flag xs ys outs` maps this bit selector directly over the three aligned registers. It costs one Toffoli per selected bit:

$$
T_{select}(w) = 7w.
$$

### 6.4 Why simply “running backward” needs hypotheses

All arithmetic primitives are self-adjoint gate types: `X`, `CX`, and `CCX`. For a well-formed H/P-free circuit `c`, the reversed gate list `c.reverse` is its inverse on basis states.

The theorem is `Arithmetic.run_reverse_cancel`:

```text
HPFree(c) and CircuitWellFormed(c)
    -> run(c.reverse, run(c, st)) = st
```

Both hypotheses matter:

- `HPFree` excludes `P`, whose inverse requires changing phase direction rather than merely reversing the list.
- `CircuitWellFormed` excludes aliasing such as `CX q q`, which is not invertible under the classical formula.

For a general quantum circuit, the repository uses `Circuit.adjoint`, which reverses gate order **and** replaces each gate by its adjoint. For arithmetic, `c.reverse` and `c.adjoint` coincide because all used gates are self-adjoint.

### 6.5 Bennett's compute-copy-uncompute pattern

Suppose a reversible forward computation builds a history and leaves the desired result in a register `source`:

```text
(input, 0_work, 0_out)
    --compute-->
(input, history, result, 0_out).
```

If we immediately reverse, the result disappears with the history. Bennett's construction first copies the result to a fresh public output:

```text
compute
copyReg(source, out)
reverse(compute)
```

The state becomes:

```text
(input, 0_work, result_out).
```

The output survives because it is disjoint from every control and target used by `compute`; the reverse pass never touches or reads it.

This pattern is used by modular multiplication and exponentiation. Modular addition uses the closely related pattern “compute both candidates, select into a fresh output, reverse the candidate computation.”

### 6.6 The price of cleanup

If copying is Clifford-only, then:

$$
T_{Bennett} = 2T_{compute}.
$$

The benefit is a simple, reusable contract. The cost is roughly doubling the forward T-count and retaining the entire forward history until copy-out. This implementation favors proof clarity over space efficiency.

---

## 7. Modular addition

Source: `ShorECDLP/Submission/Arithmetic/ModAdd.lean`.

### 7.1 The mathematical problem

Given canonical inputs

$$
0 \le a < M, \qquad 0 \le b < M,
$$

compute

$$
(a+b) \bmod M
$$

while preserving `a` and `b` and restoring all scratch.

The implementation chooses a width `w` satisfying

$$
2M \le 2^w.
$$

Because `a+b < 2M`, the unreduced sum fits in `w` bits. For secp256k1's 256-bit prime, this simple generic construction naturally uses `w=257`: one extra bit avoids overflow before reduction.

This is not a pseudo-Mersenne reduction specialized to the shape of the Bitcoin prime.

### 7.2 Building a constant adder

The helper `addConst` reuses the general ripple adder:

```text
addConst(a, c; out):
  loadConst(cReg, c)
  ripple(a, cReg; out)
  loadConst(cReg, c)       -- clear cReg
```

The two loads are T-free. Therefore:

$$
T_{addConst}(w) = 21w.
$$

### 7.3 Conditional subtraction by adding a complement

Let `s=a+b`. The circuit wants to know whether `s >= M`.

In `w`-bit arithmetic, add the constant

$$
2^w-M.
$$

There are two cases.

**Case 1: `s < M`.**

Then

$$
s + (2^w-M) < 2^w.
$$

The carry-out is `0`. The low `w` bits are a wrapped-looking candidate `s+2^w-M`, but the circuit will ignore it and keep `s`.

**Case 2: `s >= M`.**

Then

$$
s + (2^w-M) \ge 2^w.
$$

The carry-out is `1`, and the low `w` bits are exactly

$$
s-M.
$$

The carry therefore acts as a comparison flag without a separate comparator circuit.

### 7.4 The complete circuit

The forward candidate computation is:

```text
compute(a,b; sum,reduced,flag):
  ripple(a,b; sum)
  addConst(sum, 2^w-M; reduced)
```

Then:

```text
modAdd(a,b; clean out,work):
  compute
  selectPoint(flag, sum, reduced; out)
  reverse(compute)
```

If `flag=0`, the selector copies `sum`. If `flag=1`, it copies `reduced=sum-M`. In both cases:

$$
out = (a+b) \bmod M.
$$

The reverse pass clears `sum`, `reduced`, constant scratch, and carries, but does not erase `out`.

### 7.5 Example: modulo 13

Choose `M=13`. The fit condition needs `2M=26 <= 2^w`, so take `w=5`.

The subtraction constant is:

$$
2^5-13 = 19.
$$

**No reduction needed:** `a=4`, `b=7`, so `s=11`.

$$
11+19=30<32.
$$

The carry is `0`, so the selector keeps `11`.

**Reduction needed:** `a=9`, `b=8`, so `s=17`.

$$
17+19=36=32+4.
$$

The carry is `1`, the low five bits encode `4`, and the selector returns `4 = 17 mod 13`.

### 7.6 The register layout

`modAddLayout` exposes:

- public `lhs = A`;
- public `rhs = B`;
- public output `O`;
- private work containing the unreduced sum `X`, loaded-constant register `K`, reduction candidate `Y`, both carry banks, and carry-in wires.

`ModAddWiring` records the genuine construction facts:

- aligned lengths;
- valid ripple and selector layouts;
- the intended alias equations between stage inputs and outputs;
- `M > 0`;
- `2M <= 2^w`.

Global register disjointness comes from `RegisterLayout.Valid`, rather than being repeated as dozens of caller hypotheses.

### 7.7 The public theorem

`modAdd_contract` packages the exact `modAdd` circuit as a `ModAddContract` with cost

$$
T_{add}(w)=91w.
$$

The derivation is transparent:

| Component | Cost |
| --- | ---: |
| first ripple | `21w` |
| constant-add ripple | `21w` |
| forward candidate computation | `42w` |
| selector | `7w` |
| reverse candidate computation | `42w` |
| **total** | **`91w`** |

The theorem also supplies correctness, input preservation, work cleanup, full support, H/P-freedom, and well-formedness for that same term.

---

# Part III — Multiplication, exponentiation, and inversion

## 8. Modular multiplication: reference and low-space circuits

Sources: `ShorECDLP/Submission/Arithmetic/ModMul.lean`,
`InPlaceAdder.lean`, `InPlaceModular.lean`, and `LowSpaceModMul.lean`.

### 8.1 Schoolbook reference multiplication in modular form

Write the multiplier `y` in little-endian binary:

$$
y = \sum_{i=0}^{n-1} y_i 2^i.
$$

Then

$$
x y \bmod M
= \sum_{i=0}^{n-1} y_i (2^i x \bmod M) \bmod M.
$$

This suggests maintaining two live values:

- `power = 2^i x mod M`;
- `acc = x * (the already processed low bits of y) mod M`.

At each multiplier bit:

```text
acc'   = acc + (bit ? power : 0) mod M
power' = power + power mod M
```

After all bits, `acc = x*y mod M`.

### 8.2 Why a typed plan is used

`ModMul.Plan` is an inductive schedule. Each step stores:

- the current control bit;
- registers for the current `power` and `acc`;
- fresh registers for a duplicate, masked value, next power, and next accumulator;
- two supplied circuits already certified by `ModAddContract`;
- their private workspaces;
- the rest of the plan.

The multiplier does not import the private implementation of modular addition. It only consumes the public facts:

```text
this supplied circuit is a clean modular adder,
has this exact cost,
uses only this layout,
is H/P-free,
and is well-formed for valid wiring.
```

This is dependency inversion in proof form. The high-level algorithm depends on an interface, not an implementation.

### 8.3 One forward stage

The exact `stageProgram` performs:

```text
copyReg(power; duplicate)
doubleProgram(power, duplicate; nextPower)  -- power + power mod M
maskReg(control, power; mask)               -- control ? power : 0
accProgram(mask, acc; nextAcc)              -- masked power + acc mod M
```

Copying is needed because `ModAddContract` requires two disjoint input registers. The duplicate starts clean and receives `power`; the doubling adder preserves both inputs.

`maskReg` applies one `CCX control power_i mask_i` per bit. Under the plan's validity facts—the source and mask have equal lengths, `(control :: source ++ mask)` is duplicate-free, and the mask starts clean—it writes either all zeroes or the current power.

Every next value is stored in a fresh register. Earlier values remain as a reversible history.

### 8.4 The forward correctness invariant

The theorem `ModMul.Plan.forward_correct` proves, in effect:

$$
finalAcc = (acc_0 + power_0 \cdot controls) \bmod M.
$$

The public plan starts with `acc_0=0`, `power_0=x`, and `controls=y`, so:

$$
finalAcc = x y \bmod M.
$$

The one-step arithmetic lemma `schoolbook_step` is the algebraic heart of the induction. It reconciles:

- the low control bit's contribution;
- the doubled power used by the remaining higher bits;
- modular reduction after each addition.

### 8.5 Bennett-clean public program

The forward schedule leaves its entire history live. The public program is:

```text
ModMul.Plan.program:
  forward
  copyReg(finalAcc; out)
  reverse(forward)
```

The layout declares the initial zero accumulator and all recorded history as private work. After copy-out, reversal restores all of it.

The theorem `ModMul.Plan.modMul_contract` packages the result as a `ModMulContract`:

$$
out = lhs \cdot rhs \bmod M,
$$

with both inputs preserved and all private work clean.

### 8.6 Cost

Let:

- `n = controls.length`, the number of multiplier bits;
- `w`, the arithmetic register width;
- `A`, the exact cost of each supplied modular adder.

One forward step costs:

| Operation | Cost |
| --- | ---: |
| copy `power` | `0` |
| modular double | `A` |
| mask `power` | `7w` |
| modular accumulate | `A` |
| **forward step** | **`2A + 7w`** |

The outer Bennett wrapper doubles all forward work, so Lean proves:

$$
T_{mul}(n,w,A) = 2n(2A+7w).
$$

If `n=w` and the supplied adder has `A=91w`, the symbolic specialization is:

$$
T_{mul}(w)=2w(182w+7w)=378w^2.
$$

This remains a verified generic reference construction. The concrete secp256k1 instance now
uses the lower-space Horner circuit described next instead of instantiating this history-heavy
plan.

### 8.7 The active low-space Horner multiplier

For the concrete submission, `LowSpaceModMul.program` scans the little-endian multiplier from
its most significant end and updates one clean output register in place:

```text
load modulus into modulusReg
for bit in reverse(multiplier):
  out := 2*out mod modulus
  out := out + (bit ? source : 0) mod modulus
unload modulusReg
```

`InPlaceAdder` supplies the one-ancilla Cuccaro add/subtract primitive.
`InPlaceModular` builds the modular double and controlled modular add while exactly
uncomputing their comparison and overflow flags. Every Horner iteration reuses the same
modulus register, masked-addend register, carry bit, branch bit, and overflow bit.

For arithmetic width `w` and `n` multiplier bits, Lean proves

$$
T_{low\text{-}mul}(n,w)=154wn.
$$

A uniform-width layout declares exactly `5w+3` wires: `3w` public input/output wires and
`2w+3` private reusable work wires. At `w=n=257`, the checked concrete multiplier therefore
uses 1,288 declared wires (517 private) and costs 10,171,546 T gates.

### 8.8 Example: `7 * 11 mod 13`

The modular-adder fit condition for `M=13` requires width `w=5`, so the equal-width public multiplier represents `11` by the padded little-endian bits `[1,1,0,1,0]`.

| Step | bit | power before | acc before | acc after | power after |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 1 | 7 | 0 | 7 | 1 |
| 1 | 1 | 1 | 7 | 8 | 2 |
| 2 | 0 | 2 | 8 | 8 | 4 |
| 3 | 1 | 4 | 8 | 12 | 8 |
| 4 | 0 | 8 | 12 | 12 | 3 |

All values are reduced modulo `13`. The answer is `12`, and indeed `7*11=77=5*13+12`.

The table illustrates the low-to-high schoolbook reference recurrence. The active Horner
circuit processes the same padded bits in the opposite order and accumulates by repeated
doubling followed by a controlled addition.

---

## 9. Modular exponentiation

Source: `ShorECDLP/Submission/Arithmetic/ModExp.lean`.

### 9.1 LSB-first square-and-multiply

For exponent bits

$$
e = \sum_{i=0}^{n-1} e_i 2^i,
$$

maintain:

- `power = base^(2^i) mod M`;
- `acc = base^(the processed low-bit value) mod M`.

At bit `e_i`:

```text
candidate = acc * power mod M
nextAcc  = e_i ? candidate : acc
nextPower = power * power mod M
```

The circuit computes the candidate even when the bit is zero and then selects. This fixed control flow is simpler than conditionally enabling an entire multiplier.

### 9.2 Pure arithmetic is separated from circuit plumbing

The beginning of `ModExp.lean` develops a mathematical recurrence:

- `bitsValue` interprets little-endian Boolean lists;
- `mulSelectStep` updates the accumulator;
- `squareMultiplyAcc` describes the whole LSB-first algorithm;
- supporting lemmas prove it equals modular exponentiation.

Only afterward does the file define typed circuit calls and schedules. This separation makes it clear which proof is number theory and which proof is wire management.

### 9.3 Certified multiplier calls

Each `MulCall` stores:

- the exact multiplier `program`;
- its input/output/work registers;
- its exact `cost`;
- a proof `certified : ModMulContract ...`.

The exponentiation schedule never opens a multiplier's private implementation. It uses only
the certified `ModMulContract`; the concrete instance supplies the low-space multiplier above.

### 9.4 The three schedule cases

The typed `Schedule` distinguishes:

1. **No bits.** Do nothing.
2. **Last bit.** Multiply `acc * power`, select the next accumulator, and stop.
3. **Non-final bit.** Multiply/select the accumulator, copy `power` into a reusable duplicate register, square it with a second multiplier call, clear the duplicate, and continue.

The special last-bit case deliberately omits the final unused square.

Therefore an `n`-bit nonempty exponent uses:

$$
n \text{ accumulator multiplications} + (n-1) \text{ squarings}
= 2n-1 \text{ multiplier calls}.
$$

Lean proves this as `ModExp.Schedule.multiplierCalls_eq`.

### 9.5 Initializing one

Exponentiation starts from the multiplicative identity, not zero. `initOne` applies an `X` to the least-significant bit of a clean accumulator register. When that register is duplicate-free and has positive width, the accumulator then represents `1`.

This initialization is T-free.

### 9.6 The complete public program

`ModExp.Plan` contains the base, exponent, output, initial and final accumulator registers, shared multiplication scratch, a duplicate register, and a valid schedule.

The program is:

```text
compute:
  initOne(initialAcc)
  schedule.forward

program:
  compute
  copyReg(finalAcc; out)
  reverse(compute)
```

`ModExp.Plan.modExp_contract` proves:

$$
out = base^{exponent} \bmod M,
$$

while preserving base and exponent and restoring work.

No primality or coprimality is needed. Modular exponentiation is valid for any `M>1`. The shared `CleanBinaryContract` conservatively requires both public numeric inputs to be below `M`; the exponentiation proof itself does not need the exponent bound.

### 9.7 Cost

Let:

- `n` be the exponent-bit count;
- `w` be the register width;
- `C_mul` be the common exact cost of each multiplier call.

The forward pass costs:

$$
(2n-1)C_{mul} + 7wn.
$$

The second term is one `w`-bit selector per exponent bit. Initialization, copying, and duplicate-register copying are T-free.

The outer Bennett pass doubles the forward cost. For the plan's equal-width public registers, `n=w`, giving the certified closed form:

$$
T_{exp}(w,C_{mul})
= 2\left((2w-1)C_{mul}+7w^2\right).
$$

The relevant declarations are:

- `ModExp.Plan.cost_eq_of_uniform`
- `ModExp.Plan.program_tCount_eq_of_uniform`
- `ModExp.Plan.modExp_contract_uniform`

All three refer back to the same `Plan.program`.

### 9.8 Example: `3^5 mod 13`

Again `M=13` requires width `w=5` for the current equal-width stack, so the exponent register contains the padded bits `[1,0,1,0,0]`.

| Step | bit | power before | acc before | product candidate | acc after | next power |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 1 | 3 | 1 | 3 | 3 | 9 |
| 1 | 0 | 9 | 3 | 1 | 3 | 3 |
| 2 | 1 | 3 | 3 | 9 | 9 | 9 |
| 3 | 0 | 9 | 9 | 3 | 9 | 3 |
| 4 | 0 | 3 | 9 | 1 | 9 | omitted |

Thus `3^5 mod 13 = 9`.

Notice the bit-zero step: the circuit still computes `3*9 mod 13 = 1`, but the selector retains the old accumulator `3`.

---

## 10. Fermat inversion over the Bitcoin field

Sources:

- `ShorECDLP/Submission/Field.lean`
- `ShorECDLP/Submission/Arithmetic/FermatInv.lean`

### 10.1 The secp256k1 field

The base-field prime is hardcoded as:

$$
p = 2^{256}-2^{32}-977.
$$

Lean defines:

```lean
def p : Nat := 2^256 - 2^32 - 977
abbrev Fp := ZMod p
```

The curve coefficients are also explicit:

$$
a=0, \qquad b=7,
$$

so the affine equation is

$$
y^2=x^3+7.
$$

The group order `order` is separately hardcoded. The base-field prime `p` and group order are different numbers with different roles.

### 10.2 Fermat's little theorem

If `p` is prime and `x` is nonzero in `F_p`, then

$$
x^{p-1}=1.
$$

Multiplying `x^(p-2)` by `x` gives `1`, so:

$$
x^{p-2}=x^{-1}.
$$

The theorem `fermat_inv` proves exactly this field identity:

```lean
theorem fermat_inv [Fact (Nat.Prime p)]
    (x : Fp) (hx : x ≠ 0) :
    x ^ (p - 2) = x⁻¹
```

Primality is an explicit `Fact` hypothesis. The current repository does not include a machine-checked primality certificate for `p`.

### 10.3 There is no second inversion circuit

`FermatInv.lean` defines **no circuit**. Its theorem `FermatInv.correct` consumes any supplied `ModExpContract` at modulus `p`, assumes that the exponent register contains `p-2`, and reinterprets the exponentiation result as a field inverse.

The proof chain is:

```text
ModExpContract says:
  out = base^(p-2) mod p

fermat_inv says:
  base^(p-2) = base^(-1) in Fp

therefore:
  the same ModExp program computes inversion
```

Input preservation, work cleanup, H/P-freedom, well-formedness, and cost are inherited from the supplied exponentiation contract. There is no duplicate implementation that might drift from the exponentiator.

### 10.4 Why zero is excluded

Zero has no multiplicative inverse in a field. The theorem therefore requires:

```text
(base : Fp) ≠ 0.
```

Future affine point addition must branch before invoking the certified inversion theorem:

- generic addition uses a nonzero `x_2-x_1` denominator;
- doubling uses a nonzero `2y` denominator when appropriate;
- point-at-infinity, inverse-pair, and exceptional cases must be handled separately.

Lean's inverse operation is total—indeed, `0⁻¹ = 0` in a field—but `FermatInv.correct` certifies a genuine multiplicative inverse only under its explicit `hnonzero` premise. The supplied circuit contains no runtime zero check.

### 10.5 Small example in `F_13`

For intuition, take `x=5` modulo `13`. Fermat inversion uses exponent `13-2=11`:

$$
5^{11} \equiv 8 \pmod {13}.
$$

Indeed:

$$
5\cdot 8=40\equiv 1 \pmod {13}.
$$

A future concrete width-257 secp256k1 plan would use the same mathematical method with the 256-bit prime and a much larger exponentiation schedule.

### 10.6 Why this baseline is intentionally expensive

Fermat inversion replaces division by one modular exponentiation. It is simple and easy to compose from the already verified multiplier, but expensive.

The submission deliberately does not yet use:

- the extended Euclidean algorithm;
- addition-chain specialization for `p-2`;
- windowed exponentiation;
- pseudo-Mersenne reduction specialized to `p`;
- projective coordinates that avoid most inversions.

Each would be a different implementation requiring its own correctness and cost proof.

---

# Part IV — From field arithmetic toward the ECDLP oracle

## 11. The elliptic-curve boundary

Sources:

- `ShorECDLP/Submission/EllipticCurve/Secp256k1.lean`
- `ShorECDLP/Submission/EllipticCurve/Precompute.lean`
- `ShorECDLP/Submission/OrderFinding/OracleSpec.lean`
- `ShorECDLP/Submission/OrderFinding/Main.lean`

The repository has landed the mathematical EC seams and a conditional abstract-oracle order-finding theorem, but not the point-arithmetic circuits themselves.

### 11.1 The canonical mathematical point type

`Secp256k1.lean` defines the short-Weierstrass curve over `Fp` and uses Mathlib's nonsingular affine-point type:

```lean
def curve : WeierstrassCurve Fp := ...
abbrev Point := curve.toAffine.Point
```

This type includes:

- the point at infinity `O`, represented by the zero constructor;
- finite affine points with coordinates in `Fp` and a proof of nonsingularity.

The standard generator coordinates are hardcoded:

```text
Gx = 55066263022277343669578718895168534326250603453777594175500187360389116729240

Gy = 32670510020758816978083085130507043184471273380659243275938904335757337482424
```

Lean proves:

- both natural representatives are below `p`;
- the curve discriminant is nonzero;
- the coordinates satisfy `y^2 = x^3+7` modulo `p`;
- the generator is nonsingular;
- `G ≠ O`.

The module deliberately does **not** prove:

- an encoding of points into qubit registers;
- a point-addition circuit;
- that `addOrderOf G = order`.

The last item is a substantial group-order certificate, not a consequence of merely checking the curve equation.

### 11.2 Verified classical doubling tables

For any additive monoid, `Precompute.doublingTable width base` constructs:

$$
[base, [2]base, [4]base, \ldots, [2^{width-1}]base].
$$

The public theorems prove:

- `doublingTable_length`: the list has the requested length;
- `doublingTable_get` and `doublingTable_getElem`: entry `i` is exactly `[2^i]base`;
- `doublingTable_adjacent`: each entry after the first is the double of its predecessor.

This is purely mathematical data. There are no wires, gates, point encodings, concrete `P/Q` table instances, or resource counts in this module.

### 11.3 How future point addition consumes M1

For two generic finite points `R=(x_1,y_1)` and `T=(x_2,y_2)` with `x_1 ≠ x_2`, affine addition uses:

$$
\lambda = \frac{y_2-y_1}{x_2-x_1},
$$

$$
x_3 = \lambda^2-x_1-x_2,
$$

$$
y_3 = \lambda(x_1-x_3)-y_1.
$$

Doubling uses:

$$
\lambda = \frac{3x_1^2+a}{2y_1},
$$

with `a=0` for secp256k1.

The existing M1 stack supplies the expensive leaves:

- modular addition and, with suitable plumbing, subtraction;
- modular multiplication and squaring;
- Fermat inversion for a proven nonzero denominator.

They are leaves, not yet a packaged point-arithmetic interface. Current `main` has no completed modular-subtraction contract, field equality/zero-flag circuit, reversible branch layer for these cases, or `PointAdd` contract.

But a total point-addition circuit must branch over all group-law cases:

1. `R=O`;
2. `T=O`;
3. `R=-T`, whose sum is `O`;
4. `R=T`, the doubling case;
5. generic `x_1 ≠ x_2` addition.

The branch conditions are necessary to satisfy the nonzero precondition of `FermatInv.correct`. One cannot simply run the generic slope formula on every bit pattern.

### 11.4 Point encoding is part of correctness

An oracle operates on bits, while the group law operates on mathematical `Point` values. A concrete refinement therefore needs an injective, canonical encoding:

```text
encode : Point -> Fin (2^pointWidth).
```

Injectivity prevents two different points from colliding as the same basis state. Canonical output prevents one mathematical point from acquiring several history-dependent representations, which would change hidden-subgroup interference.

Current `main` has the abstract `PointEncoding` interface used by the oracle specification, but no concrete secp256k1 point encoding module is merged.

A circuit must also define a reversible action on bit strings that do **not** encode valid points. Correctness restricted to valid encodings is necessary, but a quantum circuit still needs total, bijective behavior on the rest of the computational basis.

### 11.5 From doubling tables to scalar multiplication

Once a controlled point-addition circuit exists, a little-endian scalar register `a` can drive:

```text
for i in 0 .. width-1:
  if a_i:
    R <- R + doublingTable(width,P)[i]
```

The table theorem identifies the selected constant as `[2^i]P`. Therefore the final accumulator is:

$$
R + \sum_i a_i [2^i]P = R+[a]P.
$$

Repeating the same construction with `b` and `Q` yields:

$$
R \longmapsto R+[a]P+[b]Q.
$$

This is the intended ECDLP oracle action.

### 11.6 The scratch-aware oracle interface

Every M1 arithmetic contract assumes clean workspace on input and restores it on output. A realistic point-addition and oracle circuit will also need scratch registers.

The current `ECDLPOracleSpec` therefore declares an explicit `oracleWork` register. Its global `registers_nodup` field covers

```text
aReg ++ bReg ++ pointReg ++ oracleWork,
```

and `onKet` assumes `Clean oracleWork s`. Its right-hand side applies `writeReg` only to `pointReg` in the original state `s`; it therefore specifies exact restoration of the clean oracle scratch and preservation of every outside wire, not merely the right decoded point value.

The interface gap is closed. What remains is to build the concrete point-arithmetic/oracle circuit and prove that it refines this scratch-aware specification. The same clean-ancilla discipline then runs continuously from M1 arithmetic through point addition and into the already-proved conditional order-finding theorem `Quantum.OrderFinding.orderFinding_correct`.

---

# Part V — Proof architecture, costs, and audit boundaries

## 12. How the proofs compose

### 12.1 Two dependency graphs

There is a **source import graph** and a **mathematical contract graph**. They are intentionally different.

The source-level direction is roughly:

```text
Framework semantics/cost
     |              |
   Adder         Contracts
     |              |
 Ripple         Primitives
        \        /
          ModAdd

Primitives + Contracts -> ModMul
Primitives + Contracts -> ModExp
Contracts + Field      -> FermatInv
```

The mathematical values flow as:

```text
modAdd_contract
    -> supplied to ModMul.Plan steps

ModMul.Plan.modMul_contract
    -> supplied to ModExp.MulCall values

ModExp.Plan.modExp_contract
    -> supplied to FermatInv.correct
```

`ModMul.lean` does not import `ModAdd.lean`, and `ModExp.lean` does not import `ModMul.lean`. They accept certified calls through shared contract types. This prevents a high-level correctness theorem from depending on a low-level implementation's private carry layout.

### 12.2 The apex theorem at each layer

| Layer | Main public theorem | Essential conclusion |
| --- | --- | --- |
| full adder | `fullAdder_sum`, `fullAdder_carry` | correct output bits |
| ripple | `ripple_correct` | `S + 2^n*C = A+B+cin` |
| modular add | `modAdd_contract` | clean `(A+B) mod M`, cost `91w` |
| modular multiply | `ModMul.Plan.modMul_contract` | clean `A*B mod M`, symbolic cost |
| modular exponentiate | `ModExp.Plan.modExp_contract` | clean `base^exponent mod M` |
| uniform exponentiate cost | `ModExp.Plan.modExp_contract_uniform` | same program, closed-form cost |
| Fermat inverse | `FermatInv.correct` | output cast to `Fp` equals inverse |

### 12.3 Five obligations travel together

For a composite arithmetic component, the proof is not complete after the numerical equation. The public contract carries:

```text
functional result + input preservation + work cleanup
locality/support
exact cost
HPFree
WellFormed
```

Each supports a different downstream step.

- Function and cleanup enable arithmetic composition.
- Locality proves unrelated live wires survive and makes uncomputation safe.
- Exact cost enables resource aggregation.
- H/P-freedom enables the classical-to-quantum basis-ket bridge.
- Well-formedness enables inner-product preservation.

### 12.4 Proofs are conditional on honest layouts

The theorems quantify over plans and layouts satisfying validity predicates. This is normal for a circuit library: it is analogous to proving that a compiler pass is correct for any well-typed input program.

The next integration step must still construct:

- actual wire lists;
- actual subcircuit calls;
- proofs that their layouts are valid and disjoint;
- a concrete secp256k1 arithmetic plan.

Until then, it is accurate to say:

> The repository verifies the parametric constructions and compositional contracts for every valid supplied plan.

It is not yet accurate to say:

> The repository contains a fully allocated 257-bit secp256k1 inversion circuit.

### 12.5 From classical arithmetic to a quantum oracle

Suppose a future concrete circuit `oracleCircuit` has a non-aliased combined layout and the following whole-state classical theorem for a declared scratch register:

```text
regValue aReg s = a ->
regValue bReg s = b ->
regValue pointReg s = (enc.encode R).val ->
Clean oracleWork s ->
  Classical.run oracleCircuit s
    = writeReg pointReg
        (enc.encode (R + [a]P + [b]Q)).val s
```

The whole-state equality says more than “the point register has the right value”: relative to the input state `s`, it also restores clean work and preserves all registers outside `pointReg`. This is a target refinement interface, not an immediate consequence of the current M1 contracts. Those contracts provide output values, `AgreesOn` facts for inputs, work cleanliness, and locality. The order-finding proof layer now exposes fitting-value and restoration lemmas such as `regValue_writeReg_of_lt` and `writeReg_regValue`; the concrete oracle still needs its circuit-specific extensional theorem connecting the composed arithmetic contracts to the displayed whole-state equality.

The current oracle specification already carries the clean-work premise. Once a concrete classical circuit proves the whole-state theorem, its two quantum obligations split cleanly:

```text
onKet:
  classical theorem
  + oracleCircuit is HPFree
  + Quantum.run_ket_agrees_classical

preservesInner:
  oracleCircuit is CircuitWellFormed
  + Quantum.run_preservesInner
```

The number theory, wire cleanup, quantum basis action, and physical isometry remain separate lemmas until the final refinement theorem combines them.

`Quantum.OrderFinding.orderFinding_correct` consumes `ECDLPOracleSpec` at this abstract boundary. It proves the conditional two-register Fourier-sampling success theorem, not the missing construction of the concrete oracle circuit.

### 12.6 What the automated trust gate checks

Running:

```sh
./scripts/verify.sh
```

performs several independent checks:

1. `git diff --check` catches malformed patches.
2. Lean emits warnings for `sorry`/`admit`, and `lake --wfail build` turns those warnings into build failures.
3. `scripts/check-source.py` uses compiler-derived imports to ensure every project **Lean** source is tracked, non-symlinked, sanctioned, and reachable from the root `ShorECDLP.lean` aggregator.
4. Targeted `#print axioms` commands disclose dependencies of the main arithmetic, EC, QFT, and phase-estimation theorems.
5. A pinned exhaustive axiom-audit scans every project declaration and permits only the standard dependencies `propext`, `Classical.choice`, and `Quot.sound`.

This verifies formal derivations relative to the Lean kernel, Mathlib, the stated hypotheses, and the chosen definitions. The executable trust boundary still includes the pinned Lean toolchain and kernel, Mathlib—including the hosted `.olean` cache used by CI—the CI runner and download/integrity path, and the three allowlisted standard axioms. The gate does not prove that the naive T-cost model predicts a particular hardware platform, nor does it discharge explicit hypotheses such as `[Fact (Nat.Prime p)]`.

---

## 13. Cost derivations and a secp256k1-sized illustration

### 13.1 Symbolic summary

Let:

- `w` be the arithmetic register width;
- `n` be the multiplier/exponent bit count where shown separately;
- `A` be modular-add cost;
- `C_mul` be modular-multiply cost.

| Operation | Proved symbolic T-count |
| --- | ---: |
| full adder | `21` |
| ripple add, `n` columns | `21n` |
| constant add, width `w` | `21w` |
| selector, width `w` | `7w` |
| clean modular add | `91w` |
| Bennett schoolbook modular multiply | `2n(2A+7w)` |
| low-space Horner modular multiply | `154wn` |
| modular exponentiation, uniform calls and `n=w` | `2((2w-1)C_mul+7w^2)` |
| Fermat inversion | exactly the supplied exponentiation cost |

### 13.2 Reference schoolbook and active low-space formulas

For equal-width multiplication, put `n=w` and `A=91w`:

$$
C_{mul}
= 2w(2\cdot 91w+7w)
=378w^2.
$$

Substitute that into exponentiation:

$$
C_{exp}
=2\left((2w-1)378w^2+7w^2\right).
$$

Expanding:

$$
C_{exp}=1512w^3-742w^2.
$$

That is the reference schoolbook-plan specialization. The concrete instance supplies the
low-space multiplier contract with

$$
C_{low\text{-}mul}=154w^2,
$$

so its same generic exponentiation schedule has

$$
C_{low\text{-}exp}
=2\left((2w-1)154w^2+7w^2\right)
=616w^3-294w^2.
$$

The cubic term still comes from roughly `2w` quadratic multiplier calls. Fermat inversion
inherits whichever certified exponentiation program is supplied.

### 13.3 Why `w=257` for the generic adder

The secp256k1 prime is less than `2^256`, but the modular-adder construction requires:

$$
2p \le 2^w.
$$

Since `p` is close to `2^256`, `w=256` cannot satisfy the inequality, while `w=257` does. The extra bit stores the unreduced sum of two canonical field elements.

This is a design choice of the generic one-subtraction adder, not a statement that field elements intrinsically need 257 data bits.

### 13.4 Algebraic values at `w=257`

Evaluating the proved symbolic formulas gives:

| Operation | Formula specialization | T-count | Toffoli-equivalent count |
| --- | ---: | ---: | ---: |
| modular add | `91*257` | `23,387` | `3,341` |
| reference schoolbook multiply | `378*257^2` | `24,966,522` | `3,566,646` |
| concrete low-space multiply | `154*257^2` | `10,171,546` | `1,453,078` |
| concrete modular exponentiation | `616*257^3 - 294*257^2` | `10,436,930,882` | `1,490,990,126` |
| Fermat inversion | same concrete exponentiation program | `10,436,930,882` | `1,490,990,126` |

The Toffoli-equivalent column simply divides by seven because these arithmetic circuits contain no `P` gates.

These are checked concrete values: `Secp256k1Instance` supplies the width-257 adder wiring,
the low-space multiplier layout and contract, and the exponentiation schedule, then proves the
numeric T-counts for those exact circuit terms.

### 13.5 Workspace

The concrete parametric `modAddLayout` uses:

- `3w` public wires (`lhs`, `rhs`, `out`);
- `5w+2` work wires (`X`, `K`, `Y`, two carry banks, and two carry-ins).

Thus its declared layout contains `8w+2` wires. At `w=257`, that is `2,058` wires for this deliberately straightforward modular-adder placement.

The active multiplier does not retain a per-bit history. Its public theorems
`secpMulLayout_allWires_length` and `secpMulProgram_qubitCount` certify exactly 1,288 declared
wires (771 public and 517 private) and at most 1,288 wires touched. The exponentiation plan
still retains its square-and-multiply history, so the full
Bitcoin trial uses the separately certified dense-capacity bound from `EndToEnd.lean`.

### 13.6 How to read these costs

The formulas teach three architectural facts.

1. **Cleanup is visible.** Both multiplication and exponentiation pay an outer factor of two for compute-copy-uncompute.
2. **Arithmetic nesting is expensive.** Linear-bit multiplication over linear-cost modular
   steps is quadratic; linear-bit exponentiation over quadratic multiplication is cubic.
3. **Space and time trade off.** The Horner multiplier removes the width-many Bennett history
   and lowers the active constant, while exponentiation still retains history for cleanup.

---

## 14. What is proved, assumed, and still missing

### 14.1 Status matrix

| Component | Status on the source snapshot | Exact boundary |
| --- | --- | --- |
| primitive gates and T-count | **proved/defined** | naive metric over `X,H,CX,CCX,P` |
| classical basis semantics | **proved/defined** | faithful for H/P-free circuits |
| classical-to-quantum ket bridge | **proved** | requires `HPFree` |
| inner-product preservation | **proved** | requires `CircuitWellFormed` |
| full adder | **constructed and proved** | parameterized wire indices |
| ripple adder | **constructed and proved** | valid aligned registers and clean outputs |
| modular adder | **constructed and proved parametrically** | supplied wire lists plus `ModAddWiring` |
| modular multiplier | **verified typed constructor/API** | consumes supplied `ModAddContract`s |
| modular exponentiator | **verified typed constructor/API** | consumes supplied `ModMulContract`s |
| Fermat inversion theorem | **proved conditionally** | no new circuit; consumes `ModExpContract`, prime fact, nonzero base |
| secp256k1 curve and generator equation | **defined/proved** | no generator-order theorem |
| generic doubling table | **defined/proved** | mathematical list, not a circuit |
| scratch-aware abstract ECDLP oracle | **specified** | clean `oracleWork`, global non-aliasing, basis action, inner-product preservation |
| conditional two-register order finding | **proved** | consumes the abstract oracle contract; no concrete oracle supplied |
| concrete width-257 arithmetic plan | **missing** | no final wire allocation/plan instance |
| concrete point encoding on `main` | **missing** | abstract encoding interface only |
| total point-add circuit | **missing** | all exceptional cases and cost remain |
| controlled scalar multiplication | **missing** | requires point add and instantiated tables |
| concrete ECDLP oracle | **missing** | must refine the existing scratch-aware spec with a whole-state theorem |

### 14.2 Explicit assumptions

The most important assumptions are visible, not hidden:

- `[Fact (Nat.Prime p)]` for field inversion and the Mathlib elliptic-curve instance;
- canonical numeric inputs below the modulus;
- clean output and work registers;
- valid, globally non-aliased register layouts;
- construction and schedule validity: in particular `ModAddWiring` with `2*modulus ≤ 2^width`, `ModMul.Plan.Valid width`, and `ModExp.Schedule.Valid`;
- positive modulus for addition/multiplication and modulus greater than one for exponentiation;
- positive register width for the exponentiation plan;
- nonzero base for Fermat inversion;
- supplied lower-level contract values in `ModMul.Plan` and `ModExp.Schedule`.

Outside M1, `Reduction.recoverShift_correct` separately assumes `[Fact (Nat.Prime order)]`; this snapshot contains no machine-checked certificate for that primality either. That number-theoretic assumption is distinct from the still-missing group theorem `addOrderOf Secp256k1.G = order`.

### 14.3 Common overstatements to avoid

**Overstatement:** “`HPFree` proves the circuit is unitary.”

**Correct:** `HPFree` proves applicability of the classical/quantum agreement theorem. Well-formedness proves inner-product preservation.

**Overstatement:** “The multiplier directly calls `modAdd` from `ModAdd.lean`.”

**Correct:** its typed plan accepts any circuits satisfying `ModAddContract`.

**Overstatement:** “FermatInv implements a new inverse circuit.”

**Correct:** it proves that the same supplied modular-exponentiation circuit computes inverse when the exponent is `p-2`.

**Overstatement:** “The repository proves a natural-number output equal to the inverse.”

**Correct:** `FermatInv.correct` proves that the output's cast into `Fp` equals the field inverse. A separate canonical-representative lemma would be needed to state the strongest natural-number equality.

**Overstatement:** “The old `378w²` schoolbook substitution is the concrete multiplier used by
the submission.”

**Correct:** that remains a verified reference plan. The concrete submission uses the
`154w²` low-space multiplier, whose exact width-257 cost is `10,171,546`; its same-program
Fermat inversion costs `10,436,930,882` T gates.

**Overstatement:** “The arithmetic stack proves the ECDLP oracle.”

**Correct:** it proves the field-level leaves and their compositional interfaces. The scratch-aware abstract oracle is specified, and the conditional order-finding theorem is proved, but encoding, point addition, scalar multiplication, order certification, concrete-circuit refinement, and aggregate cost are separate obligations.

---

## 15. Reading the Lean source

### 15.1 Recommended order

For a first pass, read module headers and theorem signatures before proof bodies.

1. `ShorECDLP/Framework/InstructionSet.lean`
2. `ShorECDLP/Framework/CostModel.lean`
3. `ShorECDLP/Framework/BasisState.lean`
4. `ShorECDLP/Framework/Classical/Semantics.lean`
5. `ShorECDLP/Submission/Arithmetic/Contracts.lean`
6. `ShorECDLP/Submission/Arithmetic/Adder.lean`
7. `ShorECDLP/Submission/Arithmetic/RippleAdder.lean`
8. `ShorECDLP/Submission/Arithmetic/Primitives.lean`
9. `ShorECDLP/Submission/Arithmetic/ModAdd.lean`
10. `ShorECDLP/Submission/Arithmetic/ModMul.lean`
11. `ShorECDLP/Submission/Arithmetic/ModExp.lean`
12. `ShorECDLP/Submission/Field.lean`
13. `ShorECDLP/Submission/Arithmetic/FermatInv.lean`
14. `ShorECDLP/Submission/EllipticCurve/Secp256k1.lean`
15. `ShorECDLP/Submission/EllipticCurve/Precompute.lean`
16. `ShorECDLP/Submission/OrderFinding/OracleSpec.lean`
17. `ShorECDLP/Submission/OrderFinding/Main.lean`

The directory guide `ShorECDLP/Submission/Arithmetic/README.md` contains the import and contract-composition DAGs.

### 15.2 A theorem-reading checklist

When reading an arithmetic theorem, ask:

1. What exact circuit term is in the statement?
2. Which registers are public inputs, output, and work?
3. Are register values little-endian?
4. Which registers must start clean?
5. Which numeric inputs must be canonical?
6. What modulus positivity/width facts are assumed?
7. What is preserved exactly, and what is only characterized by `regValue`?
8. Is cleanup part of this theorem or inherited through a contract?
9. Is the cost an equality or only a bound?
10. Does the theorem prove H/P-freedom, well-formedness, both, or neither?
11. Is the result a concrete instance or conditional on a supplied plan?
12. Are primality or nonzero assumptions explicit?

### 15.3 Declaration index

| Topic | Declaration |
| --- | --- |
| basis state | `ShorECDLP.BasisState` |
| LSB register interpretation | `ShorECDLP.regValue` |
| register write | `ShorECDLP.writeReg` |
| classical circuit execution | `ShorECDLP.Classical.run` |
| H/P-free predicate | `ShorECDLP.Classical.HPFree` |
| well-formed circuit | `ShorECDLP.CircuitWellFormed` |
| T-count | `ShorECDLP.tCount` |
| shared register layout | `ShorECDLP.RegisterLayout` |
| clean-register predicate | `ShorECDLP.Clean` |
| complete binary contract | `ShorECDLP.CleanBinaryContract` |
| one-bit adder | `ShorECDLP.fullAdder` |
| ripple circuit | `ShorECDLP.ripple` |
| ripple identity | `ShorECDLP.ripple_correct` |
| constant loader | `ShorECDLP.loadConst` |
| conditional selector | `ShorECDLP.selectPoint` |
| aligned register copy | `ShorECDLP.Arithmetic.copyReg` |
| reverse cancellation | `ShorECDLP.Arithmetic.run_reverse_cancel` |
| modular-adder circuit | `ShorECDLP.modAdd` |
| modular-adder public package | `ShorECDLP.modAdd_contract` |
| multiplier plan | `ShorECDLP.ModMul.Plan` |
| multiplier public package | `ShorECDLP.ModMul.Plan.modMul_contract` |
| exponentiation schedule | `ShorECDLP.ModExp.Schedule` |
| multiplier call package | `ShorECDLP.ModExp.MulCall` |
| exponentiation plan | `ShorECDLP.ModExp.Plan` |
| exponentiation public package | `ShorECDLP.ModExp.Plan.modExp_contract` |
| uniform exponentiation cost | `ShorECDLP.ModExp.Plan.program_tCount_eq_of_uniform` |
| field identity | `ShorECDLP.fermat_inv` |
| inversion closure | `ShorECDLP.FermatInv.correct` |
| secp point type | `ShorECDLP.Secp256k1.Point` |
| secp generator | `ShorECDLP.Secp256k1.G` |
| doubling table | `ShorECDLP.Precompute.doublingTable` |
| abstract point encoding | `ShorECDLP.PointEncoding` |
| abstract ECDLP oracle contract | `ShorECDLP.ECDLPOracleSpec` |
| classical/quantum bridge | `ShorECDLP.Quantum.run_ket_agrees_classical` |
| inner-product preservation | `ShorECDLP.Quantum.run_preservesInner` |

### 15.4 Useful local commands

From the repository root:

```sh
# Build everything reachable from the root module; warnings are fatal.
lake --wfail build

# Run the complete source, build, and axiom gate.
./scripts/verify.sh

# Ask Lean which axioms a particular apex theorem uses.
lake env lean /dev/stdin <<'LEAN'
import ShorECDLP
#print axioms ShorECDLP.modAdd_contract
#print axioms ShorECDLP.ModMul.Plan.modMul_contract
#print axioms ShorECDLP.ModExp.Plan.modExp_contract_uniform
#print axioms ShorECDLP.FermatInv.correct
LEAN
```

The current verifier also performs exhaustive declaration auditing, so the targeted prints are human-readable highlights rather than the only safety net.

### 15.5 How to study a proof without getting lost

For the longer modules, follow this order:

1. Read the module-level pseudocode.
2. Locate the exact `def` of the circuit.
3. Read the pure arithmetic invariant.
4. Read the cost theorem.
5. Read the support and cleanup theorem.
6. Read the H/P-free and well-formedness theorems.
7. Read the final contract constructor.
8. Only then inspect the internal induction.

This mirrors the logical architecture and keeps implementation detail from obscuring the public claim.

---

## 16. Glossary and review questions

### 16.1 Glossary

**Basis state**
A total assignment of a Boolean value to every wire. It labels a computational-basis ket in the quantum semantics.

**Canonical residue**
A natural representative in `[0,M)`. Arithmetic contracts assume public inputs are canonical.

**Circuit support**
Every wire read as a control or written as a target by a circuit.

**Clean register**
A register whose listed wires are all `false`.

**Zero-T Clifford convention**
The framework charges `X`, `H`, and `CX` zero T gates. It does not say those gates have zero physical time or space cost.

**Compute-copy-uncompute**
Bennett's method: compute a result with history, copy it to fresh output, then reverse the computation to clear history.

**Contract**
A proposition bundling a program's function, preservation/cleanup, locality, cost, H/P-freedom, and well-formedness.

**H/P-free**
Containing no Hadamard or phase gates. This is the precondition under which the repository's classical arithmetic semantics agrees with the quantum basis action.

**Little-endian / LSB-first**
The first register wire has weight `2^0`, the next `2^1`, and so on.

**Out-of-place**
Inputs are preserved and the answer is written into a separate initially clean register.

**Plan**
A typed description of a composite circuit's supplied subcalls, registers, costs, and validity facts.

**Same-program-term discipline**
Correctness and cost are proved about the identical Lean `program`, preventing implementation/specification drift.

**T-count**
The sum of the framework's declared per-gate T costs. It is not T-depth, qubit count, runtime, or full fault-tolerant overhead.

**Well-formed circuit**
A circuit whose gate roles use distinct wires where required, enabling the physical inner-product-preservation proof.

### 16.2 Review questions

1. A register `[q0,q1,q2,q3]` contains bits `[0,1,1,0]`. What is its value?
2. Why is `HPFree` insufficient to prove a circuit is physical?
3. Why does the modular adder require `2M <= 2^w` rather than only `M < 2^w`?
4. In the modular adder, why does adding `2^w-M` reveal whether subtraction is needed?
5. Why must `CircuitUsesOnly` include controls, not just targets?
6. Why does Bennett cleanup require a fresh output outside the forward computation's support?
7. Why does modular multiplication copy `power` before doubling it?
8. Does the current multiplier skip work for zero multiplier bits?
9. Why are there `2n-1`, not `2n`, multiplier calls in `n`-bit exponentiation?
10. Does exponentiation need a prime modulus? Does Fermat inversion?
11. What new circuit does `FermatInv.correct` define?
12. Why are the width-257 numerical costs in this book conditional rather than a final checked secp256k1 estimate?
13. Which current theorem lifts classical basis arithmetic to quantum basis kets?
14. Name three missing pieces between field inversion and a concrete ECDLP oracle.

### 16.3 Answers

1. `0*1 + 1*2 + 1*4 + 0*8 = 6`.
2. It only excludes `H/P`; it does not prevent aliasing such as malformed `CX q q`. Physical inner-product preservation uses `CircuitWellFormed`.
3. Canonical inputs can sum to almost `2M`; the unreduced sum must fit in the same `w`-bit register, and one conditional subtraction must suffice.
4. The addition crosses `2^w` exactly when `s >= M`. The carry is therefore the comparison bit, while the low bits are `s-M` in the carry case.
5. A reverse pass must see the same control values as the forward pass. An undeclared control changed between them can break cleanup even if it was never a target.
6. Otherwise copying can modify a forward control/target, and the reverse pass can erase the answer or fail to retrace the history.
7. The clean binary contract requires disjoint `lhs` and `rhs`; squaring/doubling cannot alias one physical register into both roles.
8. No. It always creates a zero-or-power mask and performs the accumulator modular addition. The fixed schedule does not skip zero bits.
9. Every bit computes an accumulator product, but the final bit does not need a new squared power.
10. Addition, multiplication, and exponentiation do not need primality. Fermat inversion uses the prime-field theorem and requires a nonzero base.
11. None. It specializes the correctness of the supplied modular-exponentiation program.
12. The generic symbolic theorems are checked, but `main` contains no concrete valid width-257 `ModAddWiring`, multiplier plan, exponentiation schedule, and final wire allocation connecting every call.
13. `Quantum.run_ket_agrees_classical`, under `Classical.HPFree`.
14. Examples: canonical point encoding, total exceptional-case point addition, controlled scalar multiplication, a generator-order proof/hypothesis, concrete-circuit refinement to the scratch-aware oracle contract, or the final whole-state oracle theorem.

---

## Conclusion

The arithmetic development is best understood as a verified tower of interfaces.

At the bottom, reversible full-adder cells compose into ripple circuits. The active multiplier
uses a one-ancilla Cuccaro adder to build clean in-place reduction, then scans multiplier bits
with a fixed-workspace Horner recurrence. Certified multiplier calls lift that circuit into
square-and-multiply exponentiation. Finally, a short field theorem reinterprets exponentiation
by `p-2` as inversion. The older typed-history schoolbook multiplier remains as a proved generic
reference construction.

At every composite boundary, the development carries more than a number-theoretic result: it preserves inputs, clears scratch, confines wire use, proves exact cost, records classical faithfulness, and proves physical well-formedness—all for one program term.

That foundation is substantial, but its boundary is equally important. The current repository proves parametric arithmetic constructors and contracts and a conditional abstract-oracle order-finding theorem, not yet a fully allocated secp256k1 point-addition or oracle circuit. The next trustworthy milestone is not to blur that distinction; it is to instantiate the plans, build total clean point arithmetic on top, and connect the resulting circuit to the abstract ECDLP oracle with the same proof discipline.

---

## Source map

```text
ShorECDLP/Framework/
  InstructionSet.lean
  CostModel.lean
  BasisState.lean
  Classical/Semantics.lean
  Quantum/Semantics.lean
  Quantum/InnerProduct.lean

ShorECDLP/Submission/
  Field.lean
  Arithmetic/
    README.md
    Contracts.lean
    Adder.lean
    RippleAdder.lean
    Primitives.lean
    ModAdd.lean
    ModMul.lean
    ModExp.lean
    FermatInv.lean
  EllipticCurve/
    Secp256k1.lean
    Precompute.lean
  OrderFinding/
    OracleSpec.lean
    Main.lean

scripts/
  verify.sh
  check-source.py
```

**End of textbook.**
