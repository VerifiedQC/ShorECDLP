import ShorECDLP.Submission.Arithmetic.Primitives
import Mathlib.Data.Nat.ModEq

/-!
# Modular exponentiation (M1.5)

This module constructs a deliberately simple, exact, LSB-first square-and-multiply circuit
over certified clean modular-multiplication calls.  The arithmetic development below isolates
the pure recurrence used by the later circuit proof: starting from the multiplicative identity,
it accumulates `base ^ exponent mod modulus` while repeatedly squaring the current power.

No primality or coprimality hypothesis is needed for modular exponentiation.  The eventual
Fermat-inversion layer is responsible for adding its own field hypotheses.  The shared
`CleanBinaryContract` conservatively carries an `exponent < modulus` precondition; this proof
does not otherwise need that bound.

## Program (syntax-sugared)

`Plan` contains certified modular-multiplication calls and a fully disjoint register placement.
The final unused square is deliberately omitted.

```text
schedule(base, exponentBits; acc, power = base):
  for each LSB-first bit, from first through last:
    product := ModMul(acc, power)
    nextAcc := bit ? product : acc
    if this is not the last bit:
      nextPower := ModMul(power, power)
      power := nextPower
    acc := nextAcc

modExp(base, exponent; clean out, work):
  initialize acc to 1
  run schedule(base, exponentBits; acc = 1, power = base)
  copyReg(finalAcc; out)
  reverse(initialization ++ schedule)           -- Bennett cleanup
```

## Specification

For a valid `Plan.layout`, `1 < modulus`, canonical base/exponent inputs, and clean output/work,

```text
after := run(Plan.program, before)
value(out, after) = value(base, before) ^ value(exponent, before) mod modulus
base and exponent are preserved
work is clean in after
CircuitUsesOnly(Plan.layout.allWires, Plan.program)
HPFree(Plan.program)
CircuitWellFormed(Plan.program)
```

The exact cost is `plan.cost = 2 * plan.schedule.forwardCost`. If every multiplier call costs
`mulCost`, the same program has certified cost

```text
2 * ((2 * width - 1) * mulCost + 7 * width^2).
```

`Plan.modExp_contract` and `Plan.modExp_contract_uniform` package these specifications. Pure
recurrence, schedule, locality, cost, and cleanup lemmas provide their proofs.
-/

namespace ShorECDLP
namespace ModExp

open Arithmetic

/-! ## Pure LSB-first arithmetic -/

/-- The natural value of a little-endian list of bits. -/
def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsValue bs

/-- `bitsValue` uses exactly the same little-endian convention as `regValue`. -/
theorem bitsValue_map_eq_regValue (ws : List Wire) (st : BasisState) :
    bitsValue (ws.map st) = regValue ws st := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [bitsValue, regValue_cons, ih]

/-- Every `n`-bit little-endian list denotes a value below `2^n`. -/
theorem bitsValue_lt_two_pow (bs : List Bool) :
    bitsValue bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
      cases b <;> simp only [bitsValue, List.length_cons, Bool.false_eq_true,
        ↓reduceIte, Nat.zero_add, Nat.pow_succ] <;> omega

/-- The product candidate computed on every iteration, independently of the exponent bit. -/
def productCandidate (modulus acc power : Nat) : Nat :=
  acc * power % modulus

/-- Keep the old accumulator for bit zero and choose the product candidate for bit one. -/
def selectAccumulator (bit : Bool) (acc candidate : Nat) : Nat :=
  if bit then candidate else acc

/-- One unconditional-product-plus-selector accumulator step. -/
def mulSelectStep (modulus acc power : Nat) (bit : Bool) : Nat :=
  selectAccumulator bit acc (productCandidate modulus acc power)

theorem mulSelectStep_eq (modulus acc power : Nat) (bit : Bool) :
    mulSelectStep modulus acc power bit =
      if bit then acc * power % modulus else acc := by
  cases bit <;> rfl

theorem mulSelectStep_lt {modulus acc power : Nat} (hmod : 0 < modulus)
    (hacc : acc < modulus) (bit : Bool) :
    mulSelectStep modulus acc power bit < modulus := by
  cases bit
  · exact hacc
  · exact Nat.mod_lt _ hmod

/--
The exact forward recurrence implemented by the circuit.  A product candidate is computed on
every exponent bit, while the final unused square is deliberately omitted.
-/
def squareMultiplyAcc (modulus : Nat) : Nat → Nat → List Bool → Nat
  | acc, _, [] => acc
  | acc, power, [bit] => mulSelectStep modulus acc power bit
  | acc, power, bit :: nextBit :: bits =>
      squareMultiplyAcc modulus
        (mulSelectStep modulus acc power bit)
        ((power * power) % modulus)
        (nextBit :: bits)

/-- Canonical inputs produce a canonical accumulator at every iteration. -/
theorem squareMultiplyAcc_lt {modulus acc power : Nat} (hmod : 0 < modulus)
    (hacc : acc < modulus) (bits : List Bool) :
    squareMultiplyAcc modulus acc power bits < modulus := by
  induction bits generalizing acc power with
  | nil => exact hacc
  | cons bit bits ih =>
      cases bits with
      | nil => exact mulSelectStep_lt hmod hacc bit
      | cons nextBit bits =>
          rw [squareMultiplyAcc]
          exact ih (mulSelectStep_lt hmod hacc bit)

/-- The circuit recurrence denotes multiplication by the selected binary power. -/
theorem squareMultiplyAcc_correct {modulus acc power : Nat} (hmod : 0 < modulus)
    (hacc : acc < modulus) (bits : List Bool) :
    squareMultiplyAcc modulus acc power bits =
      (acc * power ^ bitsValue bits) % modulus := by
  induction bits generalizing acc power with
  | nil => simp [squareMultiplyAcc, bitsValue, Nat.mod_eq_of_lt hacc]
  | cons bit bits ih =>
      cases bits with
      | nil =>
          cases bit
          · simp [squareMultiplyAcc, mulSelectStep, selectAccumulator,
              bitsValue, Nat.mod_eq_of_lt hacc]
          · simp [squareMultiplyAcc, mulSelectStep, selectAccumulator,
              productCandidate, bitsValue, Nat.mul_mod]
      | cons nextBit bits =>
          rw [squareMultiplyAcc, ih (mulSelectStep_lt hmod hacc bit)]
          cases bit
          · simp only [mulSelectStep, selectAccumulator,
              bitsValue, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
            rw [Nat.pow_mul]
            simp only [Nat.pow_two]
            change acc * (power * power % modulus) ^ bitsValue (nextBit :: bits) ≡
              acc * (power * power) ^ bitsValue (nextBit :: bits) [MOD modulus]
            exact Nat.ModEq.rfl.mul (by simp [Nat.ModEq, Nat.pow_mod])
          · simp only [mulSelectStep, selectAccumulator, productCandidate,
              bitsValue, ↓reduceIte]
            rw [Nat.add_comm 1, Nat.pow_succ, Nat.pow_mul]
            simp only [Nat.pow_two]
            change
              (acc * power % modulus) *
                  (power * power % modulus) ^ bitsValue (nextBit :: bits) ≡
                acc * ((power * power) ^ bitsValue (nextBit :: bits) * power)
                [MOD modulus]
            have hproduct : acc * power % modulus ≡ acc * power [MOD modulus] := by
              simp [Nat.ModEq]
            have hsquare :
                (power * power % modulus) ^ bitsValue (nextBit :: bits) ≡
                  (power * power) ^ bitsValue (nextBit :: bits) [MOD modulus] := by
              simp [Nat.ModEq, Nat.pow_mod]
            refine (hproduct.mul hsquare).trans ?_
            rw [Nat.mul_assoc,
              Nat.mul_comm power ((power * power) ^ bitsValue (nextBit :: bits))]

/-- Starting from one computes the contract's modular-power specification. -/
theorem squareMultiplyAcc_one_correct {modulus power : Nat} (hmod : 1 < modulus)
    (bits : List Bool) :
    squareMultiplyAcc modulus 1 power bits = power ^ bitsValue bits % modulus := by
  rw [squareMultiplyAcc_correct (Nat.zero_lt_of_lt hmod) hmod]
  simp

/-- Register bits specialize the recurrence to `base ^ regValue exponent mod modulus`. -/
theorem squareMultiplyAcc_register_correct {modulus power : Nat} (hmod : 1 < modulus)
    (ws : List Wire) (st : BasisState) :
    squareMultiplyAcc modulus 1 power (ws.map st) =
      power ^ regValue ws st % modulus := by
  rw [squareMultiplyAcc_one_correct hmod, bitsValue_map_eq_regValue]

/-! ## Certified multiplication schedule -/

/-- An LSB-first register whose width is recorded in its type. -/
structure Reg (width : Nat) where
  wires : List Wire
  length_eq : wires.length = width

/-! ## Reused reversible selector -/

/-- Align three equally wide registers into the column format consumed by M1.3.2's selector. -/
def selectorColumns : List Wire → List Wire → List Wire → List (Wire × Wire × Wire)
  | x :: xs, y :: ys, o :: os => (x, y, o) :: selectorColumns xs ys os
  | _, _, _ => []

/-- Aligned columns project back to all three source lists. -/
theorem selectorColumns_maps (xs ys os : List Wire)
    (hxy : xs.length = ys.length) (hxo : xs.length = os.length) :
    (selectorColumns xs ys os).map (fun c => c.1) = xs ∧
      (selectorColumns xs ys os).map (fun c => c.2.1) = ys ∧
      (selectorColumns xs ys os).map (fun c => c.2.2) = os := by
  induction xs generalizing ys os with
  | nil =>
      cases ys with
      | nil =>
          cases os with
          | nil => simp [selectorColumns]
          | cons o os => simp at hxo
      | cons y ys => simp at hxy
  | cons x xs ih =>
      cases ys with
      | nil => simp at hxy
      | cons y ys =>
          cases os with
          | nil => simp at hxo
          | cons o os =>
              have hxy' : xs.length = ys.length := by simpa using hxy
              have hxo' : xs.length = os.length := by simpa using hxo
              obtain ⟨hleft, hright, hout⟩ := ih ys os hxy' hxo'
              simp [selectorColumns, hleft, hright, hout]

/-- Selector columns for width-indexed registers. -/
def Reg.selectorColumns {width : Nat} (x y out : Reg width) :
    List (Wire × Wire × Wire) :=
  ShorECDLP.ModExp.selectorColumns x.wires y.wires out.wires

theorem Reg.selectorColumns_maps {width : Nat} (x y out : Reg width) :
    (x.selectorColumns y out).map (fun c => c.1) = x.wires ∧
      (x.selectorColumns y out).map (fun c => c.2.1) = y.wires ∧
      (x.selectorColumns y out).map (fun c => c.2.2) = out.wires := by
  apply ShorECDLP.ModExp.selectorColumns_maps
  · rw [x.length_eq, y.length_eq]
  · rw [x.length_eq, out.length_eq]

theorem Reg.selectorColumns_length {width : Nat} (x y out : Reg width) :
    (x.selectorColumns y out).length = width := by
  have h := (x.selectorColumns_maps y out).1
  have := congrArg List.length h
  simpa [x.length_eq] using this

/-- M1.3.2's reversible point selector specialized to width-indexed registers. -/
def selectReg {width : Nat} (flag : Wire) (ifFalse ifTrue out : Reg width) : Circuit :=
  selectPoint flag (ifFalse.selectorColumns ifTrue out)

/-- The specialized selector writes exactly the chosen source value into a clean output. -/
theorem selectReg_correct {width : Nat} (flag : Wire) (ifFalse ifTrue out : Reg width)
    (st : BasisState) (hok : selectOK flag (ifFalse.selectorColumns ifTrue out))
    (hclean : Clean out.wires st) :
    regValue out.wires (Classical.run (selectReg flag ifFalse ifTrue out) st) =
      if st flag then regValue ifTrue.wires st else regValue ifFalse.wires st := by
  have hcols := ifFalse.selectorColumns_maps ifTrue out
  have hfresh : ∀ c ∈ ifFalse.selectorColumns ifTrue out, st c.2.2 = false := by
    intro c hc
    apply hclean c.2.2
    rw [← hcols.2.2]
    exact List.mem_map_of_mem hc
  simpa [selectReg, hcols.1, hcols.2.1, hcols.2.2] using
    selectPoint_correct flag (ifFalse.selectorColumns ifTrue out) st hok hfresh

/-- The selector changes no wire outside its output register. -/
theorem selectReg_other {width : Nat} (flag w : Wire) (ifFalse ifTrue out : Reg width)
    (st : BasisState) (hok : selectOK flag (ifFalse.selectorColumns ifTrue out))
    (hw : w ∉ out.wires) :
    Classical.run (selectReg flag ifFalse ifTrue out) st w = st w := by
  apply selectPoint_other flag w (ifFalse.selectorColumns ifTrue out) st hok
  simpa [(ifFalse.selectorColumns_maps ifTrue out).2.2] using hw

/-- One Toffoli per output bit gives exact selector cost `7 * width`. -/
theorem selectReg_tCount {width : Nat} (flag : Wire) (ifFalse ifTrue out : Reg width) :
    tCount (selectReg flag ifFalse ifTrue out) = 7 * width := by
  rw [selectReg, selectPoint_tCount, ifFalse.selectorColumns_length ifTrue out]

theorem selectReg_HPFree {width : Nat} (flag : Wire) (ifFalse ifTrue out : Reg width) :
    Classical.HPFree (selectReg flag ifFalse ifTrue out) := by
  exact selectPoint_HPFree flag (ifFalse.selectorColumns ifTrue out)

theorem selectReg_wellFormed {width : Nat} (flag : Wire) (ifFalse ifTrue out : Reg width)
    (hok : selectOK flag (ifFalse.selectorColumns ifTrue out)) :
    CircuitWellFormed (selectReg flag ifFalse ifTrue out) := by
  exact selectPoint_wellFormed flag (ifFalse.selectorColumns ifTrue out) hok

/-- Global duplicate-freedom of the selector roles discharges M1.3.2's local `selectOK`. -/
theorem selectOK_of_nodup {width : Nat} (flag : Wire) (ifFalse ifTrue out : Reg width)
    (hnodup : (flag :: (ifFalse.wires ++ ifTrue.wires ++ out.wires)).Nodup) :
    selectOK flag (ifFalse.selectorColumns ifTrue out) := by
  have hmaps := ifFalse.selectorColumns_maps ifTrue out
  obtain ⟨hflag, hbody⟩ := List.nodup_cons.mp hnodup
  have hshape : (ifFalse.wires ++ (ifTrue.wires ++ out.wires)).Nodup := by
    simpa [List.append_assoc] using hbody
  obtain ⟨hfalseNd, htailNd, hfalseTail⟩ := List.nodup_append.mp hshape
  obtain ⟨htrueNd, houtNd, htrueOut⟩ := List.nodup_append.mp htailNd
  simp only [selectOK]
  rw [hmaps.2.2]
  refine ⟨houtNd, ?_, ?_⟩
  · intro hf
    apply hflag
    simp [hf]
  · intro c hc
    have hcFalse : c.1 ∈ ifFalse.wires := by
      rw [← hmaps.1]
      exact List.mem_map_of_mem hc
    have hcTrue : c.2.1 ∈ ifTrue.wires := by
      rw [← hmaps.2.1]
      exact List.mem_map_of_mem hc
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro ho
      exact hfalseTail c.1 hcFalse c.1 (by simp [ho]) rfl
    · intro ho
      exact htrueOut c.2.1 hcTrue c.2.1 ho rfl
    · intro heq
      apply hflag
      simp [heq, hcFalse]
    · intro heq
      apply hflag
      simp [heq, hcTrue]
    · exact hfalseTail c.1 hcFalse c.2.1 (by simp [hcTrue])

/-- The specialized selector reads and writes only its flag and three declared registers. -/
theorem selectReg_usesOnly {width : Nat} (flag : Wire) (ifFalse ifTrue out : Reg width) :
    CircuitUsesOnly (flag :: (ifFalse.wires ++ ifTrue.wires ++ out.wires))
      (selectReg flag ifFalse ifTrue out) := by
  apply usesOnly_mono (selectPoint_usesOnly flag (ifFalse.selectorColumns ifTrue out))
  intro w hw
  simp only [selectFootprint, List.mem_cons] at hw ⊢
  rcases hw with rfl | hw
  · exact Or.inl rfl
  · simp only [List.mem_flatMap] at hw
    obtain ⟨c, hc, hwc⟩ := hw
    have hmaps := ifFalse.selectorColumns_maps ifTrue out
    have hx : c.1 ∈ ifFalse.wires := by
      rw [← hmaps.1]
      exact List.mem_map_of_mem hc
    have hy : c.2.1 ∈ ifTrue.wires := by
      rw [← hmaps.2.1]
      exact List.mem_map_of_mem hc
    have ho : c.2.2 ∈ out.wires := by
      rw [← hmaps.2.2]
      exact List.mem_map_of_mem hc
    have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hwc
    rcases hw' with rfl | rfl | rfl
    · simp [hx]
    · simp [hy]
    · simp [ho]

/-! ## Multiplicative-identity initialization -/

/-- Load the literal one into a clean accumulator using the existing X-only constant loader. -/
def initOne {width : Nat} (acc : Reg width) : Circuit :=
  loadConst acc.wires 1

theorem initOne_correct {width : Nat} (acc : Reg width) (st : BasisState)
    (hnodup : acc.wires.Nodup) (hclean : Clean acc.wires st) (hwidth : 0 < width) :
    regValue acc.wires (Classical.run (initOne acc) st) = 1 := by
  apply loadConst_correct acc.wires 1 st hnodup hclean
  rw [acc.length_eq]
  exact Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)

theorem initOne_other {width : Nat} (acc : Reg width) (st : BasisState) (w : Wire)
    (hw : w ∉ acc.wires) :
    Classical.run (initOne acc) st w = st w :=
  loadConst_other w acc.wires 1 st hw

theorem initOne_usesOnly {width : Nat} (acc : Reg width) :
    CircuitUsesOnly acc.wires (initOne acc) :=
  loadConst_usesOnly acc.wires 1

theorem initOne_tCount {width : Nat} (acc : Reg width) :
    tCount (initOne acc) = 0 :=
  loadConst_tCount acc.wires 1

theorem initOne_HPFree {width : Nat} (acc : Reg width) :
    Classical.HPFree (initOne acc) :=
  loadConst_HPFree acc.wires 1

theorem initOne_wellFormed {width : Nat} (acc : Reg width) :
    CircuitWellFormed (initOne acc) :=
  loadConst_wellFormed acc.wires 1

/-- Public ports and private workspace of one placed modular-multiplication call. -/
structure MulPorts (width : Nat) where
  lhs : Reg width
  rhs : Reg width
  out : Reg width
  work : List Wire

namespace MulPorts

/-- Forget the width indices to obtain the shared arithmetic-contract layout. -/
def layout {width : Nat} (ports : MulPorts width) : RegisterLayout where
  lhs := ports.lhs.wires
  rhs := ports.rhs.wires
  out := ports.out.wires
  work := ports.work

end MulPorts

/-- One exact program, cost, placement, and M1.4 certificate. -/
structure MulCall (width modulus : Nat) where
  ports : MulPorts width
  program : Circuit
  cost : Nat
  certified : ModMulContract program ports.layout modulus cost

namespace MulCall

/-- Enlarge the certified call's four declared register roles into a caller support. -/
theorem usesOnly {width modulus : Nat} (call : MulCall width modulus) (ws : List Wire)
    (hlhs : ∀ w ∈ call.ports.lhs.wires, w ∈ ws)
    (hrhs : ∀ w ∈ call.ports.rhs.wires, w ∈ ws)
    (hout : ∀ w ∈ call.ports.out.wires, w ∈ ws)
    (hwork : ∀ w ∈ call.ports.work, w ∈ ws) :
    CircuitUsesOnly ws call.program := by
  apply usesOnly_mono call.certified.usesOnly
  intro w hw
  simp only [MulPorts.layout, RegisterLayout.allWires, List.mem_append] at hw
  rcases hw with ((hw | hw) | hw) | hw
  · exact hlhs w hw
  · exact hrhs w hw
  · exact hout w hw
  · exact hwork w hw

/-- Equal width indices reduce local validity to duplicate-freedom of the call footprint. -/
theorem layoutValid_of_nodup {width modulus : Nat} (call : MulCall width modulus)
    (hnodup : call.ports.layout.allWires.Nodup) : call.ports.layout.Valid := by
  refine ⟨?_, ?_, hnodup⟩
  · rw [MulPorts.layout, call.ports.lhs.length_eq, call.ports.rhs.length_eq]
  · rw [MulPorts.layout, call.ports.lhs.length_eq, call.ports.out.length_eq]

end MulCall

/--
A typed LSB-first execution schedule.

`last` deliberately has no squaring call.  A `cons` step has another bit to process, so it
copies the current power into a distinct register and certifies a separate square.  The
indices enforce accumulator/power continuity and bind the scheduled bits to the public
exponent register without propositional list equalities.
-/
inductive Schedule (width modulus : Nat) (mulWork : List Wire) (duplicate : Reg width) :
    Reg width → Reg width → List Wire → Reg width → Type where
  | nil (acc power : Reg width) :
      Schedule width modulus mulWork duplicate acc power List.nil acc
  | last (acc power : Reg width) (bit : Wire)
      (product nextAcc : Reg width) (accMul : MulCall width modulus)
      (accLhs : accMul.ports.lhs = power)
      (accRhs : accMul.ports.rhs = acc)
      (accOut : accMul.ports.out = product)
      (accWork : accMul.ports.work = mulWork) :
      Schedule width modulus mulWork duplicate acc power (bit :: List.nil) nextAcc
  | cons (acc power : Reg width) (bit nextBit : Wire) (bits : List Wire)
      (nextPower product nextAcc finalAcc : Reg width)
      (accMul squareMul : MulCall width modulus)
      (accLhs : accMul.ports.lhs = power)
      (accRhs : accMul.ports.rhs = acc)
      (accOut : accMul.ports.out = product)
      (accWork : accMul.ports.work = mulWork)
      (squareLhs : squareMul.ports.lhs = power)
      (squareRhs : squareMul.ports.rhs = duplicate)
      (squareOut : squareMul.ports.out = nextPower)
      (squareWork : squareMul.ports.work = mulWork)
      (tail : Schedule width modulus mulWork duplicate nextAcc nextPower
        (nextBit :: bits) finalAcc) :
      Schedule width modulus mulWork duplicate acc power (bit :: nextBit :: bits) finalAcc

namespace Schedule

/-- Registers and callee workspaces owned by a schedule, each listed exactly once. -/
def owned {width modulus : Nat} {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) : List Wire :=
  match schedule with
  | .nil _ _ => []
  | .last _ _ _ product nextAcc _ _ _ _ _ =>
      product.wires ++ nextAcc.wires
  | .cons _ _ _ _ _ nextPower product nextAcc _ _ _
      _ _ _ _ _ _ _ _ tail =>
      nextPower.wires ++ product.wires ++ nextAcc.wires ++ tail.owned

/-- Exact T-count of the forward history-building pass, assuming one Toffoli selector per bit. -/
def forwardCost {width modulus : Nat} {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) : Nat :=
  match schedule with
  | .nil _ _ => 0
  | .last _ _ _ _ _ accMul _ _ _ _ => accMul.cost + 7 * width
  | .cons _ _ _ _ _ _ _ _ _ accMul squareMul _ _ _ _ _ _ _ _ tail =>
      accMul.cost + squareMul.cost + 7 * width + tail.forwardCost

/-- Complete support of a final multiply/select step. -/
def lastSupport {width : Nat} (flag : Wire) (power acc product nextAcc : Reg width)
    (mulWork : List Wire) : List Wire :=
  flag :: (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++ mulWork)

/-- Complete support of a non-final multiply/select/copy/square step. -/
def consSupport {width : Nat} (flag : Wire) (power acc product nextAcc : Reg width)
    (duplicate nextPower : Reg width) (mulWork : List Wire) : List Wire :=
  flag :: (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
    duplicate.wires ++ nextPower.wires ++ mulWork)

/-- Pairwise cross-list wire distinctness. -/
def WireDisjoint (xs ys : List Wire) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y

/--
Static validity of a typed schedule.  Each local step support is duplicate-free, and the
step is disjoint from still-fresh exponent/history owners.  The intentionally shared
`duplicate` and `mulWork` registers are excluded from the future set: each step restores them
clean before recursion.
-/
def Valid {width modulus : Nat} {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) : Prop :=
  match schedule with
  | .nil _ _ => True
  | .last _ power flag product nextAcc _ _ _ _ _ =>
      (lastSupport flag power acc product nextAcc mulWork).Nodup
  | .cons _ power flag nextBit bits nextPower product nextAcc _ _ _
      _ _ _ _ _ _ _ _ tail =>
      (consSupport flag power acc product nextAcc duplicate nextPower mulWork).Nodup ∧
        WireDisjoint
          (consSupport flag power acc product nextAcc duplicate nextPower mulWork)
          ((nextBit :: bits) ++ tail.owned) ∧
        tail.Valid

/-- Forward history computation in exact execution order. -/
def forward {width modulus : Nat} {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) : Circuit :=
  match schedule with
  | .nil _ _ => []
  | .last acc _ flag product nextAcc accMul _ _ _ _ =>
      accMul.program ++ selectReg flag acc product nextAcc
  | .cons acc power flag _ _ _ product nextAcc _ accMul squareMul
      _ _ _ _ _ _ _ _ tail =>
      accMul.program ++ selectReg flag acc product nextAcc ++
        copyReg power.wires duplicate.wires ++ squareMul.program ++
        (copyReg power.wires duplicate.wires).reverse ++ tail.forward

/-- Every wire read or written by the forward computation. -/
def activeWires {width modulus : Nat} {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) : List Wire :=
  bits ++ power.wires ++ acc.wires ++ schedule.owned ++ duplicate.wires ++ mulWork

/-- Number of certified multiplier executions in the forward pass. -/
def multiplierCalls {width modulus : Nat} {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) : Nat :=
  match schedule with
  | .nil _ _ => 0
  | .last .. => 1
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => 2 + tail.multiplierCalls

/-- Omitting the final square gives `2*n - 1` calls for a nonempty `n`-bit schedule. -/
theorem multiplierCalls_eq {width modulus : Nat}
    {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) :
    schedule.multiplierCalls = 2 * bits.length - 1 := by
  induction schedule with
  | nil => simp [multiplierCalls]
  | last => simp [multiplierCalls]
  | cons acc power bit nextBit bits nextPower product nextAcc finalAcc
      accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
      squareWork tail ih =>
      simp only [multiplierCalls, List.length_cons]
      rw [ih]
      simp only [List.length_cons]
      omega

/-- Every certified modular-multiplication call in a schedule has one common exact cost. -/
def UniformMulCost (mulCost : Nat) :
    {width modulus : Nat} → {mulWork : List Wire} → {duplicate acc power : Reg width} →
      {bits : List Wire} → {finalAcc : Reg width} →
      Schedule width modulus mulWork duplicate acc power bits finalAcc → Prop
  | _, _, _, _, _, _, _, _, .nil .. => True
  | _, _, _, _, _, _, _, _, .last _ _ _ _ _ accMul _ _ _ _ =>
      accMul.cost = mulCost
  | _, _, _, _, _, _, _, _,
      .cons _ _ _ _ _ _ _ _ _ accMul squareMul _ _ _ _ _ _ _ _ tail =>
      accMul.cost = mulCost ∧ squareMul.cost = mulCost ∧ tail.UniformMulCost mulCost

/-- A uniform-cost schedule charges one multiplier cost per structural call and one selector
cost per exponent bit. -/
theorem forwardCost_eq_of_uniform {width modulus mulCost : Nat}
    {mulWork : List Wire} {duplicate acc power : Reg width} {bits : List Wire}
    {finalAcc : Reg width}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc)
    (huniform : schedule.UniformMulCost mulCost) :
    schedule.forwardCost =
      schedule.multiplierCalls * mulCost + 7 * width * bits.length := by
  induction schedule with
  | nil => simp [forwardCost, multiplierCalls]
  | last acc power bit product nextAcc accMul accLhs accRhs accOut accWork =>
      simp only [UniformMulCost] at huniform
      simp [forwardCost, multiplierCalls, huniform]
  | cons acc power bit nextBit bits nextPower product nextAcc finalAcc
      accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
      squareWork tail ih =>
      rcases huniform with ⟨hacc, hsquare, htail⟩
      simp only [forwardCost, multiplierCalls, List.length_cons, hacc, hsquare]
      rw [ih htail]
      simp [Nat.add_mul, Nat.mul_add, Nat.two_mul, Nat.mul_two, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

/-- The forward pass is confined to its remaining bits, live registers, owned history, and
the two deliberately shared scratch regions. -/
theorem forward_usesOnly :
    ∀ {width modulus : Nat} {mulWork duplicate acc power bits finalAcc}
      (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc)
      (ws : List Wire),
      (∀ w ∈ bits, w ∈ ws) →
      (∀ w ∈ power.wires, w ∈ ws) →
      (∀ w ∈ acc.wires, w ∈ ws) →
      (∀ w ∈ schedule.owned, w ∈ ws) →
      (∀ w ∈ duplicate.wires, w ∈ ws) →
      (∀ w ∈ mulWork, w ∈ ws) →
      CircuitUsesOnly ws schedule.forward := by
  intro width modulus mulWork duplicate acc power bits finalAcc schedule
  induction schedule with
  | nil acc power =>
      intro ws _ _ _ _ _ _
      simp [forward, CircuitUsesOnly]
  | last acc power flag product nextAcc accMul accLhs accRhs accOut accWork =>
      intro ws hbits hpower hacc howned hduplicate hwork
      have hproduct : ∀ w ∈ product.wires, w ∈ ws := by
        intro w hw
        exact howned w (by simp [owned, hw])
      have hnextAcc : ∀ w ∈ nextAcc.wires, w ∈ ws := by
        intro w hw
        exact howned w (by simp [owned, hw])
      have hmul : CircuitUsesOnly ws accMul.program := by
        apply accMul.usesOnly ws
        · intro w hw; rw [accLhs] at hw; exact hpower w hw
        · intro w hw; rw [accRhs] at hw; exact hacc w hw
        · intro w hw; rw [accOut] at hw; exact hproduct w hw
        · intro w hw; rw [accWork] at hw; exact hwork w hw
      have hselect : CircuitUsesOnly ws (selectReg flag acc product nextAcc) := by
        apply usesOnly_mono (selectReg_usesOnly flag acc product nextAcc)
        intro w hw
        rcases List.mem_cons.mp hw with hw | hw
        · rw [hw]
          exact hbits flag (List.mem_cons_self ..)
        · rcases List.mem_append.mp hw with hw | hw
          · rcases List.mem_append.mp hw with hw | hw
            · exact hacc w hw
            · exact hproduct w hw
          · exact hnextAcc w hw
      simpa [forward] using usesOnly_append hmul hselect
  | cons acc power flag nextFlag bits nextPower product nextAcc finalAcc
      accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
      squareWork tail ih =>
      intro ws hbits hpower hacc howned hduplicate hwork
      have hnextPower : ∀ w ∈ nextPower.wires, w ∈ ws := by
        intro w hw
        exact howned w (by simp [owned, hw])
      have hproduct : ∀ w ∈ product.wires, w ∈ ws := by
        intro w hw
        exact howned w (by simp [owned, hw])
      have hnextAcc : ∀ w ∈ nextAcc.wires, w ∈ ws := by
        intro w hw
        exact howned w (by simp [owned, hw])
      have htailOwned : ∀ w ∈ tail.owned, w ∈ ws := by
        intro w hw
        exact howned w (by simp [owned, hw])
      have hmul : CircuitUsesOnly ws accMul.program := by
        apply accMul.usesOnly ws
        · intro w hw; rw [accLhs] at hw; exact hpower w hw
        · intro w hw; rw [accRhs] at hw; exact hacc w hw
        · intro w hw; rw [accOut] at hw; exact hproduct w hw
        · intro w hw; rw [accWork] at hw; exact hwork w hw
      have hselect : CircuitUsesOnly ws (selectReg flag acc product nextAcc) := by
        apply usesOnly_mono (selectReg_usesOnly flag acc product nextAcc)
        intro w hw
        rcases List.mem_cons.mp hw with hw | hw
        · rw [hw]
          exact hbits flag (List.mem_cons_self ..)
        · rcases List.mem_append.mp hw with hw | hw
          · rcases List.mem_append.mp hw with hw | hw
            · exact hacc w hw
            · exact hproduct w hw
          · exact hnextAcc w hw
      have hcopy : CircuitUsesOnly ws (copyReg power.wires duplicate.wires) :=
        copyReg_usesOnly power.wires duplicate.wires ws hpower hduplicate
      have hsquare : CircuitUsesOnly ws squareMul.program := by
        apply squareMul.usesOnly ws
        · intro w hw; rw [squareLhs] at hw; exact hpower w hw
        · intro w hw; rw [squareRhs] at hw; exact hduplicate w hw
        · intro w hw; rw [squareOut] at hw; exact hnextPower w hw
        · intro w hw; rw [squareWork] at hw; exact hwork w hw
      have htailBits : ∀ w ∈ nextFlag :: bits, w ∈ ws := by
        intro w hw
        exact hbits w (List.mem_cons_of_mem flag hw)
      have htail := ih ws htailBits hnextPower hnextAcc htailOwned hduplicate hwork
      simpa [forward, List.append_assoc] using
        usesOnly_append (usesOnly_append (usesOnly_append
          (usesOnly_append (usesOnly_append hmul hselect) hcopy) hsquare)
          (usesOnly_reverse hcopy)) htail

theorem forward_usesOnly_active {width modulus : Nat}
    {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) :
    CircuitUsesOnly schedule.activeWires schedule.forward := by
  apply forward_usesOnly schedule schedule.activeWires
  · intro w hw; simp [activeWires, hw]
  · intro w hw; simp [activeWires, hw]
  · intro w hw; simp [activeWires, hw]
  · intro w hw; simp [activeWires, hw]
  · intro w hw; simp [activeWires, hw]
  · intro w hw; simp [activeWires, hw]

theorem forward_HPFree {width modulus : Nat}
    {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) :
    Classical.HPFree schedule.forward := by
  induction schedule with
  | nil => simp [forward]
  | last acc power flag product nextAcc accMul accLhs accRhs accOut accWork =>
      simp [forward, accMul.certified.hpFree, selectReg_HPFree]
  | cons acc power flag nextFlag bits nextPower product nextAcc finalAcc
      accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
      squareWork tail ih =>
      simp [forward, accMul.certified.hpFree, squareMul.certified.hpFree,
        selectReg_HPFree, copyReg_HPFree, Arithmetic.hpFree_reverse, ih]

theorem forward_tCount {width modulus : Nat}
    {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) :
    tCount schedule.forward = schedule.forwardCost := by
  induction schedule with
  | nil => simp [forward, forwardCost]
  | last acc power flag product nextAcc accMul accLhs accRhs accOut accWork =>
      rw [forward, tCount_append, accMul.certified.counted, selectReg_tCount]
      rfl
  | cons acc power flag nextFlag bits nextPower product nextAcc finalAcc
      accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
      squareWork tail ih =>
      simp only [forward, tCount_append, accMul.certified.counted,
        selectReg_tCount, copyReg_tCount, squareMul.certified.counted,
        Arithmetic.tCount_reverse, ih, Nat.add_zero, forwardCost]
      omega

theorem forward_wellFormed {width modulus : Nat}
    {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc)
    (hvalid : schedule.Valid) : CircuitWellFormed schedule.forward := by
  induction schedule with
  | nil => simp [forward]
  | last acc power flag product nextAcc accMul accLhs accRhs accOut accWork =>
      have hbody :
          (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++ mulWork).Nodup := by
        simpa [Valid, lastSupport] using (List.nodup_cons.mp hvalid).2
      let accHead := power.wires ++ acc.wires ++ product.wires
      have hmulSub :
          (power.wires ++ acc.wires ++ product.wires ++ mulWork).Sublist
            (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++ mulWork) := by
        simp [List.append_assoc]
      have hmulNd : accMul.ports.layout.allWires.Nodup := by
        have := List.Nodup.sublist hmulSub hbody
        simpa [MulPorts.layout, RegisterLayout.allWires, accLhs, accRhs, accOut, accWork,
          List.append_assoc] using this
      let selected := acc.wires ++ product.wires ++ nextAcc.wires
      have hselectBody : selected.Sublist
          (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++ mulWork) := by
        have hskipPower := List.sublist_append_right power.wires selected
        have hskipWork := List.sublist_append_left (power.wires ++ selected) mulWork
        simp [selected, List.append_assoc]
      have hselectNd : (flag :: selected).Nodup :=
        List.Nodup.sublist (hselectBody.cons₂ flag) hvalid
      have hmulWf := accMul.certified.wellFormed (accMul.layoutValid_of_nodup hmulNd)
      have hselectWf := selectReg_wellFormed flag acc product nextAcc
        (selectOK_of_nodup flag acc product nextAcc (by simpa [selected] using hselectNd))
      rw [forward, circuitWellFormed_append]
      exact ⟨hmulWf, hselectWf⟩
  | cons acc power flag nextFlag bits nextPower product nextAcc finalAcc
      accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
      squareWork tail ih =>
      rcases hvalid with ⟨hstage, hfuture, htail⟩
      have hbody :
          (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
            duplicate.wires ++ nextPower.wires ++ mulWork).Nodup := by
        simpa [consSupport] using (List.nodup_cons.mp hstage).2
      let accPrefix := power.wires ++ acc.wires ++ product.wires
      let accMiddle := nextAcc.wires ++ duplicate.wires ++ nextPower.wires
      have haccSub :
          (power.wires ++ acc.wires ++ product.wires ++ mulWork).Sublist
            (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
              duplicate.wires ++ nextPower.wires ++ mulWork) := by
        simpa [accPrefix, accMiddle, List.append_assoc] using
          (List.Sublist.refl accPrefix).append
            (List.sublist_append_right accMiddle mulWork)
      have haccNd : accMul.ports.layout.allWires.Nodup := by
        have := List.Nodup.sublist haccSub hbody
        simpa [MulPorts.layout, RegisterLayout.allWires, accLhs, accRhs, accOut, accWork,
          List.append_assoc] using this
      let squareMiddle := acc.wires ++ product.wires ++ nextAcc.wires
      let squareTail := duplicate.wires ++ nextPower.wires ++ mulWork
      have hsquareSub :
          (power.wires ++ duplicate.wires ++ nextPower.wires ++ mulWork).Sublist
            (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
              duplicate.wires ++ nextPower.wires ++ mulWork) := by
        simpa [squareMiddle, squareTail, List.append_assoc] using
          (List.Sublist.refl power.wires).append
            (List.sublist_append_right squareMiddle squareTail)
      have hsquareNd : squareMul.ports.layout.allWires.Nodup := by
        have := List.Nodup.sublist hsquareSub hbody
        simpa [MulPorts.layout, RegisterLayout.allWires, squareLhs, squareRhs, squareOut,
          squareWork, List.append_assoc] using this
      let copyPrefix := power.wires ++ squareMiddle ++ duplicate.wires
      have hcopyCore : (power.wires ++ duplicate.wires).Sublist copyPrefix := by
        simpa [copyPrefix, squareMiddle, List.append_assoc] using
          (List.Sublist.refl power.wires).append
            (List.sublist_append_right squareMiddle duplicate.wires)
      have hcopySub :
          (power.wires ++ duplicate.wires).Sublist
            (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
              duplicate.wires ++ nextPower.wires ++ mulWork) := by
        have hrest := List.sublist_append_left copyPrefix (nextPower.wires ++ mulWork)
        simpa [copyPrefix, squareMiddle, List.append_assoc] using hcopyCore.trans hrest
      have hcopyNd : (power.wires ++ duplicate.wires).Nodup :=
        List.Nodup.sublist hcopySub hbody
      let selected := acc.wires ++ product.wires ++ nextAcc.wires
      let selectSuffix := duplicate.wires ++ nextPower.wires ++ mulWork
      have hselectBody : selected.Sublist
          (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
            duplicate.wires ++ nextPower.wires ++ mulWork) := by
        have hskipPower := List.sublist_append_right power.wires selected
        have hskipSuffix := List.sublist_append_left (power.wires ++ selected) selectSuffix
        simp [selected, List.append_assoc]
      have hselectNd : (flag :: selected).Nodup :=
        List.Nodup.sublist (hselectBody.cons₂ flag) hstage
      have hmulWf := accMul.certified.wellFormed (accMul.layoutValid_of_nodup haccNd)
      have hselectWf := selectReg_wellFormed flag acc product nextAcc
        (selectOK_of_nodup flag acc product nextAcc (by simpa [selected] using hselectNd))
      have hcopyWf := copyReg_wellFormed power.wires duplicate.wires hcopyNd
      have hsquareWf :=
        squareMul.certified.wellFormed (squareMul.layoutValid_of_nodup hsquareNd)
      have htailWf := ih htail
      simp [forward, hmulWf, hselectWf, hcopyWf, hsquareWf,
        Arithmetic.wellFormed_reverse hcopyWf, htailWf]

/-- The final accumulator is one of the accumulator owners reserved in the schedule history. -/
theorem finalAcc_sublist_work {width modulus : Nat}
    {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) :
    finalAcc.wires.Sublist (acc.wires ++ schedule.owned) := by
  induction schedule with
  | nil => simp [owned]
  | last acc power flag product nextAcc accMul accLhs accRhs accOut accWork =>
      simp [owned]
  | cons acc power flag nextFlag bits nextPower product nextAcc finalAcc
      accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
      squareWork tail ih =>
      have hpref := List.sublist_append_right
        (acc.wires ++ nextPower.wires ++ product.wires) (nextAcc.wires ++ tail.owned)
      simpa [owned, List.append_assoc] using ih.trans hpref

/--
Semantic interface of the forward schedule.  Besides the accumulator recurrence it records
that the two deliberately shared scratch regions are clean at the recursive handoff.
-/
def ForwardCorrectStatement {width modulus : Nat}
    {mulWork duplicate acc power bits finalAcc}
    (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc) : Prop :=
  ∀ st : BasisState,
    schedule.Valid →
    schedule.activeWires.Nodup →
    1 < modulus →
    regValue acc.wires st < modulus →
    regValue power.wires st < modulus →
    Clean (schedule.owned ++ duplicate.wires ++ mulWork) st →
    let after := Classical.run schedule.forward st
    regValue finalAcc.wires after =
        squareMultiplyAcc modulus (regValue acc.wires st)
          (regValue power.wires st) (bits.map st) ∧
      Clean (duplicate.wires ++ mulWork) after

open Classical

theorem forward_correct :
    ∀ {width modulus : Nat} {mulWork : List Wire} {duplicate acc power : Reg width}
      {bits : List Wire} {finalAcc : Reg width}
      (schedule : Schedule width modulus mulWork duplicate acc power bits finalAcc)
      (st : BasisState),
      schedule.Valid → schedule.activeWires.Nodup → 1 < modulus →
      regValue acc.wires st < modulus → regValue power.wires st < modulus →
      Clean (schedule.owned ++ duplicate.wires ++ mulWork) st →
      let after := run schedule.forward st
      regValue finalAcc.wires after =
          squareMultiplyAcc modulus (regValue acc.wires st) (regValue power.wires st)
            (bits.map st) ∧
        Clean (duplicate.wires ++ mulWork) after := by
  intro width modulus mulWork duplicate acc power bits finalAcc schedule
  induction schedule with
  | nil acc power =>
      intro st _ _ _ _ _ hclean
      constructor
      · rfl
      · simpa [owned] using hclean
  | last acc power flag product nextAcc accMul accLhs accRhs accOut accWork =>
      intro st hvalid hactive hmod haccBound hpowerBound hclean
      have hbody :
          (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++ mulWork).Nodup := by
        simpa [Valid, lastSupport] using (List.nodup_cons.mp hvalid).2
      let front := power.wires ++ acc.wires ++ product.wires
      have hbodyShape : (front ++ (nextAcc.wires ++ mulWork)).Nodup := by
        simpa [front, List.append_assoc] using hbody
      obtain ⟨hfrontNd, hnextWorkNd, hfrontNextWork⟩ :=
        List.nodup_append.mp hbodyShape
      obtain ⟨hnextNd, hworkNd, hnextWork⟩ :=
        List.nodup_append.mp hnextWorkNd
      have hactiveShape :
          ((flag :: (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires)) ++
            (duplicate.wires ++ mulWork)).Nodup := by
        simpa [activeWires, owned, List.append_assoc] using hactive
      obtain ⟨hbeforeDupNd, hdupWorkNd, hbeforeDup⟩ :=
        List.nodup_append.mp hactiveShape
      obtain ⟨hdupNd, hworkNd', hdupWork⟩ := List.nodup_append.mp hdupWorkNd

      have hmulSub :
          (power.wires ++ acc.wires ++ product.wires ++ mulWork).Sublist
            (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++ mulWork) := by
        simp [List.append_assoc]
      have hmulNd : accMul.ports.layout.allWires.Nodup := by
        have := List.Nodup.sublist hmulSub hbody
        simpa [MulPorts.layout, RegisterLayout.allWires, accLhs, accRhs, accOut, accWork,
          List.append_assoc] using this
      have hmulValid := accMul.layoutValid_of_nodup hmulNd

      let selected := acc.wires ++ product.wires ++ nextAcc.wires
      have hselectBody : selected.Sublist
          (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++ mulWork) := by
        have hskipPower := List.sublist_append_right power.wires selected
        have hskipWork := List.sublist_append_left (power.wires ++ selected) mulWork
        simp [selected, List.append_assoc]
      have hselectNd : (flag :: selected).Nodup :=
        List.Nodup.sublist (hselectBody.cons₂ flag) hvalid
      have hselectOK := selectOK_of_nodup flag acc product nextAcc
        (by simpa [selected] using hselectNd)

      have hnextOutside (w : Wire) (hw : w ∈ nextAcc.wires) :
          w ∉ accMul.ports.layout.allWires := by
        intro hmem
        simp only [MulPorts.layout, RegisterLayout.allWires, List.mem_append,
          accLhs, accRhs, accOut, accWork] at hmem
        have hmem' : w ∈ front ∨ w ∈ mulWork := by
          rcases hmem with ((hpower | haccMem) | hproduct) | hworkMem
          · exact Or.inl (by simp [front, hpower])
          · exact Or.inl (by simp [front, haccMem])
          · exact Or.inl (by simp [front, hproduct])
          · exact Or.inr hworkMem
        rcases hmem' with hfront | hwork
        · exact (hfrontNextWork w hfront w (by simp [hw])) rfl
        · exact (hnextWork w hw w hwork) rfl
      have hflagOutside : flag ∉ accMul.ports.layout.allWires := by
        intro hmem
        simp only [MulPorts.layout, RegisterLayout.allWires, List.mem_append,
          accLhs, accRhs, accOut, accWork] at hmem
        have hmem' : flag ∈
            power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++ mulWork := by
          rcases hmem with ((hpower | haccMem) | hproduct) | hworkMem
          · simp [hpower]
          · simp [haccMem]
          · simp [hproduct]
          · simp [hworkMem]
        exact (List.nodup_cons.mp hvalid).1 hmem'
      have hdupOutside (w : Wire) (hw : w ∈ duplicate.wires) :
          w ∉ accMul.ports.layout.allWires := by
        intro hmem
        simp only [MulPorts.layout, RegisterLayout.allWires, List.mem_append,
          accLhs, accRhs, accOut, accWork] at hmem
        have hmem' : w ∈ front ∨ w ∈ mulWork := by
          rcases hmem with ((hpower | haccMem) | hproduct) | hworkMem
          · exact Or.inl (by simp [front, hpower])
          · exact Or.inl (by simp [front, haccMem])
          · exact Or.inl (by simp [front, hproduct])
          · exact Or.inr hworkMem
        rcases hmem' with hfront | hwork
        · have hpre :
              w ∈ flag :: (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires) := by
            rw [List.mem_cons]
            refine Or.inr ?_
            simp only [List.mem_append]
            exact Or.inl (by simpa only [front, List.mem_append] using hfront)
          exact (hbeforeDup w hpre w (by simp [hw])) rfl
        · exact (hdupWork w hw w hwork) rfl
      have hdupNotNext (w : Wire) (hw : w ∈ duplicate.wires) : w ∉ nextAcc.wires := by
        intro hnext
        exact (hbeforeDup w (by simp [hnext]) w (by simp [hw])) rfl
      have hworkNotNext (w : Wire) (hw : w ∈ mulWork) : w ∉ nextAcc.wires := by
        intro hnext
        exact (hnextWork w hnext w hw) rfl

      have hcleanMul : Clean (product.wires ++ mulWork) st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · simp [owned, hw]
          · simp [owned, hw])
      let st1 := run accMul.program st
      let st2 := run (selectReg flag acc product nextAcc) st1
      have hmulResult :
          AgreesOn power.wires st st1 ∧ AgreesOn acc.wires st st1 ∧
            regValue product.wires st1 =
              regValue power.wires st * regValue acc.wires st % modulus ∧
            Clean mulWork st1 := by
        have hlhsBound : regValue accMul.ports.layout.lhs st < modulus := by
          simpa [MulPorts.layout, accLhs] using hpowerBound
        have hrhsBound : regValue accMul.ports.layout.rhs st < modulus := by
          simpa [MulPorts.layout, accRhs] using haccBound
        have hcleanMul' :
            Clean (accMul.ports.layout.out ++ accMul.ports.layout.work) st := by
          simpa [MulPorts.layout, accOut, accWork] using hcleanMul
        simpa [st1, MulPorts.layout, accLhs, accRhs, accOut, accWork] using
          accMul.certified.correct st hmulValid hlhsBound hrhsBound hcleanMul'
      rcases hmulResult with ⟨hpowerAgree, haccAgree, hproductValue, hworkCleanOne⟩
      have hnextCleanOne : Clean nextAcc.wires st1 := by
        intro w hw
        calc
          st1 w = st w := accMul.certified.usesOnly.preservesOutside st w
            (hnextOutside w hw)
          _ = false := hclean w (by simp [owned, hw])
      have hdupCleanOne : Clean duplicate.wires st1 := by
        intro w hw
        calc
          st1 w = st w := accMul.certified.usesOnly.preservesOutside st w
            (hdupOutside w hw)
          _ = false := hclean w (by simp [owned, hw])
      have hflagOne : st1 flag = st flag :=
        accMul.certified.usesOnly.preservesOutside st flag hflagOutside
      have hnextValue :
          regValue nextAcc.wires st2 =
            mulSelectStep modulus (regValue acc.wires st) (regValue power.wires st)
              (st flag) := by
        rw [show regValue nextAcc.wires st2 =
          (if st1 flag then regValue product.wires st1 else regValue acc.wires st1) from
            selectReg_correct flag acc product nextAcc st1 hselectOK hnextCleanOne]
        rw [hflagOne, Arithmetic.AgreesOn.regValue haccAgree, hproductValue]
        cases st flag <;> simp [mulSelectStep, selectAccumulator, productCandidate,
          Nat.mul_comm]
      have hdupCleanTwo : Clean duplicate.wires st2 := by
        intro w hw
        rw [show st2 w = st1 w from
          selectReg_other flag w acc product nextAcc st1 hselectOK (hdupNotNext w hw)]
        exact hdupCleanOne w hw
      have hworkCleanTwo : Clean mulWork st2 := by
        intro w hw
        rw [show st2 w = st1 w from
          selectReg_other flag w acc product nextAcc st1 hselectOK (hworkNotNext w hw)]
        exact hworkCleanOne w hw
      rw [forward, run_append]
      change regValue nextAcc.wires st2 = _ ∧ Clean (duplicate.wires ++ mulWork) st2
      constructor
      · simpa [squareMultiplyAcc] using hnextValue
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hdupCleanTwo w hw
        · exact hworkCleanTwo w hw
  | cons acc power flag nextFlag bits nextPower product nextAcc finalAcc
      accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
      squareWork tail ih =>
      intro st hvalid hactive hmod haccBound hpowerBound hclean
      rcases hvalid with ⟨hstage, hfuture, htailValid⟩
      have hbody :
          (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
            duplicate.wires ++ nextPower.wires ++ mulWork).Nodup := by
        simpa [consSupport] using (List.nodup_cons.mp hstage).2
      let front := power.wires ++ acc.wires ++ product.wires
      let suffix := nextAcc.wires ++ duplicate.wires ++ nextPower.wires ++ mulWork
      have hbodyShape : (front ++ suffix).Nodup := by
        simpa [front, suffix, List.append_assoc] using hbody
      obtain ⟨hfrontNd, hsuffixNd, hfrontSuffix⟩ := List.nodup_append.mp hbodyShape
      have hsuffixShape :
          (nextAcc.wires ++ (duplicate.wires ++ (nextPower.wires ++ mulWork))).Nodup := by
        simpa [suffix, List.append_assoc] using hsuffixNd
      obtain ⟨hnextAccNd, hafterNextAccNd, hnextAccAfter⟩ :=
        List.nodup_append.mp hsuffixShape
      obtain ⟨hdupNd, hpowerWorkNd, hdupPowerWork⟩ :=
        List.nodup_append.mp hafterNextAccNd
      obtain ⟨hnextPowerNd, hworkNd, hnextPowerWork⟩ :=
        List.nodup_append.mp hpowerWorkNd

      let accPrefix := power.wires ++ acc.wires ++ product.wires
      let accMiddle := nextAcc.wires ++ duplicate.wires ++ nextPower.wires
      have haccSub :
          (power.wires ++ acc.wires ++ product.wires ++ mulWork).Sublist
            (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
              duplicate.wires ++ nextPower.wires ++ mulWork) := by
        simpa [accPrefix, accMiddle, List.append_assoc] using
          (List.Sublist.refl accPrefix).append
            (List.sublist_append_right accMiddle mulWork)
      have haccNd : accMul.ports.layout.allWires.Nodup := by
        have := List.Nodup.sublist haccSub hbody
        simpa [MulPorts.layout, RegisterLayout.allWires, accLhs, accRhs, accOut, accWork,
          List.append_assoc] using this
      have haccValid := accMul.layoutValid_of_nodup haccNd

      let squareMiddle := acc.wires ++ product.wires ++ nextAcc.wires
      let squareTail := duplicate.wires ++ nextPower.wires ++ mulWork
      have hsquareSub :
          (power.wires ++ duplicate.wires ++ nextPower.wires ++ mulWork).Sublist
            (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
              duplicate.wires ++ nextPower.wires ++ mulWork) := by
        simpa [squareMiddle, squareTail, List.append_assoc] using
          (List.Sublist.refl power.wires).append
            (List.sublist_append_right squareMiddle squareTail)
      have hsquareNd : squareMul.ports.layout.allWires.Nodup := by
        have := List.Nodup.sublist hsquareSub hbody
        simpa [MulPorts.layout, RegisterLayout.allWires, squareLhs, squareRhs, squareOut,
          squareWork, List.append_assoc] using this
      have hsquareValid := squareMul.layoutValid_of_nodup hsquareNd

      let copyPrefix := power.wires ++ squareMiddle ++ duplicate.wires
      have hcopyCore : (power.wires ++ duplicate.wires).Sublist copyPrefix := by
        simpa [copyPrefix, squareMiddle, List.append_assoc] using
          (List.Sublist.refl power.wires).append
            (List.sublist_append_right squareMiddle duplicate.wires)
      have hcopySub :
          (power.wires ++ duplicate.wires).Sublist
            (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
              duplicate.wires ++ nextPower.wires ++ mulWork) := by
        have hrest := List.sublist_append_left copyPrefix (nextPower.wires ++ mulWork)
        simpa [copyPrefix, squareMiddle, List.append_assoc] using hcopyCore.trans hrest
      have hcopyNd : (power.wires ++ duplicate.wires).Nodup :=
        List.Nodup.sublist hcopySub hbody

      let selected := acc.wires ++ product.wires ++ nextAcc.wires
      let selectSuffix := duplicate.wires ++ nextPower.wires ++ mulWork
      have hselectBody : selected.Sublist
          (power.wires ++ acc.wires ++ product.wires ++ nextAcc.wires ++
            duplicate.wires ++ nextPower.wires ++ mulWork) := by
        have hskipPower := List.sublist_append_right power.wires selected
        have hskipSuffix := List.sublist_append_left (power.wires ++ selected) selectSuffix
        simp [selected, List.append_assoc]
      have hselectNd : (flag :: selected).Nodup :=
        List.Nodup.sublist (hselectBody.cons₂ flag) hstage
      have hselectOK := selectOK_of_nodup flag acc product nextAcc
        (by simpa [selected] using hselectNd)

      have hflagOutsideAcc : flag ∉ accMul.ports.layout.allWires := by
        intro hmem
        apply (List.nodup_cons.mp hstage).1
        simp only [MulPorts.layout, RegisterLayout.allWires, List.mem_append,
          accLhs, accRhs, accOut, accWork] at hmem
        rcases hmem with ((hp | ha) | ho) | hw
        · simp [hp]
        · simp [ha]
        · simp [ho]
        · simp [hw]
      have hnextAccOutsideAcc (w : Wire) (hw : w ∈ nextAcc.wires) :
          w ∉ accMul.ports.layout.allWires := by
        intro hmem
        simp only [MulPorts.layout, RegisterLayout.allWires, List.mem_append,
          accLhs, accRhs, accOut, accWork] at hmem
        rcases hmem with ((hp | ha) | ho) | hwork
        · exact (hfrontSuffix w (by simp [front, hp]) w (by simp [suffix, hw])) rfl
        · exact (hfrontSuffix w (by simp [front, ha]) w (by simp [suffix, hw])) rfl
        · exact (hfrontSuffix w (by simp [front, ho]) w (by simp [suffix, hw])) rfl
        · exact (hnextAccAfter w hw w (by simp [hwork])) rfl
      have hdupOutsideAcc (w : Wire) (hw : w ∈ duplicate.wires) :
          w ∉ accMul.ports.layout.allWires := by
        intro hmem
        simp only [MulPorts.layout, RegisterLayout.allWires, List.mem_append,
          accLhs, accRhs, accOut, accWork] at hmem
        rcases hmem with ((hp | ha) | ho) | hwork
        · exact (hfrontSuffix w (by simp [front, hp]) w (by simp [suffix, hw])) rfl
        · exact (hfrontSuffix w (by simp [front, ha]) w (by simp [suffix, hw])) rfl
        · exact (hfrontSuffix w (by simp [front, ho]) w (by simp [suffix, hw])) rfl
        · exact (hdupPowerWork w hw w (by simp [hwork])) rfl
      have hnextPowerOutsideAcc (w : Wire) (hw : w ∈ nextPower.wires) :
          w ∉ accMul.ports.layout.allWires := by
        intro hmem
        simp only [MulPorts.layout, RegisterLayout.allWires, List.mem_append,
          accLhs, accRhs, accOut, accWork] at hmem
        rcases hmem with ((hp | ha) | ho) | hwork
        · exact (hfrontSuffix w (by simp [front, hp]) w (by simp [suffix, hw])) rfl
        · exact (hfrontSuffix w (by simp [front, ha]) w (by simp [suffix, hw])) rfl
        · exact (hfrontSuffix w (by simp [front, ho]) w (by simp [suffix, hw])) rfl
        · exact (hnextPowerWork w hw w hwork) rfl
      have hnextAccOutsideSquare (w : Wire) (hw : w ∈ nextAcc.wires) :
          w ∉ squareMul.ports.layout.allWires := by
        intro hmem
        simp only [MulPorts.layout, RegisterLayout.allWires, List.mem_append,
          squareLhs, squareRhs, squareOut, squareWork] at hmem
        rcases hmem with ((hp | hd) | hn) | hwork
        · exact (hfrontSuffix w (by simp [front, hp]) w (by simp [suffix, hw])) rfl
        · exact (hnextAccAfter w hw w (by simp [hd])) rfl
        · exact (hnextAccAfter w hw w (by simp [hn])) rfl
        · exact (hnextAccAfter w hw w (by simp [hwork])) rfl
      have hnextAccNotDup (w : Wire) (hw : w ∈ nextAcc.wires) :
          w ∉ duplicate.wires := by
        intro hd
        exact (hnextAccAfter w hw w (by simp [hd])) rfl
      have hnextPowerNotDup (w : Wire) (hw : w ∈ nextPower.wires) :
          w ∉ duplicate.wires := by
        intro hd
        exact (hdupPowerWork w hd w (by simp [hw])) rfl
      have hworkNotDup (w : Wire) (hw : w ∈ mulWork) : w ∉ duplicate.wires := by
        intro hd
        exact (hdupPowerWork w hd w (by simp [hw])) rfl
      have hdupNotNextAcc (w : Wire) (hw : w ∈ duplicate.wires) :
          w ∉ nextAcc.wires := by
        intro hn
        exact (hnextAccAfter w hn w (by simp [hw])) rfl
      have hnextPowerNotNextAcc (w : Wire) (hw : w ∈ nextPower.wires) :
          w ∉ nextAcc.wires := by
        intro hn
        exact (hnextAccAfter w hn w (by simp [hw])) rfl
      have hworkNotNextAcc (w : Wire) (hw : w ∈ mulWork) : w ∉ nextAcc.wires := by
        intro hn
        exact (hnextAccAfter w hn w (by simp [hw])) rfl

      have hcleanAccCall : Clean (product.wires ++ mulWork) st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · simp [owned, hw]
          · simp [owned, hw])
      have hcleanNextAcc : Clean nextAcc.wires st := Arithmetic.Clean.mono hclean (by
        intro w hw; simp [owned, hw])
      have hcleanDup : Clean duplicate.wires st := Arithmetic.Clean.mono hclean (by
        intro w hw; simp [owned, hw])
      have hcleanNextPower : Clean nextPower.wires st := Arithmetic.Clean.mono hclean (by
        intro w hw; simp [owned, hw])

      let copy := copyReg power.wires duplicate.wires
      let st1 := run accMul.program st
      let st2 := run (selectReg flag acc product nextAcc) st1
      let st3 := run copy st2
      let st4 := run squareMul.program st3
      let st5 := run copy.reverse st4

      have haccCallClean' :
          Clean (accMul.ports.layout.out ++ accMul.ports.layout.work) st := by
        simpa [MulPorts.layout, accOut, accWork] using hcleanAccCall
      have haccResult :
          AgreesOn power.wires st st1 ∧ AgreesOn acc.wires st st1 ∧
            regValue product.wires st1 =
              regValue power.wires st * regValue acc.wires st % modulus ∧
            Clean mulWork st1 := by
        have hlhsBound : regValue accMul.ports.layout.lhs st < modulus := by
          simpa [MulPorts.layout, accLhs] using hpowerBound
        have hrhsBound : regValue accMul.ports.layout.rhs st < modulus := by
          simpa [MulPorts.layout, accRhs] using haccBound
        simpa [st1, MulPorts.layout, accLhs, accRhs, accOut, accWork] using
          accMul.certified.correct st haccValid hlhsBound hrhsBound haccCallClean'
      rcases haccResult with ⟨hpowerAgreeOne, haccAgreeOne, hproductValue, hworkCleanOne⟩
      have hflagOne : st1 flag = st flag :=
        accMul.certified.usesOnly.preservesOutside st flag hflagOutsideAcc
      have hnextAccCleanOne : Clean nextAcc.wires st1 := by
        intro w hw
        rw [show st1 w = st w from accMul.certified.usesOnly.preservesOutside st w
          (hnextAccOutsideAcc w hw)]
        exact hcleanNextAcc w hw
      have hdupCleanOne : Clean duplicate.wires st1 := by
        intro w hw
        rw [show st1 w = st w from accMul.certified.usesOnly.preservesOutside st w
          (hdupOutsideAcc w hw)]
        exact hcleanDup w hw
      have hnextPowerCleanOne : Clean nextPower.wires st1 := by
        intro w hw
        rw [show st1 w = st w from accMul.certified.usesOnly.preservesOutside st w
          (hnextPowerOutsideAcc w hw)]
        exact hcleanNextPower w hw

      have hnextAccValueTwo :
          regValue nextAcc.wires st2 =
            mulSelectStep modulus (regValue acc.wires st) (regValue power.wires st)
              (st flag) := by
        rw [show regValue nextAcc.wires st2 =
          (if st1 flag then regValue product.wires st1 else regValue acc.wires st1) from
            selectReg_correct flag acc product nextAcc st1 hselectOK hnextAccCleanOne]
        rw [hflagOne, Arithmetic.AgreesOn.regValue haccAgreeOne, hproductValue]
        cases st flag <;> simp [mulSelectStep, selectAccumulator, productCandidate,
          Nat.mul_comm]
      have hdupCleanTwo : Clean duplicate.wires st2 := by
        intro w hw
        rw [show st2 w = st1 w from
          selectReg_other flag w acc product nextAcc st1 hselectOK (hdupNotNextAcc w hw)]
        exact hdupCleanOne w hw
      have hnextPowerCleanTwo : Clean nextPower.wires st2 := by
        intro w hw
        rw [show st2 w = st1 w from selectReg_other flag w acc product nextAcc st1
          hselectOK (hnextPowerNotNextAcc w hw)]
        exact hnextPowerCleanOne w hw
      have hworkCleanTwo : Clean mulWork st2 := by
        intro w hw
        rw [show st2 w = st1 w from selectReg_other flag w acc product nextAcc st1
          hselectOK (hworkNotNextAcc w hw)]
        exact hworkCleanOne w hw
      have hpowerTwo : regValue power.wires st2 = regValue power.wires st := by
        apply regValue_congr
        intro w hw
        rw [show st2 w = st1 w from selectReg_other flag w acc product nextAcc st1
          hselectOK (by
            intro hn
            exact (hfrontSuffix w (by simp [front, hw]) w (by simp [suffix, hn])) rfl)]
        exact hpowerAgreeOne w hw

      have hcopyValue : regValue duplicate.wires st3 = regValue power.wires st2 := by
        apply copyReg_correct power.wires duplicate.wires st2
        · rw [duplicate.length_eq, power.length_eq]
        · exact hcopyNd
        · exact hdupCleanTwo
      have hpowerThree : regValue power.wires st3 = regValue power.wires st2 := by
        apply regValue_congr
        intro w hw
        apply copyReg_other
        intro hd
        exact (List.nodup_append.mp hcopyNd).2.2 w hw w hd rfl
      have hnextAccThree : regValue nextAcc.wires st3 = regValue nextAcc.wires st2 := by
        apply regValue_congr
        intro w hw
        exact copyReg_other w power.wires duplicate.wires st2 (hnextAccNotDup w hw)
      have hnextPowerCleanThree : Clean nextPower.wires st3 := by
        intro w hw
        rw [show st3 w = st2 w from
          copyReg_other w power.wires duplicate.wires st2 (hnextPowerNotDup w hw)]
        exact hnextPowerCleanTwo w hw
      have hworkCleanThree : Clean mulWork st3 := by
        intro w hw
        rw [show st3 w = st2 w from
          copyReg_other w power.wires duplicate.wires st2 (hworkNotDup w hw)]
        exact hworkCleanTwo w hw

      have hsquareClean : Clean (nextPower.wires ++ mulWork) st3 := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hnextPowerCleanThree w hw
        · exact hworkCleanThree w hw
      have hsquareClean' :
          Clean (squareMul.ports.layout.out ++ squareMul.ports.layout.work) st3 := by
        simpa [MulPorts.layout, squareOut, squareWork] using hsquareClean
      have hpowerThreeBound : regValue power.wires st3 < modulus := by
        rw [hpowerThree, hpowerTwo]
        exact hpowerBound
      have hdupThreeBound : regValue duplicate.wires st3 < modulus := by
        rw [hcopyValue, hpowerTwo]
        exact hpowerBound
      have hsquareResult :
          AgreesOn power.wires st3 st4 ∧ AgreesOn duplicate.wires st3 st4 ∧
            regValue nextPower.wires st4 =
              regValue power.wires st3 * regValue duplicate.wires st3 % modulus ∧
            Clean mulWork st4 := by
        have hlhsBound : regValue squareMul.ports.layout.lhs st3 < modulus := by
          simpa [MulPorts.layout, squareLhs] using hpowerThreeBound
        have hrhsBound : regValue squareMul.ports.layout.rhs st3 < modulus := by
          simpa [MulPorts.layout, squareRhs] using hdupThreeBound
        simpa [st4, MulPorts.layout, squareLhs, squareRhs, squareOut, squareWork] using
          squareMul.certified.correct st3 hsquareValid hlhsBound hrhsBound hsquareClean'
      rcases hsquareResult with
        ⟨hpowerAgreeFour, hdupAgreeFour, hnextPowerValueFour, hworkCleanFour⟩
      have hnextPowerValueFour' :
          regValue nextPower.wires st4 =
            regValue power.wires st * regValue power.wires st % modulus := by
        rw [hnextPowerValueFour, hpowerThree, hcopyValue, hpowerTwo]
      have hnextAccFour : regValue nextAcc.wires st4 = regValue nextAcc.wires st2 := by
        calc
          regValue nextAcc.wires st4 = regValue nextAcc.wires st3 := by
            apply regValue_congr
            intro w hw
            exact squareMul.certified.usesOnly.preservesOutside st3 w
              (hnextAccOutsideSquare w hw)
          _ = regValue nextAcc.wires st2 := hnextAccThree

      have hcopyUses : CircuitUsesOnly (power.wires ++ duplicate.wires) copy := by
        exact copyReg_usesOnly power.wires duplicate.wires _
          (fun w hw => by simp [hw]) (fun w hw => by simp [hw])
      have hcopyWf : CircuitWellFormed copy := copyReg_wellFormed _ _ hcopyNd
      have hcopyCancel : run copy.reverse st3 = st2 := by
        simpa [copy, st3] using run_reverse_cancel copy st2 (by simp [copy]) hcopyWf
      have hcopyInputsAgree :
          ∀ w ∈ power.wires ++ duplicate.wires, st4 w = st3 w := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hpowerAgreeFour w hw
        · exact hdupAgreeFour w hw
      have hreverseCongr :
          ∀ w ∈ power.wires ++ duplicate.wires,
            run copy.reverse st4 w = run copy.reverse st3 w :=
        CircuitUsesOnly.run_congr (usesOnly_reverse hcopyUses) hcopyInputsAgree
      have hdupCleanFive : Clean duplicate.wires st5 := by
        intro w hw
        calc
          st5 w = run copy.reverse st3 w := hreverseCongr w (by simp [hw])
          _ = st2 w := by rw [hcopyCancel]
          _ = false := hdupCleanTwo w hw
      have hnextAccValueFive :
          regValue nextAcc.wires st5 =
            mulSelectStep modulus (regValue acc.wires st) (regValue power.wires st)
              (st flag) := by
        calc
          regValue nextAcc.wires st5 = regValue nextAcc.wires st4 := by
            apply regValue_congr
            intro w hw
            exact (usesOnly_reverse hcopyUses).preservesOutside st4 w (by
              intro hm
              rcases List.mem_append.mp hm with hp | hd
              · exact (hfrontSuffix w (by simp [front, hp]) w (by simp [suffix, hw])) rfl
              · exact (hnextAccAfter w hw w (by simp [hd])) rfl)
          _ = regValue nextAcc.wires st2 := hnextAccFour
          _ = _ := hnextAccValueTwo
      have hnextPowerValueFive :
          regValue nextPower.wires st5 =
            regValue power.wires st * regValue power.wires st % modulus := by
        calc
          regValue nextPower.wires st5 = regValue nextPower.wires st4 := by
            apply regValue_congr
            intro w hw
            exact (usesOnly_reverse hcopyUses).preservesOutside st4 w (by
              intro hm
              rcases List.mem_append.mp hm with hp | hd
              · exact (hfrontSuffix w (by simp [front, hp]) w (by simp [suffix, hw])) rfl
              · exact (hdupPowerWork w hd w (by simp [hw])) rfl)
          _ = _ := hnextPowerValueFour'
      have hworkCleanFive : Clean mulWork st5 := by
        intro w hw
        rw [show st5 w = st4 w from
          (usesOnly_reverse hcopyUses).preservesOutside st4 w (by
            intro hm
            rcases List.mem_append.mp hm with hp | hd
            · exact (hfrontSuffix w (by simp [front, hp]) w (by simp [suffix, hw])) rfl
            · exact (hdupPowerWork w hd w (by simp [hw])) rfl)]
        exact hworkCleanFour w hw

      let support := consSupport flag power acc product nextAcc duplicate nextPower mulWork
      let stageProgram := accMul.program ++ selectReg flag acc product nextAcc ++
        copy ++ squareMul.program ++ copy.reverse
      have hstageUses : CircuitUsesOnly support stageProgram := by
        have haccUses : CircuitUsesOnly support accMul.program := by
          apply accMul.usesOnly support
          · intro w hw; rw [accLhs] at hw; simp [support, consSupport, hw]
          · intro w hw; rw [accRhs] at hw; simp [support, consSupport, hw]
          · intro w hw; rw [accOut] at hw; simp [support, consSupport, hw]
          · intro w hw; rw [accWork] at hw; simp [support, consSupport, hw]
        have hselectUses : CircuitUsesOnly support (selectReg flag acc product nextAcc) := by
          apply usesOnly_mono (selectReg_usesOnly flag acc product nextAcc)
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · simp [support, consSupport]
          · simp only [List.mem_append] at hw
            rcases hw with (hw | hw) | hw
            · simp [support, consSupport, hw]
            · simp [support, consSupport, hw]
            · simp [support, consSupport, hw]
        have hcopyUses' : CircuitUsesOnly support copy := by
          apply usesOnly_mono hcopyUses
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · simp [support, consSupport, hw]
          · simp [support, consSupport, hw]
        have hsquareUses : CircuitUsesOnly support squareMul.program := by
          apply squareMul.usesOnly support
          · intro w hw; rw [squareLhs] at hw; simp [support, consSupport, hw]
          · intro w hw; rw [squareRhs] at hw; simp [support, consSupport, hw]
          · intro w hw; rw [squareOut] at hw; simp [support, consSupport, hw]
          · intro w hw; rw [squareWork] at hw; simp [support, consSupport, hw]
        simpa [stageProgram, List.append_assoc] using
          usesOnly_append (usesOnly_append (usesOnly_append
            (usesOnly_append haccUses hselectUses) hcopyUses') hsquareUses)
            (usesOnly_reverse hcopyUses')
      have hstageState : st5 = run stageProgram st := by
        simp [st5, st4, st3, st2, st1, stageProgram, run_append]
      have hfutureOutside (w : Wire) (hw : w ∈ (nextFlag :: bits) ++ tail.owned) :
          w ∉ support := by
        intro hs
        exact (hfuture w (by simpa [support] using hs) w hw) rfl
      have htailBitsFive : (nextFlag :: bits).map st5 = (nextFlag :: bits).map st := by
        apply List.map_congr_left
        intro w hw
        rw [hstageState]
        exact hstageUses.preservesOutside st w
          (hfutureOutside w (List.mem_append.mpr (Or.inl hw)))
      have htailOwnedCleanFive : Clean tail.owned st5 := by
        intro w hw
        rw [hstageState, hstageUses.preservesOutside st w
          (hfutureOutside w (List.mem_append.mpr (Or.inr hw)))]
        exact hclean w (by simp [owned, hw])
      have htailCleanFive : Clean (tail.owned ++ duplicate.wires ++ mulWork) st5 := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · exact htailOwnedCleanFive w hw
          · exact hdupCleanFive w hw
        · exact hworkCleanFive w hw

      have htailActiveSub : tail.activeWires.Sublist
          (cons acc power flag nextFlag bits nextPower product nextAcc finalAcc
            accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
            squareWork tail).activeWires := by
        let tailBits := nextFlag :: bits
        let rest := tail.owned ++ duplicate.wires ++ mulWork
        have hskipProduct :
            (nextPower.wires ++ nextAcc.wires ++ rest).Sublist
              (nextPower.wires ++ product.wires ++ nextAcc.wires ++ rest) := by
          simp [List.append_assoc]
        have hskipInputs :
            (nextPower.wires ++ product.wires ++ nextAcc.wires ++ rest).Sublist
              (power.wires ++ acc.wires ++ nextPower.wires ++ product.wires ++
                nextAcc.wires ++ rest) := by
          simp [List.append_assoc]
        have hsuffixSub := hskipProduct.trans hskipInputs
        have hwithBits := (List.Sublist.refl tailBits).append hsuffixSub
        simpa [activeWires, owned, tailBits, rest, List.append_assoc] using
          hwithBits.cons flag
      have htailActive : tail.activeWires.Nodup :=
        List.Nodup.sublist htailActiveSub hactive
      have hnextAccBound : regValue nextAcc.wires st5 < modulus := by
        rw [hnextAccValueFive]
        exact mulSelectStep_lt (Nat.zero_lt_of_lt hmod) haccBound (st flag)
      have hnextPowerBound : regValue nextPower.wires st5 < modulus := by
        rw [hnextPowerValueFive]
        exact Nat.mod_lt _ (Nat.zero_lt_of_lt hmod)
      have htailResult := ih st5 htailValid htailActive hmod hnextAccBound
        hnextPowerBound htailCleanFive
      rcases htailResult with ⟨htailValue, hsharedClean⟩

      have hforwardState :
          run (cons acc power flag nextFlag bits nextPower product nextAcc finalAcc
            accMul squareMul accLhs accRhs accOut accWork squareLhs squareRhs squareOut
            squareWork tail).forward st = run tail.forward st5 := by
        simp [forward, st5, st4, st3, st2, st1, copy, run_append]
      dsimp only
      rw [hforwardState]
      constructor
      · rw [htailValue, hnextAccValueFive, hnextPowerValueFive, htailBitsFive]
        rfl
      · exact hsharedClean



end Schedule

/-! ## Generic Bennett cleanup and copy-out -/

/--
If a classical well-formed computation is confined to `active`, a clean disjoint output can
copy a result register before reverse execution.  The wrapper restores every active wire and
leaves on the output exactly the source value produced by the forward computation.
-/
theorem bennett_cleanup_copyOut
    (compute : Circuit) (active source out : List Wire) (st : BasisState)
    (huses : CircuitUsesOnly active compute)
    (hfree : Classical.HPFree compute)
    (hwf : CircuitWellFormed compute)
    (hdisjoint : Schedule.WireDisjoint active out)
    (hlen : out.length = source.length)
    (hnodup : (source ++ out).Nodup)
    (hcleanOut : Clean out st) :
    let after := Classical.run
      (compute ++ copyReg source out ++ compute.reverse) st
    AgreesOn active st after ∧
      regValue out after = regValue source (Classical.run compute st) := by
  let mid := Classical.run compute st
  let copied := Classical.run (copyReg source out) mid
  let after := Classical.run compute.reverse copied
  have houtOutside (w : Wire) (hw : w ∈ out) : w ∉ active := by
    intro ha
    exact (hdisjoint w ha w hw) rfl
  have hcleanOutMid : Clean out mid := by
    intro w hw
    calc
      mid w = st w := by
        change Classical.run compute st w = st w
        exact huses.preservesOutside st w (houtOutside w hw)
      _ = false := hcleanOut w hw
  have hcopyValue : regValue out copied = regValue source mid := by
    exact copyReg_correct source out mid hlen hnodup hcleanOutMid
  have hcopyActive : ∀ w ∈ active, copied w = mid w := by
    intro w hw
    change Classical.run (copyReg source out) mid w = mid w
    apply copyReg_other
    intro ho
    exact (hdisjoint w hw w ho) rfl
  have hreverseUses : CircuitUsesOnly active compute.reverse := usesOnly_reverse huses
  have hcancel : Classical.run compute.reverse mid = st := by
    simpa [mid] using run_reverse_cancel compute st hfree hwf
  have hafterActive : AgreesOn active st after := by
    intro w hw
    calc
      after w = Classical.run compute.reverse mid w := by
        change Classical.run compute.reverse copied w = Classical.run compute.reverse mid w
        exact CircuitUsesOnly.run_congr hreverseUses hcopyActive w hw
      _ = st w := by rw [hcancel]
  have hafterOutValue : regValue out after = regValue out copied := by
    apply regValue_congr
    intro w hw
    change Classical.run compute.reverse copied w = copied w
    exact hreverseUses.preservesOutside copied w (houtOutside w hw)
  have hprogramRun :
      Classical.run (compute ++ copyReg source out ++ compute.reverse) st = after := by
    simp [after, copied, mid, Classical.run_append]
  simp only [hprogramRun]
  exact ⟨hafterActive, hafterOutValue.trans hcopyValue⟩

/-- Complete placement and arithmetic hypotheses for one modular-exponentiation circuit. -/
structure Plan (width modulus : Nat) where
  base : Reg width
  exponent : Reg width
  out : Reg width
  initialAcc : Reg width
  finalAcc : Reg width
  mulWork : List Wire
  duplicate : Reg width
  schedule : Schedule width modulus mulWork duplicate initialAcc base exponent.wires finalAcc
  valid : schedule.Valid
  widthPos : 0 < width
  modulusLarge : 1 < modulus

namespace Plan

/-- Public base/exponent/output followed by the accumulator and all scheduled history. -/
def layout {width modulus : Nat} (plan : Plan width modulus) : RegisterLayout where
  lhs := plan.base.wires
  rhs := plan.exponent.wires
  out := plan.out.wires
  work := plan.initialAcc.wires ++ plan.schedule.owned ++ plan.duplicate.wires ++ plan.mulWork

/-- Initialize one and execute the typed square-and-multiply history. -/
def compute {width modulus : Nat} (plan : Plan width modulus) : Circuit :=
  initOne plan.initialAcc ++ plan.schedule.forward

/-- Copy the final accumulator to the public output, then Bennett-uncompute the history. -/
def program {width modulus : Nat} (plan : Plan width modulus) : Circuit :=
  plan.compute ++ copyReg plan.finalAcc.wires plan.out.wires ++ plan.compute.reverse

/-- Forward read/write support; the public output is deliberately absent. -/
def activeWires {width modulus : Nat} (plan : Plan width modulus) : List Wire :=
  plan.schedule.activeWires

/-- Bennett doubles the exact cost of the forward pass; initialization and copies are Clifford. -/
def cost {width modulus : Nat} (plan : Plan width modulus) : Nat :=
  2 * plan.schedule.forwardCost

/-- The schedule's active support is exactly the two public inputs plus contract work. -/
theorem activeWires_eq {width modulus : Nat} (plan : Plan width modulus) :
    plan.activeWires =
      plan.exponent.wires ++ plan.base.wires ++ plan.layout.work := by
  simp [activeWires, Schedule.activeWires, layout, List.append_assoc]

/-- The final accumulator is contained in the public contract's workspace. -/
theorem finalAcc_sublist_layoutWork {width modulus : Nat} (plan : Plan width modulus) :
    plan.finalAcc.wires.Sublist plan.layout.work := by
  have h := Schedule.finalAcc_sublist_work plan.schedule
  exact h.trans (by
    simp [layout, List.append_assoc])

theorem compute_usesOnly {width modulus : Nat} (plan : Plan width modulus) :
    CircuitUsesOnly plan.activeWires plan.compute := by
  have hinit : CircuitUsesOnly plan.activeWires (initOne plan.initialAcc) :=
    usesOnly_mono (initOne_usesOnly plan.initialAcc) (by
      intro w hw
      simp [activeWires, Schedule.activeWires, hw])
  simpa [compute] using
    usesOnly_append hinit (Schedule.forward_usesOnly_active plan.schedule)

theorem program_usesOnly {width modulus : Nat} (plan : Plan width modulus) :
    CircuitUsesOnly plan.layout.allWires plan.program := by
  let ws := plan.layout.allWires
  have hactive : ∀ w ∈ plan.activeWires, w ∈ ws := by
    intro w hw
    rw [activeWires_eq] at hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · simp [ws, layout, RegisterLayout.allWires, hw]
      · simp [ws, layout, RegisterLayout.allWires, hw]
    · change w ∈ plan.layout.allWires
      simp only [RegisterLayout.allWires, List.mem_append]
      exact Or.inr hw
  have hcompute : CircuitUsesOnly ws plan.compute :=
    usesOnly_mono (compute_usesOnly plan) hactive
  have hfinal : ∀ w ∈ plan.finalAcc.wires, w ∈ ws := by
    intro w hw
    have hwork := (finalAcc_sublist_layoutWork plan).subset hw
    change w ∈ plan.layout.allWires
    simp only [RegisterLayout.allWires, List.mem_append]
    exact Or.inr hwork
  have hout : ∀ w ∈ plan.out.wires, w ∈ ws := by
    intro w hw
    simp [ws, layout, RegisterLayout.allWires, hw]
  have hcopy : CircuitUsesOnly ws (copyReg plan.finalAcc.wires plan.out.wires) :=
    copyReg_usesOnly plan.finalAcc.wires plan.out.wires ws hfinal hout
  simpa [program, List.append_assoc] using
    usesOnly_append (usesOnly_append hcompute hcopy) (usesOnly_reverse hcompute)

theorem compute_tCount {width modulus : Nat} (plan : Plan width modulus) :
    tCount plan.compute = plan.schedule.forwardCost := by
  rw [compute, tCount_append, initOne_tCount, Schedule.forward_tCount]
  simp

theorem program_tCount {width modulus : Nat} (plan : Plan width modulus) :
    tCount plan.program = plan.cost := by
  rw [program, tCount_append, tCount_append, copyReg_tCount,
    Arithmetic.tCount_reverse, compute_tCount]
  simp [cost, Nat.two_mul]

/-- With one common multiplier cost, a width-bit plan has `2*width-1` forward multiplier
calls, one selector per bit, and a doubled Bennett cost. -/
theorem cost_eq_of_uniform {width modulus mulCost : Nat} (plan : Plan width modulus)
    (huniform : plan.schedule.UniformMulCost mulCost) :
    plan.cost = 2 * ((2 * width - 1) * mulCost + 7 * width * width) := by
  rw [cost, Schedule.forwardCost_eq_of_uniform plan.schedule huniform,
    Schedule.multiplierCalls_eq, plan.exponent.length_eq]

/-- The symbolic closed form is proved for the exact program term used by the contract. -/
theorem program_tCount_eq_of_uniform {width modulus mulCost : Nat}
    (plan : Plan width modulus) (huniform : plan.schedule.UniformMulCost mulCost) :
    tCount plan.program = 2 * ((2 * width - 1) * mulCost + 7 * width * width) := by
  rw [program_tCount, cost_eq_of_uniform plan huniform]

theorem compute_HPFree {width modulus : Nat} (plan : Plan width modulus) :
    Classical.HPFree plan.compute := by
  simp [compute, initOne_HPFree, Schedule.forward_HPFree]

theorem program_HPFree {width modulus : Nat} (plan : Plan width modulus) :
    Classical.HPFree plan.program := by
  simp [program, compute_HPFree, Arithmetic.hpFree_reverse]

/-- Split global layout duplicate-freedom into input/output/work blocks and their crossings. -/
theorem layout_nodup_parts {width modulus : Nat} (plan : Plan width modulus)
    (hlayout : plan.layout.Valid) :
    (plan.base.wires ++ plan.exponent.wires).Nodup ∧
      plan.out.wires.Nodup ∧ plan.layout.work.Nodup ∧
      Schedule.WireDisjoint (plan.base.wires ++ plan.exponent.wires) plan.out.wires ∧
      Schedule.WireDisjoint (plan.base.wires ++ plan.exponent.wires) plan.layout.work ∧
      Schedule.WireDisjoint plan.out.wires plan.layout.work := by
  have hshape :
      ((plan.base.wires ++ plan.exponent.wires) ++
        (plan.out.wires ++ plan.layout.work)).Nodup := by
    simpa [layout, RegisterLayout.allWires, List.append_assoc] using hlayout.2.2
  obtain ⟨hinputs, htail, hinputsTail⟩ := List.nodup_append.mp hshape
  obtain ⟨hout, hwork, houtWork⟩ := List.nodup_append.mp htail
  exact ⟨hinputs, hout, hwork,
    fun x hx y hy => hinputsTail x hx y (List.mem_append.mpr (Or.inl hy)),
    fun x hx y hy => hinputsTail x hx y (List.mem_append.mpr (Or.inr hy)),
    houtWork⟩

theorem activeWires_nodup {width modulus : Nat} (plan : Plan width modulus)
    (hlayout : plan.layout.Valid) : plan.activeWires.Nodup := by
  obtain ⟨hinputs, hout, hwork, hinputsOut, hinputsWork, houtWork⟩ :=
    layout_nodup_parts plan hlayout
  obtain ⟨hbase, hexponent, hbaseExponent⟩ := List.nodup_append.mp hinputs
  have hswapped : (plan.exponent.wires ++ plan.base.wires).Nodup :=
    List.nodup_append.mpr ⟨hexponent, hbase,
      fun x hx y hy => (hbaseExponent y hy x hx).symm⟩
  have hswappedWork : Schedule.WireDisjoint
      (plan.exponent.wires ++ plan.base.wires) plan.layout.work := by
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · exact hinputsWork x (List.mem_append.mpr (Or.inr hx)) y hy
    · exact hinputsWork x (List.mem_append.mpr (Or.inl hx)) y hy
  have hcombined := List.nodup_append.mpr ⟨hswapped, hwork, hswappedWork⟩
  simpa [activeWires_eq, List.append_assoc] using hcombined

theorem activeWires_out_disjoint {width modulus : Nat} (plan : Plan width modulus)
    (hlayout : plan.layout.Valid) :
    Schedule.WireDisjoint plan.activeWires plan.out.wires := by
  obtain ⟨hinputs, hout, hwork, hinputsOut, hinputsWork, houtWork⟩ :=
    layout_nodup_parts plan hlayout
  intro x hx y hy
  have hx' : x ∈ (plan.exponent.wires ++ plan.base.wires) ++ plan.layout.work := by
    simpa [activeWires_eq] using hx
  rcases List.mem_append.mp hx' with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact hinputsOut x (List.mem_append.mpr (Or.inr hx)) y hy
    · exact hinputsOut x (List.mem_append.mpr (Or.inl hx)) y hy
  · exact (houtWork y hy x hx).symm

theorem finalAcc_out_nodup {width modulus : Nat} (plan : Plan width modulus)
    (hlayout : plan.layout.Valid) :
    (plan.finalAcc.wires ++ plan.out.wires).Nodup := by
  obtain ⟨hinputs, hout, hwork, hinputsOut, hinputsWork, houtWork⟩ :=
    layout_nodup_parts plan hlayout
  have hfinalSub : plan.finalAcc.wires.Sublist plan.layout.work :=
    finalAcc_sublist_layoutWork plan
  have hfinal := List.Nodup.sublist hfinalSub hwork
  refine List.nodup_append.mpr ⟨hfinal, hout, ?_⟩
  intro x hx y hy
  exact (houtWork y hy x (hfinalSub.subset hx)).symm

theorem finalAcc_out_length {width modulus : Nat} (plan : Plan width modulus) :
    plan.out.wires.length = plan.finalAcc.wires.length := by
  rw [plan.out.length_eq, plan.finalAcc.length_eq]

theorem compute_wellFormed {width modulus : Nat} (plan : Plan width modulus) :
    CircuitWellFormed plan.compute := by
  rw [compute, circuitWellFormed_append]
  exact ⟨initOne_wellFormed plan.initialAcc,
    Schedule.forward_wellFormed plan.schedule plan.valid⟩

theorem program_wellFormed {width modulus : Nat} (plan : Plan width modulus)
    (hlayout : plan.layout.Valid) : CircuitWellFormed plan.program := by
  have hcompute := compute_wellFormed plan
  have hcopy := copyReg_wellFormed plan.finalAcc.wires plan.out.wires
    (finalAcc_out_nodup plan hlayout)
  rw [program, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨hcompute, hcopy⟩, Arithmetic.wellFormed_reverse hcompute⟩

/-! ## Contract packaging -/

/-- The initial accumulator is the first register in the contract workspace. -/
theorem initialAcc_sublist_layoutWork {width modulus : Nat} (plan : Plan width modulus) :
    plan.initialAcc.wires.Sublist plan.layout.work := by
  simp [layout]

/-- Everything after the initial accumulator is also contained in contract work. -/
theorem scheduleScratch_sublist_layoutWork {width modulus : Nat}
    (plan : Plan width modulus) :
    (plan.schedule.owned ++ plan.duplicate.wires ++ plan.mulWork).Sublist
      plan.layout.work := by
  simp [layout]

theorem base_subset_activeWires {width modulus : Nat} (plan : Plan width modulus) :
    ∀ w ∈ plan.base.wires, w ∈ plan.activeWires := by
  intro w hw
  simp [activeWires, Schedule.activeWires, hw]

theorem exponent_subset_activeWires {width modulus : Nat} (plan : Plan width modulus) :
    ∀ w ∈ plan.exponent.wires, w ∈ plan.activeWires := by
  intro w hw
  simp [activeWires, Schedule.activeWires, hw]

theorem work_subset_activeWires {width modulus : Nat} (plan : Plan width modulus) :
    ∀ w ∈ plan.layout.work, w ∈ plan.activeWires := by
  intro w hw
  rw [activeWires_eq]
  exact List.mem_append.mpr (Or.inr hw)

/--
Package the exact `Plan.program` term into the shared exponentiation contract.  The schedule
proof supplies only the forward recurrence; initialization, Bennett cleanup, copying, cost,
locality, and physical validity are all discharged here.
-/
theorem modExp_contract_of_forward {width modulus : Nat} (plan : Plan width modulus)
    (hforwardCorrect : Schedule.ForwardCorrectStatement plan.schedule) :
    ModExpContract plan.program plan.layout modulus plan.cost := by
  refine
    { correct := ?_
      usesOnly := program_usesOnly plan
      counted := program_tCount plan
      hpFree := program_HPFree plan
      wellFormed := fun hlayout => program_wellFormed plan hlayout }
  intro st hlayout hbaseBound _hexponentBound hclean
  have hcleanOut : Clean plan.out.wires st := Arithmetic.Clean.mono hclean (by
    intro w hw
    exact List.mem_append.mpr (Or.inl hw))
  have hcleanWork : Clean plan.layout.work st := Arithmetic.Clean.mono hclean (by
    intro w hw
    exact List.mem_append.mpr (Or.inr hw))
  have hcleanAcc : Clean plan.initialAcc.wires st :=
    Arithmetic.Clean.mono hcleanWork (initialAcc_sublist_layoutWork plan).subset
  have hcleanScheduleScratch :
      Clean (plan.schedule.owned ++ plan.duplicate.wires ++ plan.mulWork) st :=
    Arithmetic.Clean.mono hcleanWork (scheduleScratch_sublist_layoutWork plan).subset

  obtain ⟨hinputsNd, houtNd, hworkNd, hinputsOut, hinputsWork, houtWork⟩ :=
    layout_nodup_parts plan hlayout
  have hworkShape :
      (plan.initialAcc.wires ++
        (plan.schedule.owned ++ plan.duplicate.wires ++ plan.mulWork)).Nodup := by
    simpa [layout, List.append_assoc] using hworkNd
  obtain ⟨haccNd, hscratchNd, haccScratch⟩ := List.nodup_append.mp hworkShape

  let initialized := Classical.run (initOne plan.initialAcc) st
  have hinitialValue : regValue plan.initialAcc.wires initialized = 1 := by
    simpa [initialized] using
      initOne_correct plan.initialAcc st haccNd hcleanAcc plan.widthPos
  have hbaseInitialized : AgreesOn plan.base.wires st initialized := by
    intro w hw
    apply initOne_other plan.initialAcc st w
    intro hacc
    exact hinputsWork w (List.mem_append.mpr (Or.inl hw)) w
      ((initialAcc_sublist_layoutWork plan).subset hacc) rfl
  have hexponentInitialized : AgreesOn plan.exponent.wires st initialized := by
    intro w hw
    apply initOne_other plan.initialAcc st w
    intro hacc
    exact hinputsWork w (List.mem_append.mpr (Or.inr hw)) w
      ((initialAcc_sublist_layoutWork plan).subset hacc) rfl
  have hbaseValue :
      regValue plan.base.wires initialized = regValue plan.base.wires st :=
    Arithmetic.AgreesOn.regValue hbaseInitialized
  have hexponentBits :
      plan.exponent.wires.map initialized = plan.exponent.wires.map st := by
    apply List.map_congr_left
    intro w hw
    exact hexponentInitialized w hw
  have hcleanScratchInitialized :
      Clean (plan.schedule.owned ++ plan.duplicate.wires ++ plan.mulWork) initialized := by
    intro w hw
    rw [show initialized w = st w from initOne_other plan.initialAcc st w (by
      intro hacc
      exact haccScratch w hacc w hw rfl)]
    exact hcleanScheduleScratch w hw
  have hscheduleActiveNodup : plan.schedule.activeWires.Nodup := by
    simpa [activeWires] using activeWires_nodup plan hlayout
  have hinitialBound : regValue plan.initialAcc.wires initialized < modulus := by
    rw [hinitialValue]
    exact plan.modulusLarge
  have hbaseBoundInitialized : regValue plan.base.wires initialized < modulus := by
    rw [hbaseValue]
    exact hbaseBound

  have hforward := hforwardCorrect initialized plan.valid hscheduleActiveNodup
    plan.modulusLarge hinitialBound hbaseBoundInitialized hcleanScratchInitialized
  dsimp only at hforward
  have hcomputeValue :
      regValue plan.finalAcc.wires (Classical.run plan.compute st) =
        squareMultiplyAcc modulus 1 (regValue plan.base.wires st)
          (plan.exponent.wires.map st) := by
    rw [compute, Classical.run_append]
    rw [hforward.1, hinitialValue, hbaseValue, hexponentBits]
  have hcomputeMath :
      regValue plan.finalAcc.wires (Classical.run plan.compute st) =
        regValue plan.base.wires st ^ regValue plan.exponent.wires st % modulus := by
    rw [hcomputeValue]
    exact squareMultiplyAcc_register_correct plan.modulusLarge plan.exponent.wires st

  have hbennett := bennett_cleanup_copyOut plan.compute plan.activeWires
    plan.finalAcc.wires plan.out.wires st
    (compute_usesOnly plan) (compute_HPFree plan) (compute_wellFormed plan)
    (activeWires_out_disjoint plan hlayout)
    (finalAcc_out_length plan)
    (finalAcc_out_nodup plan hlayout) hcleanOut
  dsimp only at hbennett
  have hprogramRun :
      Classical.run plan.program st =
        Classical.run
          (plan.compute ++ copyReg plan.finalAcc.wires plan.out.wires ++
            plan.compute.reverse) st := by
    rfl
  have hbaseAgree : AgreesOn plan.base.wires st (Classical.run plan.program st) := by
    intro w hw
    rw [hprogramRun]
    exact hbennett.1 w (base_subset_activeWires plan w hw)
  have hexponentAgree :
      AgreesOn plan.exponent.wires st (Classical.run plan.program st) := by
    intro w hw
    rw [hprogramRun]
    exact hbennett.1 w (exponent_subset_activeWires plan w hw)
  have houtputValue :
      regValue plan.out.wires (Classical.run plan.program st) =
        regValue plan.base.wires st ^ regValue plan.exponent.wires st % modulus := by
    rw [hprogramRun, hbennett.2, hcomputeMath]
  have hworkCleanAfter : Clean plan.layout.work (Classical.run plan.program st) := by
    intro w hw
    rw [hprogramRun, hbennett.1 w (work_subset_activeWires plan w hw)]
    exact hcleanWork w hw
  change
    AgreesOn plan.base.wires st (Classical.run plan.program st) ∧
      AgreesOn plan.exponent.wires st (Classical.run plan.program st) ∧
      regValue plan.out.wires (Classical.run plan.program st) =
        (regValue plan.base.wires st ^ regValue plan.exponent.wires st) % modulus ∧
      Clean plan.layout.work (Classical.run plan.program st)
  exact ⟨hbaseAgree, hexponentAgree, houtputValue, hworkCleanAfter⟩

/-- The concrete schedule proof closes the public modular-exponentiation contract. -/
theorem modExp_contract {width modulus : Nat} (plan : Plan width modulus) :
    ModExpContract plan.program plan.layout modulus plan.cost :=
  modExp_contract_of_forward plan (Schedule.forward_correct plan.schedule)

/-- Uniform multiplier costs expose the same certified program under its symbolic cost. -/
theorem modExp_contract_uniform {width modulus mulCost : Nat} (plan : Plan width modulus)
    (huniform : plan.schedule.UniformMulCost mulCost) :
    ModExpContract plan.program plan.layout modulus
      (2 * ((2 * width - 1) * mulCost + 7 * width * width)) := by
  rw [← cost_eq_of_uniform plan huniform]
  exact modExp_contract plan

end Plan

end ModExp
end ShorECDLP
