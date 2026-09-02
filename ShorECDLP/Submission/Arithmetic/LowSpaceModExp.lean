import ShorECDLP.Submission.Arithmetic.ModExp
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Reversible-pebbled modular exponentiation

This module evaluates the usual most-significant-bit square-and-multiply recurrence with a
balanced reversible pebbling schedule.  A leaf computes one accumulator transition into a clean
register and Bennett-uncomputes its local square/product temporaries.  An internal node computes
a midpoint, computes the right half, then reverses the left half, so one checkpoint register per
tree level is reused instead of retaining one register per exponent bit.
-/

namespace ShorECDLP
namespace LowSpaceModExp

open Classical
open Arithmetic
open scoped ArithmeticNotation

/-! ## Pure most-significant-bit arithmetic -/

/-- One MSB-first square-and-multiply accumulator transition. -/
def powStep (modulus base acc : Nat) (bit : Bool) : Nat :=
  ((acc * acc) % modulus * (if bit then base else 1)) % modulus

/-- Fold MSB-first exponent bits through `powStep`. -/
def powFold (modulus base : Nat) : Nat → List Bool → Nat
  | acc, [] => acc
  | acc, bit :: bits => powFold modulus base (powStep modulus base acc bit) bits

/-- Big-endian numeric value of a Boolean list. -/
def msbValue : List Bool → Nat
  | [] => 0
  | bit :: bits => (if bit then 2 ^ bits.length else 0) + msbValue bits

theorem powStep_lt {modulus base acc : Nat} (hmod : 0 < modulus) (bit : Bool) :
    powStep modulus base acc bit < modulus := by
  exact Nat.mod_lt _ hmod

theorem powFold_lt {modulus base acc : Nat} (hmod : 0 < modulus)
    (hacc : acc < modulus) (bits : List Bool) :
    powFold modulus base acc bits < modulus := by
  induction bits generalizing acc with
  | nil => exact hacc
  | cons bit bits ih =>
      exact ih (powStep_lt hmod bit)

theorem powFold_append (modulus base acc : Nat) (left right : List Bool) :
    powFold modulus base acc (left ++ right) =
      powFold modulus base (powFold modulus base acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons bit bits ih =>
      simp only [List.cons_append, powFold]
      exact ih (powStep modulus base acc bit)

/-- Reversing little-endian bits gives the corresponding big-endian value. -/
private theorem msbValue_append_singleton (bits : List Bool) (bit : Bool) :
    msbValue (bits ++ [bit]) = 2 * msbValue bits + if bit then 1 else 0 := by
  induction bits with
  | nil => cases bit <;> rfl
  | cons head tail ih =>
      simp only [List.cons_append, msbValue, List.length_append, List.length_singleton]
      rw [ih]
      cases head <;> cases bit <;> simp [Nat.pow_succ]
      <;> omega

theorem msbValue_reverse_eq_bitsValue (bits : List Bool) :
    msbValue bits.reverse = ModExp.bitsValue bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [List.reverse_cons, msbValue_append_singleton, ih]
      cases bit
      · simp [ModExp.bitsValue]
      · simp [ModExp.bitsValue]
        omega

/-- Closed form of the MSB-first accumulator fold. -/
theorem powFold_formula {modulus base acc : Nat} (hmod : 0 < modulus)
    (hacc : acc < modulus) (bits : List Bool) :
    powFold modulus base acc bits =
      (acc ^ (2 ^ bits.length) * base ^ msbValue bits) % modulus := by
  induction bits generalizing acc with
  | nil => simp [powFold, msbValue, Nat.mod_eq_of_lt hacc]
  | cons bit bits ih =>
      rw [powFold, ih (powStep_lt hmod bit)]
      change
        powStep modulus base acc bit ^ (2 ^ bits.length) *
              base ^ msbValue bits ≡
          acc ^ (2 ^ (bit :: bits).length) *
              base ^ msbValue (bit :: bits) [MOD modulus]
      cases bit
      · have hstep :
            powStep modulus base acc false ≡ acc ^ 2 [MOD modulus] := by
          simp [powStep, Nat.ModEq, Nat.mul_mod, Nat.pow_two]
        refine ((hstep.pow (2 ^ bits.length)).mul (Nat.ModEq.refl _)).trans ?_
        simpa [List.length_cons, msbValue, Nat.pow_mul, Nat.pow_succ,
          Nat.mul_comm, Nat.mul_left_comm] using (Nat.ModEq.rfl :
            acc ^ (2 * 2 ^ bits.length) * base ^ msbValue bits ≡
              acc ^ (2 * 2 ^ bits.length) * base ^ msbValue bits [MOD modulus])
      · have hstep :
            powStep modulus base acc true ≡ acc ^ 2 * base [MOD modulus] := by
          simp [powStep, Nat.ModEq, Nat.mul_mod, Nat.pow_two]
        refine ((hstep.pow (2 ^ bits.length)).mul (Nat.ModEq.refl _)).trans ?_
        simpa [List.length_cons, msbValue, mul_pow, Nat.pow_mul, Nat.pow_succ,
          Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.ModEq.rfl :
            acc ^ (2 * 2 ^ bits.length) *
                base ^ (2 ^ bits.length + msbValue bits) ≡
              acc ^ (2 * 2 ^ bits.length) *
                base ^ (2 ^ bits.length + msbValue bits) [MOD modulus])

/-- Starting from one computes the modular power represented by the MSB-first bits. -/
theorem powFold_one_correct {modulus base : Nat} (hmod : 1 < modulus)
    (bits : List Bool) :
    powFold modulus base 1 bits = base ^ msbValue bits % modulus := by
  rw [powFold_formula (Nat.zero_lt_of_lt hmod) hmod]
  simp

/-! ## One clean accumulator transition -/

/-- Registers reused by every leaf transition. -/
def scratch {width : Nat} (duplicate square product : ModExp.Reg width)
    (mulWork : List Wire) : List Wire :=
  duplicate.wires ++ square.wires ++ product.wires ++ mulWork

/-- The two certified multiplications and their exact port bindings for one exponent bit. -/
structure Step (width modulus : Nat) (base exponent duplicate square product : ModExp.Reg width)
    (mulWork : List Wire) (bit : Wire) (input output : ModExp.Reg width) where
  squareMul : ModExp.MulCall width modulus
  squareLhs : squareMul.ports.lhs = input
  squareRhs : squareMul.ports.rhs = duplicate
  squareOut : squareMul.ports.out = square
  squareWork : squareMul.ports.work = mulWork
  productMul : ModExp.MulCall width modulus
  productLhs : productMul.ports.lhs = square
  productRhs : productMul.ports.rhs = base
  productOut : productMul.ports.out = product
  productWork : productMul.ports.work = mulWork
  bit_mem : bit ∈ exponent.wires

namespace Step

/-- Compute the square and its optional product with the public base. -/
def compute {width modulus : Nat} {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    Circuit :=
  let copy := copyReg input.wires duplicate.wires
  circuit! {
    copy;
    step.squareMul.program;
    copy.reverse;
    step.productMul.program
  }

/-- Select the bit-dependent result, then reverse the local arithmetic history. -/
def program {width modulus : Nat} {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    Circuit :=
  circuit! {
    step.compute;
    ModExp.selectReg bit square product output;
    step.compute.reverse
  }

/-- Exact T-count charged by one leaf transition. -/
def cost {width modulus : Nat} {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    Nat :=
  2 * (step.squareMul.cost + step.productMul.cost) + 7 * width

/-- Complete local support, including the full preserved exponent register. -/
def allWires {width modulus : Nat} {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (_step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    List Wire :=
  base.wires ++ exponent.wires ++ input.wires ++ output.wires ++
    scratch duplicate square product mulWork

/-- The local forward computation does not touch the selected output register. -/
def activeWires {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (_step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    List Wire :=
  base.wires ++ exponent.wires ++ input.wires ++
    scratch duplicate square product mulWork

theorem compute_usesOnly {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    CircuitUsesOnly step.activeWires step.compute := by
  let copy := copyReg input.wires duplicate.wires
  have hcopy : CircuitUsesOnly step.activeWires copy := by
    apply copyReg_usesOnly input.wires duplicate.wires step.activeWires
    · intro w hw
      simp [activeWires, hw]
    · intro w hw
      simp [activeWires, scratch, hw]
  have hsquare : CircuitUsesOnly step.activeWires step.squareMul.program := by
    apply step.squareMul.usesOnly step.activeWires
    · intro w hw
      rw [step.squareLhs] at hw
      simp [activeWires, hw]
    · intro w hw
      rw [step.squareRhs] at hw
      simp [activeWires, scratch, hw]
    · intro w hw
      rw [step.squareOut] at hw
      simp [activeWires, scratch, hw]
    · intro w hw
      rw [step.squareWork] at hw
      simp [activeWires, scratch, hw]
  have hproduct : CircuitUsesOnly step.activeWires step.productMul.program := by
    apply step.productMul.usesOnly step.activeWires
    · intro w hw
      rw [step.productLhs] at hw
      simp [activeWires, scratch, hw]
    · intro w hw
      rw [step.productRhs] at hw
      simp [activeWires, hw]
    · intro w hw
      rw [step.productOut] at hw
      simp [activeWires, scratch, hw]
    · intro w hw
      rw [step.productWork] at hw
      simp [activeWires, scratch, hw]
  simpa [compute, copy, List.append_assoc] using
    usesOnly_append (usesOnly_append (usesOnly_append hcopy hsquare)
      (usesOnly_reverse hcopy)) hproduct

theorem program_usesOnly {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    CircuitUsesOnly step.allWires step.program := by
  have hcompute : CircuitUsesOnly step.allWires step.compute := by
    apply usesOnly_mono step.compute_usesOnly
    intro w hw
    simp only [activeWires, allWires, scratch, List.mem_append] at hw ⊢
    tauto
  have hselect : CircuitUsesOnly step.allWires
      (ModExp.selectReg bit square product output) := by
    apply usesOnly_mono (ModExp.selectReg_usesOnly bit square product output)
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | ((hsquare | hproduct) | houtput)
    · simp [allWires, scratch, step.bit_mem]
    · simp [allWires, scratch, hsquare]
    · simp [allWires, scratch, hproduct]
    · simp [allWires, houtput]
  simpa [program, List.append_assoc] using
    usesOnly_append (usesOnly_append hcompute hselect) (usesOnly_reverse hcompute)

theorem compute_HPFree {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    HPFree step.compute := by
  simp [compute, copyReg_HPFree, step.squareMul.certified.hpFree,
    step.productMul.certified.hpFree, Arithmetic.hpFree_reverse]

theorem program_HPFree {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    HPFree step.program := by
  simp [program, step.compute_HPFree, ModExp.selectReg_HPFree,
    Arithmetic.hpFree_reverse]

theorem program_tCount {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output) :
    tCount step.program = step.cost := by
  simp [program, compute, cost, tCount_append, copyReg_tCount,
    step.squareMul.certified.counted, step.productMul.certified.counted,
    ModExp.selectReg_tCount, Arithmetic.tCount_reverse]
  omega

private theorem copy_nodup {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output)
    (hvalid : step.allWires.Nodup) :
    (input.wires ++ duplicate.wires).Nodup := by
  apply List.Nodup.sublist _ hvalid
  have hsub := (((((((List.nil_sublist base.wires).append
      (List.nil_sublist exponent.wires)).append (List.Sublist.refl input.wires)).append
      (List.nil_sublist output.wires)).append (List.Sublist.refl duplicate.wires)).append
      (List.nil_sublist square.wires)).append (List.nil_sublist product.wires)).append
      (List.nil_sublist mulWork)
  simpa [allWires, scratch, List.append_assoc] using hsub

private theorem square_layout_nodup {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output)
    (hvalid : step.allWires.Nodup) : step.squareMul.ports.layout.allWires.Nodup := by
  have hlocal :
      (input.wires ++ duplicate.wires ++ square.wires ++ mulWork).Nodup := by
    apply List.Nodup.sublist _ hvalid
    have hsub := (((((((List.nil_sublist base.wires).append
        (List.nil_sublist exponent.wires)).append (List.Sublist.refl input.wires)).append
        (List.nil_sublist output.wires)).append (List.Sublist.refl duplicate.wires)).append
        (List.Sublist.refl square.wires)).append (List.nil_sublist product.wires)).append
        (List.Sublist.refl mulWork)
    simpa [allWires, scratch, List.append_assoc] using hsub
  simpa [ModExp.MulPorts.layout, RegisterLayout.allWires, step.squareLhs,
    step.squareRhs, step.squareOut, step.squareWork, List.append_assoc] using hlocal

private theorem product_layout_nodup {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output)
    (hvalid : step.allWires.Nodup) : step.productMul.ports.layout.allWires.Nodup := by
  have hordered :
      (base.wires ++ square.wires ++ product.wires ++ mulWork).Nodup := by
    apply List.Nodup.sublist _ hvalid
    have hsub := (((((((List.Sublist.refl base.wires).append
        (List.nil_sublist exponent.wires)).append (List.nil_sublist input.wires)).append
        (List.nil_sublist output.wires)).append (List.nil_sublist duplicate.wires)).append
        (List.Sublist.refl square.wires)).append (List.Sublist.refl product.wires)).append
        (List.Sublist.refl mulWork)
    simpa [allWires, scratch, List.append_assoc] using hsub
  have hperm :
      (base.wires ++ square.wires ++ product.wires ++ mulWork).Perm
        (square.wires ++ base.wires ++ product.wires ++ mulWork) := by
    simpa [List.append_assoc] using
      (List.perm_append_comm (l₁ := base.wires) (l₂ := square.wires)).append_right
        (product.wires ++ mulWork)
  have hlocal := hordered.perm hperm
  simpa [ModExp.MulPorts.layout, RegisterLayout.allWires, step.productLhs,
    step.productRhs, step.productOut, step.productWork, List.append_assoc] using hlocal

private theorem select_nodup {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output)
    (hvalid : step.allWires.Nodup) :
    (bit :: (square.wires ++ product.wires ++ output.wires)).Nodup := by
  have hordered :
      (bit :: (output.wires ++ square.wires ++ product.wires)).Nodup := by
    apply List.Nodup.sublist _ hvalid
    have hbit : [bit].Sublist exponent.wires := by
      simpa using step.bit_mem
    have hsub := (((((((List.nil_sublist base.wires).append hbit).append
        (List.nil_sublist input.wires)).append (List.Sublist.refl output.wires)).append
        (List.nil_sublist duplicate.wires)).append (List.Sublist.refl square.wires)).append
        (List.Sublist.refl product.wires)).append (List.nil_sublist mulWork)
    simpa [allWires, scratch, List.append_assoc] using hsub
  have hperm :
      (bit :: (output.wires ++ square.wires ++ product.wires)).Perm
        (bit :: (square.wires ++ product.wires ++ output.wires)) := by
    apply List.Perm.cons bit
    simpa [List.append_assoc] using
      (List.perm_append_comm (l₁ := output.wires)
        (l₂ := square.wires ++ product.wires))
  exact hordered.perm hperm

theorem compute_wellFormed {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output)
    (hvalid : step.allWires.Nodup) : CircuitWellFormed step.compute := by
  let copy := copyReg input.wires duplicate.wires
  have hcopy := copyReg_wellFormed input.wires duplicate.wires (step.copy_nodup hvalid)
  have hsquare := step.squareMul.certified.wellFormed
    (step.squareMul.layoutValid_of_nodup (step.square_layout_nodup hvalid))
  have hproduct := step.productMul.certified.wellFormed
    (step.productMul.layoutValid_of_nodup (step.product_layout_nodup hvalid))
  simp [compute, circuitWellFormed_append, hcopy, hsquare, hproduct,
    Arithmetic.wellFormed_reverse]

theorem program_wellFormed {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output)
    (hvalid : step.allWires.Nodup) : CircuitWellFormed step.program := by
  have hcompute := step.compute_wellFormed hvalid
  have hselect := ModExp.selectReg_wellFormed bit square product output
    (ModExp.selectOK_of_nodup bit square product output (step.select_nodup hvalid))
  simp [program, circuitWellFormed_append, hcompute, hselect,
    Arithmetic.wellFormed_reverse]

/-- Bennett cleanup with a reversible two-way selector instead of a plain copy. -/
private theorem bennett_cleanup_select
    {width : Nat} (compute : Circuit) (active : List Wire) (flag : Wire)
    (ifFalse ifTrue output : ModExp.Reg width) (st : BasisState)
    (huses : CircuitUsesOnly active compute)
    (hfree : HPFree compute)
    (hwf : CircuitWellFormed compute)
    (hdisjoint : ModExp.Schedule.WireDisjoint active output.wires)
    (hselect : selectOK flag ifFalse.wires ifTrue.wires output.wires)
    (hclean : Clean output.wires st) :
    let after := run
      (compute ++ ModExp.selectReg flag ifFalse ifTrue output ++ compute.reverse) st
    AgreesOn active st after ∧
      after⟦ᵣoutput.wires⟧ =
        if (run compute st) flag then
          (run compute st)⟦ᵣifTrue.wires⟧
        else (run compute st)⟦ᵣifFalse.wires⟧ := by
  let mid := run compute st
  let selected := run (ModExp.selectReg flag ifFalse ifTrue output) mid
  let after := run compute.reverse selected
  have houtOutside (w : Wire) (hw : w ∈ output.wires) : w ∉ active := by
    intro ha
    exact (hdisjoint w ha w hw) rfl
  have hcleanMid : Clean output.wires mid := by
    intro w hw
    rw [show mid w = st w from huses.preservesOutside st w (houtOutside w hw)]
    exact hclean w hw
  have hselectedValue : selected⟦ᵣoutput.wires⟧ =
      if mid flag then mid⟦ᵣifTrue.wires⟧ else mid⟦ᵣifFalse.wires⟧ := by
    exact ModExp.selectReg_correct flag ifFalse ifTrue output mid hselect hcleanMid
  have hselectedActive : ∀ w ∈ active, selected w = mid w := by
    intro w hw
    exact ModExp.selectReg_other flag w ifFalse ifTrue output mid hselect (by
      intro ho
      exact (hdisjoint w hw w ho) rfl)
  have hreverseUses : CircuitUsesOnly active compute.reverse := usesOnly_reverse huses
  have hcancel : run compute.reverse mid = st := by
    simpa [mid] using run_reverse_cancel compute st hfree hwf
  have hafterActive : AgreesOn active st after := by
    intro w hw
    calc
      after w = run compute.reverse mid w := by
        exact CircuitUsesOnly.run_congr hreverseUses hselectedActive w hw
      _ = st w := by rw [hcancel]
  have hafterOut : after⟦ᵣoutput.wires⟧ = selected⟦ᵣoutput.wires⟧ := by
    apply regValue_congr
    intro w hw
    exact hreverseUses.preservesOutside selected w (houtOutside w hw)
  have hrun :
      run (compute ++ ModExp.selectReg flag ifFalse ifTrue output ++ compute.reverse) st =
        after := by
    simp [after, selected, mid, run_append]
  dsimp only
  rw [hrun]
  exact ⟨hafterActive, hafterOut.trans hselectedValue⟩

/-- Exact values left by the local square/product computation before its Bennett reverse. -/
private theorem compute_correct {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output)
    (st : BasisState) (hvalid : step.allWires.Nodup) (hmod : 0 < modulus)
    (hbaseBound : st⟦ᵣbase.wires⟧ < modulus)
    (hinputBound : st⟦ᵣinput.wires⟧ < modulus)
    (hclean : Clean (scratch duplicate square product mulWork) st) :
    let after := run step.compute st
    AgreesOn base.wires st after ∧
      AgreesOn exponent.wires st after ∧
      AgreesOn input.wires st after ∧
      after⟦ᵣsquare.wires⟧ = st⟦ᵣinput.wires⟧ * st⟦ᵣinput.wires⟧ % modulus ∧
      after⟦ᵣproduct.wires⟧ =
        (st⟦ᵣinput.wires⟧ * st⟦ᵣinput.wires⟧ % modulus) *
          st⟦ᵣbase.wires⟧ % modulus := by
  let copy := copyReg input.wires duplicate.wires
  let st1 := run copy st
  let st2 := run step.squareMul.program st1
  let st3 := run copy.reverse st2
  let st4 := run step.productMul.program st3
  have hshape :
      (base.wires ++ exponent.wires ++ input.wires ++ output.wires ++ duplicate.wires ++
        square.wires ++ product.wires ++ mulWork).Nodup := by
    simpa [allWires, scratch, List.append_assoc] using hvalid
  obtain ⟨hbaseNd, htail1, hbaseCross⟩ := List.nodup_append.mp (by
    simpa [List.append_assoc] using hshape :
      (base.wires ++ (exponent.wires ++ input.wires ++ output.wires ++ duplicate.wires ++
        square.wires ++ product.wires ++ mulWork)).Nodup)
  obtain ⟨hexponentNd, htail2, hexponentCross⟩ := List.nodup_append.mp (by
    simpa [List.append_assoc] using htail1 :
      (exponent.wires ++ (input.wires ++ output.wires ++ duplicate.wires ++ square.wires ++
        product.wires ++ mulWork)).Nodup)
  obtain ⟨hinputNd, htail3, hinputCross⟩ := List.nodup_append.mp (by
    simpa [List.append_assoc] using htail2 :
      (input.wires ++ (output.wires ++ duplicate.wires ++ square.wires ++ product.wires ++
        mulWork)).Nodup)
  obtain ⟨houtputNd, htail4, houtputCross⟩ := List.nodup_append.mp (by
    simpa [List.append_assoc] using htail3 :
      (output.wires ++ (duplicate.wires ++ square.wires ++ product.wires ++ mulWork)).Nodup)
  obtain ⟨hduplicateNd, htail5, hduplicateCross⟩ := List.nodup_append.mp (by
    simpa [List.append_assoc] using htail4 :
      (duplicate.wires ++ (square.wires ++ product.wires ++ mulWork)).Nodup)
  obtain ⟨hsquareNd, htail6, hsquareCross⟩ := List.nodup_append.mp (by
    simpa [List.append_assoc] using htail5 :
      (square.wires ++ (product.wires ++ mulWork)).Nodup)
  obtain ⟨hproductNd, hmulWorkNd, hproductCross⟩ := List.nodup_append.mp htail6

  have hbaseNotDuplicate (w : Wire) (hw : w ∈ base.wires) : w ∉ duplicate.wires := by
    intro hd
    exact hbaseCross w hw w (by simp [hd]) rfl
  have hexponentNotDuplicate (w : Wire) (hw : w ∈ exponent.wires) :
      w ∉ duplicate.wires := by
    intro hd
    exact hexponentCross w hw w (by simp [hd]) rfl
  have hinputNotDuplicate (w : Wire) (hw : w ∈ input.wires) : w ∉ duplicate.wires := by
    intro hd
    exact hinputCross w hw w (by simp [hd]) rfl
  have hsquareNotDuplicate (w : Wire) (hw : w ∈ square.wires) :
      w ∉ duplicate.wires := by
    intro hd
    exact hduplicateCross w hd w (by simp [hw]) rfl
  have hproductNotDuplicate (w : Wire) (hw : w ∈ product.wires) :
      w ∉ duplicate.wires := by
    intro hd
    exact hduplicateCross w hd w (by simp [hw]) rfl
  have hworkNotDuplicate (w : Wire) (hw : w ∈ mulWork) : w ∉ duplicate.wires := by
    intro hd
    exact hduplicateCross w hd w (by simp [hw]) rfl

  have hcopyValue : st1⟦ᵣduplicate.wires⟧ = st⟦ᵣinput.wires⟧ := by
    exact copyReg_correct input.wires duplicate.wires st
      (by rw [input.length_eq, duplicate.length_eq]) (step.copy_nodup hvalid)
      (Arithmetic.Clean.mono hclean (by intro w hw; simp [scratch, hw]))
  have hinputOne : st1⟦ᵣinput.wires⟧ = st⟦ᵣinput.wires⟧ := by
    apply regValue_congr
    intro w hw
    exact copyReg_other w input.wires duplicate.wires st (hinputNotDuplicate w hw)
  have hbaseOne : st1⟦ᵣbase.wires⟧ = st⟦ᵣbase.wires⟧ := by
    apply regValue_congr
    intro w hw
    exact copyReg_other w input.wires duplicate.wires st (hbaseNotDuplicate w hw)
  have hexponentOne : AgreesOn exponent.wires st st1 := by
    intro w hw
    exact copyReg_other w input.wires duplicate.wires st (hexponentNotDuplicate w hw)
  have hsquareCleanOne : Clean square.wires st1 := by
    intro w hw
    calc
      st1 w = st w := copyReg_other w input.wires duplicate.wires st
        (hsquareNotDuplicate w hw)
      _ = false := hclean w (by simp [scratch, hw])
  have hproductCleanOne : Clean product.wires st1 := by
    intro w hw
    calc
      st1 w = st w := copyReg_other w input.wires duplicate.wires st
        (hproductNotDuplicate w hw)
      _ = false := hclean w (by simp [scratch, hw])
  have hworkCleanOne : Clean mulWork st1 := by
    intro w hw
    calc
      st1 w = st w := copyReg_other w input.wires duplicate.wires st
        (hworkNotDuplicate w hw)
      _ = false := hclean w (by simp [scratch, hw])

  have hbaseOutsideSquare (w : Wire) (hw : w ∈ base.wires) :
      w ∉ step.squareMul.ports.layout.allWires := by
    intro hm
    simp only [ModExp.MulPorts.layout, RegisterLayout.allWires, List.mem_append,
      step.squareLhs, step.squareRhs, step.squareOut, step.squareWork] at hm
    rcases hm with ((hi | hd) | hs) | hwork
    · exact hbaseCross w hw w (by simp [hi]) rfl
    · exact hbaseCross w hw w (by simp [hd]) rfl
    · exact hbaseCross w hw w (by simp [hs]) rfl
    · exact hbaseCross w hw w (by simp [hwork]) rfl
  have hexponentOutsideSquare (w : Wire) (hw : w ∈ exponent.wires) :
      w ∉ step.squareMul.ports.layout.allWires := by
    intro hm
    simp only [ModExp.MulPorts.layout, RegisterLayout.allWires, List.mem_append,
      step.squareLhs, step.squareRhs, step.squareOut, step.squareWork] at hm
    rcases hm with ((hi | hd) | hs) | hwork
    · exact hexponentCross w hw w (by simp [hi]) rfl
    · exact hexponentCross w hw w (by simp [hd]) rfl
    · exact hexponentCross w hw w (by simp [hs]) rfl
    · exact hexponentCross w hw w (by simp [hwork]) rfl
  have hproductOutsideSquare (w : Wire) (hw : w ∈ product.wires) :
      w ∉ step.squareMul.ports.layout.allWires := by
    intro hm
    simp only [ModExp.MulPorts.layout, RegisterLayout.allWires, List.mem_append,
      step.squareLhs, step.squareRhs, step.squareOut, step.squareWork] at hm
    rcases hm with ((hi | hd) | hs) | hwork
    · exact hinputCross w hi w (by simp [hw]) rfl
    · exact hduplicateCross w hd w (by simp [hw]) rfl
    · exact hsquareCross w hs w (by simp [hw]) rfl
    · exact hproductCross w hw w hwork rfl

  have hsquareWorkClean : Clean (square.wires ++ mulWork) st1 := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hsquareCleanOne w hw
    · exact hworkCleanOne w hw
  have hsquareResultRaw := step.squareMul.certified.correct st1
    (step.squareMul.layoutValid_of_nodup (step.square_layout_nodup hvalid))
    (by simpa [ModExp.MulPorts.layout, step.squareLhs, hinputOne] using hinputBound)
    (by simpa [ModExp.MulPorts.layout, step.squareRhs, hcopyValue] using hinputBound)
    (by
      simpa [ModExp.MulPorts.layout, step.squareOut, step.squareWork] using
        hsquareWorkClean)
  have hsquareResult :
      AgreesOn input.wires st1 st2 ∧ AgreesOn duplicate.wires st1 st2 ∧
        st2⟦ᵣsquare.wires⟧ = st1⟦ᵣinput.wires⟧ * st1⟦ᵣduplicate.wires⟧ % modulus ∧
        Clean mulWork st2 := by
    simpa [st2, ModExp.MulPorts.layout, step.squareLhs, step.squareRhs,
      step.squareOut, step.squareWork] using hsquareResultRaw
  rcases hsquareResult with ⟨hinputAgreeTwo, hduplicateAgreeTwo, hsquareValueTwo,
    hworkCleanTwo⟩
  have hbaseTwo : st2⟦ᵣbase.wires⟧ = st⟦ᵣbase.wires⟧ := by
    calc
      st2⟦ᵣbase.wires⟧ = st1⟦ᵣbase.wires⟧ := by
        apply regValue_congr
        intro w hw
        exact step.squareMul.certified.usesOnly.preservesOutside st1 w
          (hbaseOutsideSquare w hw)
      _ = _ := hbaseOne
  have hexponentTwo : AgreesOn exponent.wires st st2 := by
    intro w hw
    calc
      st2 w = st1 w := step.squareMul.certified.usesOnly.preservesOutside st1 w
        (hexponentOutsideSquare w hw)
      _ = st w := hexponentOne w hw
  have hproductCleanTwo : Clean product.wires st2 := by
    intro w hw
    calc
      st2 w = st1 w := step.squareMul.certified.usesOnly.preservesOutside st1 w
        (hproductOutsideSquare w hw)
      _ = false := hproductCleanOne w hw

  have hcopyUses : CircuitUsesOnly (input.wires ++ duplicate.wires) copy :=
    copyReg_usesOnly input.wires duplicate.wires _
      (fun w hw => by simp [hw]) (fun w hw => by simp [hw])
  have hcopyWf := copyReg_wellFormed input.wires duplicate.wires (step.copy_nodup hvalid)
  have hcopyCancel : run copy.reverse st1 = st := by
    simpa [st1, copy] using run_reverse_cancel copy st (by simp [copy]) hcopyWf
  have hcopyInputsAgree : ∀ w ∈ input.wires ++ duplicate.wires, st2 w = st1 w := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hinputAgreeTwo w hw
    · exact hduplicateAgreeTwo w hw
  have hcopyReverseAgree : ∀ w ∈ input.wires ++ duplicate.wires,
      st3 w = run copy.reverse st1 w := by
    exact CircuitUsesOnly.run_congr (usesOnly_reverse hcopyUses) hcopyInputsAgree
  have hinputThreeAgree : AgreesOn input.wires st st3 := by
    intro w hw
    calc
      st3 w = run copy.reverse st1 w := hcopyReverseAgree w (by simp [hw])
      _ = st w := congrFun hcopyCancel w
  have hinputThree : st3⟦ᵣinput.wires⟧ = st⟦ᵣinput.wires⟧ :=
    Arithmetic.AgreesOn.regValue hinputThreeAgree
  have hduplicateCleanThree : Clean duplicate.wires st3 := by
    intro w hw
    calc
      st3 w = run copy.reverse st1 w := hcopyReverseAgree w (by simp [hw])
      _ = st w := congrFun hcopyCancel w
      _ = false := hclean w (by simp [scratch, hw])
  have hsquareThree : st3⟦ᵣsquare.wires⟧ =
      st⟦ᵣinput.wires⟧ * st⟦ᵣinput.wires⟧ % modulus := by
    calc
      st3⟦ᵣsquare.wires⟧ = st2⟦ᵣsquare.wires⟧ := by
        apply regValue_congr
        intro w hw
        exact (usesOnly_reverse hcopyUses).preservesOutside st2 w (by
          intro hm
          rcases List.mem_append.mp hm with hi | hd
          · exact hinputCross w hi w (by simp [hw]) rfl
          · exact hduplicateCross w hd w (by simp [hw]) rfl)
      _ = st1⟦ᵣinput.wires⟧ * st1⟦ᵣduplicate.wires⟧ % modulus := hsquareValueTwo
      _ = _ := by rw [hinputOne, hcopyValue]
  have hbaseTwoAgree : AgreesOn base.wires st st2 := by
    intro w hw
    calc
      st2 w = st1 w := step.squareMul.certified.usesOnly.preservesOutside st1 w
        (hbaseOutsideSquare w hw)
      _ = st w := copyReg_other w input.wires duplicate.wires st
        (hbaseNotDuplicate w hw)
  have hbaseThreeAgree : AgreesOn base.wires st st3 := by
    intro w hw
    calc
      st3 w = st2 w := (usesOnly_reverse hcopyUses).preservesOutside st2 w (by
        intro hm
        rcases List.mem_append.mp hm with hi | hd
        · exact hbaseCross w hw w (by simp [hi]) rfl
        · exact hbaseCross w hw w (by simp [hd]) rfl)
      _ = st w := hbaseTwoAgree w hw
  have hbaseThree : st3⟦ᵣbase.wires⟧ = st⟦ᵣbase.wires⟧ :=
    Arithmetic.AgreesOn.regValue hbaseThreeAgree
  have hexponentThree : AgreesOn exponent.wires st st3 := by
    intro w hw
    calc
      st3 w = st2 w := (usesOnly_reverse hcopyUses).preservesOutside st2 w (by
        intro hm
        rcases List.mem_append.mp hm with hi | hd
        · exact hexponentCross w hw w (by simp [hi]) rfl
        · exact hexponentCross w hw w (by simp [hd]) rfl)
      _ = st w := hexponentTwo w hw
  have hproductCleanThree : Clean product.wires st3 := by
    intro w hw
    calc
      st3 w = st2 w := (usesOnly_reverse hcopyUses).preservesOutside st2 w (by
        intro hm
        rcases List.mem_append.mp hm with hi | hd
        · exact hinputCross w hi w (by simp [hw]) rfl
        · exact hduplicateCross w hd w (by simp [hw]) rfl)
      _ = false := hproductCleanTwo w hw
  have hworkCleanThree : Clean mulWork st3 := by
    intro w hw
    calc
      st3 w = st2 w := (usesOnly_reverse hcopyUses).preservesOutside st2 w (by
        intro hm
        rcases List.mem_append.mp hm with hi | hd
        · exact hinputCross w hi w (by simp [hw]) rfl
        · exact hduplicateCross w hd w (by simp [hw]) rfl)
      _ = false := hworkCleanTwo w hw

  have hinputOutsideProduct (w : Wire) (hw : w ∈ input.wires) :
      w ∉ step.productMul.ports.layout.allWires := by
    intro hm
    simp only [ModExp.MulPorts.layout, RegisterLayout.allWires, List.mem_append,
      step.productLhs, step.productRhs, step.productOut, step.productWork] at hm
    rcases hm with ((hs | hb) | hp) | hwork
    · exact hinputCross w hw w (by simp [hs]) rfl
    · exact hbaseCross w hb w (by simp [hw]) rfl
    · exact hinputCross w hw w (by simp [hp]) rfl
    · exact hinputCross w hw w (by simp [hwork]) rfl
  have hexponentOutsideProduct (w : Wire) (hw : w ∈ exponent.wires) :
      w ∉ step.productMul.ports.layout.allWires := by
    intro hm
    simp only [ModExp.MulPorts.layout, RegisterLayout.allWires, List.mem_append,
      step.productLhs, step.productRhs, step.productOut, step.productWork] at hm
    rcases hm with ((hs | hb) | hp) | hwork
    · exact hexponentCross w hw w (by simp [hs]) rfl
    · exact hbaseCross w hb w (by simp [hw]) rfl
    · exact hexponentCross w hw w (by simp [hp]) rfl
    · exact hexponentCross w hw w (by simp [hwork]) rfl

  have hproductWorkClean : Clean (product.wires ++ mulWork) st3 := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hproductCleanThree w hw
    · exact hworkCleanThree w hw
  have hproductResultRaw := step.productMul.certified.correct st3
    (step.productMul.layoutValid_of_nodup (step.product_layout_nodup hvalid))
    (by simpa [ModExp.MulPorts.layout, step.productLhs] using
      (show st3⟦ᵣsquare.wires⟧ < modulus by rw [hsquareThree]; exact Nat.mod_lt _ hmod))
    (by simpa [ModExp.MulPorts.layout, step.productRhs, hbaseThree] using hbaseBound)
    (by
      simpa [ModExp.MulPorts.layout, step.productOut, step.productWork] using
        hproductWorkClean)
  have hproductResult :
      AgreesOn square.wires st3 st4 ∧ AgreesOn base.wires st3 st4 ∧
        st4⟦ᵣproduct.wires⟧ = st3⟦ᵣsquare.wires⟧ * st3⟦ᵣbase.wires⟧ % modulus ∧
        Clean mulWork st4 := by
    simpa [st4, ModExp.MulPorts.layout, step.productLhs, step.productRhs,
      step.productOut, step.productWork] using hproductResultRaw
  rcases hproductResult with ⟨hsquareAgreeFour, hbaseAgreeFour, hproductValueFour,
    hworkCleanFour⟩
  have hbaseFour : AgreesOn base.wires st st4 := by
    intro w hw
    calc
      st4 w = st3 w := hbaseAgreeFour w hw
      _ = st w := hbaseThreeAgree w hw
  have hexponentFour : AgreesOn exponent.wires st st4 := by
    intro w hw
    calc
      st4 w = st3 w := step.productMul.certified.usesOnly.preservesOutside st3 w
        (hexponentOutsideProduct w hw)
      _ = st w := hexponentThree w hw
  have hinputFour : AgreesOn input.wires st st4 := by
    intro w hw
    calc
      st4 w = st3 w := step.productMul.certified.usesOnly.preservesOutside st3 w
        (hinputOutsideProduct w hw)
      _ = st w := hinputThreeAgree w hw
  have hsquareFour : st4⟦ᵣsquare.wires⟧ =
      st⟦ᵣinput.wires⟧ * st⟦ᵣinput.wires⟧ % modulus := by
    rw [Arithmetic.AgreesOn.regValue hsquareAgreeFour, hsquareThree]
  have hproductFour : st4⟦ᵣproduct.wires⟧ =
      (st⟦ᵣinput.wires⟧ * st⟦ᵣinput.wires⟧ % modulus) *
        st⟦ᵣbase.wires⟧ % modulus := by
    rw [hproductValueFour, hsquareThree, hbaseThree]
  have hrun : run step.compute st = st4 := by
    simp [compute, st4, st3, st2, st1, copy, run_append]
  dsimp only
  rw [hrun]
  exact ⟨hbaseFour, hexponentFour, hinputFour, hsquareFour, hproductFour⟩

/-- One leaf maps a clean accumulator to its next MSB-first square-and-multiply value while
restoring all local scratch. -/
theorem correct {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork bit input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output)
    (st : BasisState) (hvalid : step.allWires.Nodup) (hmod : 0 < modulus)
    (hbaseBound : st⟦ᵣbase.wires⟧ < modulus)
    (hinputBound : st⟦ᵣinput.wires⟧ < modulus)
    (hclean : Clean (output.wires ++ scratch duplicate square product mulWork) st) :
    let after := run step.program st
    AgreesOn base.wires st after ∧
      AgreesOn exponent.wires st after ∧
      AgreesOn input.wires st after ∧
      after⟦ᵣoutput.wires⟧ =
        powStep modulus st⟦ᵣbase.wires⟧ st⟦ᵣinput.wires⟧ (st bit) ∧
      Clean (scratch duplicate square product mulWork) after := by
  have hactiveOutput :
      (step.activeWires ++ output.wires).Nodup := by
    have hperm : step.allWires.Perm (step.activeWires ++ output.wires) := by
      let front := base.wires ++ exponent.wires ++ input.wires
      let scratchVars := scratch duplicate square product mulWork
      simpa [allWires, activeWires, front, scratchVars, List.append_assoc] using
        ((List.perm_append_comm (l₁ := output.wires)
          (l₂ := scratchVars)).append_left front)
    exact hvalid.perm hperm
  obtain ⟨hactiveNd, houtputNd, hdisjoint⟩ := List.nodup_append.mp hactiveOutput
  have hcleanOutput : Clean output.wires st :=
    Arithmetic.Clean.mono hclean (by intro w hw; simp [hw])
  have hcleanScratch : Clean (scratch duplicate square product mulWork) st :=
    Arithmetic.Clean.mono hclean (by intro w hw; simp [hw])
  have hcompute := step.compute_correct st hvalid hmod hbaseBound hinputBound hcleanScratch
  have hcleanup := bennett_cleanup_select step.compute step.activeWires bit square product output
    st step.compute_usesOnly step.compute_HPFree (step.compute_wellFormed hvalid)
    hdisjoint (ModExp.selectOK_of_nodup bit square product output (step.select_nodup hvalid))
    hcleanOutput
  dsimp only at hcompute hcleanup
  rcases hcompute with ⟨hbaseMid, hexponentMid, hinputMid, hsquareMid, hproductMid⟩
  rcases hcleanup with ⟨hactiveAfter, houtputAfter⟩
  let after := run step.program st
  have hactiveAfter' : AgreesOn step.activeWires st after := by
    simpa [after, program, run_append] using hactiveAfter
  have houtputAfter' : after⟦ᵣoutput.wires⟧ =
      if (run step.compute st) bit then
        (run step.compute st)⟦ᵣproduct.wires⟧
      else (run step.compute st)⟦ᵣsquare.wires⟧ := by
    simpa [after, program, run_append] using houtputAfter
  have hbaseAfter : AgreesOn base.wires st after := by
    intro w hw
    exact hactiveAfter' w (by simp [activeWires, hw])
  have hexponentAfter : AgreesOn exponent.wires st after := by
    intro w hw
    exact hactiveAfter' w (by simp [activeWires, hw])
  have hinputAfter : AgreesOn input.wires st after := by
    intro w hw
    exact hactiveAfter' w (by simp [activeWires, hw])
  have hscratchAfter : Clean (scratch duplicate square product mulWork) after := by
    intro w hw
    rw [hactiveAfter' w (by
      simp only [scratch, List.mem_append] at hw
      simp only [activeWires, scratch, List.mem_append]
      tauto)]
    exact hcleanScratch w hw
  have hbitMid : (run step.compute st) bit = st bit :=
    hexponentMid bit step.bit_mem
  have hvalue : after⟦ᵣoutput.wires⟧ =
      powStep modulus st⟦ᵣbase.wires⟧ st⟦ᵣinput.wires⟧ (st bit) := by
    rw [houtputAfter', hbitMid, hsquareMid, hproductMid]
    cases st bit <;> simp [powStep, Nat.mul_mod]
  exact ⟨hbaseAfter, hexponentAfter, hinputAfter, hvalue, hscratchAfter⟩

end Step

/-! ## Balanced checkpoint schedule -/

/-- Wires of checkpoint registers in list order. -/
def checkpointWires {width : Nat} (checkpoints : List (ModExp.Reg width)) : List Wire :=
  checkpoints.flatMap ModExp.Reg.wires

/-- A binary exponent-bit tree.  `wires` is its left-to-right (execution) order. -/
inductive BitTree where
  | leaf (bit : Wire)
  | node (left right : BitTree)
  deriving Repr

namespace BitTree

def wires : BitTree → List Wire
  | .leaf bit => [bit]
  | .node left right => left.wires ++ right.wires

end BitTree

/-- A schedule uses the same checkpoint tail in both children; shallow leaves simply leave any
remaining checkpoint registers untouched. -/
inductive Schedule (width modulus : Nat)
    (base exponent duplicate square product : ModExp.Reg width) (mulWork : List Wire) :
    (tree : BitTree) → (checkpoints : List (ModExp.Reg width)) →
      (input output : ModExp.Reg width) → Type where
  | leaf (bit : Wire) (checkpoints : List (ModExp.Reg width))
      (input output : ModExp.Reg width)
      (step : Step width modulus base exponent duplicate square product mulWork bit input output) :
      Schedule width modulus base exponent duplicate square product mulWork
        (.leaf bit) checkpoints input output
  | node (leftTree rightTree : BitTree) (mid : ModExp.Reg width)
      (checkpoints : List (ModExp.Reg width)) (input output : ModExp.Reg width)
      (left : Schedule width modulus base exponent duplicate square product mulWork
        leftTree checkpoints input mid)
      (right : Schedule width modulus base exponent duplicate square product mulWork
        rightTree checkpoints mid output) :
      Schedule width modulus base exponent duplicate square product mulWork
        (.node leftTree rightTree) (mid :: checkpoints) input output

namespace Schedule

/-- Reversible pebbling: compute the midpoint, compute the right half, uncompute the midpoint. -/
def program {width modulus : Nat} {base exponent duplicate square product : ModExp.Reg width}
    {mulWork tree checkpoints input output}
    (schedule : Schedule width modulus base exponent duplicate square product mulWork
      tree checkpoints input output) : Circuit :=
  match schedule with
  | .leaf _ _ _ _ step => step.program
  | .node _ _ _ _ _ _ left right =>
      circuit! {
        left.program;
        right.program;
        left.program.reverse
      }

def cost {width modulus : Nat} {base exponent duplicate square product : ModExp.Reg width}
    {mulWork tree checkpoints input output}
    (schedule : Schedule width modulus base exponent duplicate square product mulWork
      tree checkpoints input output) : Nat :=
  match schedule with
  | .leaf _ _ _ _ step => step.cost
  | .node _ _ _ _ _ _ left right => 2 * left.cost + right.cost

/-- Complete segment support. -/
def allWires {width modulus : Nat} {base exponent duplicate square product : ModExp.Reg width}
    {mulWork tree checkpoints input output}
    (_schedule : Schedule width modulus base exponent duplicate square product mulWork
      tree checkpoints input output) : List Wire :=
  base.wires ++ exponent.wires ++ input.wires ++ output.wires ++
    checkpointWires checkpoints ++ scratch duplicate square product mulWork

private theorem leaf_step_nodup {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width} {mulWork bit checkpoints input output}
    (step : Step width modulus base exponent duplicate square product mulWork bit input output)
    (hvalid :
      (Schedule.leaf bit checkpoints input output step).allWires.Nodup) :
    step.allWires.Nodup := by
  apply List.Nodup.sublist _ hvalid
  have hsub := (((((List.Sublist.refl base.wires).append
      (List.Sublist.refl exponent.wires)).append (List.Sublist.refl input.wires)).append
      (List.Sublist.refl output.wires)).append (List.nil_sublist (checkpointWires checkpoints))).append
      (List.Sublist.refl (scratch duplicate square product mulWork))
  simp [allWires, Step.allWires, List.append_assoc] at hsub ⊢

private theorem node_left_nodup {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width} {mulWork leftTree rightTree}
    {mid : ModExp.Reg width} {checkpoints : List (ModExp.Reg width)} {input output}
    (left : Schedule width modulus base exponent duplicate square product mulWork
      leftTree checkpoints input mid)
    (right : Schedule width modulus base exponent duplicate square product mulWork
      rightTree checkpoints mid output)
    (hvalid : (Schedule.node leftTree rightTree mid checkpoints input output left right).allWires.Nodup) :
    left.allWires.Nodup := by
  apply List.Nodup.sublist _ hvalid
  have hsub := (((((List.Sublist.refl base.wires).append
      (List.Sublist.refl exponent.wires)).append (List.Sublist.refl input.wires)).append
      (List.nil_sublist output.wires)).append (List.Sublist.refl mid.wires)).append
      (List.Sublist.refl (checkpointWires checkpoints ++
        scratch duplicate square product mulWork))
  simp [allWires, checkpointWires, List.append_assoc] at hsub ⊢

private theorem node_right_nodup {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width} {mulWork leftTree rightTree}
    {mid : ModExp.Reg width} {checkpoints : List (ModExp.Reg width)} {input output}
    (left : Schedule width modulus base exponent duplicate square product mulWork
      leftTree checkpoints input mid)
    (right : Schedule width modulus base exponent duplicate square product mulWork
      rightTree checkpoints mid output)
    (hvalid : (Schedule.node leftTree rightTree mid checkpoints input output left right).allWires.Nodup) :
    right.allWires.Nodup := by
  have hordered :
      (base.wires ++ exponent.wires ++ output.wires ++ mid.wires ++
        checkpointWires checkpoints ++ scratch duplicate square product mulWork).Nodup := by
    apply List.Nodup.sublist _ hvalid
    have hsub := (((((List.Sublist.refl base.wires).append
        (List.Sublist.refl exponent.wires)).append (List.nil_sublist input.wires)).append
        (List.Sublist.refl output.wires)).append (List.Sublist.refl mid.wires)).append
        (List.Sublist.refl (checkpointWires checkpoints ++
          scratch duplicate square product mulWork))
    simp [allWires, checkpointWires, List.append_assoc] at hsub ⊢
  have hperm :
      (base.wires ++ exponent.wires ++ output.wires ++ mid.wires ++
          checkpointWires checkpoints ++ scratch duplicate square product mulWork).Perm
        (base.wires ++ exponent.wires ++ mid.wires ++ output.wires ++
          checkpointWires checkpoints ++ scratch duplicate square product mulWork) := by
    simpa [List.append_assoc] using
      ((List.perm_append_comm (l₁ := output.wires) (l₂ := mid.wires)).append_left
        (base.wires ++ exponent.wires)).append_right
          (checkpointWires checkpoints ++ scratch duplicate square product mulWork)
  simpa [allWires, List.append_assoc] using hordered.perm hperm

theorem program_usesOnly {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork tree checkpoints input output}
    (schedule : Schedule width modulus base exponent duplicate square product mulWork
      tree checkpoints input output) :
    CircuitUsesOnly schedule.allWires schedule.program := by
  induction schedule with
  | leaf bit checkpoints input output step =>
      apply usesOnly_mono step.program_usesOnly
      intro w hw
      simp only [Step.allWires, allWires, checkpointWires, scratch,
        List.mem_append] at hw ⊢
      tauto
  | node leftTree rightTree mid checkpoints input output left right ihLeft ihRight =>
      have hleft : CircuitUsesOnly
          (Schedule.node leftTree rightTree mid checkpoints input output left right).allWires
          left.program := by
        apply usesOnly_mono ihLeft
        intro w hw
        simp only [allWires, checkpointWires, List.flatMap_cons, scratch,
          List.mem_append] at hw ⊢
        tauto
      have hright : CircuitUsesOnly
          (Schedule.node leftTree rightTree mid checkpoints input output left right).allWires
          right.program := by
        apply usesOnly_mono ihRight
        intro w hw
        simp only [allWires, checkpointWires, List.flatMap_cons, scratch,
          List.mem_append] at hw ⊢
        tauto
      simpa [program, List.append_assoc] using
        usesOnly_append (usesOnly_append hleft hright) (usesOnly_reverse hleft)

theorem program_HPFree {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork tree checkpoints input output}
    (schedule : Schedule width modulus base exponent duplicate square product mulWork
      tree checkpoints input output) : HPFree schedule.program := by
  induction schedule with
  | leaf bit checkpoints input output step => exact step.program_HPFree
  | node leftTree rightTree mid checkpoints input output left right ihLeft ihRight =>
      simp [program, ihLeft, ihRight, Arithmetic.hpFree_reverse]

theorem program_tCount {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork tree checkpoints input output}
    (schedule : Schedule width modulus base exponent duplicate square product mulWork
      tree checkpoints input output) : tCount schedule.program = schedule.cost := by
  induction schedule with
  | leaf bit checkpoints input output step => exact step.program_tCount
  | node leftTree rightTree mid checkpoints input output left right ihLeft ihRight =>
      simp [program, cost, tCount_append, Arithmetic.tCount_reverse, ihLeft, ihRight]
      omega

theorem program_wellFormed {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork tree checkpoints input output}
    (schedule : Schedule width modulus base exponent duplicate square product mulWork
      tree checkpoints input output) (hvalid : schedule.allWires.Nodup) :
    CircuitWellFormed schedule.program := by
  induction schedule with
  | leaf bit checkpoints input output step =>
      exact step.program_wellFormed (leaf_step_nodup step hvalid)
  | node leftTree rightTree mid checkpoints input output left right ihLeft ihRight =>
      have hleft := ihLeft (node_left_nodup left right hvalid)
      have hright := ihRight (node_right_nodup left right hvalid)
      simp [program, circuitWellFormed_append, hleft, hright,
        Arithmetic.wellFormed_reverse]

theorem tree_wires_subset_exponent {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork tree checkpoints input output}
    (schedule : Schedule width modulus base exponent duplicate square product mulWork
      tree checkpoints input output) :
    ∀ w ∈ tree.wires, w ∈ exponent.wires := by
  induction schedule with
  | leaf bit checkpoints input output step =>
      intro w hw
      simpa [BitTree.wires] using (show w = bit from by simpa [BitTree.wires] using hw) ▸
        step.bit_mem
  | node leftTree rightTree mid checkpoints input output left right ihLeft ihRight =>
      intro w hw
      simp only [BitTree.wires, List.mem_append] at hw
      exact hw.elim (ihLeft w) (ihRight w)

/-- A scheduled segment computes its MSB-first accumulator fold and returns every checkpoint and
leaf-local scratch wire to zero. -/
theorem correct {width modulus : Nat}
    {base exponent duplicate square product : ModExp.Reg width}
    {mulWork tree checkpoints input output}
    (schedule : Schedule width modulus base exponent duplicate square product mulWork
      tree checkpoints input output)
    (st : BasisState) (hvalid : schedule.allWires.Nodup) (hmod : 0 < modulus)
    (hbaseBound : st⟦ᵣbase.wires⟧ < modulus)
    (hinputBound : st⟦ᵣinput.wires⟧ < modulus)
    (hclean : Clean (output.wires ++ checkpointWires checkpoints ++
      scratch duplicate square product mulWork) st) :
    let after := run schedule.program st
    AgreesOn base.wires st after ∧
      AgreesOn exponent.wires st after ∧
      AgreesOn input.wires st after ∧
      after⟦ᵣoutput.wires⟧ =
        powFold modulus st⟦ᵣbase.wires⟧ st⟦ᵣinput.wires⟧ (tree.wires.map st) ∧
      Clean (checkpointWires checkpoints ++ scratch duplicate square product mulWork) after := by
  induction schedule generalizing st with
  | leaf bit checkpoints input output step =>
      have hstepValid := leaf_step_nodup step hvalid
      have hstepClean : Clean
          (output.wires ++ scratch duplicate square product mulWork) st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          simp only [List.mem_append] at hw ⊢
          tauto)
      have hstep := step.correct st hstepValid hmod hbaseBound hinputBound hstepClean
      dsimp only at hstep
      let after := run step.program st
      have hstepAllCheckpoints :
          (step.allWires ++ checkpointWires checkpoints).Nodup := by
        let front := base.wires ++ exponent.wires ++ input.wires ++ output.wires
        let localScratch := scratch duplicate square product mulWork
        have hperm :
            (Schedule.leaf bit checkpoints input output step).allWires.Perm
              (step.allWires ++ checkpointWires checkpoints) := by
          simpa [allWires, Step.allWires, front, localScratch, List.append_assoc] using
            (List.perm_append_comm (l₁ := checkpointWires checkpoints)
              (l₂ := localScratch)).append_left front
        exact hvalid.perm hperm
      have hstepCheckpoints := (List.nodup_append.mp hstepAllCheckpoints).2.2
      have hcheckpointsClean : Clean (checkpointWires checkpoints) after := by
        intro w hw
        rw [show after w = st w from step.program_usesOnly.preservesOutside st w (by
          intro hs
          exact (hstepCheckpoints w hs w hw) rfl)]
        exact hclean w (by simp [hw])
      have hworkClean :
          Clean (checkpointWires checkpoints ++ scratch duplicate square product mulWork)
            after := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hcheckpointsClean w hw
        · exact hstep.2.2.2.2 w hw
      change
        AgreesOn base.wires st after ∧
          AgreesOn exponent.wires st after ∧
          AgreesOn input.wires st after ∧
          after⟦ᵣoutput.wires⟧ =
            powFold modulus st⟦ᵣbase.wires⟧ st⟦ᵣinput.wires⟧
              ((BitTree.leaf bit).wires.map st) ∧
          Clean (checkpointWires checkpoints ++ scratch duplicate square product mulWork)
            after
      simpa [after, BitTree.wires, powFold] using
        ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hworkClean⟩
  | node leftTree rightTree mid checkpoints input output left right ihLeft ihRight =>
      let front := base.wires ++ exponent.wires
      let tail := checkpointWires checkpoints ++ scratch duplicate square product mulWork
      let shared := mid.wires ++ tail
      have hshape :
          (front ++ (input.wires ++ (output.wires ++ shared))).Nodup := by
        simpa [allWires, checkpointWires, front, tail, shared, List.append_assoc] using hvalid
      obtain ⟨hfrontNd, hrestNd, hfrontRest⟩ := List.nodup_append.mp hshape
      obtain ⟨hinputNd, hafterInputNd, hinputAfter⟩ := List.nodup_append.mp hrestNd
      obtain ⟨houtputNd, hsharedNd, houtputShared⟩ :=
        List.nodup_append.mp hafterInputNd

      have hinputOutsideRight (w : Wire) (hw : w ∈ input.wires) :
          w ∉ right.allWires := by
        intro hr
        have hr' : w ∈ front ∨ w ∈ output.wires ∨ w ∈ shared := by
          simp only [allWires, front, shared, tail, List.mem_append] at hr ⊢
          tauto
        rcases hr' with hf | ho | hs
        · exact (hfrontRest w hf w (by simp [hw])) rfl
        · exact (hinputAfter w hw w (by simp [ho])) rfl
        · exact (hinputAfter w hw w (by simp [hs])) rfl
      have houtputOutsideLeft (w : Wire) (hw : w ∈ output.wires) :
          w ∉ left.allWires := by
        intro hl
        have hl' : w ∈ front ∨ w ∈ input.wires ∨ w ∈ shared := by
          simp only [allWires, front, shared, tail, List.mem_append] at hl ⊢
          tauto
        rcases hl' with hf | hi | hs
        · exact (hfrontRest w hf w (by simp [hw])) rfl
        · exact (hinputAfter w hi w (by simp [hw])) rfl
        · exact (houtputShared w hw w hs) rfl

      have hleftValid := node_left_nodup left right hvalid
      have hrightValid := node_right_nodup left right hvalid
      have hcleanLeft : Clean
          (mid.wires ++ checkpointWires checkpoints ++
            scratch duplicate square product mulWork) st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          simp only [checkpointWires, List.flatMap_cons, List.mem_append] at hw ⊢
          tauto)
      have hleft := ihLeft st hleftValid hbaseBound hinputBound hcleanLeft
      dsimp only at hleft
      let st₁ := run left.program st
      have hleft' :
          AgreesOn base.wires st st₁ ∧
            AgreesOn exponent.wires st st₁ ∧
            AgreesOn input.wires st st₁ ∧
            st₁⟦ᵣmid.wires⟧ =
              powFold modulus st⟦ᵣbase.wires⟧ st⟦ᵣinput.wires⟧
                (leftTree.wires.map st) ∧
            Clean (checkpointWires checkpoints ++
              scratch duplicate square product mulWork) st₁ := by
        simpa [st₁] using hleft
      have houtputCleanOne : Clean output.wires st₁ := by
        intro w hw
        rw [show st₁ w = st w from left.program_usesOnly.preservesOutside st w
          (houtputOutsideLeft w hw)]
        exact hclean w (by simp [hw])
      have hrightClean : Clean
          (output.wires ++ checkpointWires checkpoints ++
            scratch duplicate square product mulWork) st₁ := by
        intro w hw
        simp only [List.mem_append] at hw
        rcases hw with (hw | hw) | hw
        · exact houtputCleanOne w hw
        · exact hleft'.2.2.2.2 w (by simp [hw])
        · exact hleft'.2.2.2.2 w (by simp [hw])
      have hbaseBoundOne : st₁⟦ᵣbase.wires⟧ < modulus := by
        rw [Arithmetic.AgreesOn.regValue hleft'.1]
        exact hbaseBound
      have hmidBoundOne : st₁⟦ᵣmid.wires⟧ < modulus := by
        rw [hleft'.2.2.2.1]
        exact powFold_lt hmod hinputBound _
      have hright := ihRight st₁ hrightValid hbaseBoundOne hmidBoundOne hrightClean
      dsimp only at hright
      let st₂ := run right.program st₁
      have hright' :
          AgreesOn base.wires st₁ st₂ ∧
            AgreesOn exponent.wires st₁ st₂ ∧
            AgreesOn mid.wires st₁ st₂ ∧
            st₂⟦ᵣoutput.wires⟧ =
              powFold modulus st₁⟦ᵣbase.wires⟧ st₁⟦ᵣmid.wires⟧
                (rightTree.wires.map st₁) ∧
            Clean (checkpointWires checkpoints ++
              scratch duplicate square product mulWork) st₂ := by
        simpa [st₂] using hright

      have hrightBits : rightTree.wires.map st₁ = rightTree.wires.map st := by
        apply List.map_congr_left
        intro w hw
        exact hleft'.2.1 w (right.tree_wires_subset_exponent w hw)
      have hstatesAgreeLeft : ∀ w ∈ left.allWires, st₂ w = st₁ w := by
        intro w hw
        simp only [allWires, List.mem_append] at hw
        rcases hw with ((((hb | he) | hi) | hm) | hc) | hs
        · exact hright'.1 w hb
        · exact hright'.2.1 w he
        · exact right.program_usesOnly.preservesOutside st₁ w
            (hinputOutsideRight w hi)
        · exact hright'.2.2.1 w hm
        · rw [hright'.2.2.2.2 w (by simp [hc]), hleft'.2.2.2.2 w (by simp [hc])]
        · rw [hright'.2.2.2.2 w (by simp [hs]), hleft'.2.2.2.2 w (by simp [hs])]
      have hleftCancel : run left.program.reverse st₁ = st := by
        simpa [st₁] using run_reverse_cancel left.program st left.program_HPFree
          (left.program_wellFormed hleftValid)
      have hreverseAgree : ∀ w ∈ left.allWires,
          run left.program.reverse st₂ w = run left.program.reverse st₁ w :=
        CircuitUsesOnly.run_congr (usesOnly_reverse left.program_usesOnly) hstatesAgreeLeft
      let after := run left.program.reverse st₂
      have hrestoreLeft : ∀ w ∈ left.allWires, after w = st w := by
        intro w hw
        calc
          after w = run left.program.reverse st₁ w := hreverseAgree w hw
          _ = st w := congrFun hleftCancel w
      have hbaseAfter : AgreesOn base.wires st after := by
        intro w hw
        exact hrestoreLeft w (by simp [allWires, hw])
      have hexponentAfter : AgreesOn exponent.wires st after := by
        intro w hw
        exact hrestoreLeft w (by simp [allWires, hw])
      have hinputAfter : AgreesOn input.wires st after := by
        intro w hw
        exact hrestoreLeft w (by simp [allWires, hw])
      have houtputAfter : after⟦ᵣoutput.wires⟧ = st₂⟦ᵣoutput.wires⟧ := by
        apply regValue_congr
        intro w hw
        exact (usesOnly_reverse left.program_usesOnly).preservesOutside st₂ w
          (houtputOutsideLeft w hw)
      have hvalue : after⟦ᵣoutput.wires⟧ =
          powFold modulus st⟦ᵣbase.wires⟧ st⟦ᵣinput.wires⟧
            ((BitTree.node leftTree rightTree).wires.map st) := by
        rw [houtputAfter, hright'.2.2.2.1,
          Arithmetic.AgreesOn.regValue hleft'.1, hleft'.2.2.2.1, hrightBits]
        simpa [BitTree.wires, List.map_append] using
          (powFold_append modulus st⟦ᵣbase.wires⟧ st⟦ᵣinput.wires⟧
            (leftTree.wires.map st) (rightTree.wires.map st)).symm
      have hworkAfter : Clean
          (checkpointWires (mid :: checkpoints) ++
            scratch duplicate square product mulWork) after := by
        intro w hw
        rw [hrestoreLeft w (by
          simp only [allWires, checkpointWires, List.flatMap_cons, List.mem_append] at hw ⊢
          tauto)]
        exact hclean w (by
          simp only [checkpointWires, List.flatMap_cons, List.mem_append] at hw ⊢
          tauto)
      dsimp only
      simpa [after, st₂, st₁, program, run_append, List.append_assoc] using
        ⟨hbaseAfter, hexponentAfter, hinputAfter, hvalue, hworkAfter⟩

end Schedule

/-! ## Complete executable plan -/

structure Plan (width modulus : Nat) where
  base : ModExp.Reg width
  exponent : ModExp.Reg width
  out : ModExp.Reg width
  initialAcc : ModExp.Reg width
  duplicate : ModExp.Reg width
  square : ModExp.Reg width
  product : ModExp.Reg width
  mulWork : List Wire
  tree : BitTree
  checkpoints : List (ModExp.Reg width)
  schedule : Schedule width modulus base exponent duplicate square product mulWork
    tree checkpoints initialAcc out
  valid : schedule.allWires.Nodup
  tree_bits : tree.wires = exponent.wires.reverse
  widthPos : 0 < width
  modulusLarge : 1 < modulus

namespace Plan

def program {width modulus : Nat} (plan : Plan width modulus) : Circuit :=
  let init := ModExp.initOne plan.initialAcc
  circuit! {
    init;
    plan.schedule.program;
    init.reverse
  }

def layout {width modulus : Nat} (plan : Plan width modulus) : RegisterLayout where
  lhs := plan.base.wires
  rhs := plan.exponent.wires
  out := plan.out.wires
  work := plan.initialAcc.wires ++ checkpointWires plan.checkpoints ++
    scratch plan.duplicate plan.square plan.product plan.mulWork

def cost {width modulus : Nat} (plan : Plan width modulus) : Nat :=
  plan.schedule.cost

theorem layout_valid {width modulus : Nat} (plan : Plan width modulus) :
    plan.layout.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · rw [layout, plan.base.length_eq, plan.exponent.length_eq]
  · rw [layout, plan.base.length_eq, plan.out.length_eq]
  · have hperm : plan.schedule.allWires.Perm plan.layout.allWires := by
      let front := plan.base.wires ++ plan.exponent.wires
      let tail := checkpointWires plan.checkpoints ++
        scratch plan.duplicate plan.square plan.product plan.mulWork
      simpa [Schedule.allWires, layout, RegisterLayout.allWires, front, tail,
        List.append_assoc] using
        ((List.perm_append_comm (l₁ := plan.initialAcc.wires)
          (l₂ := plan.out.wires)).append_left front).append_right tail
    exact plan.valid.perm hperm

theorem program_usesOnly {width modulus : Nat} (plan : Plan width modulus) :
    CircuitUsesOnly plan.layout.allWires plan.program := by
  have hinit : CircuitUsesOnly plan.layout.allWires (ModExp.initOne plan.initialAcc) := by
    apply usesOnly_mono (ModExp.initOne_usesOnly plan.initialAcc)
    intro w hw
    simp [layout, RegisterLayout.allWires, hw]
  have hschedule : CircuitUsesOnly plan.layout.allWires plan.schedule.program := by
    apply usesOnly_mono plan.schedule.program_usesOnly
    intro w hw
    simp only [Schedule.allWires, layout, RegisterLayout.allWires, checkpointWires,
      scratch, List.mem_append] at hw ⊢
    tauto
  simpa [program, List.append_assoc] using
    usesOnly_append (usesOnly_append hinit hschedule) (usesOnly_reverse hinit)

theorem program_HPFree {width modulus : Nat} (plan : Plan width modulus) :
    HPFree plan.program := by
  simp [program, ModExp.initOne_HPFree, plan.schedule.program_HPFree,
    Arithmetic.hpFree_reverse]

theorem program_tCount {width modulus : Nat} (plan : Plan width modulus) :
    tCount plan.program = plan.cost := by
  simp [program, cost, tCount_append, ModExp.initOne_tCount,
    plan.schedule.program_tCount, Arithmetic.tCount_reverse]

theorem program_wellFormed {width modulus : Nat} (plan : Plan width modulus) :
    CircuitWellFormed plan.program := by
  have hinit := ModExp.initOne_wellFormed plan.initialAcc
  have hschedule := plan.schedule.program_wellFormed plan.valid
  simp [program, circuitWellFormed_append, hinit, hschedule,
    Arithmetic.wellFormed_reverse]

/-- Direct correctness of the low-space exponentiator on the exact executable program term. -/
theorem program_correct {width modulus : Nat} (plan : Plan width modulus)
    (st : BasisState) (hlayout : plan.layout.Valid)
    (hbaseBound : st⟦ᵣplan.base.wires⟧ < modulus)
    (_hexponentBound : st⟦ᵣplan.exponent.wires⟧ < modulus)
    (hclean : Clean (plan.out.wires ++ plan.layout.work) st) :
    let after := run plan.program st
    AgreesOn plan.base.wires st after ∧
      AgreesOn plan.exponent.wires st after ∧
      after⟦ᵣplan.out.wires⟧ =
        st⟦ᵣplan.base.wires⟧ ^ st⟦ᵣplan.exponent.wires⟧ % modulus ∧
      Clean plan.layout.work after := by
  let init := ModExp.initOne plan.initialAcc
  let tail := checkpointWires plan.checkpoints ++
    scratch plan.duplicate plan.square plan.product plan.mulWork
  let front := plan.base.wires ++ plan.exponent.wires ++ plan.out.wires
  have hshape : (front ++ (plan.initialAcc.wires ++ tail)).Nodup := by
    simpa [front, tail, layout, RegisterLayout.allWires, List.append_assoc] using hlayout.2.2
  obtain ⟨hfrontNd, hrestNd, hfrontRest⟩ := List.nodup_append.mp hshape
  obtain ⟨hinitNd, htailNd, hinitTail⟩ := List.nodup_append.mp hrestNd
  have hfrontOutsideInit (w : Wire) (hw : w ∈ front) : w ∉ plan.initialAcc.wires := by
    intro hi
    exact (hfrontRest w hw w (by simp [hi])) rfl
  have htailOutsideInit (w : Wire) (hw : w ∈ tail) : w ∉ plan.initialAcc.wires := by
    intro hi
    exact (hinitTail w hi w hw) rfl

  have hcleanInit : Clean plan.initialAcc.wires st :=
    Arithmetic.Clean.mono hclean (by
      intro w hw
      simp [layout, hw])
  let initialized := run init st
  have hinitialValue : initialized⟦ᵣplan.initialAcc.wires⟧ = 1 := by
    simpa [initialized, init] using
      ModExp.initOne_correct plan.initialAcc st hinitNd hcleanInit plan.widthPos
  have hbaseInitialized : AgreesOn plan.base.wires st initialized := by
    intro w hw
    exact ModExp.initOne_other plan.initialAcc st w
      (hfrontOutsideInit w (by simp [front, hw]))
  have hexponentInitialized : AgreesOn plan.exponent.wires st initialized := by
    intro w hw
    exact ModExp.initOne_other plan.initialAcc st w
      (hfrontOutsideInit w (by simp [front, hw]))
  have hbaseValue : initialized⟦ᵣplan.base.wires⟧ = st⟦ᵣplan.base.wires⟧ :=
    Arithmetic.AgreesOn.regValue hbaseInitialized
  have hexponentMap : plan.exponent.wires.map initialized = plan.exponent.wires.map st := by
    apply List.map_congr_left
    intro w hw
    exact hexponentInitialized w hw
  have hcleanSchedule : Clean (plan.out.wires ++ tail) initialized := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [show initialized w = st w from ModExp.initOne_other plan.initialAcc st w
          (hfrontOutsideInit w (by simp [front, hw]))]
      exact hclean w (by simp [hw])
    · rw [show initialized w = st w from ModExp.initOne_other plan.initialAcc st w
          (htailOutsideInit w hw)]
      exact hclean w (by
        simp only [layout, tail, List.mem_append] at hw ⊢
        tauto)
  have hbaseBoundInitialized : initialized⟦ᵣplan.base.wires⟧ < modulus := by
    rw [hbaseValue]
    exact hbaseBound
  have hinitialBound : initialized⟦ᵣplan.initialAcc.wires⟧ < modulus := by
    rw [hinitialValue]
    exact plan.modulusLarge
  have hschedule := plan.schedule.correct initialized plan.valid
    (Nat.zero_lt_of_lt plan.modulusLarge) hbaseBoundInitialized hinitialBound (by
      simpa [tail, List.append_assoc] using hcleanSchedule)
  dsimp only at hschedule
  let middle := run plan.schedule.program initialized
  have hschedule' :
      AgreesOn plan.base.wires initialized middle ∧
        AgreesOn plan.exponent.wires initialized middle ∧
        AgreesOn plan.initialAcc.wires initialized middle ∧
        middle⟦ᵣplan.out.wires⟧ =
          powFold modulus initialized⟦ᵣplan.base.wires⟧
            initialized⟦ᵣplan.initialAcc.wires⟧ (plan.tree.wires.map initialized) ∧
        Clean tail middle := by
    simpa [middle, tail] using hschedule
  have htreeBits : plan.tree.wires.map initialized =
      (plan.exponent.wires.map st).reverse := by
    rw [plan.tree_bits, List.map_reverse, hexponentMap]
  have hmiddleValue : middle⟦ᵣplan.out.wires⟧ =
      st⟦ᵣplan.base.wires⟧ ^ st⟦ᵣplan.exponent.wires⟧ % modulus := by
    rw [hschedule'.2.2.2.1, hbaseValue, hinitialValue, htreeBits,
      powFold_one_correct plan.modulusLarge,
      msbValue_reverse_eq_bitsValue, ModExp.bitsValue_map_eq_regValue]

  have hinitUses : CircuitUsesOnly plan.initialAcc.wires init := by
    simpa [init] using ModExp.initOne_usesOnly plan.initialAcc
  have hinitCancel : run init.reverse initialized = st := by
    simpa [initialized, init] using run_reverse_cancel init st
      (by simpa [init] using ModExp.initOne_HPFree plan.initialAcc)
      (by simpa [init] using ModExp.initOne_wellFormed plan.initialAcc)
  have hreverseCongr : ∀ w ∈ plan.initialAcc.wires,
      run init.reverse middle w = run init.reverse initialized w :=
    CircuitUsesOnly.run_congr (usesOnly_reverse hinitUses) hschedule'.2.2.1
  let after := run init.reverse middle
  have hinitCleanAfter : Clean plan.initialAcc.wires after := by
    intro w hw
    calc
      after w = run init.reverse initialized w := hreverseCongr w hw
      _ = st w := congrFun hinitCancel w
      _ = false := hcleanInit w hw
  have hbaseAfter : AgreesOn plan.base.wires st after := by
    intro w hw
    calc
      after w = middle w := (usesOnly_reverse hinitUses).preservesOutside middle w
        (hfrontOutsideInit w (by simp [front, hw]))
      _ = initialized w := hschedule'.1 w hw
      _ = st w := hbaseInitialized w hw
  have hexponentAfter : AgreesOn plan.exponent.wires st after := by
    intro w hw
    calc
      after w = middle w := (usesOnly_reverse hinitUses).preservesOutside middle w
        (hfrontOutsideInit w (by simp [front, hw]))
      _ = initialized w := hschedule'.2.1 w hw
      _ = st w := hexponentInitialized w hw
  have houtputAfter : after⟦ᵣplan.out.wires⟧ = middle⟦ᵣplan.out.wires⟧ := by
    apply regValue_congr
    intro w hw
    exact (usesOnly_reverse hinitUses).preservesOutside middle w
      (hfrontOutsideInit w (by simp [front, hw]))
  have htailCleanAfter : Clean tail after := by
    intro w hw
    rw [show after w = middle w from
      (usesOnly_reverse hinitUses).preservesOutside middle w (htailOutsideInit w hw)]
    exact hschedule'.2.2.2.2 w hw
  have hworkCleanAfter : Clean plan.layout.work after := by
    intro w hw
    simp only [layout, List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · exact hinitCleanAfter w hw
    · exact htailCleanAfter w (by simp [tail, hw])
    · exact htailCleanAfter w (by simp [tail, hw])
  dsimp only
  simpa [program, init, initialized, middle, after, run_append, List.append_assoc] using
    ⟨hbaseAfter, hexponentAfter, houtputAfter.trans hmiddleValue, hworkCleanAfter⟩

/-- Package the exact low-space program, layout, and cost into the shared exponentiation API. -/
theorem modExp_contract {width modulus : Nat} (plan : Plan width modulus) :
    ModExpContract plan.program plan.layout modulus plan.cost := by
  refine
    { correct := ?_
      usesOnly := plan.program_usesOnly
      counted := plan.program_tCount
      hpFree := plan.program_HPFree
      wellFormed := fun _ => plan.program_wellFormed }
  intro st hlayout hbaseBound hexponentBound hclean
  exact plan.program_correct st hlayout hbaseBound hexponentBound hclean

end Plan

end LowSpaceModExp
end ShorECDLP
