import ShorECDLP.Submission.Arithmetic.InPlaceModular
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Low-space modular multiplication

This module evaluates multiplication in a clean output register by scanning the multiplier
from most significant bit to least significant bit.  Each Horner step doubles the accumulator
modulo the loaded modulus and conditionally adds the multiplicand.  The same mask, modulus,
and three flag wires are reused at every step, avoiding the width-many Bennett history of the
older schoolbook construction.
-/

namespace ShorECDLP
namespace LowSpaceModMul

open Classical
open Arithmetic
open scoped ArithmeticNotation

/-- Reusable wires touched by one low-space multiplication, in the order convenient for the
recursive proof. -/
def hornerWires (controls source modulusReg : List Wire) (low : Wire)
    (high mask : List Wire) (carry branch overflow : Wire) : List Wire :=
  controls ++ source ++ reductionWires modulusReg (low :: high) mask carry branch overflow

/-- MSB-first Horner evaluation over an LSB-first multiplier register.  Recursing over the tail
first makes the last list element execute first. -/
def horner (source modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) : List Wire → Circuit
  | [] => circuit! {}
  | control :: controls => circuit! {
      horner source modulusReg low high mask carry branch overflow controls;
      modularDouble modulusReg low high mask carry branch overflow;
      controlledModAdd control source modulusReg (low :: high) mask carry branch overflow
    }

/-- Separating the accumulator from all stable registers only permutes the declared footprint. -/
private theorem hornerWires_perm_outsideTarget
    (controls source modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) :
    (hornerWires controls source modulusReg low high mask carry branch overflow).Perm
      ((controls ++ source ++ [branch] ++ modulusReg ++ mask ++ [carry, overflow]) ++
        (low :: high)) := by
  simpa [hornerWires, reductionWires, List.append_assoc] using
    (List.perm_append_comm (l₁ := low :: high) (l₂ := [carry, overflow])).append_left
      (controls ++ source ++ [branch] ++ modulusReg ++ mask)

/-- Every stable register is disjoint from the accumulator in a duplicate-free Horner layout. -/
private theorem stable_not_mem_target
    (controls source modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow w : Wire)
    (hnd : (hornerWires controls source modulusReg low high mask
      carry branch overflow).Nodup)
    (hw : w ∈ controls ++ source ++ [branch] ++ modulusReg ++ mask ++ [carry, overflow]) :
    w ∉ low :: high := by
  have hpermuted := hnd.perm
    (hornerWires_perm_outsideTarget controls source modulusReg low high mask
      carry branch overflow)
  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hpermuted
  intro ht
  exact hcross w hw w ht rfl

/-- Removing the first control preserves the recursive footprint and supplies the local
controlled-add footprint. -/
private theorem horner_cons_nodup
    (control : Wire) (controls source modulusReg : List Wire) (low : Wire)
    (high mask : List Wire) (carry branch overflow : Wire)
    (hnd : (hornerWires (control :: controls) source modulusReg low high mask
      carry branch overflow).Nodup) :
    (hornerWires controls source modulusReg low high mask carry branch overflow).Nodup ∧
      (controlledModAddWires control source modulusReg (low :: high) mask
        carry branch overflow).Nodup := by
  have hcons : (control :: (controls ++ source ++
      reductionWires modulusReg (low :: high) mask carry branch overflow)).Nodup := by
    simpa [hornerWires, List.append_assoc] using hnd
  obtain ⟨hcontrol, htail⟩ := List.nodup_cons.mp hcons
  have htail' : (controls ++ (source ++
      reductionWires modulusReg (low :: high) mask carry branch overflow)).Nodup := by
    simpa [List.append_assoc] using htail
  have hsourceReduction : (source ++
      reductionWires modulusReg (low :: high) mask carry branch overflow).Nodup :=
    (List.nodup_append.mp htail').2.1
  have hcontrolSourceReduction : control ∉ source ++
      reductionWires modulusReg (low :: high) mask carry branch overflow := by
    intro hw
    exact hcontrol (by simp [hw])
  constructor
  · simpa [hornerWires, List.append_assoc] using htail
  · simpa [controlledModAddWires] using
      List.nodup_cons.mpr ⟨hcontrolSourceReduction, hsourceReduction⟩

/-- The one-step reduction footprint is a suffix of every nonempty Horner footprint. -/
private theorem reduction_nodup_of_horner_cons
    (control : Wire) (controls source modulusReg : List Wire) (low : Wire)
    (high mask : List Wire) (carry branch overflow : Wire)
    (hnd : (hornerWires (control :: controls) source modulusReg low high mask
      carry branch overflow).Nodup) :
    (reductionWires modulusReg (low :: high) mask carry branch overflow).Nodup := by
  have hlocal := (horner_cons_nodup control controls source modulusReg low high mask
    carry branch overflow hnd).2
  have hmaster : (control :: (source ++
      reductionWires modulusReg (low :: high) mask carry branch overflow)).Nodup := by
    simpa [controlledModAddWires, List.append_assoc] using hlocal
  exact (List.nodup_append.mp (List.nodup_cons.mp hmaster).2).2.1

/-- One Horner step respects the intended modular arithmetic recurrence. -/
private theorem horner_step (modulus initial source count tailValue : Nat) (control : Bool) :
    (((2 * ((2 ^ count * initial + source * tailValue) % modulus)) % modulus +
        if control then source else 0) % modulus) =
      (2 ^ (count + 1) * initial +
        source * ((if control then 1 else 0) + 2 * tailValue)) % modulus := by
  change
    (2 * ((2 ^ count * initial + source * tailValue) % modulus)) % modulus +
        (if control then source else 0) ≡
      2 ^ (count + 1) * initial +
        source * ((if control then 1 else 0) + 2 * tailValue) [MOD modulus]
  apply Nat.ModEq.trans
    ((Nat.mod_modEq _ _).add (Nat.ModEq.refl _))
  apply Nat.ModEq.trans
    (((Nat.ModEq.refl 2).mul (Nat.mod_modEq _ _)).add (Nat.ModEq.refl _))
  have hraw :
      2 * (2 ^ count * initial + source * tailValue) +
          (if control then source else 0) =
        2 ^ (count + 1) * initial +
          source * ((if control then 1 else 0) + 2 * tailValue) := by
    cases control <;> simp [pow_succ] <;> ring
  rw [hraw]

/-- Exact whole-state action of the MSB-first Horner fold.  The statement permits a nonzero
initial accumulator, which makes the recursive invariant compositional. -/
theorem horner_correct (source modulusReg : List Wire) (low : Wire)
    (high mask : List Wire) (carry branch overflow : Wire) :
    ∀ (controls : List Wire) (st : BasisState),
      source.length = (low :: high).length →
      modulusReg.length = (low :: high).length →
      mask.length = (low :: high).length →
      (hornerWires controls source modulusReg low high mask
        carry branch overflow).Nodup →
      0 < st⟦ᵣmodulusReg⟧ →
      st⟦ᵣmodulusReg⟧ % 2 = 1 →
      2 * st⟦ᵣmodulusReg⟧ ≤ 2 ^ (low :: high).length →
      st⟦ᵣsource⟧ < st⟦ᵣmodulusReg⟧ →
      st⟦ᵣlow :: high⟧ < st⟦ᵣmodulusReg⟧ →
      Clean mask st → st carry = false → st branch = false → st overflow = false →
      let after := run
        (horner source modulusReg low high mask carry branch overflow controls) st
      after⟦ᵣlow :: high⟧ =
          (2 ^ controls.length * st⟦ᵣlow :: high⟧ +
            st⟦ᵣsource⟧ * st⟦ᵣcontrols⟧) % st⟦ᵣmodulusReg⟧ ∧
        ∀ w, w ∉ low :: high → after w = st w := by
  intro controls
  induction controls with
  | nil =>
      intro st _ _ _ _ hmod _ _ _ htarget _ _ _ _
      dsimp only
      simp [horner, Nat.mod_eq_of_lt htarget]
  | cons control controls ih =>
      intro st hsourceLen hmodLen hmaskLen hnd hmod hodd hfit hsource htarget
        hmask hcarry hbranch hoverflow
      let target := low :: high
      let mid := run
        (horner source modulusReg low high mask carry branch overflow controls) st
      let doubled := run
        (modularDouble modulusReg low high mask carry branch overflow) mid
      let after := run
        (controlledModAdd control source modulusReg target mask carry branch overflow) doubled
      have htailNd := (horner_cons_nodup control controls source modulusReg low high mask
        carry branch overflow hnd).1
      have hlocalNd := (horner_cons_nodup control controls source modulusReg low high mask
        carry branch overflow hnd).2
      have hredNd := reduction_nodup_of_horner_cons control controls source modulusReg
        low high mask carry branch overflow hnd
      have hih := ih st hsourceLen hmodLen hmaskLen htailNd hmod hodd hfit hsource
        htarget hmask hcarry hbranch hoverflow
      dsimp only at hih
      change mid⟦ᵣtarget⟧ =
          (2 ^ controls.length * st⟦ᵣtarget⟧ +
            st⟦ᵣsource⟧ * st⟦ᵣcontrols⟧) % st⟦ᵣmodulusReg⟧ ∧
        ∀ w, w ∉ target → mid w = st w at hih
      have hstableOutside : ∀ w,
          w ∈ (control :: controls) ++ source ++ [branch] ++ modulusReg ++ mask ++
            [carry, overflow] →
          w ∉ target := by
        intro w hw
        exact stable_not_mem_target (control :: controls) source modulusReg low high mask
          carry branch overflow w hnd (by simpa [target] using hw)
      have hsourceMid : mid⟦ᵣsource⟧ = st⟦ᵣsource⟧ := by
        apply regValue_congr
        intro w hw
        exact hih.2 w (hstableOutside w (by simp [hw]))
      have hmodulusMid : mid⟦ᵣmodulusReg⟧ = st⟦ᵣmodulusReg⟧ := by
        apply regValue_congr
        intro w hw
        exact hih.2 w (hstableOutside w (by simp [hw]))
      have hcontrolMid : mid control = st control :=
        hih.2 control (hstableOutside control (by simp))
      have hmaskMid : Clean mask mid := by
        intro w hw
        rw [hih.2 w (hstableOutside w (by simp [hw]))]
        exact hmask w hw
      have hcarryMid : mid carry = false := by
        rw [hih.2 carry (hstableOutside carry (by simp)), hcarry]
      have hbranchMid : mid branch = false := by
        rw [hih.2 branch (hstableOutside branch (by simp)), hbranch]
      have hoverflowMid : mid overflow = false := by
        rw [hih.2 overflow (hstableOutside overflow (by simp)), hoverflow]
      have htargetMid : mid⟦ᵣtarget⟧ < mid⟦ᵣmodulusReg⟧ := by
        rw [hih.1, hmodulusMid]
        exact Nat.mod_lt _ hmod
      have hdouble := modularDouble_correct modulusReg low high mask carry branch overflow mid
        hmodLen hmaskLen hredNd (by rw [hmodulusMid]; exact hmod)
        (by rw [hmodulusMid]; exact hodd)
        (by simpa [target, hmodulusMid] using hfit)
        (by simpa [target] using htargetMid)
        hmaskMid hcarryMid hbranchMid hoverflowMid
      dsimp only at hdouble
      change doubled⟦ᵣtarget⟧ =
          (2 * mid⟦ᵣtarget⟧) % mid⟦ᵣmodulusReg⟧ ∧
        ∀ w, w ∉ target → doubled w = mid w at hdouble
      have hsourceDoubled : doubled⟦ᵣsource⟧ = st⟦ᵣsource⟧ := by
        apply regValue_congr
        intro w hw
        rw [hdouble.2 w (hstableOutside w (by simp [hw])),
          hih.2 w (hstableOutside w (by simp [hw]))]
      have hmodulusDoubled : doubled⟦ᵣmodulusReg⟧ = st⟦ᵣmodulusReg⟧ := by
        apply regValue_congr
        intro w hw
        rw [hdouble.2 w (hstableOutside w (by simp [hw])),
          hih.2 w (hstableOutside w (by simp [hw]))]
      have hcontrolDoubled : doubled control = st control := by
        rw [hdouble.2 control (hstableOutside control (by simp)), hcontrolMid]
      have hmaskDoubled : Clean mask doubled := by
        intro w hw
        rw [hdouble.2 w (hstableOutside w (by simp [hw]))]
        exact hmaskMid w hw
      have hcarryDoubled : doubled carry = false := by
        rw [hdouble.2 carry (hstableOutside carry (by simp)), hcarryMid]
      have hbranchDoubled : doubled branch = false := by
        rw [hdouble.2 branch (hstableOutside branch (by simp)), hbranchMid]
      have hoverflowDoubled : doubled overflow = false := by
        rw [hdouble.2 overflow (hstableOutside overflow (by simp)), hoverflowMid]
      have htargetDoubled : doubled⟦ᵣtarget⟧ < doubled⟦ᵣmodulusReg⟧ := by
        rw [hdouble.1, hmodulusDoubled, hmodulusMid]
        exact Nat.mod_lt _ hmod
      have hadd := controlledModAdd_correct control source modulusReg target mask
        carry branch overflow doubled hsourceLen hmodLen hmaskLen
        (by simpa [target] using hlocalNd)
        (by rw [hmodulusDoubled]; exact hmod)
        (by simpa [target, hmodulusDoubled] using hfit)
        (by rw [hsourceDoubled, hmodulusDoubled]; exact hsource)
        htargetDoubled hmaskDoubled hcarryDoubled hbranchDoubled hoverflowDoubled
      dsimp only at hadd
      change after⟦ᵣtarget⟧ =
          (doubled⟦ᵣtarget⟧ +
            if doubled control then doubled⟦ᵣsource⟧ else 0) %
              doubled⟦ᵣmodulusReg⟧ ∧
        ∀ w, w ∉ target → after w = doubled w at hadd
      have hafterValue : after⟦ᵣtarget⟧ =
          (2 ^ (control :: controls).length * st⟦ᵣtarget⟧ +
            st⟦ᵣsource⟧ * st⟦ᵣcontrol :: controls⟧) % st⟦ᵣmodulusReg⟧ := by
        rw [hadd.1, hdouble.1, hsourceDoubled, hmodulusDoubled, hcontrolDoubled,
          hmodulusMid, hih.1]
        rw [horner_step st⟦ᵣmodulusReg⟧ st⟦ᵣtarget⟧ st⟦ᵣsource⟧
          controls.length st⟦ᵣcontrols⟧ (st control)]
        simp [regValue_cons]
      have hother : ∀ w, w ∉ target → after w = st w := by
        intro w hw
        rw [hadd.2 w hw, hdouble.2 w hw, hih.2 w hw]
      have hrun :
          run (horner source modulusReg low high mask carry branch overflow
            (control :: controls)) st = after := by
        simp [horner, after, doubled, mid, target, run_append]
      dsimp only
      rw [hrun]
      simpa [target] using And.intro hafterValue hother

/-- Exact T-count of the Horner fold: `42n` for doubling and `112n` for controlled addition
at each multiplier bit. -/
theorem horner_tCount (source modulusReg : List Wire) (low : Wire)
    (high mask controls : List Wire) (carry branch overflow : Wire)
    (hsourceLen : source.length = (low :: high).length)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length) :
    tCount (horner source modulusReg low high mask carry branch overflow controls) =
      154 * (low :: high).length * controls.length := by
  induction controls with
  | nil => simp [horner]
  | cons control controls ih =>
      simp only [horner, tCount_append]
      rw [ih,
        modularDouble_tCount modulusReg low high mask carry branch overflow hmodLen hmaskLen,
        controlledModAdd_tCount control source modulusReg (low :: high) mask
          carry branch overflow hsourceLen hmodLen hmaskLen]
      simp only [List.length_cons]
      ring

theorem horner_HPFree (source modulusReg : List Wire) (low : Wire)
    (high mask controls : List Wire) (carry branch overflow : Wire) :
    HPFree (horner source modulusReg low high mask carry branch overflow controls) := by
  induction controls with
  | nil => simp [horner]
  | cons control controls ih =>
      simp [horner, ih, modularDouble_HPFree, controlledModAdd_HPFree]

theorem horner_wellFormed (source modulusReg : List Wire) (low : Wire)
    (high mask controls : List Wire) (carry branch overflow : Wire)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length)
    (hnd : (hornerWires controls source modulusReg low high mask
      carry branch overflow).Nodup) :
    CircuitWellFormed
      (horner source modulusReg low high mask carry branch overflow controls) := by
  induction controls with
  | nil => simp [horner]
  | cons control controls ih =>
      have htailNd := (horner_cons_nodup control controls source modulusReg low high mask
        carry branch overflow hnd).1
      have hlocalNd := (horner_cons_nodup control controls source modulusReg low high mask
        carry branch overflow hnd).2
      have hredNd := reduction_nodup_of_horner_cons control controls source modulusReg
        low high mask carry branch overflow hnd
      have htail := ih htailNd
      have hdouble := modularDouble_wellFormed modulusReg low high mask carry branch overflow
        hmodLen hmaskLen hredNd
      have hadd := controlledModAdd_wellFormed control source modulusReg (low :: high) mask
        carry branch overflow hmodLen hmaskLen hlocalNd
      simp [horner, circuitWellFormed_append, htail, hdouble, hadd]

theorem horner_usesOnly (source modulusReg : List Wire) (low : Wire)
    (high mask controls : List Wire) (carry branch overflow : Wire) :
    CircuitUsesOnly
      (hornerWires controls source modulusReg low high mask carry branch overflow)
      (horner source modulusReg low high mask carry branch overflow controls) := by
  induction controls with
  | nil => simp [horner, CircuitUsesOnly]
  | cons control controls ih =>
      let ws := hornerWires (control :: controls) source modulusReg low high mask
        carry branch overflow
      have htail : CircuitUsesOnly ws
          (horner source modulusReg low high mask carry branch overflow controls) := by
        apply usesOnly_mono ih
        intro w hw
        simpa [ws, hornerWires, List.append_assoc] using Or.inr hw
      have hdouble : CircuitUsesOnly ws
          (modularDouble modulusReg low high mask carry branch overflow) := by
        apply usesOnly_mono
          (modularDouble_usesOnly modulusReg low high mask carry branch overflow)
        intro w hw
        simp [ws, hornerWires, hw]
      have hadd : CircuitUsesOnly ws
          (controlledModAdd control source modulusReg (low :: high) mask
            carry branch overflow) := by
        apply usesOnly_mono
          (controlledModAdd_usesOnly control source modulusReg (low :: high) mask
            carry branch overflow)
        intro w hw
        simp only [controlledModAddWires, List.mem_cons, List.mem_append] at hw
        rcases hw with (rfl | hw) | hw
        · simp [ws, hornerWires]
        · simp [ws, hornerWires, hw]
        · simp [ws, hornerWires, hw]
      change CircuitUsesOnly ws _
      simp only [horner]
      exact usesOnly_append (usesOnly_append htail hdouble) hadd

/-! ## Clean out-of-place multiplier wrapper -/

/-- The fixed reusable workspace: loaded modulus, masked addend, and three flag wires. -/
def work (modulusReg mask : List Wire) (carry branch overflow : Wire) : List Wire :=
  branch :: modulusReg ++ mask ++ [carry, overflow]

/-- Public multiplication layout. -/
def layout (source controls : List Wire) (low : Wire) (high modulusReg mask : List Wire)
    (carry branch overflow : Wire) : RegisterLayout :=
  { lhs := source
    rhs := controls
    out := low :: high
    work := work modulusReg mask carry branch overflow }

/-- Load the modulus, evaluate the Horner fold, then unload the restored modulus register. -/
def program (modulus : Nat) (source controls modulusReg : List Wire) (low : Wire)
    (high mask : List Wire) (carry branch overflow : Wire) : Circuit :=
  let load := loadConst modulusReg modulus
  circuit! {
    load;
    horner source modulusReg low high mask carry branch overflow controls;
    load.reverse
  }

/-- The proof-oriented Horner footprint is only a permutation of the public layout. -/
private theorem hornerWires_perm_layoutAll
    (source controls modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) :
    (hornerWires controls source modulusReg low high mask carry branch overflow).Perm
      (layout source controls low high modulusReg mask carry branch overflow).allWires := by
  let pre := branch :: modulusReg ++ mask
  let flags := [carry, overflow]
  have hswapInputs :
      (controls ++ source ++ pre ++ (low :: high) ++ flags).Perm
        (source ++ controls ++ pre ++ (low :: high) ++ flags) := by
    simpa [List.append_assoc] using
      (List.perm_append_comm (l₁ := controls) (l₂ := source)).append_right
        (pre ++ (low :: high) ++ flags)
  have hmoveTarget :
      (source ++ controls ++ pre ++ (low :: high) ++ flags).Perm
        (source ++ controls ++ (low :: high) ++ pre ++ flags) := by
    simpa [List.append_assoc] using
      ((List.perm_append_comm (l₁ := pre) (l₂ := low :: high)).append_left
        (source ++ controls)).append_right flags
  simpa [hornerWires, reductionWires, layout, work, pre, flags,
    RegisterLayout.allWires, List.append_assoc] using hswapInputs.trans hmoveTarget

/-- Move the loaded modulus to the front of the layout, exposing its disjoint complement. -/
private theorem layoutAll_perm_modulusFirst
    (source controls modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) :
    (layout source controls low high modulusReg mask carry branch overflow).allWires.Perm
      (modulusReg ++
        (source ++ controls ++ (low :: high) ++ [branch] ++ mask ++ [carry, overflow])) := by
  let pre := source ++ controls ++ (low :: high) ++ [branch]
  let suffix := mask ++ [carry, overflow]
  simpa [layout, work, RegisterLayout.allWires, pre, suffix, List.append_assoc] using
    (List.perm_append_comm (l₁ := pre) (l₂ := modulusReg)).append_right suffix

/-- Every non-modulus register is disjoint from the modulus register in a valid layout. -/
private theorem stable_not_mem_modulus
    (source controls modulusReg : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow w : Wire)
    (hvalid : (layout source controls low high modulusReg mask
      carry branch overflow).Valid)
    (hw : w ∈ source ++ controls ++ (low :: high) ++ [branch] ++ mask ++
      [carry, overflow]) :
    w ∉ modulusReg := by
  have hpermuted := hvalid.2.2.perm
    (layoutAll_perm_modulusFirst source controls modulusReg low high mask
      carry branch overflow)
  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hpermuted
  intro hm
  exact hcross w hm w hw rfl

theorem program_tCount (modulus : Nat) (source controls modulusReg : List Wire)
    (low : Wire) (high mask : List Wire) (carry branch overflow : Wire)
    (hsourceLen : source.length = (low :: high).length)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length) :
    tCount (program modulus source controls modulusReg low high mask
      carry branch overflow) =
      154 * (low :: high).length * controls.length := by
  simp [program, tCount_append, loadConst_tCount, Arithmetic.tCount_reverse,
    horner_tCount source modulusReg low high mask controls carry branch overflow
      hsourceLen hmodLen hmaskLen]

theorem program_HPFree (modulus : Nat) (source controls modulusReg : List Wire)
    (low : Wire) (high mask : List Wire) (carry branch overflow : Wire) :
    HPFree (program modulus source controls modulusReg low high mask
      carry branch overflow) := by
  simp [program, loadConst_HPFree, horner_HPFree, Arithmetic.hpFree_reverse]

theorem program_usesOnly (modulus : Nat) (source controls modulusReg : List Wire)
    (low : Wire) (high mask : List Wire) (carry branch overflow : Wire) :
    CircuitUsesOnly
      (layout source controls low high modulusReg mask carry branch overflow).allWires
      (program modulus source controls modulusReg low high mask
        carry branch overflow) := by
  let ws :=
    (layout source controls low high modulusReg mask carry branch overflow).allWires
  have hload : CircuitUsesOnly ws (loadConst modulusReg modulus) := by
    apply usesOnly_mono (loadConst_usesOnly modulusReg modulus)
    intro w hw
    simp [ws, layout, work, RegisterLayout.allWires, hw]
  have hhorner : CircuitUsesOnly ws
      (horner source modulusReg low high mask carry branch overflow controls) := by
    apply usesOnly_mono
      (horner_usesOnly source modulusReg low high mask controls carry branch overflow)
    intro w hw
    exact (hornerWires_perm_layoutAll source controls modulusReg low high mask
      carry branch overflow).mem_iff.mp hw
  change CircuitUsesOnly ws _
  simp only [program]
  exact usesOnly_append (usesOnly_append hload hhorner) (usesOnly_reverse hload)

theorem program_wellFormed (modulus : Nat) (source controls modulusReg : List Wire)
    (low : Wire) (high mask : List Wire) (carry branch overflow : Wire)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length)
    (hvalid : (layout source controls low high modulusReg mask
      carry branch overflow).Valid) :
    CircuitWellFormed (program modulus source controls modulusReg low high mask
      carry branch overflow) := by
  have hload := loadConst_wellFormed modulusReg modulus
  have hhornerNd : (hornerWires controls source modulusReg low high mask
      carry branch overflow).Nodup :=
    hvalid.2.2.perm (hornerWires_perm_layoutAll source controls modulusReg low high mask
      carry branch overflow).symm
  have hhorner := horner_wellFormed source modulusReg low high mask controls
    carry branch overflow hmodLen hmaskLen hhornerNd
  simp [program, circuitWellFormed_append, hload, hhorner,
    Arithmetic.wellFormed_reverse]

/-- Direct clean multiplication theorem for the exact executable `program`. -/
theorem program_correct (modulus : Nat) (source controls modulusReg : List Wire)
    (low : Wire) (high mask : List Wire) (carry branch overflow : Wire)
    (hmod : 0 < modulus) (hodd : modulus % 2 = 1)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length)
    (hfit : 2 * modulus ≤ 2 ^ (low :: high).length)
    (st : BasisState)
    (hvalid : (layout source controls low high modulusReg mask
      carry branch overflow).Valid)
    (hsourceBound : st⟦ᵣsource⟧ < modulus)
    (hclean : Clean ((low :: high) ++ work modulusReg mask carry branch overflow) st) :
    let after := run (program modulus source controls modulusReg low high mask
      carry branch overflow) st
    AgreesOn source st after ∧
      AgreesOn controls st after ∧
      after⟦ᵣlow :: high⟧ = st⟦ᵣsource⟧ * st⟦ᵣcontrols⟧ % modulus ∧
      Clean (work modulusReg mask carry branch overflow) after := by
  let target := low :: high
  let load := loadConst modulusReg modulus
  let loaded := run load st
  let mid := run
    (horner source modulusReg low high mask carry branch overflow controls) loaded
  let after := run load.reverse mid
  have hsourceLen : source.length = target.length := by
    simpa [layout, target] using hvalid.2.1
  have hhornerNd : (hornerWires controls source modulusReg low high mask
      carry branch overflow).Nodup :=
    hvalid.2.2.perm (hornerWires_perm_layoutAll source controls modulusReg low high mask
      carry branch overflow).symm
  have hmodFirst := hvalid.2.2.perm
    (layoutAll_perm_modulusFirst source controls modulusReg low high mask
      carry branch overflow)
  have hmodulusNd : modulusReg.Nodup := (List.nodup_append.mp hmodFirst).1
  have hcleanTarget : Clean target st := Arithmetic.Clean.mono hclean (by
    intro w hw
    exact List.mem_append.mpr (Or.inl hw))
  have hcleanWork : Clean (work modulusReg mask carry branch overflow) st :=
    Arithmetic.Clean.mono hclean (by
      intro w hw
      exact List.mem_append.mpr (Or.inr hw))
  have hcleanModulus : Clean modulusReg st := Arithmetic.Clean.mono hcleanWork (by
    intro w hw
    simp [work, hw])
  have hcleanMask : Clean mask st := Arithmetic.Clean.mono hcleanWork (by
    intro w hw
    simp [work, hw])
  have hcarry : st carry = false := hcleanWork carry (by simp [work])
  have hbranch : st branch = false := hcleanWork branch (by simp [work])
  have hoverflow : st overflow = false := hcleanWork overflow (by simp [work])
  have hmodFitsRegister : modulus < 2 ^ modulusReg.length := by
    rw [hmodLen]
    omega
  have hloadedModulus : loaded⟦ᵣmodulusReg⟧ = modulus := by
    simpa [loaded, load] using
      loadConst_correct modulusReg modulus st hmodulusNd hcleanModulus hmodFitsRegister
  have hnotModulus : ∀ w,
      w ∈ source ++ controls ++ target ++ [branch] ++ mask ++ [carry, overflow] →
      w ∉ modulusReg := by
    intro w hw
    exact stable_not_mem_modulus source controls modulusReg low high mask
      carry branch overflow w hvalid (by simpa [target] using hw)
  have hloadOther : ∀ w, w ∉ modulusReg → loaded w = st w := by
    intro w hw
    exact loadConst_other w modulusReg modulus st hw
  have hsourceLoaded : loaded⟦ᵣsource⟧ = st⟦ᵣsource⟧ := by
    apply regValue_congr
    intro w hw
    exact hloadOther w (hnotModulus w (by simp [hw]))
  have hcontrolsLoaded : loaded⟦ᵣcontrols⟧ = st⟦ᵣcontrols⟧ := by
    apply regValue_congr
    intro w hw
    exact hloadOther w (hnotModulus w (by simp [hw]))
  have htargetLoaded : loaded⟦ᵣtarget⟧ = 0 := by
    apply Arithmetic.Clean.regValue_eq_zero
    intro w hw
    rw [hloadOther w (hnotModulus w (by simp [hw]))]
    exact hcleanTarget w hw
  have hmaskLoaded : Clean mask loaded := by
    intro w hw
    rw [hloadOther w (hnotModulus w (by simp [hw]))]
    exact hcleanMask w hw
  have hcarryLoaded : loaded carry = false := by
    rw [hloadOther carry (hnotModulus carry (by simp)), hcarry]
  have hbranchLoaded : loaded branch = false := by
    rw [hloadOther branch (hnotModulus branch (by simp)), hbranch]
  have hoverflowLoaded : loaded overflow = false := by
    rw [hloadOther overflow (hnotModulus overflow (by simp)), hoverflow]
  have hfold := horner_correct source modulusReg low high mask carry branch overflow
    controls loaded hsourceLen hmodLen hmaskLen hhornerNd
    (by rw [hloadedModulus]; exact hmod)
    (by rw [hloadedModulus]; exact hodd)
    (by simpa [target, hloadedModulus] using hfit)
    (by rw [hsourceLoaded, hloadedModulus]; exact hsourceBound)
    (by rw [htargetLoaded, hloadedModulus]; exact hmod)
    hmaskLoaded hcarryLoaded hbranchLoaded hoverflowLoaded
  dsimp only at hfold
  change mid⟦ᵣtarget⟧ =
      (2 ^ controls.length * loaded⟦ᵣtarget⟧ +
        loaded⟦ᵣsource⟧ * loaded⟦ᵣcontrols⟧) % loaded⟦ᵣmodulusReg⟧ ∧
    ∀ w, w ∉ target → mid w = loaded w at hfold
  have hmidValue : mid⟦ᵣtarget⟧ =
      st⟦ᵣsource⟧ * st⟦ᵣcontrols⟧ % modulus := by
    rw [hfold.1, htargetLoaded, hsourceLoaded, hcontrolsLoaded, hloadedModulus]
    simp
  have hstableTarget : ∀ w,
      w ∈ controls ++ source ++ [branch] ++ modulusReg ++ mask ++ [carry, overflow] →
      w ∉ target := by
    intro w hw
    exact stable_not_mem_target controls source modulusReg low high mask
      carry branch overflow w hhornerNd (by simpa [target] using hw)
  have hmidLoadedModulus : ∀ w ∈ modulusReg, mid w = loaded w := by
    intro w hw
    exact hfold.2 w (hstableTarget w (by simp [hw]))
  have hloadUses : CircuitUsesOnly modulusReg load := by
    simpa [load] using loadConst_usesOnly modulusReg modulus
  have hloadFree : HPFree load := by simpa [load] using loadConst_HPFree modulusReg modulus
  have hloadWf : CircuitWellFormed load := by
    simpa [load] using loadConst_wellFormed modulusReg modulus
  have hcancel : run load.reverse loaded = st := by
    simpa [loaded] using run_reverse_cancel load st hloadFree hloadWf
  have hother : ∀ w, w ∉ target → after w = st w := by
    intro w hwTarget
    by_cases hwModulus : w ∈ modulusReg
    · calc
        after w = run load.reverse loaded w :=
          CircuitUsesOnly.run_congr (usesOnly_reverse hloadUses)
            hmidLoadedModulus w hwModulus
        _ = st w := congrFun hcancel w
    · calc
        after w = mid w :=
          (usesOnly_reverse hloadUses).preservesOutside mid w hwModulus
        _ = loaded w := hfold.2 w hwTarget
        _ = st w := hloadOther w hwModulus
  have hafterTarget : after⟦ᵣtarget⟧ = mid⟦ᵣtarget⟧ := by
    apply regValue_congr
    intro w hw
    exact (usesOnly_reverse hloadUses).preservesOutside mid w
      (hnotModulus w (by simp [hw]))
  have hsourceAgree : AgreesOn source st after := by
    intro w hw
    exact hother w (hstableTarget w (by simp [hw]))
  have hcontrolsAgree : AgreesOn controls st after := by
    intro w hw
    exact hother w (hstableTarget w (by simp [hw]))
  have hworkClean : Clean (work modulusReg mask carry branch overflow) after := by
    intro w hw
    rw [hother w]
    · exact hcleanWork w hw
    · have hw' : w ∈ controls ++ source ++ [branch] ++ modulusReg ++ mask ++
          [carry, overflow] := by
        simp only [work, List.mem_cons, List.mem_append] at hw ⊢
        tauto
      exact hstableTarget w hw'
  have hrun : run (program modulus source controls modulusReg low high mask
      carry branch overflow) st = after := by
    simp [program, after, mid, loaded, load, run_append]
  dsimp only
  rw [hrun]
  exact ⟨hsourceAgree, hcontrolsAgree,
    hafterTarget.trans hmidValue, hworkClean⟩

/-- Package the direct theorem and structural facts into the standard multiplication contract. -/
theorem modMul_contract (modulus : Nat) (source controls modulusReg : List Wire)
    (low : Wire) (high mask : List Wire) (carry branch overflow : Wire)
    (hmod : 0 < modulus) (hodd : modulus % 2 = 1)
    (hsourceLen : source.length = (low :: high).length)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length)
    (hfit : 2 * modulus ≤ 2 ^ (low :: high).length) :
    ModMulContract
      (program modulus source controls modulusReg low high mask carry branch overflow)
      (layout source controls low high modulusReg mask carry branch overflow)
      modulus (154 * (low :: high).length * controls.length) := by
  refine
    { correct := ?_
      usesOnly := program_usesOnly modulus source controls modulusReg low high mask
        carry branch overflow
      counted := program_tCount modulus source controls modulusReg low high mask
        carry branch overflow hsourceLen hmodLen hmaskLen
      hpFree := program_HPFree modulus source controls modulusReg low high mask
        carry branch overflow
      wellFormed := fun hvalid => program_wellFormed modulus source controls modulusReg
        low high mask carry branch overflow hmodLen hmaskLen hvalid }
  intro st hvalid hsourceBound _hcontrolsBound hclean
  have hdirect := program_correct modulus source controls modulusReg low high mask
    carry branch overflow hmod hodd hmodLen hmaskLen hfit st hvalid hsourceBound (by
      simpa [layout] using hclean)
  simpa [layout] using hdirect

/-- The reusable private workspace is exactly two width-sized registers plus three bits. -/
theorem work_length (modulusReg mask : List Wire) (carry branch overflow : Wire) :
    (work modulusReg mask carry branch overflow).length =
      modulusReg.length + mask.length + 3 := by
  simp [work]
  omega

/-- A uniform-width valid multiplier layout contains exactly `5n + 3` declared wires. -/
theorem layout_allWires_length (source controls modulusReg : List Wire) (low : Wire)
    (high mask : List Wire) (carry branch overflow : Wire)
    (hcontrolsLen : controls.length = (low :: high).length)
    (hsourceLen : source.length = (low :: high).length)
    (hmodLen : modulusReg.length = (low :: high).length)
    (hmaskLen : mask.length = (low :: high).length) :
    (layout source controls low high modulusReg mask carry branch overflow).allWires.length =
      5 * (low :: high).length + 3 := by
  simp [layout, work, RegisterLayout.allWires, hcontrolsLen, hsourceLen, hmodLen, hmaskLen]
  omega

end LowSpaceModMul
end ShorECDLP
