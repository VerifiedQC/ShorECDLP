import ShorECDLP.Submission.Arithmetic.Primitives
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-
# Clean schoolbook modular multiplication (M1.4)

This module builds a modular multiplier only from the public `ModAddContract` boundary.
The construction is deliberately naive and out-of-place.  It records a schoolbook history of
modular doublings and conditionally masked additions, copies the final accumulator to the
public output, and reverses the whole history (Bennett cleanup).  No theorem depends on a
modular adder's private carry or reduction wiring.
-/

namespace ShorECDLP
namespace ModMul

open Classical
open Arithmetic

/-- Toffoli-mask aligned source bits into a clean destination register. -/
def maskReg (control : Wire) : List Wire → List Wire → Circuit
  | s :: src, d :: dst => Gate.CCX control s d :: maskReg control src dst
  | _, _ => []

theorem maskReg_tCount (control : Wire) (src dst : List Wire)
    (hlen : dst.length = src.length) :
    tCount (maskReg control src dst) = 7 * src.length := by
  induction src generalizing dst with
  | nil =>
      have : dst = [] := List.length_eq_zero_iff.mp hlen
      subst dst
      simp [maskReg]
  | cons s src ih =>
      cases dst with
      | nil => simp at hlen
      | cons d dst =>
          have htail : dst.length = src.length := by simpa using hlen
          rw [maskReg, tCount_cons, ih dst htail]
          simp only [tCost, List.length_cons]
          omega

@[simp]
theorem maskReg_HPFree (control : Wire) (src dst : List Wire) :
    HPFree (maskReg control src dst) := by
  induction src generalizing dst with
  | nil => simp [maskReg]
  | cons s src ih =>
      cases dst with
      | nil => simp [maskReg]
      | cons d dst => simp [maskReg, ih]

theorem maskReg_usesOnly (control : Wire) (src dst ws : List Wire)
    (hc : control ∈ ws) (hsrc : ∀ w ∈ src, w ∈ ws)
    (hdst : ∀ w ∈ dst, w ∈ ws) :
    CircuitUsesOnly ws (maskReg control src dst) := by
  intro g hg
  induction src generalizing dst with
  | nil => simp [maskReg] at hg
  | cons s src ih =>
      cases dst with
      | nil => simp [maskReg] at hg
      | cons d dst =>
          simp only [maskReg, List.mem_cons] at hg
          cases hg with
          | inl heq =>
              subst g
              exact ⟨hc, hsrc s (List.mem_cons_self ..), hdst d (List.mem_cons_self ..)⟩
          | inr htail =>
              exact ih dst (fun w hw => hsrc w (List.mem_cons_of_mem _ hw))
                (fun w hw => hdst w (List.mem_cons_of_mem _ hw)) htail

/-- Masking changes only destination wires. -/
theorem maskReg_other (control w : Wire) :
    ∀ (src dst : List Wire) (st : BasisState), w ∉ dst →
      run (maskReg control src dst) st w = st w := by
  intro src
  induction src with
  | nil => intro dst st _; simp [maskReg]
  | cons s src ih =>
      intro dst st hw
      cases dst with
      | nil => simp [maskReg]
      | cons d dst =>
          simp only [List.mem_cons, not_or] at hw
          rw [maskReg, run_cons, ih dst (applyGate (Gate.CCX control s d) st) hw.2]
          exact upd_other st d (Bool.xor (st d) (st control && st s)) hw.1

/-- Toffoli-mask correctness on duplicate-free, disjoint aligned registers. -/
theorem maskReg_correct (control : Wire) :
    ∀ (src dst : List Wire) (st : BasisState),
      dst.length = src.length → (control :: src ++ dst).Nodup → Clean dst st →
      regValue dst (run (maskReg control src dst) st) =
        if st control then regValue src st else 0 := by
  intro src
  induction src with
  | nil =>
      intro dst st hlen _ _
      have : dst = [] := List.length_eq_zero_iff.mp hlen
      subst dst
      simp
  | cons s src ih =>
      intro dst st hlen hnd hclean
      cases dst with
      | nil => simp at hlen
      | cons d dst =>
          have hlenTail : dst.length = src.length := by simpa using hlen
          obtain ⟨hcRest, hrestNd⟩ := List.nodup_cons.mp hnd
          obtain ⟨hsrcNd, hdstNd, hcross⟩ := List.nodup_append.mp hrestNd
          obtain ⟨_, hsrcTailNd⟩ := List.nodup_cons.mp hsrcNd
          obtain ⟨hdDst, hdstTailNd⟩ := List.nodup_cons.mp hdstNd
          have hcTail : control ∉ src ++ dst := by
            intro hm
            apply hcRest
            rcases List.mem_append.mp hm with hs | hd
            · exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem s hs))
            · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem d hd))
          have htailNd : (control :: src ++ dst).Nodup := List.nodup_cons.mpr ⟨hcTail,
            List.nodup_append.mpr
              ⟨hsrcTailNd, hdstTailNd,
                fun a ha b hb => hcross a (List.mem_cons_of_mem s ha) b
                  (List.mem_cons_of_mem d hb)⟩⟩
          have hdSrc : d ∉ src := by
            intro hd
            exact (hcross d (List.mem_cons_of_mem s hd) d (List.mem_cons_self ..)) rfl
          have hdControl : d ≠ control := by
            intro heq
            apply hcRest
            exact List.mem_append.mpr (Or.inr (heq ▸ List.mem_cons_self ..))
          let st₁ := applyGate (Gate.CCX control s d) st
          have hcleanTail : Clean dst st₁ := by
            intro w hw
            change st[d ↦ Bool.xor (st d) (st control && st s)] w = false
            have hwd : w ≠ d := by
              intro e
              subst w
              exact hdDst hw
            rw [upd_other _ _ _ hwd]
            exact hclean w (List.mem_cons_of_mem d hw)
          have hih := ih dst st₁ hlenTail htailNd hcleanTail
          have hsrcKeep : regValue src st₁ = regValue src st :=
            regValue_upd_not_mem src st d (Bool.xor (st d) (st control && st s)) hdSrc
          have hcontrolKeep : st₁ control = st control := by
            exact upd_other st d (Bool.xor (st d) (st control && st s)) hdControl.symm
          have hdFinal : run (maskReg control src dst) st₁ d = (st control && st s) := by
            rw [maskReg_other control d src dst st₁ hdDst]
            simp [st₁, applyGate, hclean d (List.mem_cons_self ..)]
          rw [maskReg, run_cons, regValue_cons, hdFinal, hih, hcontrolKeep, hsrcKeep,
            regValue_cons]
          cases st control <;> cases st s <;> simp

theorem maskReg_wellFormed (control : Wire) :
    ∀ (src dst : List Wire), (control :: src ++ dst).Nodup →
      CircuitWellFormed (maskReg control src dst) := by
  intro src
  induction src with
  | nil => intro dst _; simp [maskReg]
  | cons s src ih =>
      intro dst hnd
      cases dst with
      | nil => simp [maskReg]
      | cons d dst =>
          obtain ⟨hcRest, hrestNd⟩ := List.nodup_cons.mp hnd
          obtain ⟨hsrcNd, hdstNd, hcross⟩ := List.nodup_append.mp hrestNd
          obtain ⟨_, hsrcTailNd⟩ := List.nodup_cons.mp hsrcNd
          obtain ⟨_, hdstTailNd⟩ := List.nodup_cons.mp hdstNd
          have hcTail : control ∉ src ++ dst := by
            intro hm
            apply hcRest
            rcases List.mem_append.mp hm with hs | hd
            · exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem s hs))
            · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem d hd))
          have htailNd : (control :: src ++ dst).Nodup := List.nodup_cons.mpr ⟨hcTail,
            List.nodup_append.mpr
              ⟨hsrcTailNd, hdstTailNd,
                fun a ha b hb => hcross a (List.mem_cons_of_mem s ha) b
                  (List.mem_cons_of_mem d hb)⟩⟩
          have hcs : control ≠ s := by
            intro e
            exact hcRest (List.mem_append.mpr (Or.inl (e ▸ List.mem_cons_self ..)))
          have hcd : control ≠ d := by
            intro e
            exact hcRest (List.mem_append.mpr (Or.inr (e ▸ List.mem_cons_self ..)))
          rw [maskReg, circuitWellFormed_cons]
          exact ⟨⟨hcs, hcd, hcross s (List.mem_cons_self ..) d (List.mem_cons_self ..)⟩,
            ih dst htailNd⟩

/-! ## Abstract schoolbook schedule -/

/-- A schoolbook multiplication schedule.  At each low-to-high multiplier bit, one abstract
modular-add call doubles the current power and another adds a controlled mask into the
accumulator.  Every output is kept as history for the final Bennett reverse pass. -/
inductive Plan (modulus addCost : Nat) : List Wire → List Wire → List Wire → Type where
  | done (power acc : List Wire) : Plan modulus addCost (List.nil : List Wire) power acc
  | step {control : Wire} {controls power acc : List Wire}
      (duplicate nextPower mask nextAcc doubleWork accWork : List Wire)
      (doubleProgram accProgram : Circuit)
      (doubleSpec : ModAddContract doubleProgram
        { lhs := power, rhs := duplicate, out := nextPower, work := doubleWork }
        modulus addCost)
      (accSpec : ModAddContract accProgram
        { lhs := mask, rhs := acc, out := nextAcc, work := accWork }
        modulus addCost)
      (rest : Plan modulus addCost controls nextPower nextAcc) :
      Plan modulus addCost (control :: controls) power acc

/-- The four operations performed by one schoolbook schedule node. -/
def stageProgram (control : Wire) (power duplicate mask : List Wire)
    (doubleProgram accProgram : Circuit) : Circuit :=
  copyReg power duplicate ++ doubleProgram ++ maskReg control power mask ++ accProgram

namespace Plan

/-- Wires allocated by the schedule, excluding its current power/accumulator inputs and
remaining multiplier controls. -/
def privateWires : {controls power acc : List Wire} →
    Plan modulus addCost controls power acc → List Wire
  | _, _, _, .done .. => []
  | _, _, _, .step duplicate nextPower mask nextAcc doubleWork accWork _ _ _ _ rest =>
      duplicate ++ nextPower ++ doubleWork ++ mask ++ nextAcc ++ accWork ++ rest.privateWires

/-- The accumulator produced by the last schedule node. -/
def finalAcc : {controls power acc : List Wire} →
    Plan modulus addCost controls power acc → List Wire
  | _, _, _, .done _ acc => acc
  | _, _, _, .step _ _ _ _ _ _ _ _ _ _ rest => rest.finalAcc

/-- Forward schoolbook history computation. -/
def forward : {controls power acc : List Wire} →
    Plan modulus addCost controls power acc → Circuit
  | _, _, _, .done .. => []
  | control :: _, power, _, .step duplicate _ mask _ _ _ doubleProgram accProgram _ _ rest =>
      stageProgram control power duplicate mask doubleProgram accProgram ++ rest.forward

/-- Public multiplier layout; the initial zero accumulator and all recorded history are work. -/
def layout {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) (out : List Wire) : RegisterLayout :=
  { lhs := power
    rhs := controls
    out := out
    work := acc ++ plan.privateWires }

/-- Wires used by the forward history; the public copy-out register is deliberately absent. -/
def activeWires {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) : List Wire :=
  power ++ controls ++ acc ++ plan.privateWires

/-- Bennett-clean modular multiplication built from a forward history, copy-out, and reverse. -/
def program {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) (out : List Wire) : Circuit :=
  plan.forward ++ copyReg plan.finalAcc out ++ plan.forward.reverse

/-- The final accumulator is one of the registers reserved in the multiplier workspace. -/
theorem finalAcc_sublist_work :
    ∀ {controls power acc : List Wire} (plan : Plan modulus addCost controls power acc),
      plan.finalAcc.Sublist (acc ++ plan.privateWires) := by
  intro controls power acc plan
  induction plan with
  | done => simp [finalAcc, privateWires]
  | @step control controls power acc duplicate nextPower mask nextAcc doubleWork accWork
      doubleProgram accProgram doubleSpec accSpec rest ih =>
      let pref := acc ++ duplicate ++ nextPower ++ doubleWork ++ mask
      have hinsert :
          (nextAcc ++ rest.privateWires).Sublist
            (nextAcc ++ accWork ++ rest.privateWires) := by
        rw [List.append_assoc]
        exact (List.Sublist.refl nextAcc).append
          (List.sublist_append_right accWork rest.privateWires)
      have hpref :
          (nextAcc ++ accWork ++ rest.privateWires).Sublist
            (pref ++ (nextAcc ++ accWork ++ rest.privateWires)) :=
        List.sublist_append_right pref _
      simpa [finalAcc, privateWires, pref, List.append_assoc] using
        (ih.trans hinsert).trans hpref

/-- Complete support of one schedule stage, in an order that exposes its two add layouts as
contiguous duplicate-free blocks. -/
def stageSupport (control : Wire) (power duplicate nextPower doubleWork mask acc nextAcc accWork :
    List Wire) : List Wire :=
  control :: power ++ duplicate ++ nextPower ++ doubleWork ++ mask ++ acc ++ nextAcc ++ accWork

theorem stageProgram_usesOnly (control : Wire)
    (power duplicate nextPower doubleWork mask acc nextAcc accWork : List Wire)
    (doubleProgram accProgram : Circuit)
    (doubleSpec : ModAddContract doubleProgram
      { lhs := power, rhs := duplicate, out := nextPower, work := doubleWork }
      modulus addCost)
    (accSpec : ModAddContract accProgram
      { lhs := mask, rhs := acc, out := nextAcc, work := accWork }
      modulus addCost) :
    CircuitUsesOnly
      (stageSupport control power duplicate nextPower doubleWork mask acc nextAcc accWork)
      (stageProgram control power duplicate mask doubleProgram accProgram) := by
  let ws := stageSupport control power duplicate nextPower doubleWork mask acc nextAcc accWork
  have hcopy : CircuitUsesOnly ws (copyReg power duplicate) :=
    copyReg_usesOnly power duplicate ws
      (by intro w hw; simp [ws, stageSupport, hw])
      (by intro w hw; simp [ws, stageSupport, hw])
  have hdouble : CircuitUsesOnly ws doubleProgram := usesOnly_mono doubleSpec.usesOnly (by
    intro w hw
    simp only [RegisterLayout.allWires, List.mem_append] at hw
    rcases hw with ((hw | hw) | hw) | hw
    · simp [ws, stageSupport, hw]
    · simp [ws, stageSupport, hw]
    · simp [ws, stageSupport, hw]
    · simp [ws, stageSupport, hw])
  have hmask : CircuitUsesOnly ws (maskReg control power mask) :=
    maskReg_usesOnly control power mask ws
      (by simp [ws, stageSupport])
      (by intro w hw; simp [ws, stageSupport, hw])
      (by intro w hw; simp [ws, stageSupport, hw])
  have hacc : CircuitUsesOnly ws accProgram := usesOnly_mono accSpec.usesOnly (by
    intro w hw
    simp only [RegisterLayout.allWires, List.mem_append] at hw
    rcases hw with ((hw | hw) | hw) | hw
    · simp [ws, stageSupport, hw]
    · simp [ws, stageSupport, hw]
    · simp [ws, stageSupport, hw]
    · simp [ws, stageSupport, hw])
  simpa [stageProgram, List.append_assoc] using
    usesOnly_append (usesOnly_append (usesOnly_append hcopy hdouble) hmask) hacc

/-- Pairwise cross-list distinctness. -/
def WireDisjoint (xs ys : List Wire) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y

/-- Static validity of a schoolbook schedule.  Register width is uniform; each stage is
duplicate-free; and its current support is disjoint from all still-fresh future wires. -/
def Valid (width : Nat) : {controls power acc : List Wire} →
    Plan modulus addCost controls power acc → Prop
  | _, power, acc, .done .. => power.length = width ∧ acc.length = width
  | control :: controls, power, acc,
      .step duplicate nextPower mask nextAcc doubleWork accWork _ _ _ _ rest =>
      power.length = width ∧ acc.length = width ∧ duplicate.length = width ∧
      nextPower.length = width ∧ mask.length = width ∧ nextAcc.length = width ∧
      (stageSupport control power duplicate nextPower doubleWork mask acc nextAcc accWork).Nodup ∧
      WireDisjoint
        (stageSupport control power duplicate nextPower doubleWork mask acc nextAcc accWork)
        (controls ++ rest.privateWires) ∧
      rest.Valid width

theorem finalAcc_length :
    ∀ {controls power acc : List Wire} (plan : Plan modulus addCost controls power acc)
      (width : Nat), plan.Valid width → plan.finalAcc.length = width := by
  intro controls power acc plan
  induction plan with
  | done => intro width hvalid; exact hvalid.2
  | step duplicate nextPower mask nextAcc doubleWork accWork doubleProgram accProgram
      doubleSpec accSpec rest ih =>
      intro width hvalid
      exact ih width hvalid.2.2.2.2.2.2.2.2

theorem initialPower_length {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) (width : Nat)
    (hvalid : plan.Valid width) : power.length = width := by
  cases plan <;> exact hvalid.1

theorem layout_nodup_parts {controls power acc out : List Wire}
    (plan : Plan modulus addCost controls power acc) (hlayout : (plan.layout out).Valid) :
    (power ++ controls).Nodup ∧ out.Nodup ∧ (acc ++ plan.privateWires).Nodup ∧
      WireDisjoint (power ++ controls) out ∧
      WireDisjoint (power ++ controls) (acc ++ plan.privateWires) ∧
      WireDisjoint out (acc ++ plan.privateWires) := by
  have hshape :
      ((power ++ controls) ++ (out ++ (acc ++ plan.privateWires))).Nodup := by
    simpa [layout, RegisterLayout.allWires, List.append_assoc] using hlayout.2.2
  obtain ⟨hinputs, htail, hinputsTail⟩ := List.nodup_append.mp hshape
  obtain ⟨hout, hwork, houtWork⟩ := List.nodup_append.mp htail
  exact ⟨hinputs, hout, hwork,
    fun x hx y hy => hinputsTail x hx y (List.mem_append.mpr (Or.inl hy)),
    fun x hx y hy => hinputsTail x hx y (List.mem_append.mpr (Or.inr hy)),
    houtWork⟩

theorem activeWires_nodup {controls power acc out : List Wire}
    (plan : Plan modulus addCost controls power acc) (hlayout : (plan.layout out).Valid) :
    plan.activeWires.Nodup := by
  obtain ⟨hinputs, hout, hwork, hinputsOut, hinputsWork, houtWork⟩ :=
    layout_nodup_parts plan hlayout
  simpa [activeWires, List.append_assoc] using
    List.nodup_append.mpr ⟨hinputs, hwork, hinputsWork⟩

theorem activeWires_out_disjoint {controls power acc out : List Wire}
    (plan : Plan modulus addCost controls power acc) (hlayout : (plan.layout out).Valid) :
    WireDisjoint plan.activeWires out := by
  obtain ⟨hinputs, hout, hwork, hinputsOut, hinputsWork, houtWork⟩ :=
    layout_nodup_parts plan hlayout
  intro x hx y hy
  have hx' : x ∈ (power ++ controls) ++ (acc ++ plan.privateWires) := by
    simpa [activeWires, List.append_assoc] using hx
  rcases List.mem_append.mp hx' with hx | hx
  · exact hinputsOut x hx y hy
  · exact (houtWork y hy x hx).symm

theorem finalAcc_out_nodup {controls power acc out : List Wire}
    (plan : Plan modulus addCost controls power acc) (hlayout : (plan.layout out).Valid) :
    (plan.finalAcc ++ out).Nodup := by
  obtain ⟨hinputs, hout, hwork, hinputsOut, hinputsWork, houtWork⟩ :=
    layout_nodup_parts plan hlayout
  have hfinal : plan.finalAcc.Nodup :=
    List.Nodup.sublist (finalAcc_sublist_work plan) hwork
  refine List.nodup_append.mpr ⟨hfinal, hout, ?_⟩
  intro x hx y hy
  exact (houtWork y hy x ((finalAcc_sublist_work plan).subset hx)).symm

/-- One low-to-high schoolbook step preserves the intended modular product recurrence. -/
theorem schoolbook_step (modulus acc power tail : Nat) (bit : Bool) :
    ((((if bit then power else 0) + acc) % modulus +
        ((power + power) % modulus) * tail) % modulus) =
      (acc + power * ((if bit then 1 else 0) + 2 * tail)) % modulus := by
  change
    ((if bit then power else 0) + acc) % modulus +
        (power + power) % modulus * tail ≡
      acc + power * ((if bit then 1 else 0) + 2 * tail) [MOD modulus]
  apply Nat.ModEq.trans
    ((Nat.mod_modEq _ _).add ((Nat.mod_modEq _ _).mul (Nat.ModEq.refl tail)))
  have hraw :
      (if bit then power else 0) + acc + (power + power) * tail =
        acc + power * ((if bit then 1 else 0) + 2 * tail) := by
    cases bit <;> simp <;> ring
  rw [hraw]

/-- The forward history uses only its multiplier controls, current power/accumulator, and
declared private wires. -/
theorem forward_usesOnly :
    ∀ {controls power acc : List Wire} (plan : Plan modulus addCost controls power acc)
      (ws : List Wire),
      (∀ w ∈ controls, w ∈ ws) → (∀ w ∈ power, w ∈ ws) →
      (∀ w ∈ acc, w ∈ ws) → (∀ w ∈ plan.privateWires, w ∈ ws) →
      CircuitUsesOnly ws plan.forward := by
  intro controls power acc plan
  induction plan with
  | done => intro ws _ _ _ _; simp [forward, CircuitUsesOnly]
  | @step control controls power acc duplicate nextPower mask nextAcc doubleWork accWork
      doubleProgram accProgram doubleSpec accSpec rest ih =>
      intro ws hcontrols hpower hacc hprivate
      have hdup : ∀ w ∈ duplicate, w ∈ ws := by
        intro w hw; exact hprivate w (by simp [privateWires, hw])
      have hnextPower : ∀ w ∈ nextPower, w ∈ ws := by
        intro w hw; exact hprivate w (by simp [privateWires, hw])
      have hdoubleWork : ∀ w ∈ doubleWork, w ∈ ws := by
        intro w hw; exact hprivate w (by simp [privateWires, hw])
      have hmask : ∀ w ∈ mask, w ∈ ws := by
        intro w hw; exact hprivate w (by simp [privateWires, hw])
      have hnextAcc : ∀ w ∈ nextAcc, w ∈ ws := by
        intro w hw; exact hprivate w (by simp [privateWires, hw])
      have haccWork : ∀ w ∈ accWork, w ∈ ws := by
        intro w hw; exact hprivate w (by simp [privateWires, hw])
      have hrestPrivate : ∀ w ∈ rest.privateWires, w ∈ ws := by
        intro w hw; exact hprivate w (by simp [privateWires, hw])
      have hcopy := copyReg_usesOnly power duplicate ws hpower hdup
      have hdouble : CircuitUsesOnly ws doubleProgram := usesOnly_mono doubleSpec.usesOnly (by
        intro w hw
        simp only [RegisterLayout.allWires, List.mem_append] at hw
        rcases hw with ((hw | hw) | hw) | hw
        · exact hpower w hw
        · exact hdup w hw
        · exact hnextPower w hw
        · exact hdoubleWork w hw)
      have hmasked := maskReg_usesOnly control power mask ws
        (hcontrols control (List.mem_cons_self ..)) hpower hmask
      have haccumulate : CircuitUsesOnly ws accProgram := usesOnly_mono accSpec.usesOnly (by
        intro w hw
        simp only [RegisterLayout.allWires, List.mem_append] at hw
        rcases hw with ((hw | hw) | hw) | hw
        · exact hmask w hw
        · exact hacc w hw
        · exact hnextAcc w hw
        · exact haccWork w hw)
      have hrest := ih ws (fun w hw => hcontrols w (List.mem_cons_of_mem control hw))
        hnextPower hnextAcc hrestPrivate
      simpa [forward, stageProgram, List.append_assoc] using
        usesOnly_append (usesOnly_append (usesOnly_append (usesOnly_append hcopy hdouble) hmasked)
          haccumulate) hrest

theorem forward_usesOnly_active {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) :
    CircuitUsesOnly plan.activeWires plan.forward := by
  apply forward_usesOnly plan plan.activeWires
  · intro w hw; simp [activeWires, hw]
  · intro w hw; simp [activeWires, hw]
  · intro w hw; simp [activeWires, hw]
  · intro w hw; simp [activeWires, hw]

theorem forward_HPFree :
    ∀ {controls power acc : List Wire} (plan : Plan modulus addCost controls power acc),
      HPFree plan.forward := by
  intro controls power acc plan
  induction plan with
  | done => simp [forward]
  | step duplicate nextPower mask nextAcc doubleWork accWork doubleProgram accProgram
      doubleSpec accSpec rest ih =>
      simp [forward, stageProgram, doubleSpec.hpFree, accSpec.hpFree, ih]

theorem forward_tCount :
    ∀ {controls power acc : List Wire} (plan : Plan modulus addCost controls power acc)
      (width : Nat), plan.Valid width →
      tCount plan.forward = controls.length * (2 * addCost + 7 * width) := by
  intro controls power acc plan
  induction plan with
  | done => intro width _; simp [forward]
  | @step control controls power acc duplicate nextPower mask nextAcc doubleWork accWork
      doubleProgram accProgram doubleSpec accSpec rest ih =>
      intro width hvalid
      rcases hvalid with ⟨hpower, hacc, hdup, hnextPower, hmask, hnextAcc, hstage,
        hfuture, hrest⟩
      have hmaskLen : mask.length = power.length := hmask.trans hpower.symm
      rw [forward, stageProgram, tCount_append, tCount_append, tCount_append, tCount_append,
        copyReg_tCount, doubleSpec.counted, maskReg_tCount control power mask hmaskLen,
        accSpec.counted, ih width hrest]
      simp only [List.length_cons]
      rw [hpower]
      simp [Nat.add_mul, two_mul, Nat.add_assoc, Nat.add_comm]

theorem forward_wellFormed :
    ∀ {controls power acc : List Wire} (plan : Plan modulus addCost controls power acc)
      (width : Nat), plan.Valid width → CircuitWellFormed plan.forward := by
  intro controls power acc plan
  induction plan with
  | done => intro width _; simp [forward]
  | @step control controls power acc duplicate nextPower mask nextAcc doubleWork accWork
      doubleProgram accProgram doubleSpec accSpec rest ih =>
      intro width hvalid
      rcases hvalid with ⟨hpower, hacc, hdup, hnextPower, hmask, hnextAcc, hstage,
        hfuture, hrest⟩
      have hblocks :
          (control ::
            ((power ++ duplicate ++ nextPower ++ doubleWork) ++
              (mask ++ acc ++ nextAcc ++ accWork))).Nodup := by
        simpa [stageSupport, List.append_assoc] using hstage
      obtain ⟨hcontrol, hcombined⟩ := List.nodup_cons.mp hblocks
      obtain ⟨hdoubleNd, haccNd, hcross⟩ := List.nodup_append.mp hcombined
      have hdoubleValid :
          RegisterLayout.Valid
            { lhs := power, rhs := duplicate, out := nextPower, work := doubleWork } := by
        refine ⟨hpower.trans hdup.symm, hpower.trans hnextPower.symm, ?_⟩
        simpa [RegisterLayout.allWires, List.append_assoc] using hdoubleNd
      have haccValid :
          RegisterLayout.Valid
            { lhs := mask, rhs := acc, out := nextAcc, work := accWork } := by
        refine ⟨hmask.trans hacc.symm, hmask.trans hnextAcc.symm, ?_⟩
        simpa [RegisterLayout.allWires, List.append_assoc] using haccNd
      have hcopyNd : (power ++ duplicate).Nodup := by
        have hprefix :
            ((power ++ duplicate) ++ (nextPower ++ doubleWork)).Nodup := by
          simpa [List.append_assoc] using hdoubleNd
        exact (List.nodup_append.mp hprefix).1
      have hpowerNd : power.Nodup := by
        have hsplit : (power ++ (duplicate ++ nextPower ++ doubleWork)).Nodup := by
          simpa [List.append_assoc] using hdoubleNd
        exact (List.nodup_append.mp hsplit).1
      have hmaskNd : mask.Nodup := by
        have hsplit : (mask ++ (acc ++ nextAcc ++ accWork)).Nodup := by
          simpa [List.append_assoc] using haccNd
        exact (List.nodup_append.mp hsplit).1
      have hpowerMask : ∀ x ∈ power, ∀ y ∈ mask, x ≠ y := by
        intro x hx y hy
        apply hcross x
        · simp [hx]
        · simp [hy]
      have hmaskBody : (power ++ mask).Nodup :=
        List.nodup_append.mpr ⟨hpowerNd, hmaskNd, hpowerMask⟩
      have hcontrolMask : control ∉ power ++ mask := by
        intro hm
        apply hcontrol
        rcases List.mem_append.mp hm with hp | hm
        · exact List.mem_append.mpr (Or.inl (by simp [hp]))
        · exact List.mem_append.mpr (Or.inr (by simp [hm]))
      have hmaskedNd : (control :: (power ++ mask)).Nodup :=
        List.nodup_cons.mpr ⟨hcontrolMask, hmaskBody⟩
      rw [forward, stageProgram, circuitWellFormed_append, circuitWellFormed_append,
        circuitWellFormed_append, circuitWellFormed_append]
      exact ⟨⟨⟨⟨copyReg_wellFormed power duplicate hcopyNd,
        doubleSpec.wellFormed hdoubleValid⟩,
        maskReg_wellFormed control power mask hmaskedNd⟩,
        accSpec.wellFormed haccValid⟩,
        ih width hrest⟩

/-- The forward history computes `acc + power * controls` modulo `modulus` in its final
accumulator.  It intentionally makes no cleanup claim; cleanup is supplied by the Bennett
wrapper below. -/
theorem forward_correct :
    ∀ {controls power acc : List Wire} (plan : Plan modulus addCost controls power acc)
      (width : Nat) (st : BasisState),
      plan.Valid width → 0 < modulus →
      regValue power st < modulus → regValue acc st < modulus →
      Clean plan.privateWires st →
      regValue plan.finalAcc (run plan.forward st) =
        (regValue acc st + regValue power st * regValue controls st) % modulus := by
  intro controls power acc plan
  induction plan with
  | done =>
      intro width st _ hmod hpower hacc hclean
      simp [forward, finalAcc, Nat.mod_eq_of_lt hacc]
  | @step control controls power acc duplicate nextPower mask nextAcc doubleWork accWork
      doubleProgram accProgram doubleSpec accSpec rest ih =>
      intro width st hvalid hmod hpowerBound haccBound hclean
      rcases hvalid with ⟨hpower, hacc, hdup, hnextPower, hmask, hnextAcc, hstage,
        hfuture, hrest⟩
      have hblocks :
          (control ::
            ((power ++ duplicate ++ nextPower ++ doubleWork) ++
              (mask ++ acc ++ nextAcc ++ accWork))).Nodup := by
        simpa [stageSupport, List.append_assoc] using hstage
      obtain ⟨hcontrol, hcombined⟩ := List.nodup_cons.mp hblocks
      obtain ⟨hdoubleNd, haccBlockNd, hcross⟩ := List.nodup_append.mp hcombined
      have hdoubleShape :
          (power ++ (duplicate ++ (nextPower ++ doubleWork))).Nodup := by
        simpa [List.append_assoc] using hdoubleNd
      obtain ⟨hpowerNd, hdoubleTailNd, hpowerTail⟩ :=
        List.nodup_append.mp hdoubleShape
      obtain ⟨hdupNd, hnextPowerWorkNd, hdupTail⟩ :=
        List.nodup_append.mp hdoubleTailNd
      obtain ⟨hnextPowerNd, hdoubleWorkNd, hnextPowerWork⟩ :=
        List.nodup_append.mp hnextPowerWorkNd
      have haccShape : (mask ++ (acc ++ (nextAcc ++ accWork))).Nodup := by
        simpa [List.append_assoc] using haccBlockNd
      obtain ⟨hmaskNd, haccTailNd, hmaskTail⟩ := List.nodup_append.mp haccShape
      obtain ⟨haccNd, hnextAccWorkNd, haccTail⟩ := List.nodup_append.mp haccTailNd
      obtain ⟨hnextAccNd, haccWorkNd, hnextAccWork⟩ :=
        List.nodup_append.mp hnextAccWorkNd
      have hcopyNd : (power ++ duplicate).Nodup := List.nodup_append.mpr
        ⟨hpowerNd, hdupNd, fun x hx y hy => hpowerTail x hx y (by simp [hy])⟩
      have hdoubleValid :
          RegisterLayout.Valid
            { lhs := power, rhs := duplicate, out := nextPower, work := doubleWork } := by
        refine ⟨hpower.trans hdup.symm, hpower.trans hnextPower.symm, ?_⟩
        simpa [RegisterLayout.allWires, List.append_assoc] using hdoubleNd
      have haccValid :
          RegisterLayout.Valid
            { lhs := mask, rhs := acc, out := nextAcc, work := accWork } := by
        refine ⟨hmask.trans hacc.symm, hmask.trans hnextAcc.symm, ?_⟩
        simpa [RegisterLayout.allWires, List.append_assoc] using haccBlockNd
      have hpowerMask : ∀ x ∈ power, ∀ y ∈ mask, x ≠ y := by
        intro x hx y hy
        exact hcross x (by simp [hx]) y (by simp [hy])
      have hcontrolMask : control ∉ power ++ mask := by
        intro hm
        apply hcontrol
        rcases List.mem_append.mp hm with hp | hm
        · exact List.mem_append.mpr (Or.inl (by simp [hp]))
        · exact List.mem_append.mpr (Or.inr (by simp [hm]))
      have hmaskedNd : (control :: (power ++ mask)).Nodup := List.nodup_cons.mpr
        ⟨hcontrolMask,
          List.nodup_append.mpr ⟨hpowerNd, hmaskNd, hpowerMask⟩⟩

      have hcleanDup : Clean duplicate st := Arithmetic.Clean.mono hclean (by
        intro w hw; simp [privateWires, hw])
      have hcleanDoubleOut : Clean (nextPower ++ doubleWork) st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · simp [privateWires, hw]
          · simp [privateWires, hw])
      have hcleanMask : Clean mask st := Arithmetic.Clean.mono hclean (by
        intro w hw; simp [privateWires, hw])
      have hcleanAccOut : Clean (nextAcc ++ accWork) st := Arithmetic.Clean.mono hclean (by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · simp [privateWires, hw]
        · simp [privateWires, hw])
      have hcleanRestPrivate : Clean rest.privateWires st := Arithmetic.Clean.mono hclean (by
        intro w hw; simp [privateWires, hw])

      let st1 := run (copyReg power duplicate) st
      let st2 := run doubleProgram st1
      let st3 := run (maskReg control power mask) st2
      let st4 := run accProgram st3
      have hdupLen : duplicate.length = power.length := hdup.trans hpower.symm
      have hcopyValue : regValue duplicate st1 = regValue power st := by
        exact copyReg_correct power duplicate st hdupLen hcopyNd hcleanDup
      have hpowerOne : regValue power st1 = regValue power st := by
        apply regValue_congr
        intro w hw
        apply copyReg_other
        intro hwd
        exact (hpowerTail w hw w (by simp [hwd])) rfl
      have hcleanDoubleOne : Clean (nextPower ++ doubleWork) st1 := by
        intro w hw
        have hwd : w ∉ duplicate := by
          intro hmem
          exact (hdupTail w hmem w hw) rfl
        rw [show st1 w = st w from copyReg_other w power duplicate st hwd]
        exact hcleanDoubleOut w hw
      have hpowerOneBound : regValue power st1 < modulus := by
        rw [hpowerOne]
        exact hpowerBound
      have hdupOneBound : regValue duplicate st1 < modulus := by
        rw [hcopyValue]
        exact hpowerBound
      have hdoubleResult :
          AgreesOn power st1 st2 ∧ AgreesOn duplicate st1 st2 ∧
            regValue nextPower st2 =
              (regValue power st1 + regValue duplicate st1) % modulus ∧
            Clean doubleWork st2 := by
        simpa [st2] using doubleSpec.correct st1 hdoubleValid hpowerOneBound hdupOneBound
          hcleanDoubleOne
      rcases hdoubleResult with
        ⟨hpowerAgree, hdupAgree, hnextPowerValueRaw, hdoubleWorkClean⟩
      have hpowerTwo : regValue power st2 = regValue power st :=
        (Arithmetic.AgreesOn.regValue hpowerAgree).trans hpowerOne
      have hnextPowerValue :
          regValue nextPower st2 = (regValue power st + regValue power st) % modulus := by
        rw [hnextPowerValueRaw, hpowerOne, hcopyValue]
      have hcontrolNotDup : control ∉ duplicate := by
        intro hw
        apply hcontrol
        exact List.mem_append.mpr (Or.inl (by simp [hw]))
      have hcontrolNotDouble :
          control ∉
            ({ lhs := power, rhs := duplicate, out := nextPower, work := doubleWork } :
              RegisterLayout).allWires := by
        intro hw
        apply hcontrol
        exact List.mem_append.mpr (Or.inl (by
          simpa [RegisterLayout.allWires, List.append_assoc] using hw))
      have hcontrolTwo : st2 control = st control := by
        calc
          st2 control = st1 control := by
            change run doubleProgram st1 control = st1 control
            exact doubleSpec.usesOnly.preservesOutside st1 control hcontrolNotDouble
          _ = st control := copyReg_other control power duplicate st hcontrolNotDup
      have hmaskNotDouble (w : Wire) (hw : w ∈ mask) :
          w ∉
            ({ lhs := power, rhs := duplicate, out := nextPower, work := doubleWork } :
              RegisterLayout).allWires := by
        intro hd
        exact (hcross w (by
          simpa [RegisterLayout.allWires, List.append_assoc] using hd)
          w (by simp [hw])) rfl
      have hmaskNotDup (w : Wire) (hw : w ∈ mask) : w ∉ duplicate := by
        intro hd
        exact (hcross w (by simp [hd]) w (by simp [hw])) rfl
      have hcleanMaskTwo : Clean mask st2 := by
        intro w hw
        calc
          st2 w = st1 w := by
            change run doubleProgram st1 w = st1 w
            exact doubleSpec.usesOnly.preservesOutside st1 w (hmaskNotDouble w hw)
          _ = st w := copyReg_other w power duplicate st (hmaskNotDup w hw)
          _ = false := hcleanMask w hw
      have hmaskLen : mask.length = power.length := hmask.trans hpower.symm
      have hmaskValue :
          regValue mask st3 = if st control then regValue power st else 0 := by
        rw [maskReg_correct control power mask st2 hmaskLen hmaskedNd hcleanMaskTwo,
          hcontrolTwo, hpowerTwo]
      have hmaskBound : regValue mask st3 < modulus := by
        rw [hmaskValue]
        cases st control <;> simp [hmod, hpowerBound]

      have haccNotDouble (w : Wire) (hw : w ∈ acc) :
          w ∉
            ({ lhs := power, rhs := duplicate, out := nextPower, work := doubleWork } :
              RegisterLayout).allWires := by
        intro hd
        exact (hcross w (by
          simpa [RegisterLayout.allWires, List.append_assoc] using hd)
          w (by simp [hw])) rfl
      have haccNotDup (w : Wire) (hw : w ∈ acc) : w ∉ duplicate := by
        intro hd
        exact (hcross w (by simp [hd]) w (by simp [hw])) rfl
      have haccNotMask (w : Wire) (hw : w ∈ acc) : w ∉ mask := by
        intro hm
        exact (hmaskTail w hm w (by simp [hw])) rfl
      have haccThree : regValue acc st3 = regValue acc st := by
        apply regValue_congr
        intro w hw
        calc
          st3 w = st2 w := by
            change run (maskReg control power mask) st2 w = st2 w
            exact maskReg_other control w power mask st2 (haccNotMask w hw)
          _ = st1 w := by
            change run doubleProgram st1 w = st1 w
            exact doubleSpec.usesOnly.preservesOutside st1 w (haccNotDouble w hw)
          _ = st w := copyReg_other w power duplicate st (haccNotDup w hw)
      have haccThreeBound : regValue acc st3 < modulus := by
        rw [haccThree]
        exact haccBound
      have haccOutNotDouble (w : Wire) (hw : w ∈ nextAcc ++ accWork) :
          w ∉
            ({ lhs := power, rhs := duplicate, out := nextPower, work := doubleWork } :
              RegisterLayout).allWires := by
        intro hd
        exact (hcross w (by
          simpa [RegisterLayout.allWires, List.append_assoc] using hd)
          w (by simp [hw])) rfl
      have haccOutNotDup (w : Wire) (hw : w ∈ nextAcc ++ accWork) : w ∉ duplicate := by
        intro hd
        exact (hcross w (by simp [hd]) w (by simp [hw])) rfl
      have haccOutNotMask (w : Wire) (hw : w ∈ nextAcc ++ accWork) : w ∉ mask := by
        intro hm
        exact (hmaskTail w hm w (by simp [hw])) rfl
      have hcleanAccOutThree : Clean (nextAcc ++ accWork) st3 := by
        intro w hw
        calc
          st3 w = st2 w := by
            change run (maskReg control power mask) st2 w = st2 w
            exact maskReg_other control w power mask st2 (haccOutNotMask w hw)
          _ = st1 w := by
            change run doubleProgram st1 w = st1 w
            exact doubleSpec.usesOnly.preservesOutside st1 w (haccOutNotDouble w hw)
          _ = st w := copyReg_other w power duplicate st (haccOutNotDup w hw)
          _ = false := hcleanAccOut w hw
      have haccResult :
          AgreesOn mask st3 st4 ∧ AgreesOn acc st3 st4 ∧
            regValue nextAcc st4 = (regValue mask st3 + regValue acc st3) % modulus ∧
            Clean accWork st4 := by
        simpa [st4] using
          accSpec.correct st3 haccValid hmaskBound haccThreeBound hcleanAccOutThree
      rcases haccResult with ⟨hmaskAgree, haccAgree, hnextAccValueRaw, haccWorkClean⟩
      have hnextAccValue :
          regValue nextAcc st4 =
            ((if st control then regValue power st else 0) + regValue acc st) % modulus := by
        rw [hnextAccValueRaw, hmaskValue, haccThree]
      have hnextPowerFour : regValue nextPower st4 = regValue nextPower st2 := by
        apply regValue_congr
        intro w hw
        have hnotAccLayout :
            w ∉ ({ lhs := mask, rhs := acc, out := nextAcc, work := accWork } :
              RegisterLayout).allWires := by
          intro ha
          exact (hcross w (by simp [hw]) w (by
            simpa [RegisterLayout.allWires, List.append_assoc] using ha)) rfl
        have hnotMask : w ∉ mask := by
          intro hm
          exact (hcross w (by simp [hw]) w (by simp [hm])) rfl
        calc
          st4 w = st3 w := by
            change run accProgram st3 w = st3 w
            exact accSpec.usesOnly.preservesOutside st3 w hnotAccLayout
          _ = st2 w := by
            change run (maskReg control power mask) st2 w = st2 w
            exact maskReg_other control w power mask st2 hnotMask
      have hnextPowerFourValue :
          regValue nextPower st4 = (regValue power st + regValue power st) % modulus :=
        hnextPowerFour.trans hnextPowerValue
      have hnextPowerBound : regValue nextPower st4 < modulus := by
        rw [hnextPowerFourValue]
        exact Nat.mod_lt _ hmod
      have hnextAccBound : regValue nextAcc st4 < modulus := by
        rw [hnextAccValue]
        exact Nat.mod_lt _ hmod

      let support :=
        stageSupport control power duplicate nextPower doubleWork mask acc nextAcc accWork
      have hstageUses : CircuitUsesOnly support
          (stageProgram control power duplicate mask doubleProgram accProgram) := by
        simpa [support] using stageProgram_usesOnly control power duplicate nextPower doubleWork
          mask acc nextAcc accWork doubleProgram accProgram doubleSpec accSpec
      have hst4 :
          st4 = run (stageProgram control power duplicate mask doubleProgram accProgram) st := by
        simp [st4, st3, st2, st1, stageProgram, run_append]
      have hfutureOutside (w : Wire) (hw : w ∈ controls ++ rest.privateWires) :
          w ∉ support := by
        intro hs
        exact (hfuture w (by simpa [support] using hs) w hw) rfl
      have hcontrolsFour : regValue controls st4 = regValue controls st := by
        apply regValue_congr
        intro w hw
        rw [hst4, hstageUses.preservesOutside st w
          (hfutureOutside w (List.mem_append.mpr (Or.inl hw)))]
      have hrestCleanFour : Clean rest.privateWires st4 := by
        intro w hw
        rw [hst4, hstageUses.preservesOutside st w
          (hfutureOutside w (List.mem_append.mpr (Or.inr hw)))]
        exact hcleanRestPrivate w hw
      have htailCorrect := ih width st4 hrest hmod hnextPowerBound hnextAccBound hrestCleanFour

      rw [forward, run_append]
      change regValue rest.finalAcc
          (run rest.forward
            (run (stageProgram control power duplicate mask doubleProgram accProgram) st)) = _
      rw [← hst4, htailCorrect]
      calc
        (regValue nextAcc st4 + regValue nextPower st4 * regValue controls st4) % modulus =
            ((((if st control then regValue power st else 0) + regValue acc st) % modulus +
              ((regValue power st + regValue power st) % modulus) *
                regValue controls st) % modulus) := by
                  rw [hnextAccValue, hnextPowerFourValue, hcontrolsFour]
        _ = (regValue acc st + regValue power st *
              ((if st control then 1 else 0) + 2 * regValue controls st)) % modulus :=
          schoolbook_step modulus (regValue acc st) (regValue power st)
            (regValue controls st) (st control)
        _ = (regValue acc st + regValue power st * regValue (control :: controls) st) %
              modulus := by rw [regValue_cons]

theorem program_usesOnly {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) (out : List Wire) :
    CircuitUsesOnly (plan.layout out).allWires (plan.program out) := by
  let ws := (plan.layout out).allWires
  have hactive : ∀ w ∈ plan.activeWires, w ∈ ws := by
    intro w hw
    have hw' : w ∈ (power ++ controls) ++ (acc ++ plan.privateWires) := by
      simpa [activeWires, List.append_assoc] using hw
    rcases List.mem_append.mp hw' with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · simp [ws, layout, RegisterLayout.allWires, hw]
      · simp [ws, layout, RegisterLayout.allWires, hw]
    · rcases List.mem_append.mp hw with hw | hw
      · simp [ws, layout, RegisterLayout.allWires, hw]
      · simp [ws, layout, RegisterLayout.allWires, hw]
  have hforward : CircuitUsesOnly ws plan.forward :=
    usesOnly_mono (forward_usesOnly_active plan) hactive
  have hfinal : ∀ w ∈ plan.finalAcc, w ∈ ws := by
    intro w hw
    have hwork := (finalAcc_sublist_work plan).subset hw
    simp [ws, layout, RegisterLayout.allWires, hwork]
  have hout : ∀ w ∈ out, w ∈ ws := by
    intro w hw
    simp [ws, layout, RegisterLayout.allWires, hw]
  have hcopy : CircuitUsesOnly ws (copyReg plan.finalAcc out) :=
    copyReg_usesOnly plan.finalAcc out ws hfinal hout
  simpa [program, List.append_assoc] using
    usesOnly_append (usesOnly_append hforward hcopy) (usesOnly_reverse hforward)

theorem program_tCount {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) (out : List Wire) (width : Nat)
    (hvalid : plan.Valid width) :
    tCount (plan.program out) = 2 * controls.length * (2 * addCost + 7 * width) := by
  rw [program, tCount_append, tCount_append, copyReg_tCount, tCount_reverse,
    forward_tCount plan width hvalid]
  ring

theorem program_HPFree {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) (out : List Wire) :
    HPFree (plan.program out) := by
  simp [program, forward_HPFree plan, hpFree_reverse (forward_HPFree plan)]

theorem program_wellFormed {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) (out : List Wire) (width : Nat)
    (hvalid : plan.Valid width) (hlayout : (plan.layout out).Valid) :
    CircuitWellFormed (plan.program out) := by
  have hforward := forward_wellFormed plan width hvalid
  have hcopy := copyReg_wellFormed plan.finalAcc out (finalAcc_out_nodup plan hlayout)
  rw [program, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨hforward, hcopy⟩, wellFormed_reverse hforward⟩

/-- The Bennett wrapper packages the exact same program term into the public multiplication
contract.  The cost allows an arbitrary multiplier-register length; a valid public layout
later identifies that length with `width`. -/
theorem modMul_contract {controls power acc : List Wire}
    (plan : Plan modulus addCost controls power acc) (out : List Wire) (width : Nat)
    (hvalid : plan.Valid width) (hmod : 0 < modulus) :
    ModMulContract (plan.program out) (plan.layout out) modulus
      (2 * controls.length * (2 * addCost + 7 * width)) := by
  refine
    { correct := ?_
      usesOnly := program_usesOnly plan out
      counted := program_tCount plan out width hvalid
      hpFree := program_HPFree plan out
      wellFormed := fun hlayout => program_wellFormed plan out width hvalid hlayout }
  intro st hlayout hpowerBound hcontrolsBound hclean
  have hcleanOut : Clean out st := Arithmetic.Clean.mono hclean (by
    intro w hw; simp [layout, hw])
  have hcleanWork : Clean (acc ++ plan.privateWires) st := Arithmetic.Clean.mono hclean (by
    intro w hw; simp [layout, hw])
  have hcleanAcc : Clean acc st := Arithmetic.Clean.mono hcleanWork (by
    intro w hw; exact List.mem_append.mpr (Or.inl hw))
  have hcleanPrivate : Clean plan.privateWires st := Arithmetic.Clean.mono hcleanWork (by
    intro w hw; exact List.mem_append.mpr (Or.inr hw))
  have haccZero : regValue acc st = 0 := Arithmetic.Clean.regValue_eq_zero hcleanAcc
  have haccBound : regValue acc st < modulus := by
    rw [haccZero]
    exact hmod
  let mid := run plan.forward st
  let copied := run (copyReg plan.finalAcc out) mid
  let after := run plan.forward.reverse copied
  have hforwardValue :
      regValue plan.finalAcc mid =
        (regValue acc st + regValue power st * regValue controls st) % modulus := by
    simpa [mid] using
      forward_correct plan width st hvalid hmod hpowerBound haccBound hcleanPrivate
  have hforwardUses : CircuitUsesOnly plan.activeWires plan.forward :=
    forward_usesOnly_active plan
  have hforwardFree : HPFree plan.forward := forward_HPFree plan
  have hforwardWf : CircuitWellFormed plan.forward := forward_wellFormed plan width hvalid
  have hactiveOut : WireDisjoint plan.activeWires out :=
    activeWires_out_disjoint plan hlayout
  have houtOutside (w : Wire) (hw : w ∈ out) : w ∉ plan.activeWires := by
    intro ha
    exact (hactiveOut w ha w hw) rfl
  have hcleanOutMid : Clean out mid := by
    intro w hw
    calc
      mid w = st w := by
        change run plan.forward st w = st w
        exact hforwardUses.preservesOutside st w (houtOutside w hw)
      _ = false := hcleanOut w hw
  have houtWidth : out.length = width :=
    hlayout.2.1.symm.trans (initialPower_length plan width hvalid)
  have houtFinal : out.length = plan.finalAcc.length :=
    houtWidth.trans (finalAcc_length plan width hvalid).symm
  have hcopyValue : regValue out copied = regValue plan.finalAcc mid := by
    exact copyReg_correct plan.finalAcc out mid houtFinal (finalAcc_out_nodup plan hlayout)
      hcleanOutMid
  have hcopyActive : ∀ w ∈ plan.activeWires, copied w = mid w := by
    intro w hw
    change run (copyReg plan.finalAcc out) mid w = mid w
    apply copyReg_other
    intro ho
    exact (hactiveOut w hw w ho) rfl
  have hreverseUses : CircuitUsesOnly plan.activeWires plan.forward.reverse :=
    usesOnly_reverse hforwardUses
  have hcancel : run plan.forward.reverse mid = st := by
    simpa [mid] using run_reverse_cancel plan.forward st hforwardFree hforwardWf
  have hafterActive : ∀ w ∈ plan.activeWires, after w = st w := by
    intro w hw
    calc
      after w = run plan.forward.reverse mid w := by
        change run plan.forward.reverse copied w = run plan.forward.reverse mid w
        exact Arithmetic.CircuitUsesOnly.run_congr hreverseUses hcopyActive w hw
      _ = st w := by rw [hcancel]
  have hafterOutValue : regValue out after = regValue out copied := by
    apply regValue_congr
    intro w hw
    change run plan.forward.reverse copied w = copied w
    exact hreverseUses.preservesOutside copied w (houtOutside w hw)
  have hpowerActive : ∀ w ∈ power, w ∈ plan.activeWires := by
    intro w hw; simp [activeWires, hw]
  have hcontrolsActive : ∀ w ∈ controls, w ∈ plan.activeWires := by
    intro w hw; simp [activeWires, hw]
  have hworkActive : ∀ w ∈ acc ++ plan.privateWires, w ∈ plan.activeWires := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · simp [activeWires, hw]
    · simp [activeWires, hw]
  have hpowerAgree : AgreesOn power st after := by
    intro w hw; exact hafterActive w (hpowerActive w hw)
  have hcontrolsAgree : AgreesOn controls st after := by
    intro w hw; exact hafterActive w (hcontrolsActive w hw)
  have hworkCleanAfter : Clean (acc ++ plan.privateWires) after := by
    intro w hw
    rw [hafterActive w (hworkActive w hw)]
    exact hcleanWork w hw
  have houtputValue :
      regValue out after = (regValue power st * regValue controls st) % modulus := by
    rw [hafterOutValue, hcopyValue, hforwardValue, haccZero]
    simp
  have hprogramRun : run (plan.program out) st = after := by
    simp [program, after, copied, mid, run_append]
  change
    AgreesOn power st (run (plan.program out) st) ∧
      AgreesOn controls st (run (plan.program out) st) ∧
      regValue out (run (plan.program out) st) =
        (regValue power st * regValue controls st) % modulus ∧
      Clean (acc ++ plan.privateWires) (run (plan.program out) st)
  rw [hprogramRun]
  exact ⟨hpowerAgree, hcontrolsAgree, houtputValue, hworkCleanAfter⟩

end Plan

end ModMul
end ShorECDLP
