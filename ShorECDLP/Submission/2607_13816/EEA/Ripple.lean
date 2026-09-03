import ShorECDLP.Submission.«2607_13816».EEA.UnaryIteration

/-!
# Dirty-controlled ripple cells

This file formalizes the four location-controlled Cuccaro cells used by the pinned
arXiv:2607.13816v2 supplement.  The unconditional CNOT skeleton is intentional: on a lane
outside the selected interval it cancels between the two passes, while the carry update is
controlled by the unary range accumulator.  A single arbitrary dirty wire realizes each
three-controlled X and is restored exactly.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

set_option linter.unusedSimpArgs false

/-- The three Boolean data roles carried through one ripple cell. -/
structure RippleCellBits where
  target : Bool
  addend : Bool
  carry : Bool
deriving DecidableEq, Repr

/-- Boolean action of Figure 11(a), including the location control. -/
def controlledMajBits (control : Bool) (bits : RippleCellBits) : RippleCellBits :=
  let target := Bool.xor bits.target bits.carry
  let addend := Bool.xor bits.addend bits.carry
  { target := target
    addend := addend
    carry := Bool.xor bits.carry (control && target && addend) }

/-- Boolean action of Figure 11(b), including the location control. -/
def controlledUmaBits (control : Bool) (bits : RippleCellBits) : RippleCellBits :=
  let carry := Bool.xor bits.carry
    (control && bits.target && bits.addend)
  let target := Bool.xor bits.target (control && bits.addend)
  let addend := Bool.xor bits.addend carry
  { target := Bool.xor target carry
    addend := addend
    carry := carry }

/-- Boolean action of the inverse of Figure 11(a). -/
def controlledMajInvBits (control : Bool) (bits : RippleCellBits) : RippleCellBits :=
  let carry := Bool.xor bits.carry
    (control && bits.target && bits.addend)
  { target := Bool.xor bits.target carry
    addend := Bool.xor bits.addend carry
    carry := carry }

/-- Boolean action of the inverse of Figure 11(b). -/
def controlledUmaInvBits (control : Bool) (bits : RippleCellBits) : RippleCellBits :=
  let target := Bool.xor bits.target bits.carry
  let addend := Bool.xor bits.addend bits.carry
  let target := Bool.xor target (control && addend)
  { target := target
    addend := addend
    carry := Bool.xor bits.carry (control && target && addend) }

theorem controlledMajInvBits_controlledMajBits
    (control : Bool) (bits : RippleCellBits) :
    controlledMajInvBits control (controlledMajBits control bits) = bits := by
  cases bits with
  | mk target addend carry =>
      cases control <;> cases target <;> cases addend <;> cases carry <;>
        decide

theorem controlledMajBits_controlledMajInvBits
    (control : Bool) (bits : RippleCellBits) :
    controlledMajBits control (controlledMajInvBits control bits) = bits := by
  cases bits with
  | mk target addend carry =>
      cases control <;> cases target <;> cases addend <;> cases carry <;>
        decide

theorem controlledUmaInvBits_controlledUmaBits
    (control : Bool) (bits : RippleCellBits) :
    controlledUmaInvBits control (controlledUmaBits control bits) = bits := by
  cases bits with
  | mk target addend carry =>
      cases control <;> cases target <;> cases addend <;> cases carry <;>
        decide

theorem controlledUmaBits_controlledUmaInvBits
    (control : Bool) (bits : RippleCellBits) :
    controlledUmaBits control (controlledUmaInvBits control bits) = bits := by
  cases bits with
  | mk target addend carry =>
      cases control <;> cases target <;> cases addend <;> cases carry <;>
        decide

/-- Location-controlled MAJ with the supplement's one-dirty-wire C3X. -/
def controlledMajDirty
    (control target addend carry dirty : Wire) : Circuit :=
  [.CX carry target, .CX carry addend] ++
    dirtyC3X control target addend carry dirty

/-- Location-controlled UMA with the supplement's one-dirty-wire C3X. -/
def controlledUmaDirty
    (control target addend carry dirty : Wire) : Circuit :=
  dirtyC3X control target addend carry dirty ++
    [.CCX control addend target, .CX carry addend, .CX carry target]

/-- Exact inverse of `controlledMajDirty`. -/
def controlledMajInvDirty
    (control target addend carry dirty : Wire) : Circuit :=
  dirtyC3X control target addend carry dirty ++
    [.CX carry addend, .CX carry target]

/-- Exact inverse of `controlledUmaDirty`. -/
def controlledUmaInvDirty
    (control target addend carry dirty : Wire) : Circuit :=
  [.CX carry target, .CX carry addend, .CCX control addend target] ++
    dirtyC3X control target addend carry dirty

/-- Read the three logical data roles of a ripple cell. -/
def readRippleCell
    (target addend carry : Wire) (state : BasisState) : RippleCellBits where
  target := state target
  addend := state addend
  carry := state carry

/-- Write the three logical data roles of a ripple cell. -/
def writeRippleCell
    (target addend carry : Wire) (bits : RippleCellBits)
    (state : BasisState) : BasisState :=
  state[target ↦ bits.target][addend ↦ bits.addend][carry ↦ bits.carry]

private theorem cell_nodup_parts
    (control target addend carry dirty : Wire)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    control ≠ target ∧ control ≠ addend ∧ control ≠ carry ∧ control ≠ dirty ∧
      target ≠ addend ∧ target ≠ carry ∧ target ≠ dirty ∧
      addend ≠ carry ∧ addend ≠ dirty ∧ carry ≠ dirty := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  rcases hnd with
    ⟨⟨hct, hca, hcc, hcd⟩,
      ⟨⟨hta, htc, htd⟩,
        ⟨⟨hac, had⟩, ⟨hcarryDirty, _⟩⟩⟩⟩
  exact ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryDirty⟩

private theorem run_controlledMajDirty_eq
    (control target addend carry dirty : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    run (controlledMajDirty control target addend carry dirty) state =
      writeRippleCell target addend carry
        (controlledMajBits (state control)
          (readRippleCell target addend carry state)) state := by
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryDirty⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledMajDirty, run_append]
  let first := run [.CX carry target, .CX carry addend] state
  have hfirst : first =
      state[target ↦ Bool.xor (state target) (state carry)]
        [addend ↦ Bool.xor (state addend) (state carry)] := by
    funext wire
    by_cases hwt : wire = target
    · subst wire
      simp [first, run, applyGate, upd, hta, htc, hta', htc', hac']
    · by_cases hwa : wire = addend
      · subst wire
        simp [first, run, applyGate, upd, hta, hac, hta', htc', hac']
      · simp [first, run, applyGate, upd, hwt, hwa]
  have hndFirst : [control, target, addend, carry, dirty].Nodup := hnd
  rw [run_dirtyC3X control target addend carry dirty first hndFirst, hfirst]
  funext wire
  by_cases hwt : wire = target
  · subst wire
    cases hc : state control <;> cases ht : state target <;>
      cases ha : state addend <;> cases hcarry : state carry <;>
      simp [writeRippleCell, controlledMajBits, readRippleCell, upd,
        hta, htc, hac, hta', htc', hac', hct, hca, hcc,
        hc, ht, ha, hcarry]
  · by_cases hwa : wire = addend
    · subst wire
      cases hc : state control <;> cases ht : state target <;>
        cases ha : state addend <;> cases hcarry : state carry <;>
        simp [writeRippleCell, controlledMajBits, readRippleCell, upd,
          hta, htc, hac, hta', htc', hac', hct, hca, hcc,
          hc, ht, ha, hcarry]
    · by_cases hwc : wire = carry
      · subst wire
        cases hc : state control <;> cases ht : state target <;>
          cases ha : state addend <;> cases hcarry : state carry <;>
          simp [writeRippleCell, controlledMajBits, readRippleCell, upd,
            hta, htc, hac, hta', htc', hac', hct, hca, hcc,
            hc, ht, ha, hcarry]
      · simp [writeRippleCell, controlledMajBits, readRippleCell, upd,
          hwt, hwa, hwc]

private theorem run_controlledUmaDirty_eq
    (control target addend carry dirty : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    run (controlledUmaDirty control target addend carry dirty) state =
      writeRippleCell target addend carry
        (controlledUmaBits (state control)
          (readRippleCell target addend carry state)) state := by
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryDirty⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledUmaDirty, run_append,
    run_dirtyC3X control target addend carry dirty state hnd]
  funext wire
  by_cases hwt : wire = target
  · subst wire
    cases hc : state control <;> cases ht : state target <;>
      cases ha : state addend <;> cases hcarry : state carry <;>
      simp [run, applyGate, writeRippleCell, controlledUmaBits,
        readRippleCell, upd, hta, htc, hac, hta', htc', hac', hct, hca, hcc,
        hc, ht, ha, hcarry]
  · by_cases hwa : wire = addend
    · subst wire
      cases hc : state control <;> cases ht : state target <;>
        cases ha : state addend <;> cases hcarry : state carry <;>
        simp [run, applyGate, writeRippleCell, controlledUmaBits,
          readRippleCell, upd, hta, htc, hac, hta', htc', hac', hct, hca, hcc,
          hc, ht, ha, hcarry]
    · by_cases hwc : wire = carry
      · subst wire
        cases hc : state control <;> cases ht : state target <;>
          cases ha : state addend <;> cases hcarry : state carry <;>
          simp [run, applyGate, writeRippleCell, controlledUmaBits,
            readRippleCell, upd, hta, htc, hac, hta', htc', hac', hct, hca, hcc,
            hc, ht, ha, hcarry]
      · simp [run, applyGate, writeRippleCell, controlledUmaBits,
          readRippleCell, upd, hwt, hwa, hwc]

private theorem run_controlledMajInvDirty_eq
    (control target addend carry dirty : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    run (controlledMajInvDirty control target addend carry dirty) state =
      writeRippleCell target addend carry
        (controlledMajInvBits (state control)
          (readRippleCell target addend carry state)) state := by
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryDirty⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledMajInvDirty, run_append,
    run_dirtyC3X control target addend carry dirty state hnd]
  funext wire
  by_cases hwt : wire = target
  · subst wire
    cases hc : state control <;> cases ht : state target <;>
      cases ha : state addend <;> cases hcarry : state carry <;>
      simp [run, applyGate, writeRippleCell, controlledMajInvBits,
        readRippleCell, upd, hta, htc, hac, hta', htc', hac', hct, hca, hcc,
        hc, ht, ha, hcarry]
  · by_cases hwa : wire = addend
    · subst wire
      cases hc : state control <;> cases ht : state target <;>
        cases ha : state addend <;> cases hcarry : state carry <;>
        simp [run, applyGate, writeRippleCell, controlledMajInvBits,
          readRippleCell, upd, hta, htc, hac, hta', htc', hac', hct, hca, hcc,
          hc, ht, ha, hcarry]
    · by_cases hwc : wire = carry
      · subst wire
        cases hc : state control <;> cases ht : state target <;>
          cases ha : state addend <;> cases hcarry : state carry <;>
          simp [run, applyGate, writeRippleCell, controlledMajInvBits,
            readRippleCell, upd, hta, htc, hac, hta', htc', hac', hct, hca, hcc,
            hc, ht, ha, hcarry]
      · simp [run, applyGate, writeRippleCell, controlledMajInvBits,
          readRippleCell, upd, hwt, hwa, hwc]

private theorem run_controlledUmaInvDirty_eq
    (control target addend carry dirty : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    run (controlledUmaInvDirty control target addend carry dirty) state =
      writeRippleCell target addend carry
        (controlledUmaInvBits (state control)
          (readRippleCell target addend carry state)) state := by
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryDirty⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledUmaInvDirty, run_append]
  let first := run
    [.CX carry target, .CX carry addend, .CCX control addend target] state
  have hfirst : first = writeRippleCell target addend carry
      { target := Bool.xor (Bool.xor (state target) (state carry))
          (state control && Bool.xor (state addend) (state carry))
        addend := Bool.xor (state addend) (state carry)
        carry := state carry } state := by
    funext wire
    by_cases hwt : wire = target
    · subst wire
      cases hc : state control <;> cases ht : state target <;>
        cases ha : state addend <;> cases hcarry : state carry <;>
        simp [first, run, applyGate, writeRippleCell, upd,
          hta, htc, hac, hta', htc', hac', hct, hca, hcc,
          hc, ht, ha, hcarry]
    · by_cases hwa : wire = addend
      · subst wire
        cases hc : state control <;> cases ht : state target <;>
          cases ha : state addend <;> cases hcarry : state carry <;>
          simp [first, run, applyGate, writeRippleCell, upd,
            hta, htc, hac, hta', htc', hac', hct, hca, hcc,
            hc, ht, ha, hcarry]
      · by_cases hwc : wire = carry
        · subst wire
          simp [first, run, applyGate, writeRippleCell, upd,
            hta, htc, hac, hta', htc', hac', hct, hca, hcc]
        · simp [first, run, applyGate, writeRippleCell, upd,
            hwt, hwa, hwc]
  rw [run_dirtyC3X control target addend carry dirty first hnd, hfirst]
  funext wire
  by_cases hwt : wire = target
  · subst wire
    cases hc : state control <;> cases ht : state target <;>
      cases ha : state addend <;> cases hcarry : state carry <;>
      simp [writeRippleCell, controlledUmaInvBits, readRippleCell, upd,
        hta, htc, hac, hta', htc', hac', hct, hca, hcc,
        hc, ht, ha, hcarry]
  · by_cases hwa : wire = addend
    · subst wire
      cases hc : state control <;> cases ht : state target <;>
        cases ha : state addend <;> cases hcarry : state carry <;>
        simp [writeRippleCell, controlledUmaInvBits, readRippleCell, upd,
          hta, htc, hac, hta', htc', hac', hct, hca, hcc,
          hc, ht, ha, hcarry]
    · by_cases hwc : wire = carry
      · subst wire
        cases hc : state control <;> cases ht : state target <;>
          cases ha : state addend <;> cases hcarry : state carry <;>
          simp [writeRippleCell, controlledUmaInvBits, readRippleCell, upd,
            hta, htc, hac, hta', htc', hac', hct, hca, hcc,
            hc, ht, ha, hcarry]
      · simp [writeRippleCell, controlledUmaInvBits, readRippleCell, upd,
          hwt, hwa, hwc]

/-- Direct basis-state contract for every exact ripple-cell constructor. -/
theorem run_controlledMajDirty
    (control target addend carry dirty : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    readRippleCell target addend carry
        (run (controlledMajDirty control target addend carry dirty) state) =
      controlledMajBits (state control)
        (readRippleCell target addend carry state) := by
  rw [run_controlledMajDirty_eq control target addend carry dirty state hnd]
  obtain ⟨_, _, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  simp [readRippleCell, writeRippleCell, upd, hta, htc, hac]

theorem run_controlledUmaDirty
    (control target addend carry dirty : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    readRippleCell target addend carry
        (run (controlledUmaDirty control target addend carry dirty) state) =
      controlledUmaBits (state control)
        (readRippleCell target addend carry state) := by
  rw [run_controlledUmaDirty_eq control target addend carry dirty state hnd]
  obtain ⟨_, _, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  simp [readRippleCell, writeRippleCell, upd, hta, htc, hac]

theorem run_controlledMajInvDirty
    (control target addend carry dirty : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    readRippleCell target addend carry
        (run (controlledMajInvDirty control target addend carry dirty) state) =
      controlledMajInvBits (state control)
        (readRippleCell target addend carry state) := by
  rw [run_controlledMajInvDirty_eq control target addend carry dirty state hnd]
  obtain ⟨_, _, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  simp [readRippleCell, writeRippleCell, upd, hta, htc, hac]

theorem run_controlledUmaInvDirty
    (control target addend carry dirty : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    readRippleCell target addend carry
        (run (controlledUmaInvDirty control target addend carry dirty) state) =
      controlledUmaInvBits (state control)
        (readRippleCell target addend carry state) := by
  rw [run_controlledUmaInvDirty_eq control target addend carry dirty state hnd]
  obtain ⟨_, _, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  simp [readRippleCell, writeRippleCell, upd, hta, htc, hac]

private theorem cell_usesOnly
    (cell : Wire → Wire → Wire → Wire → Wire → Circuit)
    (hcell : ∀ control target addend carry dirty,
      PaperCircuitUsesOnly [control, target, addend, carry, dirty]
        (cell control target addend carry dirty)) :
    ∀ control target addend carry dirty,
      PaperCircuitUsesOnly [control, target, addend, carry, dirty]
        (cell control target addend carry dirty) := hcell

theorem controlledMajDirty_usesOnly
    (control target addend carry dirty : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, dirty]
      (controlledMajDirty control target addend carry dirty) := by
  apply PaperCircuitUsesOnly.append
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
  · exact dirtyC3X_usesOnly control target addend carry dirty

theorem controlledUmaDirty_usesOnly
    (control target addend carry dirty : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, dirty]
      (controlledUmaDirty control target addend carry dirty) := by
  apply PaperCircuitUsesOnly.append
  · exact dirtyC3X_usesOnly control target addend carry dirty
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

theorem controlledMajInvDirty_usesOnly
    (control target addend carry dirty : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, dirty]
      (controlledMajInvDirty control target addend carry dirty) := by
  apply PaperCircuitUsesOnly.append
  · exact dirtyC3X_usesOnly control target addend carry dirty
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

theorem controlledUmaInvDirty_usesOnly
    (control target addend carry dirty : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, dirty]
      (controlledUmaInvDirty control target addend carry dirty) := by
  apply PaperCircuitUsesOnly.append
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
  · exact dirtyC3X_usesOnly control target addend carry dirty

theorem controlledMajDirty_wellFormed
    (control target addend carry dirty : Wire)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    CircuitWellFormed
      (controlledMajDirty control target addend carry dirty) := by
  obtain ⟨_, _, _, _, _, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  rw [controlledMajDirty, circuitWellFormed_append]
  exact ⟨by simp [CircuitWellFormed, Gate.WellFormed, htc', hac'],
    dirtyC3X_wellFormed control target addend carry dirty hnd⟩

theorem controlledUmaDirty_wellFormed
    (control target addend carry dirty : Wire)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    CircuitWellFormed
      (controlledUmaDirty control target addend carry dirty) := by
  obtain ⟨hct, hca, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledUmaDirty, circuitWellFormed_append]
  exact ⟨dirtyC3X_wellFormed control target addend carry dirty hnd,
    by simp [CircuitWellFormed, Gate.WellFormed,
      hct, hca, hta', htc', hac']⟩

theorem controlledMajInvDirty_wellFormed
    (control target addend carry dirty : Wire)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    CircuitWellFormed
      (controlledMajInvDirty control target addend carry dirty) := by
  obtain ⟨_, _, _, _, _, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  rw [controlledMajInvDirty, circuitWellFormed_append]
  exact ⟨dirtyC3X_wellFormed control target addend carry dirty hnd,
    by simp [CircuitWellFormed, Gate.WellFormed, htc', hac']⟩

theorem controlledUmaInvDirty_wellFormed
    (control target addend carry dirty : Wire)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    CircuitWellFormed
      (controlledUmaInvDirty control target addend carry dirty) := by
  obtain ⟨hct, hca, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledUmaInvDirty, circuitWellFormed_append]
  exact ⟨by simp [CircuitWellFormed, Gate.WellFormed,
      hct, hca, hta', htc', hac'],
    dirtyC3X_wellFormed control target addend carry dirty hnd⟩

@[simp] theorem controlledMajDirty_HPFree
    (control target addend carry dirty : Wire) :
    HPFree (controlledMajDirty control target addend carry dirty) := by
  simp [controlledMajDirty]

@[simp] theorem controlledUmaDirty_HPFree
    (control target addend carry dirty : Wire) :
    HPFree (controlledUmaDirty control target addend carry dirty) := by
  simp [controlledUmaDirty]

@[simp] theorem controlledMajInvDirty_HPFree
    (control target addend carry dirty : Wire) :
    HPFree (controlledMajInvDirty control target addend carry dirty) := by
  simp [controlledMajInvDirty]

@[simp] theorem controlledUmaInvDirty_HPFree
    (control target addend carry dirty : Wire) :
    HPFree (controlledUmaInvDirty control target addend carry dirty) := by
  simp [controlledUmaInvDirty]

@[simp] theorem controlledMajDirty_toffoliCount
    (control target addend carry dirty : Wire) :
    eeaToffoliCount (controlledMajDirty control target addend carry dirty) = 4 := by
  rfl

@[simp] theorem controlledUmaDirty_toffoliCount
    (control target addend carry dirty : Wire) :
    eeaToffoliCount (controlledUmaDirty control target addend carry dirty) = 5 := by
  rfl

@[simp] theorem controlledMajInvDirty_toffoliCount
    (control target addend carry dirty : Wire) :
    eeaToffoliCount (controlledMajInvDirty control target addend carry dirty) = 4 := by
  rfl

@[simp] theorem controlledUmaInvDirty_toffoliCount
    (control target addend carry dirty : Wire) :
    eeaToffoliCount (controlledUmaInvDirty control target addend carry dirty) = 5 := by
  rfl

@[simp] theorem controlledMajDirty_cnotCount
    (control target addend carry dirty : Wire) :
    eeaCnotCount (controlledMajDirty control target addend carry dirty) = 2 := by
  rfl

@[simp] theorem controlledUmaDirty_cnotCount
    (control target addend carry dirty : Wire) :
    eeaCnotCount (controlledUmaDirty control target addend carry dirty) = 2 := by
  rfl

@[simp] theorem controlledMajInvDirty_cnotCount
    (control target addend carry dirty : Wire) :
    eeaCnotCount (controlledMajInvDirty control target addend carry dirty) = 2 := by
  rfl

@[simp] theorem controlledUmaInvDirty_cnotCount
    (control target addend carry dirty : Wire) :
    eeaCnotCount (controlledUmaInvDirty control target addend carry dirty) = 2 := by
  rfl

@[simp] theorem controlledMajDirty_tCount
    (control target addend carry dirty : Wire) :
    ShorECDLP.tCount (controlledMajDirty control target addend carry dirty) = 28 := by
  rfl

@[simp] theorem controlledUmaDirty_tCount
    (control target addend carry dirty : Wire) :
    ShorECDLP.tCount (controlledUmaDirty control target addend carry dirty) = 35 := by
  rfl

@[simp] theorem controlledMajInvDirty_tCount
    (control target addend carry dirty : Wire) :
    ShorECDLP.tCount (controlledMajInvDirty control target addend carry dirty) = 28 := by
  rfl

@[simp] theorem controlledUmaInvDirty_tCount
    (control target addend carry dirty : Wire) :
    ShorECDLP.tCount (controlledUmaInvDirty control target addend carry dirty) = 35 := by
  rfl

/-! ## Exact two-pass window ripple -/

inductive RippleMode where
  | add
  | sub
deriving DecidableEq, Repr

def rippleFirstCell (mode : RippleMode)
    (control target addend carry dirty : Wire) : Circuit :=
  match mode with
  | .add => controlledMajDirty control target addend carry dirty
  | .sub => controlledUmaInvDirty control target addend carry dirty

def rippleSecondCell (mode : RippleMode)
    (control target addend carry dirty : Wire) : Circuit :=
  match mode with
  | .add => controlledUmaDirty control target addend carry dirty
  | .sub => controlledMajInvDirty control target addend carry dirty

def rippleFirstBits (mode : RippleMode)
    (control : Bool) (bits : RippleCellBits) : RippleCellBits :=
  match mode with
  | .add => controlledMajBits control bits
  | .sub => controlledUmaInvBits control bits

def rippleSecondBits (mode : RippleMode)
    (control : Bool) (bits : RippleCellBits) : RippleCellBits :=
  match mode with
  | .add => controlledUmaBits control bits
  | .sub => controlledMajInvBits control bits

/-- First Figure-11 pass.  `targets` and `addends` are ordered from the high physical lane to
the low one, so this recursion emits the gates from the list's end back to its head. -/
def rippleFirstPass (mode : RippleMode) (control : Wire) :
    List Wire → List Wire → Wire → Wire → Circuit
  | target :: targets, addend :: addends, carry, dirty =>
      rippleFirstPass mode control targets addends carry dirty ++
        rippleFirstCell mode control target addend carry dirty
  | _, _, _, _ => []

/-- Second Figure-11 pass, emitted from the high physical lane to the low one. -/
def rippleSecondPass (mode : RippleMode) (control : Wire) :
    List Wire → List Wire → Wire → Wire → Circuit
  | target :: targets, addend :: addends, carry, dirty =>
      rippleSecondCell mode control target addend carry dirty ++
        rippleSecondPass mode control targets addends carry dirty
  | _, _, _, _ => []

/-- The literal two-pass ripple core used by both interval and prefix arithmetic after the caller
has prepared the location control for this physical slice.  Endpoint/unary control preparation is
a separate composition layer. -/
def controlledWindowRipple (mode : RippleMode) (control : Wire)
    (targets addends : List Wire) (carry dirty : Wire) : Circuit :=
  rippleFirstPass mode control targets addends carry dirty ++
    rippleSecondPass mode control targets addends carry dirty

/-- Pure Boolean execution of the high-to-low first pass. -/
def rippleFirstState (mode : RippleMode) (control : Wire) :
    List Wire → List Wire → Wire → BasisState → BasisState
  | target :: targets, addend :: addends, carry, state =>
      let middle := rippleFirstState mode control targets addends carry state
      writeRippleCell target addend carry
        (rippleFirstBits mode (middle control)
          (readRippleCell target addend carry middle)) middle
  | _, _, _, state => state

/-- Pure Boolean execution of the high-to-low second pass. -/
def rippleSecondState (mode : RippleMode) (control : Wire) :
    List Wire → List Wire → Wire → BasisState → BasisState
  | target :: targets, addend :: addends, carry, state =>
      let middle := writeRippleCell target addend carry
        (rippleSecondBits mode (state control)
          (readRippleCell target addend carry state)) state
      rippleSecondState mode control targets addends carry middle
  | _, _, _, state => state

/-- Gate-independent Boolean specification of the complete two-pass ripple. -/
def controlledWindowRippleState (mode : RippleMode) (control : Wire)
    (targets addends : List Wire) (carry : Wire) (state : BasisState) : BasisState :=
  rippleSecondState mode control targets addends carry
    (rippleFirstState mode control targets addends carry state)

/-- Each aligned lane has the five distinct roles required by the dirty C3X decomposition. -/
def RippleLaneLayouts (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) : Prop :=
  List.Forall₂
    (fun target addend => [control, target, addend, carry, dirty].Nodup)
    targets addends

private theorem run_rippleFirstCell
    (mode : RippleMode) (control target addend carry dirty : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    run (rippleFirstCell mode control target addend carry dirty) state =
      writeRippleCell target addend carry
        (rippleFirstBits mode (state control)
          (readRippleCell target addend carry state)) state := by
  cases mode with
  | add => simpa [rippleFirstCell, rippleFirstBits] using
      run_controlledMajDirty_eq control target addend carry dirty state hnd
  | sub => simpa [rippleFirstCell, rippleFirstBits] using
      run_controlledUmaInvDirty_eq control target addend carry dirty state hnd

private theorem run_rippleSecondCell
    (mode : RippleMode) (control target addend carry dirty : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup) :
    run (rippleSecondCell mode control target addend carry dirty) state =
      writeRippleCell target addend carry
        (rippleSecondBits mode (state control)
          (readRippleCell target addend carry state)) state := by
  cases mode with
  | add => simpa [rippleSecondCell, rippleSecondBits] using
      run_controlledUmaDirty_eq control target addend carry dirty state hnd
  | sub => simpa [rippleSecondCell, rippleSecondBits] using
      run_controlledMajInvDirty_eq control target addend carry dirty state hnd

private theorem run_rippleFirstPass
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    run (rippleFirstPass mode control targets addends carry dirty) state =
      rippleFirstState mode control targets addends carry state := by
  induction targets generalizing addends state with
  | nil =>
      cases addends with
      | nil => rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleFirstPass, run_append, ih addends _ htail]
              exact run_rippleFirstCell mode control target addend carry dirty _ hhead

private theorem run_rippleSecondPass
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    run (rippleSecondPass mode control targets addends carry dirty) state =
      rippleSecondState mode control targets addends carry state := by
  induction targets generalizing addends state with
  | nil =>
      cases addends with
      | nil => rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleSecondPass, run_append,
                run_rippleSecondCell mode control target addend carry dirty state hhead,
                ih addends _ htail]
              rfl

/-- Direct whole-basis-state semantics of the literal two-pass window ripple. -/
theorem run_controlledWindowRipple
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    run (controlledWindowRipple mode control targets addends carry dirty) state =
      controlledWindowRippleState mode control targets addends carry state := by
  rw [controlledWindowRipple, run_append,
    run_rippleFirstPass mode control targets addends carry dirty state hlayouts,
    run_rippleSecondPass mode control targets addends carry dirty _ hlayouts]
  rfl

private theorem rippleFirstPass_HPFree
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) :
    HPFree (rippleFirstPass mode control targets addends carry dirty) := by
  induction targets generalizing addends with
  | nil => cases addends <;> simp [rippleFirstPass]
  | cons target targets ih =>
      cases addends with
      | nil => simp [rippleFirstPass]
      | cons addend addends =>
          cases mode <;> simp [rippleFirstPass, rippleFirstCell, ih]

private theorem rippleSecondPass_HPFree
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) :
    HPFree (rippleSecondPass mode control targets addends carry dirty) := by
  induction targets generalizing addends with
  | nil => cases addends <;> simp [rippleSecondPass]
  | cons target targets ih =>
      cases addends with
      | nil => simp [rippleSecondPass]
      | cons addend addends =>
          cases mode <;> simp [rippleSecondPass, rippleSecondCell, ih]

@[simp]
theorem controlledWindowRipple_HPFree
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) :
    HPFree (controlledWindowRipple mode control targets addends carry dirty) := by
  simp [controlledWindowRipple, rippleFirstPass_HPFree,
    rippleSecondPass_HPFree]

private theorem rippleFirstPass_wellFormed
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    CircuitWellFormed
      (rippleFirstPass mode control targets addends carry dirty) := by
  induction targets generalizing addends with
  | nil =>
      cases addends with
      | nil => simp [rippleFirstPass, CircuitWellFormed]
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleFirstPass, circuitWellFormed_append]
              constructor
              · exact ih addends htail
              · cases mode with
                | add =>
                    change CircuitWellFormed
                      (controlledMajDirty control target addend carry dirty)
                    exact controlledMajDirty_wellFormed
                      control target addend carry dirty hhead
                | sub =>
                    change CircuitWellFormed
                      (controlledUmaInvDirty control target addend carry dirty)
                    exact controlledUmaInvDirty_wellFormed
                      control target addend carry dirty hhead

private theorem rippleSecondPass_wellFormed
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    CircuitWellFormed
      (rippleSecondPass mode control targets addends carry dirty) := by
  induction targets generalizing addends with
  | nil =>
      cases addends with
      | nil => simp [rippleSecondPass, CircuitWellFormed]
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleSecondPass, circuitWellFormed_append]
              constructor
              · cases mode with
                | add =>
                    change CircuitWellFormed
                      (controlledUmaDirty control target addend carry dirty)
                    exact controlledUmaDirty_wellFormed
                      control target addend carry dirty hhead
                | sub =>
                    change CircuitWellFormed
                      (controlledMajInvDirty control target addend carry dirty)
                    exact controlledMajInvDirty_wellFormed
                      control target addend carry dirty hhead
              · exact ih addends htail

theorem controlledWindowRipple_wellFormed
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    CircuitWellFormed
      (controlledWindowRipple mode control targets addends carry dirty) := by
  rw [controlledWindowRipple, circuitWellFormed_append]
  exact ⟨rippleFirstPass_wellFormed mode control targets addends carry dirty hlayouts,
    rippleSecondPass_wellFormed mode control targets addends carry dirty hlayouts⟩

/-- Complete named support of a two-pass ripple block. -/
def controlledWindowRippleSupport (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) : List Wire :=
  control :: targets ++ addends ++ [carry, dirty]

private theorem rippleFirstPass_usesOnly
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) :
    PaperCircuitUsesOnly
      (controlledWindowRippleSupport control targets addends carry dirty)
      (rippleFirstPass mode control targets addends carry dirty) := by
  induction targets generalizing addends with
  | nil => cases addends <;> simp [rippleFirstPass, PaperCircuitUsesOnly]
  | cons target targets ih =>
      cases addends with
      | nil => simp [rippleFirstPass, PaperCircuitUsesOnly]
      | cons addend addends =>
          rw [rippleFirstPass]
          apply PaperCircuitUsesOnly.append
          · apply (ih addends).mono
            intro wire hwire
            simp only [controlledWindowRippleSupport, List.mem_cons,
              List.mem_append] at hwire ⊢
            aesop
          · cases mode with
            | add =>
                apply (controlledMajDirty_usesOnly
                  control target addend carry dirty).mono
                intro wire hwire
                simp only [controlledWindowRippleSupport, List.mem_cons,
                  List.mem_append] at hwire ⊢
                aesop
            | sub =>
                apply (controlledUmaInvDirty_usesOnly
                  control target addend carry dirty).mono
                intro wire hwire
                simp only [controlledWindowRippleSupport, List.mem_cons,
                  List.mem_append] at hwire ⊢
                aesop

private theorem rippleSecondPass_usesOnly
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) :
    PaperCircuitUsesOnly
      (controlledWindowRippleSupport control targets addends carry dirty)
      (rippleSecondPass mode control targets addends carry dirty) := by
  induction targets generalizing addends with
  | nil => cases addends <;> simp [rippleSecondPass, PaperCircuitUsesOnly]
  | cons target targets ih =>
      cases addends with
      | nil => simp [rippleSecondPass, PaperCircuitUsesOnly]
      | cons addend addends =>
          rw [rippleSecondPass]
          apply PaperCircuitUsesOnly.append
          · cases mode with
            | add =>
                apply (controlledUmaDirty_usesOnly
                  control target addend carry dirty).mono
                intro wire hwire
                simp only [controlledWindowRippleSupport, List.mem_cons,
                  List.mem_append] at hwire ⊢
                aesop
            | sub =>
                apply (controlledMajInvDirty_usesOnly
                  control target addend carry dirty).mono
                intro wire hwire
                simp only [controlledWindowRippleSupport, List.mem_cons,
                  List.mem_append] at hwire ⊢
                aesop
          · apply (ih addends).mono
            intro wire hwire
            simp only [controlledWindowRippleSupport, List.mem_cons,
              List.mem_append] at hwire ⊢
            aesop

/-- The exact two-pass circuit stays inside its declared control, data, carry, and borrowed
dirty-wire footprint. -/
theorem controlledWindowRipple_usesOnly
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) :
    PaperCircuitUsesOnly
      (controlledWindowRippleSupport control targets addends carry dirty)
      (controlledWindowRipple mode control targets addends carry dirty) := by
  apply PaperCircuitUsesOnly.append
  · exact rippleFirstPass_usesOnly mode control targets addends carry dirty
  · exact rippleSecondPass_usesOnly mode control targets addends carry dirty

/-- Every wire outside the named ripple footprint is unchanged. -/
theorem controlledWindowRipple_preservesOutside
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire) (state : BasisState) (wire : Wire)
    (hwire : wire ∉
      controlledWindowRippleSupport control targets addends carry dirty) :
    run (controlledWindowRipple mode control targets addends carry dirty) state wire =
      state wire :=
  PaperCircuitUsesOnly.preservesOutside
    (controlledWindowRipple_usesOnly mode control targets addends carry dirty)
    state hwire

private theorem run_rippleFirstCell_protected
    (mode : RippleMode) (control target addend carry dirty wire : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup)
    (hprotected : wire = control ∨ wire = dirty) :
    run (rippleFirstCell mode control target addend carry dirty) state wire =
      state wire := by
  rw [run_rippleFirstCell mode control target addend carry dirty state hnd]
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryDirty⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  rcases hprotected with rfl | rfl
  · simp only [writeRippleCell]
    rw [upd_other _ carry _ hcc, upd_other _ addend _ hca,
      upd_other _ target _ hct]
  · simp only [writeRippleCell]
    rw [upd_other _ carry _ (Ne.symm hcarryDirty),
      upd_other _ addend _ (Ne.symm had),
      upd_other _ target _ (Ne.symm htd)]

private theorem run_rippleSecondCell_protected
    (mode : RippleMode) (control target addend carry dirty wire : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, dirty].Nodup)
    (hprotected : wire = control ∨ wire = dirty) :
    run (rippleSecondCell mode control target addend carry dirty) state wire =
      state wire := by
  rw [run_rippleSecondCell mode control target addend carry dirty state hnd]
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryDirty⟩ :=
    cell_nodup_parts control target addend carry dirty hnd
  rcases hprotected with rfl | rfl
  · simp only [writeRippleCell]
    rw [upd_other _ carry _ hcc, upd_other _ addend _ hca,
      upd_other _ target _ hct]
  · simp only [writeRippleCell]
    rw [upd_other _ carry _ (Ne.symm hcarryDirty),
      upd_other _ addend _ (Ne.symm had),
      upd_other _ target _ (Ne.symm htd)]

private theorem run_rippleFirstPass_protected
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty wire : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty)
    (hprotected : wire = control ∨ wire = dirty) :
    run (rippleFirstPass mode control targets addends carry dirty) state wire =
      state wire := by
  induction targets generalizing addends state with
  | nil =>
      cases addends with
      | nil => rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleFirstPass, run_append,
                run_rippleFirstCell_protected mode control target addend carry dirty
                  wire _ hhead hprotected,
                ih addends state htail]

private theorem run_rippleSecondPass_protected
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty wire : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty)
    (hprotected : wire = control ∨ wire = dirty) :
    run (rippleSecondPass mode control targets addends carry dirty) state wire =
      state wire := by
  induction targets generalizing addends state with
  | nil =>
      cases addends with
      | nil => rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleSecondPass, run_append,
                ih addends _ htail,
                run_rippleSecondCell_protected mode control target addend carry dirty
                  wire state hhead hprotected]

/-- The location control and the borrowed dirty wire are restored exactly. -/
theorem controlledWindowRipple_protected
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty wire : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty)
    (hprotected : wire = control ∨ wire = dirty) :
    run (controlledWindowRipple mode control targets addends carry dirty) state wire =
      state wire := by
  rw [controlledWindowRipple, run_append,
    run_rippleSecondPass_protected mode control targets addends carry dirty wire _
      hlayouts hprotected,
    run_rippleFirstPass_protected mode control targets addends carry dirty wire state
      hlayouts hprotected]

private theorem rippleFirstPass_toffoliCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    eeaToffoliCount (rippleFirstPass mode control targets addends carry dirty) =
      match mode with
      | .add => 4 * targets.length
      | .sub => 5 * targets.length := by
  induction targets generalizing addends with
  | nil =>
      cases addends with
      | nil => cases mode <;> rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleFirstPass, eeaToffoliCount_append,
                ih addends htail]
              cases mode <;> simp [rippleFirstCell] <;> omega

private theorem rippleSecondPass_toffoliCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    eeaToffoliCount (rippleSecondPass mode control targets addends carry dirty) =
      match mode with
      | .add => 5 * targets.length
      | .sub => 4 * targets.length := by
  induction targets generalizing addends with
  | nil =>
      cases addends with
      | nil => cases mode <;> rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleSecondPass, eeaToffoliCount_append,
                ih addends htail]
              cases mode <;> simp [rippleSecondCell] <;> omega

/-- Nine Toffolis per physical lane: four for C3X in one pass and five in the other. -/
theorem controlledWindowRipple_toffoliCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    eeaToffoliCount
        (controlledWindowRipple mode control targets addends carry dirty) =
      9 * targets.length := by
  rw [controlledWindowRipple, eeaToffoliCount_append,
    rippleFirstPass_toffoliCount mode control targets addends carry dirty hlayouts,
    rippleSecondPass_toffoliCount mode control targets addends carry dirty hlayouts]
  cases mode <;> simp [← Nat.add_mul]

private theorem rippleFirstPass_cnotCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    eeaCnotCount (rippleFirstPass mode control targets addends carry dirty) =
      2 * targets.length := by
  induction targets generalizing addends with
  | nil =>
      cases addends with
      | nil => rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleFirstPass, eeaCnotCount_append,
                ih addends htail]
              cases mode <;> simp [rippleFirstCell] <;> omega

private theorem rippleSecondPass_cnotCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    eeaCnotCount (rippleSecondPass mode control targets addends carry dirty) =
      2 * targets.length := by
  induction targets generalizing addends with
  | nil =>
      cases addends with
      | nil => rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleSecondPass, eeaCnotCount_append,
                ih addends htail]
              cases mode <;> simp [rippleSecondCell] <;> omega

theorem controlledWindowRipple_cnotCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    eeaCnotCount
        (controlledWindowRipple mode control targets addends carry dirty) =
      4 * targets.length := by
  rw [controlledWindowRipple, eeaCnotCount_append,
    rippleFirstPass_cnotCount mode control targets addends carry dirty hlayouts,
    rippleSecondPass_cnotCount mode control targets addends carry dirty hlayouts]
  omega

private theorem rippleFirstPass_tCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    ShorECDLP.tCount (rippleFirstPass mode control targets addends carry dirty) =
      match mode with
      | .add => 28 * targets.length
      | .sub => 35 * targets.length := by
  induction targets generalizing addends with
  | nil =>
      cases addends with
      | nil => cases mode <;> rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleFirstPass, tCount_append, ih addends htail]
              cases mode <;> simp [rippleFirstCell] <;> omega

private theorem rippleSecondPass_tCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    ShorECDLP.tCount (rippleSecondPass mode control targets addends carry dirty) =
      match mode with
      | .add => 35 * targets.length
      | .sub => 28 * targets.length := by
  induction targets generalizing addends with
  | nil =>
      cases addends with
      | nil => cases mode <;> rfl
      | cons addend addends => cases hlayouts
  | cons target targets ih =>
      cases addends with
      | nil => cases hlayouts
      | cons addend addends =>
          cases hlayouts with
          | cons hhead htail =>
              rw [rippleSecondPass, tCount_append, ih addends htail]
              cases mode <;> simp [rippleSecondCell] <;> omega

/-- Constructor-derived 63-T cost per active physical lane. -/
theorem controlledWindowRipple_tCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry dirty : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry dirty) :
    ShorECDLP.tCount
        (controlledWindowRipple mode control targets addends carry dirty) =
      63 * targets.length := by
  rw [controlledWindowRipple, tCount_append,
    rippleFirstPass_tCount mode control targets addends carry dirty hlayouts,
    rippleSecondPass_tCount mode control targets addends carry dirty hlayouts]
  cases mode <;> simp [← Nat.add_mul]

end ShorECDLP.Paper2607_13816
