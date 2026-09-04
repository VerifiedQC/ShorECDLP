import ShorECDLP.Submission.«2607_13816».EEA.UnaryIteration

/-!
# Clean-v-chain controlled ripple cells

This file formalizes the four location-controlled Cuccaro cells used by the pinned
arXiv:2607.13816v2 supplement.  The unconditional CNOT skeleton is intentional: on a lane
outside the selected interval it cancels between the two passes, while the carry update is
controlled by the unary range accumulator.  A single clean scratch wire realizes each
three-controlled X using the pinned supplement's coherent `mcx_vchain` specialization
(`MEASUREMENT_UNCOMPUTE = False`) and is restored exactly.  The adaptive generator mode replaces
the final coherent cleanup Toffoli with measurement and feed-forward correction.
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

/-- Location-controlled MAJ with the supplement's coherent one-clean-wire C3X. -/
def controlledMaj
    (control target addend carry scratch : Wire) : Circuit :=
  [.CX carry target, .CX carry addend] ++
    cleanC3X control target addend carry scratch

/-- Location-controlled UMA with the supplement's coherent one-clean-wire C3X. -/
def controlledUma
    (control target addend carry scratch : Wire) : Circuit :=
  cleanC3X control target addend carry scratch ++
    [.CCX control addend target, .CX carry addend, .CX carry target]

/-- Exact inverse of `controlledMaj`. -/
def controlledMajInv
    (control target addend carry scratch : Wire) : Circuit :=
  cleanC3X control target addend carry scratch ++
    [.CX carry addend, .CX carry target]

/-- Exact inverse of `controlledUma`. -/
def controlledUmaInv
    (control target addend carry scratch : Wire) : Circuit :=
  [.CX carry target, .CX carry addend, .CCX control addend target] ++
    cleanC3X control target addend carry scratch

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
    (control target addend carry scratch : Wire)
    (hnd : [control, target, addend, carry, scratch].Nodup) :
    control ≠ target ∧ control ≠ addend ∧ control ≠ carry ∧ control ≠ scratch ∧
      target ≠ addend ∧ target ≠ carry ∧ target ≠ scratch ∧
      addend ≠ carry ∧ addend ≠ scratch ∧ carry ≠ scratch := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  rcases hnd with
    ⟨⟨hct, hca, hcc, hcd⟩,
      ⟨⟨hta, htc, htd⟩,
        ⟨⟨hac, had⟩, ⟨hcarryScratch, _⟩⟩⟩⟩
  exact ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryScratch⟩

private theorem writeRippleCell_preservesScratch
    (control target addend carry scratch : Wire)
    (bits : RippleCellBits) (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup) :
    writeRippleCell target addend carry bits state scratch = state scratch := by
  obtain ⟨_, _, _, _, _, _, htargetScratch, _, haddendScratch,
    hcarryScratch⟩ := cell_nodup_parts control target addend carry scratch hnd
  simp [writeRippleCell, upd, Ne.symm htargetScratch,
    Ne.symm haddendScratch, Ne.symm hcarryScratch]

/-- Whole-state MAJ semantics, including restoration of the clean scratch wire. -/
theorem run_controlledMaj_state
    (control target addend carry scratch : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    run (controlledMaj control target addend carry scratch) state =
      writeRippleCell target addend carry
        (controlledMajBits (state control)
          (readRippleCell target addend carry state)) state := by
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryScratch⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledMaj, run_append]
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
  have hndFirst : [control, target, addend, carry, scratch].Nodup := hnd
  have hcleanFirst : first scratch = false := by
    rw [hfirst]
    simp [upd, Ne.symm htd, Ne.symm had, hclean]
  rw [run_cleanC3X control target addend carry scratch first hndFirst hcleanFirst,
    hfirst]
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

/-- Whole-state UMA semantics, including restoration of the clean scratch wire. -/
theorem run_controlledUma_state
    (control target addend carry scratch : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    run (controlledUma control target addend carry scratch) state =
      writeRippleCell target addend carry
        (controlledUmaBits (state control)
          (readRippleCell target addend carry state)) state := by
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryScratch⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledUma, run_append,
    run_cleanC3X control target addend carry scratch state hnd hclean]
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

/-- Whole-state inverse-MAJ semantics, including restoration of the clean scratch wire. -/
theorem run_controlledMajInv_state
    (control target addend carry scratch : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    run (controlledMajInv control target addend carry scratch) state =
      writeRippleCell target addend carry
        (controlledMajInvBits (state control)
          (readRippleCell target addend carry state)) state := by
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryScratch⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledMajInv, run_append,
    run_cleanC3X control target addend carry scratch state hnd hclean]
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

/-- Whole-state inverse-UMA semantics, including restoration of the clean scratch wire. -/
theorem run_controlledUmaInv_state
    (control target addend carry scratch : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    run (controlledUmaInv control target addend carry scratch) state =
      writeRippleCell target addend carry
        (controlledUmaInvBits (state control)
          (readRippleCell target addend carry state)) state := by
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryScratch⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledUmaInv, run_append]
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
  have hcleanFirst : first scratch = false := by
    rw [hfirst]
    simp [writeRippleCell, upd, Ne.symm htd, Ne.symm had,
      Ne.symm hcarryScratch, hclean]
  rw [run_cleanC3X control target addend carry scratch first hnd hcleanFirst,
    hfirst]
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
theorem run_controlledMaj
    (control target addend carry scratch : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    readRippleCell target addend carry
        (run (controlledMaj control target addend carry scratch) state) =
      controlledMajBits (state control)
        (readRippleCell target addend carry state) := by
  rw [run_controlledMaj_state control target addend carry scratch state hnd hclean]
  obtain ⟨_, _, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  simp [readRippleCell, writeRippleCell, upd, hta, htc, hac]

theorem run_controlledUma
    (control target addend carry scratch : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    readRippleCell target addend carry
        (run (controlledUma control target addend carry scratch) state) =
      controlledUmaBits (state control)
        (readRippleCell target addend carry state) := by
  rw [run_controlledUma_state control target addend carry scratch state hnd hclean]
  obtain ⟨_, _, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  simp [readRippleCell, writeRippleCell, upd, hta, htc, hac]

theorem run_controlledMajInv
    (control target addend carry scratch : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    readRippleCell target addend carry
        (run (controlledMajInv control target addend carry scratch) state) =
      controlledMajInvBits (state control)
        (readRippleCell target addend carry state) := by
  rw [run_controlledMajInv_state control target addend carry scratch state hnd hclean]
  obtain ⟨_, _, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  simp [readRippleCell, writeRippleCell, upd, hta, htc, hac]

theorem run_controlledUmaInv
    (control target addend carry scratch : Wire) (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    readRippleCell target addend carry
        (run (controlledUmaInv control target addend carry scratch) state) =
      controlledUmaInvBits (state control)
        (readRippleCell target addend carry state) := by
  rw [run_controlledUmaInv_state control target addend carry scratch state hnd hclean]
  obtain ⟨_, _, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  simp [readRippleCell, writeRippleCell, upd, hta, htc, hac]

private theorem cell_usesOnly
    (cell : Wire → Wire → Wire → Wire → Wire → Circuit)
    (hcell : ∀ control target addend carry scratch,
      PaperCircuitUsesOnly [control, target, addend, carry, scratch]
        (cell control target addend carry scratch)) :
    ∀ control target addend carry scratch,
      PaperCircuitUsesOnly [control, target, addend, carry, scratch]
        (cell control target addend carry scratch) := hcell

theorem controlledMaj_usesOnly
    (control target addend carry scratch : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, scratch]
      (controlledMaj control target addend carry scratch) := by
  apply PaperCircuitUsesOnly.append
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
  · exact cleanC3X_usesOnly control target addend carry scratch

theorem controlledUma_usesOnly
    (control target addend carry scratch : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, scratch]
      (controlledUma control target addend carry scratch) := by
  apply PaperCircuitUsesOnly.append
  · exact cleanC3X_usesOnly control target addend carry scratch
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

theorem controlledMajInv_usesOnly
    (control target addend carry scratch : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, scratch]
      (controlledMajInv control target addend carry scratch) := by
  apply PaperCircuitUsesOnly.append
  · exact cleanC3X_usesOnly control target addend carry scratch
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

theorem controlledUmaInv_usesOnly
    (control target addend carry scratch : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, scratch]
      (controlledUmaInv control target addend carry scratch) := by
  apply PaperCircuitUsesOnly.append
  · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
  · exact cleanC3X_usesOnly control target addend carry scratch

theorem controlledMaj_wellFormed
    (control target addend carry scratch : Wire)
    (hnd : [control, target, addend, carry, scratch].Nodup) :
    CircuitWellFormed
      (controlledMaj control target addend carry scratch) := by
  obtain ⟨_, _, _, _, _, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  rw [controlledMaj, circuitWellFormed_append]
  exact ⟨by simp [CircuitWellFormed, Gate.WellFormed, htc', hac'],
    cleanC3X_wellFormed control target addend carry scratch hnd⟩

theorem controlledUma_wellFormed
    (control target addend carry scratch : Wire)
    (hnd : [control, target, addend, carry, scratch].Nodup) :
    CircuitWellFormed
      (controlledUma control target addend carry scratch) := by
  obtain ⟨hct, hca, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledUma, circuitWellFormed_append]
  exact ⟨cleanC3X_wellFormed control target addend carry scratch hnd,
    by simp [CircuitWellFormed, Gate.WellFormed,
      hct, hca, hta', htc', hac']⟩

theorem controlledMajInv_wellFormed
    (control target addend carry scratch : Wire)
    (hnd : [control, target, addend, carry, scratch].Nodup) :
    CircuitWellFormed
      (controlledMajInv control target addend carry scratch) := by
  obtain ⟨_, _, _, _, _, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  rw [controlledMajInv, circuitWellFormed_append]
  exact ⟨cleanC3X_wellFormed control target addend carry scratch hnd,
    by simp [CircuitWellFormed, Gate.WellFormed, htc', hac']⟩

theorem controlledUmaInv_wellFormed
    (control target addend carry scratch : Wire)
    (hnd : [control, target, addend, carry, scratch].Nodup) :
    CircuitWellFormed
      (controlledUmaInv control target addend carry scratch) := by
  obtain ⟨hct, hca, _, _, hta, htc, _, hac, _, _⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  have htc' : carry ≠ target := Ne.symm htc
  have hac' : carry ≠ addend := Ne.symm hac
  have hta' : addend ≠ target := Ne.symm hta
  rw [controlledUmaInv, circuitWellFormed_append]
  exact ⟨by simp [CircuitWellFormed, Gate.WellFormed,
      hct, hca, hta', htc', hac'],
    cleanC3X_wellFormed control target addend carry scratch hnd⟩

@[simp] theorem controlledMaj_HPFree
    (control target addend carry scratch : Wire) :
    HPFree (controlledMaj control target addend carry scratch) := by
  simp [controlledMaj]

@[simp] theorem controlledUma_HPFree
    (control target addend carry scratch : Wire) :
    HPFree (controlledUma control target addend carry scratch) := by
  simp [controlledUma]

@[simp] theorem controlledMajInv_HPFree
    (control target addend carry scratch : Wire) :
    HPFree (controlledMajInv control target addend carry scratch) := by
  simp [controlledMajInv]

@[simp] theorem controlledUmaInv_HPFree
    (control target addend carry scratch : Wire) :
    HPFree (controlledUmaInv control target addend carry scratch) := by
  simp [controlledUmaInv]

@[simp] theorem controlledMaj_toffoliCount
    (control target addend carry scratch : Wire) :
    eeaToffoliCount (controlledMaj control target addend carry scratch) = 3 := by
  rfl

@[simp] theorem controlledUma_toffoliCount
    (control target addend carry scratch : Wire) :
    eeaToffoliCount (controlledUma control target addend carry scratch) = 4 := by
  rfl

@[simp] theorem controlledMajInv_toffoliCount
    (control target addend carry scratch : Wire) :
    eeaToffoliCount (controlledMajInv control target addend carry scratch) = 3 := by
  rfl

@[simp] theorem controlledUmaInv_toffoliCount
    (control target addend carry scratch : Wire) :
    eeaToffoliCount (controlledUmaInv control target addend carry scratch) = 4 := by
  rfl

@[simp] theorem controlledMaj_cnotCount
    (control target addend carry scratch : Wire) :
    eeaCnotCount (controlledMaj control target addend carry scratch) = 2 := by
  rfl

@[simp] theorem controlledUma_cnotCount
    (control target addend carry scratch : Wire) :
    eeaCnotCount (controlledUma control target addend carry scratch) = 2 := by
  rfl

@[simp] theorem controlledMajInv_cnotCount
    (control target addend carry scratch : Wire) :
    eeaCnotCount (controlledMajInv control target addend carry scratch) = 2 := by
  rfl

@[simp] theorem controlledUmaInv_cnotCount
    (control target addend carry scratch : Wire) :
    eeaCnotCount (controlledUmaInv control target addend carry scratch) = 2 := by
  rfl

@[simp] theorem controlledMaj_tCount
    (control target addend carry scratch : Wire) :
    ShorECDLP.tCount (controlledMaj control target addend carry scratch) = 21 := by
  rfl

@[simp] theorem controlledUma_tCount
    (control target addend carry scratch : Wire) :
    ShorECDLP.tCount (controlledUma control target addend carry scratch) = 28 := by
  rfl

@[simp] theorem controlledMajInv_tCount
    (control target addend carry scratch : Wire) :
    ShorECDLP.tCount (controlledMajInv control target addend carry scratch) = 21 := by
  rfl

@[simp] theorem controlledUmaInv_tCount
    (control target addend carry scratch : Wire) :
    ShorECDLP.tCount (controlledUmaInv control target addend carry scratch) = 28 := by
  rfl

/-! ## Exact two-pass window ripple -/

inductive RippleMode where
  | add
  | sub
deriving DecidableEq, Repr

def rippleFirstCell (mode : RippleMode)
    (control target addend carry scratch : Wire) : Circuit :=
  match mode with
  | .add => controlledMaj control target addend carry scratch
  | .sub => controlledUmaInv control target addend carry scratch

def rippleSecondCell (mode : RippleMode)
    (control target addend carry scratch : Wire) : Circuit :=
  match mode with
  | .add => controlledUma control target addend carry scratch
  | .sub => controlledMajInv control target addend carry scratch

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

/-- Every first-pass cell restores its clean-v-chain work wire, even when that wire starts dirty. -/
theorem rippleFirstCell_preservesScratch
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup) :
    run (rippleFirstCell mode control target addend carry scratch) state scratch =
      state scratch := by
  obtain ⟨_, _, _, _, _, _, htargetScratch, _, haddendScratch,
    hcarryScratch⟩ := cell_nodup_parts control target addend carry scratch hnd
  cases mode with
  | add =>
      let middle := run [.CX carry target, .CX carry addend] state
      calc
        run (rippleFirstCell .add control target addend carry scratch) state scratch =
            run (cleanC3X control target addend carry scratch) middle scratch := rfl
        _ = middle scratch :=
          cleanC3X_preservesScratch control target addend carry scratch middle hnd
        _ = state scratch := by
          simp [middle, run, applyGate, upd, Ne.symm htargetScratch,
            Ne.symm haddendScratch, Ne.symm hcarryScratch]
  | sub =>
      let middle := run
        [.CX carry target, .CX carry addend, .CCX control addend target] state
      calc
        run (rippleFirstCell .sub control target addend carry scratch) state scratch =
            run (cleanC3X control target addend carry scratch) middle scratch := rfl
        _ = middle scratch :=
          cleanC3X_preservesScratch control target addend carry scratch middle hnd
        _ = state scratch := by
          simp [middle, run, applyGate, upd, Ne.symm htargetScratch,
            Ne.symm haddendScratch, Ne.symm hcarryScratch]

/-- Every second-pass cell likewise restores its clean-v-chain work wire off-domain. -/
theorem rippleSecondCell_preservesScratch
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup) :
    run (rippleSecondCell mode control target addend carry scratch) state scratch =
      state scratch := by
  obtain ⟨_, _, _, _, _, _, htargetScratch, _, haddendScratch,
    hcarryScratch⟩ := cell_nodup_parts control target addend carry scratch hnd
  cases mode with
  | add =>
      let middle := run (cleanC3X control target addend carry scratch) state
      calc
        run (rippleSecondCell .add control target addend carry scratch) state scratch =
            run [.CCX control addend target, .CX carry addend, .CX carry target]
              middle scratch := rfl
        _ = middle scratch := by
          simp [run, applyGate, upd, Ne.symm htargetScratch,
            Ne.symm haddendScratch, Ne.symm hcarryScratch]
        _ = state scratch :=
          cleanC3X_preservesScratch control target addend carry scratch state hnd
  | sub =>
      let middle := run (cleanC3X control target addend carry scratch) state
      calc
        run (rippleSecondCell .sub control target addend carry scratch) state scratch =
            run [.CX carry addend, .CX carry target] middle scratch := rfl
        _ = middle scratch := by
          simp [run, applyGate, upd, Ne.symm htargetScratch,
            Ne.symm haddendScratch, Ne.symm hcarryScratch]
        _ = state scratch :=
          cleanC3X_preservesScratch control target addend carry scratch state hnd

/-- First Figure-11 pass.  `targets` and `addends` are ordered from the high physical lane to
the low one, so this recursion emits the gates from the list's end back to its head. -/
def rippleFirstPass (mode : RippleMode) (control : Wire) :
    List Wire → List Wire → Wire → Wire → Circuit
  | target :: targets, addend :: addends, carry, scratch =>
      rippleFirstPass mode control targets addends carry scratch ++
        rippleFirstCell mode control target addend carry scratch
  | _, _, _, _ => []

/-- Second Figure-11 pass, emitted from the high physical lane to the low one. -/
def rippleSecondPass (mode : RippleMode) (control : Wire) :
    List Wire → List Wire → Wire → Wire → Circuit
  | target :: targets, addend :: addends, carry, scratch =>
      rippleSecondCell mode control target addend carry scratch ++
        rippleSecondPass mode control targets addends carry scratch
  | _, _, _, _ => []

/-- The literal two-pass ripple core used by both interval and prefix arithmetic after the caller
has prepared the location control for this physical slice.  Endpoint/unary control preparation is
a separate composition layer. -/
def controlledWindowRipple (mode : RippleMode) (control : Wire)
    (targets addends : List Wire) (carry scratch : Wire) : Circuit :=
  rippleFirstPass mode control targets addends carry scratch ++
    rippleSecondPass mode control targets addends carry scratch

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

/-- Each aligned lane has the five distinct roles required by the clean C3X decomposition. -/
def RippleLaneLayouts (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) : Prop :=
  List.Forall₂
    (fun target addend => [control, target, addend, carry, scratch].Nodup)
    targets addends

private theorem rippleFirstState_preservesScratch
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    rippleFirstState mode control targets addends carry state scratch =
      state scratch := by
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
              rw [rippleFirstState,
                writeRippleCell_preservesScratch control target addend carry scratch
                  _ _ hhead,
                ih addends state htail]

private theorem rippleSecondState_preservesScratch
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    rippleSecondState mode control targets addends carry state scratch =
      state scratch := by
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
              rw [rippleSecondState, ih addends _ htail,
                writeRippleCell_preservesScratch control target addend carry scratch
                  _ state hhead]

private theorem run_rippleFirstCell
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    run (rippleFirstCell mode control target addend carry scratch) state =
      writeRippleCell target addend carry
        (rippleFirstBits mode (state control)
          (readRippleCell target addend carry state)) state := by
  cases mode with
  | add => simpa [rippleFirstCell, rippleFirstBits] using
      run_controlledMaj_state control target addend carry scratch state hnd hclean
  | sub => simpa [rippleFirstCell, rippleFirstBits] using
      run_controlledUmaInv_state control target addend carry scratch state hnd hclean

private theorem run_rippleSecondCell
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    run (rippleSecondCell mode control target addend carry scratch) state =
      writeRippleCell target addend carry
        (rippleSecondBits mode (state control)
          (readRippleCell target addend carry state)) state := by
  cases mode with
  | add => simpa [rippleSecondCell, rippleSecondBits] using
      run_controlledUma_state control target addend carry scratch state hnd hclean
  | sub => simpa [rippleSecondCell, rippleSecondBits] using
      run_controlledMajInv_state control target addend carry scratch state hnd hclean

private theorem run_rippleFirstPass
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch)
    (hclean : state scratch = false) :
    run (rippleFirstPass mode control targets addends carry scratch) state =
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
              have hmiddleClean :
                  rippleFirstState mode control targets addends carry state scratch =
                    false := by
                rw [rippleFirstState_preservesScratch mode control targets addends
                  carry scratch state htail]
                exact hclean
              rw [rippleFirstPass, run_append, ih addends _ htail hclean]
              exact run_rippleFirstCell mode control target addend carry scratch _
                hhead hmiddleClean

private theorem run_rippleSecondPass
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch)
    (hclean : state scratch = false) :
    run (rippleSecondPass mode control targets addends carry scratch) state =
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
              have hnextClean :
                  writeRippleCell target addend carry
                      (rippleSecondBits mode (state control)
                        (readRippleCell target addend carry state)) state scratch =
                    false := by
                rw [writeRippleCell_preservesScratch control target addend carry scratch
                  _ state hhead]
                exact hclean
              rw [rippleSecondPass, run_append,
                run_rippleSecondCell mode control target addend carry scratch state hhead hclean,
                ih addends _ htail hnextClean]
              rfl

/-- Direct whole-basis-state semantics of the literal two-pass window ripple. -/
theorem run_controlledWindowRipple
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch)
    (hclean : state scratch = false) :
    run (controlledWindowRipple mode control targets addends carry scratch) state =
      controlledWindowRippleState mode control targets addends carry state := by
  have hmiddleClean :
      rippleFirstState mode control targets addends carry state scratch = false := by
    rw [rippleFirstState_preservesScratch mode control targets addends carry scratch
      state hlayouts]
    exact hclean
  rw [controlledWindowRipple, run_append,
    run_rippleFirstPass mode control targets addends carry scratch state hlayouts hclean,
    run_rippleSecondPass mode control targets addends carry scratch _ hlayouts hmiddleClean]
  rfl

private theorem rippleFirstPass_HPFree
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) :
    HPFree (rippleFirstPass mode control targets addends carry scratch) := by
  induction targets generalizing addends with
  | nil => cases addends <;> simp [rippleFirstPass]
  | cons target targets ih =>
      cases addends with
      | nil => simp [rippleFirstPass]
      | cons addend addends =>
          cases mode <;> simp [rippleFirstPass, rippleFirstCell, ih]

private theorem rippleSecondPass_HPFree
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) :
    HPFree (rippleSecondPass mode control targets addends carry scratch) := by
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
    (carry scratch : Wire) :
    HPFree (controlledWindowRipple mode control targets addends carry scratch) := by
  simp [controlledWindowRipple, rippleFirstPass_HPFree,
    rippleSecondPass_HPFree]

private theorem rippleFirstPass_wellFormed
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    CircuitWellFormed
      (rippleFirstPass mode control targets addends carry scratch) := by
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
                      (controlledMaj control target addend carry scratch)
                    exact controlledMaj_wellFormed
                      control target addend carry scratch hhead
                | sub =>
                    change CircuitWellFormed
                      (controlledUmaInv control target addend carry scratch)
                    exact controlledUmaInv_wellFormed
                      control target addend carry scratch hhead

private theorem rippleSecondPass_wellFormed
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    CircuitWellFormed
      (rippleSecondPass mode control targets addends carry scratch) := by
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
                      (controlledUma control target addend carry scratch)
                    exact controlledUma_wellFormed
                      control target addend carry scratch hhead
                | sub =>
                    change CircuitWellFormed
                      (controlledMajInv control target addend carry scratch)
                    exact controlledMajInv_wellFormed
                      control target addend carry scratch hhead
              · exact ih addends htail

theorem controlledWindowRipple_wellFormed
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    CircuitWellFormed
      (controlledWindowRipple mode control targets addends carry scratch) := by
  rw [controlledWindowRipple, circuitWellFormed_append]
  exact ⟨rippleFirstPass_wellFormed mode control targets addends carry scratch hlayouts,
    rippleSecondPass_wellFormed mode control targets addends carry scratch hlayouts⟩

/-- Complete named support of a two-pass ripple block. -/
def controlledWindowRippleSupport (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) : List Wire :=
  control :: targets ++ addends ++ [carry, scratch]

private theorem rippleFirstPass_usesOnly
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) :
    PaperCircuitUsesOnly
      (controlledWindowRippleSupport control targets addends carry scratch)
      (rippleFirstPass mode control targets addends carry scratch) := by
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
                apply (controlledMaj_usesOnly
                  control target addend carry scratch).mono
                intro wire hwire
                simp only [controlledWindowRippleSupport, List.mem_cons,
                  List.mem_append] at hwire ⊢
                aesop
            | sub =>
                apply (controlledUmaInv_usesOnly
                  control target addend carry scratch).mono
                intro wire hwire
                simp only [controlledWindowRippleSupport, List.mem_cons,
                  List.mem_append] at hwire ⊢
                aesop

private theorem rippleSecondPass_usesOnly
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) :
    PaperCircuitUsesOnly
      (controlledWindowRippleSupport control targets addends carry scratch)
      (rippleSecondPass mode control targets addends carry scratch) := by
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
                apply (controlledUma_usesOnly
                  control target addend carry scratch).mono
                intro wire hwire
                simp only [controlledWindowRippleSupport, List.mem_cons,
                  List.mem_append] at hwire ⊢
                aesop
            | sub =>
                apply (controlledMajInv_usesOnly
                  control target addend carry scratch).mono
                intro wire hwire
                simp only [controlledWindowRippleSupport, List.mem_cons,
                  List.mem_append] at hwire ⊢
                aesop
          · apply (ih addends).mono
            intro wire hwire
            simp only [controlledWindowRippleSupport, List.mem_cons,
              List.mem_append] at hwire ⊢
            aesop

/-- The exact two-pass circuit stays inside its declared control, data, carry, and clean-scratch
footprint. -/
theorem controlledWindowRipple_usesOnly
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) :
    PaperCircuitUsesOnly
      (controlledWindowRippleSupport control targets addends carry scratch)
      (controlledWindowRipple mode control targets addends carry scratch) := by
  apply PaperCircuitUsesOnly.append
  · exact rippleFirstPass_usesOnly mode control targets addends carry scratch
  · exact rippleSecondPass_usesOnly mode control targets addends carry scratch

/-- Every wire outside the named ripple footprint is unchanged. -/
theorem controlledWindowRipple_preservesOutside
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) (state : BasisState) (wire : Wire)
    (hwire : wire ∉
      controlledWindowRippleSupport control targets addends carry scratch) :
    run (controlledWindowRipple mode control targets addends carry scratch) state wire =
      state wire :=
  PaperCircuitUsesOnly.preservesOutside
    (controlledWindowRipple_usesOnly mode control targets addends carry scratch)
    state hwire

private theorem run_rippleFirstCell_protected
    (mode : RippleMode) (control target addend carry scratch wire : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false)
    (hprotected : wire = control ∨ wire = scratch) :
    run (rippleFirstCell mode control target addend carry scratch) state wire =
      state wire := by
  rw [run_rippleFirstCell mode control target addend carry scratch state hnd hclean]
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryScratch⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  rcases hprotected with rfl | rfl
  · simp only [writeRippleCell]
    rw [upd_other _ carry _ hcc, upd_other _ addend _ hca,
      upd_other _ target _ hct]
  · simp only [writeRippleCell]
    rw [upd_other _ carry _ (Ne.symm hcarryScratch),
      upd_other _ addend _ (Ne.symm had),
      upd_other _ target _ (Ne.symm htd)]

private theorem run_rippleSecondCell_protected
    (mode : RippleMode) (control target addend carry scratch wire : Wire)
    (state : BasisState)
    (hnd : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false)
    (hprotected : wire = control ∨ wire = scratch) :
    run (rippleSecondCell mode control target addend carry scratch) state wire =
      state wire := by
  rw [run_rippleSecondCell mode control target addend carry scratch state hnd hclean]
  obtain ⟨hct, hca, hcc, hcd, hta, htc, htd, hac, had, hcarryScratch⟩ :=
    cell_nodup_parts control target addend carry scratch hnd
  rcases hprotected with rfl | rfl
  · simp only [writeRippleCell]
    rw [upd_other _ carry _ hcc, upd_other _ addend _ hca,
      upd_other _ target _ hct]
  · simp only [writeRippleCell]
    rw [upd_other _ carry _ (Ne.symm hcarryScratch),
      upd_other _ addend _ (Ne.symm had),
      upd_other _ target _ (Ne.symm htd)]

private theorem run_rippleFirstPass_protected
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch wire : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch)
    (hclean : state scratch = false)
    (hprotected : wire = control ∨ wire = scratch) :
    run (rippleFirstPass mode control targets addends carry scratch) state wire =
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
              have hmiddleClean :
                  run (rippleFirstPass mode control targets addends carry scratch)
                      state scratch = false := by
                rw [run_rippleFirstPass mode control targets addends carry scratch state
                  htail hclean,
                  rippleFirstState_preservesScratch mode control targets addends carry
                    scratch state htail]
                exact hclean
              rw [rippleFirstPass, run_append,
                run_rippleFirstCell_protected mode control target addend carry scratch
                  wire _ hhead hmiddleClean hprotected,
                ih addends state htail hclean]

private theorem run_rippleSecondPass_protected
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch wire : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch)
    (hclean : state scratch = false)
    (hprotected : wire = control ∨ wire = scratch) :
    run (rippleSecondPass mode control targets addends carry scratch) state wire =
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
              have hnextClean :
                  run (rippleSecondCell mode control target addend carry scratch)
                      state scratch = false := by
                rw [run_rippleSecondCell mode control target addend carry scratch state
                  hhead hclean,
                  writeRippleCell_preservesScratch control target addend carry scratch
                    _ state hhead]
                exact hclean
              rw [rippleSecondPass, run_append,
                ih addends _ htail hnextClean,
                run_rippleSecondCell_protected mode control target addend carry scratch
                  wire state hhead hclean hprotected]

/-- The location control is preserved and the clean scratch wire is restored. -/
theorem controlledWindowRipple_protected
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch wire : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch)
    (hclean : state scratch = false)
    (hprotected : wire = control ∨ wire = scratch) :
    run (controlledWindowRipple mode control targets addends carry scratch) state wire =
      state wire := by
  have hmiddleClean :
      run (rippleFirstPass mode control targets addends carry scratch) state scratch =
        false := by
    rw [run_rippleFirstPass mode control targets addends carry scratch state hlayouts
      hclean,
      rippleFirstState_preservesScratch mode control targets addends carry scratch state
        hlayouts]
    exact hclean
  rw [controlledWindowRipple, run_append,
    run_rippleSecondPass_protected mode control targets addends carry scratch wire _
      hlayouts hmiddleClean hprotected,
    run_rippleFirstPass_protected mode control targets addends carry scratch wire state
      hlayouts hclean hprotected]

private theorem rippleFirstPass_toffoliCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    eeaToffoliCount (rippleFirstPass mode control targets addends carry scratch) =
      match mode with
      | .add => 3 * targets.length
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
              rw [rippleFirstPass, eeaToffoliCount_append,
                ih addends htail]
              cases mode <;> simp [rippleFirstCell] <;> omega

private theorem rippleSecondPass_toffoliCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    eeaToffoliCount (rippleSecondPass mode control targets addends carry scratch) =
      match mode with
      | .add => 4 * targets.length
      | .sub => 3 * targets.length := by
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

/-- Seven Toffolis per physical lane, matching the paper's 3+4 count and the pinned coherent
`_apply_cell` stream (`MEASUREMENT_UNCOMPUTE = False`): three in the MAJ pass and four in the UMA
pass (or the inverse order for subtraction). -/
theorem controlledWindowRipple_toffoliCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    eeaToffoliCount
        (controlledWindowRipple mode control targets addends carry scratch) =
      7 * targets.length := by
  rw [controlledWindowRipple, eeaToffoliCount_append,
    rippleFirstPass_toffoliCount mode control targets addends carry scratch hlayouts,
    rippleSecondPass_toffoliCount mode control targets addends carry scratch hlayouts]
  cases mode <;> simp [← Nat.add_mul]

private theorem rippleFirstPass_cnotCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    eeaCnotCount (rippleFirstPass mode control targets addends carry scratch) =
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
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    eeaCnotCount (rippleSecondPass mode control targets addends carry scratch) =
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
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    eeaCnotCount
        (controlledWindowRipple mode control targets addends carry scratch) =
      4 * targets.length := by
  rw [controlledWindowRipple, eeaCnotCount_append,
    rippleFirstPass_cnotCount mode control targets addends carry scratch hlayouts,
    rippleSecondPass_cnotCount mode control targets addends carry scratch hlayouts]
  omega

private theorem rippleFirstPass_tCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    ShorECDLP.tCount (rippleFirstPass mode control targets addends carry scratch) =
      match mode with
      | .add => 21 * targets.length
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
              rw [rippleFirstPass, tCount_append, ih addends htail]
              cases mode <;> simp [rippleFirstCell] <;> omega

private theorem rippleSecondPass_tCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    ShorECDLP.tCount (rippleSecondPass mode control targets addends carry scratch) =
      match mode with
      | .add => 28 * targets.length
      | .sub => 21 * targets.length := by
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

/-- The repository Framework's constructor-derived 49-T cost per lane for this coherent reference
circuit (`tCount` charges seven T gates per `CCX`).  This is not an adaptive paper aggregate. -/
theorem controlledWindowRipple_tCount
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch) :
    ShorECDLP.tCount
        (controlledWindowRipple mode control targets addends carry scratch) =
      49 * targets.length := by
  rw [controlledWindowRipple, tCount_append,
    rippleFirstPass_tCount mode control targets addends carry scratch hlayouts,
    rippleSecondPass_tCount mode control targets addends carry scratch hlayouts]
  cases mode <;> simp [← Nat.add_mul]

end ShorECDLP.Paper2607_13816
