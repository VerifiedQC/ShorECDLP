import ShorECDLP.Framework.Quantum.MeasurementUncompute

/-!
# Measurement-uncomputation canary

This isolated paper-side gadget replaces the trailing Toffoli of a controlled
phase by X-measure/reset of the computed AND and a classically selected
Clifford controlled-Z.  It validates coherent phase cancellation and exact
resources without changing or importing the Naive QFT.
-/

namespace ShorECDLP.Paper2607_13816

open Quantum

noncomputable section

/-- The ordinary compute/phase/uncompute reference circuit, defined locally
so that the paper submission remains independent of the Naive QFT. -/
def idealCPhase
    (k : Nat) (control target ancilla : Wire) : Circuit :=
  [.CCX control target ancilla,
    .P .forward k ancilla,
    .CCX control target ancilla]

/-- Compute the AND and apply the requested phase, leaving the AND live. -/
def cPhasePrefix
    (k : Nat) (control target ancilla : Wire) : Circuit :=
  [.CCX control target ancilla, .P .forward k ancilla]

/-- The optimized one-bit phase correction: the false branch is empty and
the true branch applies controlled-Z directly to the surviving inputs. -/
def andCorrection
    (control target : Wire) : List Bool → Circuit
  | [true] => controlledZ control target
  | _ => []

/-- Controlled phase with measurement-based erasure of its AND ancilla. -/
def adaptiveCPhase
    (k : Nat) (control target ancilla : Wire) : AdaptiveCircuit :=
  .unitary (cPhasePrefix k control target ancilla)
    (measureResetWithCorrection [ancilla]
      (andCorrection control target))

/-- The clean-input validity predicate for the complete canary. -/
def AncillaClean (ancilla : Wire) (s : BasisState) : Prop :=
  s ancilla = false

/-- The intermediate validity predicate after the prefix computed the AND. -/
def AndComputed
    (control target ancilla : Wire) (s : BasisState) : Prop :=
  s ancilla = (s control && s target)

private theorem upd_twice
    (s : BasisState) (wire : Wire) (first second : Bool) :
    s[wire ↦ first][wire ↦ second] = s[wire ↦ second] := by
  funext i
  by_cases hi : i = wire
  · subst i
    simp
  · simp [upd, hi]

private theorem upd_eq_self
    (s : BasisState) (wire : Wire) (bit : Bool)
    (h : s wire = bit) :
    s[wire ↦ bit] = s := by
  funext i
  by_cases hi : i = wire
  · subst i
    simpa using h.symm
  · simp [upd, hi]

private theorem supportedOn_smul_ket
    (Valid : BasisState → Prop)
    (coefficient : ℂ)
    (s : BasisState)
    (hs : Valid s) :
    SupportedOn Valid (coefficient • ket s) := by
  intro u hu
  by_cases hsu : s = u
  · subst u
    exact hs
  · have hzero : (coefficient • ket s) u = 0 := by
      simp [Finsupp.smul_apply, ket_ne hsu]
    exact (hu hzero).elim

/-- The prefix computes the AND into a clean ancilla and applies its phase. -/
theorem run_cPhasePrefix_ket
    (k : Nat)
    (control target ancilla : Wire)
    (s : BasisState)
    (hancilla : s ancilla = false) :
    Quantum.run (cPhasePrefix k control target ancilla) (ket s) =
      (if s control && s target then phaseCoeff .forward k else 1) •
        ket (s[ancilla ↦ s control && s target]) := by
  simp only [cPhasePrefix, Quantum.run_cons, Quantum.run_nil]
  rw [applyGate_CCX_ket]
  rw [applyGate_P_ket]
  cases hc : s control <;> cases ht : s target <;>
    simp [hancilla]

/-- The local unitary reference restores the clean ancilla. -/
theorem run_idealCPhase_ket
    (k : Nat)
    (control target ancilla : Wire)
    (s : BasisState)
    (hca : control ≠ ancilla)
    (hta : target ≠ ancilla)
    (hancilla : s ancilla = false) :
    Quantum.run (idealCPhase k control target ancilla) (ket s) =
      (if s control && s target then phaseCoeff .forward k else 1) •
        ket s := by
  rw [show idealCPhase k control target ancilla =
      cPhasePrefix k control target ancilla ++
        [.CCX control target ancilla] by rfl]
  rw [Quantum.run_append]
  rw [run_cPhasePrefix_ket k control target ancilla s hancilla]
  rw [Quantum.run_smul, Quantum.run_singleton, applyGate_CCX_ket]
  have hcontrol :
      s[ancilla ↦ s control && s target] control = s control := by
    exact upd_other s ancilla (s control && s target) hca
  have htarget :
      s[ancilla ↦ s control && s target] target = s target := by
    exact upd_other s ancilla (s control && s target) hta
  have hxor :
      Bool.xor
          (s[ancilla ↦ s control && s target] ancilla)
          (s[ancilla ↦ s control && s target] control &&
            s[ancilla ↦ s control && s target] target) = false := by
    simp [hcontrol, htarget]
  rw [hxor]
  have hrestore :
      s[ancilla ↦ s control && s target][ancilla ↦ false] = s := by
    rw [upd_twice]
    exact upd_eq_self s ancilla false hancilla
  rw [hrestore]

/-- The direct controlled-Z family supplies the exact phase required to erase
one computed AND bit. -/
theorem andCorrection_phase
    (control target ancilla : Wire)
    (hct : control ≠ target)
    (hca : control ≠ ancilla)
    (hta : target ≠ ancilla) :
    RegisterXPhaseCorrectionOn [ancilla]
      (andCorrection control target)
      (AndComputed control target ancilla) := by
  intro outcomes hlength s hcomputed
  cases outcomes with
  | nil => simp at hlength
  | cons outcome outcomes =>
      have houtcomes : outcomes = [] := by
        simpa using hlength
      subst outcomes
      cases outcome with
      | false =>
          simp [andCorrection, clearRegister, registerXPhase]
      | true =>
          simp only [andCorrection]
          rw [run_controlledZ_ket control target
            (clearRegister [ancilla] s) hct]
          have hcontrol : clearRegister [ancilla] s control = s control := by
            simp [clearRegister, upd, hca]
          have htarget : clearRegister [ancilla] s target = s target := by
            simp [clearRegister, upd, hta]
          rw [hcontrol, htarget, ← hcomputed]
          simp [registerXPhase]

/-- The corrected one-bit erasure is a coherent implementation of clearing
the computed AND, with coefficients independent of the input. -/
theorem andErase_coherent
    (control target ancilla : Wire)
    (hct : control ≠ target)
    (hca : control ≠ ancilla)
    (hta : target ≠ ancilla) :
    CoherentlyImplementsOn
      (measureResetWithCorrection [ancilla]
        (andCorrection control target))
      (clearRegisterMap [ancilla])
      (AndComputed control target ancilla) := by
  apply measureResetWithCorrection_coherent
  · simp
  · exact andCorrection_phase control target ancilla hct hca hta

/-- The adaptive canary coherently implements the ordinary unitary controlled
phase on every clean computational-basis input. -/
theorem adaptiveCPhase_coherent
    (k : Nat)
    (control target ancilla : Wire)
    (hct : control ≠ target)
    (hca : control ≠ ancilla)
    (hta : target ≠ ancilla) :
    CoherentlyImplementsOn
      (adaptiveCPhase k control target ancilla)
      (Quantum.run (idealCPhase k control target ancilla))
      (AncillaClean ancilla) := by
  have hprefix := CoherentlyImplementsOn.unitary
    (cPhasePrefix k control target ancilla) (AncillaClean ancilla)
  have herase := andErase_coherent control target ancilla hct hca hta
  have hsupport :
      ∀ s, AncillaClean ancilla s →
        SupportedOn (AndComputed control target ancilla)
          (Quantum.run (cPhasePrefix k control target ancilla) (ket s)) := by
    intro s hs
    rw [run_cPhasePrefix_ket k control target ancilla s hs]
    apply supportedOn_smul_ket
    unfold AndComputed
    rw [upd_same]
    rw [upd_other s ancilla (s control && s target) hca]
    rw [upd_other s ancilla (s control && s target) hta]
  have hseq := hprefix.seq herase hsupport
  have hsameProgram :
      (AdaptiveCircuit.unitary
          (cPhasePrefix k control target ancilla)
          AdaptiveCircuit.done).seq
          (measureResetWithCorrection [ancilla]
            (andCorrection control target)) =
        adaptiveCPhase k control target ancilla := rfl
  rw [hsameProgram] at hseq
  apply hseq.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply]
  rw [run_cPhasePrefix_ket k control target ancilla s hs]
  rw [map_smul, clearRegisterMap_ket]
  have hclear :
      clearRegister [ancilla]
          (s[ancilla ↦ s control && s target]) = s := by
    simp only [clearRegister]
    rw [upd_twice]
    exact upd_eq_self s ancilla false hs
  rw [hclear]
  exact (run_idealCPhase_ket k control target ancilla s hca hta hs).symm

/-- Physical well-formedness of the adaptive controlled phase. -/
theorem adaptiveCPhase_wellFormed
    (k : Nat)
    (control target ancilla : Wire)
    (hct : control ≠ target)
    (hca : control ≠ ancilla)
    (hta : target ≠ ancilla) :
    (adaptiveCPhase k control target ancilla).WellFormed := by
  refine ⟨?_, ?_⟩
  · simp [cPhasePrefix, CircuitWellFormed, Gate.WellFormed,
      hct, hca, hta]
  · apply measureResetWithCorrection_wellFormed
    intro outcomes hlength
    cases outcomes with
    | nil => simp at hlength
    | cons outcome outcomes =>
        have houtcomes : outcomes = [] := by simpa using hlength
        subst outcomes
        cases outcome <;>
          simp [andCorrection, controlledZ_wellFormed, hct]

/-- One mid-circuit measurement/reset event occurs. -/
@[simp]
theorem adaptiveCPhase_measurementCount
    (k : Nat) (control target ancilla : Wire) :
    (adaptiveCPhase k control target ancilla).measurementCount = 1 := by
  rfl

/-- The adaptive gadget costs one Toffoli and one phase gate, hence eight
naive T gates instead of fifteen for the unitary reference. -/
@[simp]
theorem adaptiveCPhase_tCount
    (k : Nat) (control target ancilla : Wire) :
    (adaptiveCPhase k control target ancilla).tCount = 8 := by
  rfl

@[simp]
theorem idealCPhase_tCount
    (k : Nat) (control target ancilla : Wire) :
    ShorECDLP.tCount (idealCPhase k control target ancilla) = 15 := by
  rfl

/-- Submission-side Toffoli tally; the shared framework intentionally exposes
only its baseline T metric. -/
def toffoliCount (circuit : Circuit) : Nat :=
  (circuit.map fun gate => match gate with
    | .CCX _ _ _ => 1
    | _ => 0).sum

/-- Worst-case Toffoli tally across adaptive outcomes. -/
def adaptiveToffoliCount : AdaptiveCircuit → Nat
  | .done => 0
  | .unitary circuit next =>
      toffoliCount circuit + adaptiveToffoliCount next
  | .xMeasureReset _ onFalse onTrue =>
      max (adaptiveToffoliCount onFalse)
        (adaptiveToffoliCount onTrue)

/-- No Toffoli is used after the canary's measurement: either correction
branch is Clifford-only. -/
theorem andCorrection_toffoliCount
    (control target : Wire)
    (outcomes : List Bool) :
    toffoliCount (andCorrection control target outcomes) = 0 := by
  cases outcomes with
  | nil => rfl
  | cons outcome outcomes =>
      cases outcomes with
      | nil => cases outcome <;> rfl
      | cons next rest =>
          simp [andCorrection, toffoliCount]

/-- The whole adaptive canary uses exactly one Toffoli, versus two in the
ordinary unitary reference. -/
@[simp]
theorem adaptiveCPhase_toffoliCount
    (k : Nat) (control target ancilla : Wire) :
    adaptiveToffoliCount
        (adaptiveCPhase k control target ancilla) = 1 := by
  rfl

@[simp]
theorem idealCPhase_toffoliCount
    (k : Nat) (control target ancilla : Wire) :
    toffoliCount (idealCPhase k control target ancilla) = 2 := by
  rfl

/-- Measurement/reset reuses the same AND ancilla, so exactly three physical
wires are touched. -/
theorem adaptiveCPhase_qubitCount
    (k : Nat)
    (control target ancilla : Wire)
    (hct : control ≠ target)
    (hca : control ≠ ancilla)
    (hta : target ≠ ancilla) :
    (adaptiveCPhase k control target ancilla).qubitCount = 3 := by
  simp [AdaptiveCircuit.qubitCount, AdaptiveCircuit.wires, adaptiveCPhase,
    cPhasePrefix, measureResetWithCorrection, andCorrection,
    controlledZ, circuitWires, gateWires,
    hct, hca, hta, Ne.symm hct, Ne.symm hca, Ne.symm hta]

/-- Summing the two measurement branches preserves Born mass for arbitrary
input states. -/
theorem adaptiveCPhase_preservesBornMass
    (k : Nat)
    (control target ancilla : Wire)
    (hct : control ≠ target)
    (hca : control ≠ ancilla)
    (hta : target ≠ ancilla)
    (psi : State) :
    Instrument.bornMass
        (adaptiveCPhase k control target ancilla).run psi =
      normSq psi := by
  exact AdaptiveCircuit.run_preservesBornMass
    (adaptiveCPhase k control target ancilla)
    (adaptiveCPhase_wellFormed k control target ancilla hct hca hta)
    psi

end

end ShorECDLP.Paper2607_13816
