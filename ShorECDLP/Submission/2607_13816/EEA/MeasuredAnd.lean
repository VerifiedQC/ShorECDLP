import ShorECDLP.Submission.«2607_13816».EEA.BitCircuits
import ShorECDLP.Framework.Quantum.MeasurementUncompute

/-!
# Measurement-assisted AND erasure

The unary decoder computes one path AND with a Toffoli and erases it in the X basis.  The true
measurement branch applies the feed-forward controlled-Z prescribed by the pinned supplement.
This module packages that exact dynamic primitive independently of the canary example.
-/

namespace ShorECDLP.Paper2607_13816

open Quantum

noncomputable section

/-- The relation at a path-AND uncompute site. -/
def PathAndComputed (first second target : Wire) (state : BasisState) : Prop :=
  state target = (state first && state second)

/-- False needs no correction; true applies the phase `(-1)^(first * second)`. -/
def measuredAndCorrection (first second : Wire) : List Bool → Circuit
  | [true] => controlledZ first second
  | _ => []

/-- X-measure/reset of a computed AND, with the supplement's selected Clifford correction. -/
def measuredAndErase (first second target : Wire) : AdaptiveCircuit :=
  measureResetWithCorrection [target]
    (measuredAndCorrection first second)

/-- The selected controlled-Z supplies exactly the phase left by X-measuring the AND. -/
theorem measuredAndCorrection_phase
    (first second target : Wire)
    (hfs : first ≠ second)
    (hft : first ≠ target)
    (hst : second ≠ target) :
    RegisterXPhaseCorrectionOn [target]
      (measuredAndCorrection first second)
      (PathAndComputed first second target) := by
  intro outcomes hlength state hcomputed
  cases outcomes with
  | nil => simp at hlength
  | cons outcome outcomes =>
      have houtcomes : outcomes = [] := by
        simpa using hlength
      subst outcomes
      cases outcome with
      | false =>
          simp [measuredAndCorrection, clearRegister, registerXPhase]
      | true =>
          simp only [measuredAndCorrection]
          rw [run_controlledZ_ket first second
            (clearRegister [target] state) hfs]
          have hfirst :
              clearRegister [target] state first = state first := by
            simp [clearRegister, upd, hft]
          have hsecond :
              clearRegister [target] state second = state second := by
            simp [clearRegister, upd, hst]
          rw [hfirst, hsecond, ← hcomputed]
          simp [registerXPhase]

/-- Corrected AND erasure is coherent: every transcript has an input-independent coefficient and
the only ideal effect is clearing the computed target. -/
theorem measuredAndErase_coherent
    (first second target : Wire)
    (hfs : first ≠ second)
    (hft : first ≠ target)
    (hst : second ≠ target) :
    CoherentlyImplementsOn
      (measuredAndErase first second target)
      (clearRegisterMap [target])
      (PathAndComputed first second target) := by
  apply measureResetWithCorrection_coherent
  · simp
  · exact measuredAndCorrection_phase first second target hfs hft hst

/-- Physical well-formedness of the one-AND adaptive erasure. -/
theorem measuredAndErase_wellFormed
    (first second target : Wire)
    (hfs : first ≠ second) :
    (measuredAndErase first second target).WellFormed := by
  apply measureResetWithCorrection_wellFormed
  intro outcomes hlength
  cases outcomes with
  | nil => simp at hlength
  | cons outcome outcomes =>
      have houtcomes : outcomes = [] := by simpa using hlength
      subst outcomes
      cases outcome <;>
        simp [measuredAndCorrection, controlledZ_wellFormed, hfs]

/-- One AND erasure performs one measurement/reset. -/
@[simp]
theorem measuredAndErase_measurementCount
    (first second target : Wire) :
    (measuredAndErase first second target).measurementCount = 1 := by
  rfl

/-- The correction is Clifford-only, so the erasure adds no T gates. -/
@[simp]
theorem measuredAndErase_tCount
    (first second target : Wire) :
    (measuredAndErase first second target).tCount = 0 := by
  rfl

/-- The zero-branch path predicate used by unary iteration. -/
def ZeroAndComputed (control indexBit target : Wire)
    (state : BasisState) : Prop :=
  state target = (state control && !state indexBit)

/-- Compute `target = control AND NOT indexBit` into a clean target. -/
def computeZeroAnd (control indexBit target : Wire) : Circuit :=
  [.X indexBit, .CCX control indexBit target, .X indexBit]

/-- Literal source-order cleanup for a zero-branch path AND: invert the index bit, erase the
ordinary AND by measurement, then restore the index bit. -/
def eraseZeroAnd (control indexBit target : Wire) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary [.X indexBit]
      (measuredAndErase control indexBit target)).seq
    (AdaptiveCircuit.unitary [.X indexBit] .done)

/-- Classical action of the zero-branch AND computation. -/
theorem run_computeZeroAnd
    (control indexBit target : Wire) (state : BasisState)
    (hci : control ≠ indexBit)
    (_hct : control ≠ target)
    (hit : indexBit ≠ target)
    (hclean : state target = false) :
    Classical.run (computeZeroAnd control indexBit target) state =
      state[target ↦ state control && !state indexBit] := by
  funext wire
  by_cases hw : wire = target
  · subst wire
    simp [computeZeroAnd, Classical.run, Classical.applyGate, upd,
      hci, hit, Ne.symm hit, hclean]
  · by_cases hwi : wire = indexBit
    · subst wire
      simp [computeZeroAnd, Classical.run, Classical.applyGate, upd,
        hci, hit, Ne.symm hit]
    · simp [computeZeroAnd, Classical.run, Classical.applyGate, upd,
        hw, hwi]

/-- The coherent reference cleanup is the same self-inverse X/Toffoli/X circuit. -/
theorem run_computeZeroAnd_of_computed
    (control indexBit target : Wire) (state : BasisState)
    (hci : control ≠ indexBit)
    (_hct : control ≠ target)
    (hit : indexBit ≠ target)
    (hcomputed : ZeroAndComputed control indexBit target state) :
    Classical.run (computeZeroAnd control indexBit target) state =
      state[target ↦ false] := by
  funext wire
  by_cases hw : wire = target
  · subst wire
    simp [computeZeroAnd, Classical.run, Classical.applyGate, upd,
      hci, hit, Ne.symm hit]
    exact hcomputed
  · by_cases hwi : wire = indexBit
    · subst wire
      simp [computeZeroAnd, Classical.run, Classical.applyGate, upd,
        hci, hit, Ne.symm hit]
    · simp [computeZeroAnd, Classical.run, Classical.applyGate, upd,
        hw, hwi]

@[simp]
theorem computeZeroAnd_HPFree
    (control indexBit target : Wire) :
    Classical.HPFree (computeZeroAnd control indexBit target) := by
  simp [computeZeroAnd]

theorem computeZeroAnd_wellFormed
    (control indexBit target : Wire)
    (hci : control ≠ indexBit)
    (hct : control ≠ target)
    (hit : indexBit ≠ target) :
    CircuitWellFormed (computeZeroAnd control indexBit target) := by
  simp [computeZeroAnd, CircuitWellFormed, Gate.WellFormed,
    hci, hct, hit]

@[simp]
theorem computeZeroAnd_tCount
    (control indexBit target : Wire) :
    ShorECDLP.tCount (computeZeroAnd control indexBit target) = 7 := by
  rfl

@[simp]
theorem computeZeroAnd_toffoliCount
    (control indexBit target : Wire) :
    eeaToffoliCount (computeZeroAnd control indexBit target) = 1 := by
  rfl

@[simp]
theorem computeZeroAnd_cnotCount
    (control indexBit target : Wire) :
    eeaCnotCount (computeZeroAnd control indexBit target) = 0 := by
  rfl

/-- Measurement-assisted zero-AND cleanup coherently implements the literal Toffoli cleanup. -/
theorem eraseZeroAnd_coherent
    (control indexBit target : Wire)
    (hci : control ≠ indexBit)
    (hct : control ≠ target)
    (hit : indexBit ≠ target) :
    CoherentlyImplementsOn
      (eraseZeroAnd control indexBit target)
      (Quantum.run (computeZeroAnd control indexBit target))
      (ZeroAndComputed control indexBit target) := by
  have hflip := CoherentlyImplementsOn.unitary
    [.X indexBit] (ZeroAndComputed control indexBit target)
  have herase := measuredAndErase_coherent
    control indexBit target hci hct hit
  have hflipSupport :
      ∀ state, ZeroAndComputed control indexBit target state →
        SupportedOn (PathAndComputed control indexBit target)
          (Quantum.run [.X indexBit] (ket state)) := by
    intro state hcomputed
    rw [Quantum.run_singleton, applyGate_X_ket]
    apply supportedOn_ket
    unfold PathAndComputed
    unfold ZeroAndComputed at hcomputed
    rw [upd_other state indexBit (!state indexBit) (Ne.symm hit)]
    rw [upd_other state indexBit (!state indexBit) hci]
    simp [hcomputed]
  have hprefix := hflip.seq herase hflipSupport
  have hfinal := CoherentlyImplementsOn.unitary
    [.X indexBit] (fun _ => True)
  have hfinalSupport :
      ∀ state, ZeroAndComputed control indexBit target state →
        SupportedOn (fun _ => True)
          ((clearRegisterMap [target]).comp
            (Quantum.run [.X indexBit]) (ket state)) := by
    intro state hstate output houtput
    trivial
  have hall := hprefix.seq hfinal hfinalSupport
  have hprogram :
      ((AdaptiveCircuit.unitary [.X indexBit] .done).seq
          (measuredAndErase control indexBit target)).seq
          (AdaptiveCircuit.unitary [.X indexBit] .done) =
        eraseZeroAnd control indexBit target := rfl
  rw [hprogram] at hall
  apply hall.congrIdeal
  intro state hcomputed
  simp only [LinearMap.comp_apply]
  simp only [Quantum.run_singleton]
  rw [applyGate_X_ket]
  rw [clearRegisterMap_ket]
  rw [applyGate_X_ket]
  rw [run_ket_agrees_classical
    (computeZeroAnd control indexBit target) state
    (computeZeroAnd_HPFree control indexBit target)]
  rw [run_computeZeroAnd_of_computed control indexBit target state
    hci hct hit hcomputed]
  congr 1
  funext wire
  by_cases hwTarget : wire = target
  · subst wire
    simp [clearRegister, upd, Ne.symm hit]
  · by_cases hwIndex : wire = indexBit
    · subst wire
      simp [clearRegister, upd, hit]
    · simp [clearRegister, upd, hwTarget, hwIndex]

/-- Physical well-formedness of the literal source-order zero-AND cleanup. -/
theorem eraseZeroAnd_wellFormed
    (control indexBit target : Wire)
    (hci : control ≠ indexBit)
    (_hct : control ≠ target)
    (_hit : indexBit ≠ target) :
    (eraseZeroAnd control indexBit target).WellFormed := by
  apply AdaptiveCircuit.WellFormed.seq
  · exact ⟨by simp [CircuitWellFormed, Gate.WellFormed],
      measuredAndErase_wellFormed control indexBit target hci⟩
  · simp [AdaptiveCircuit.WellFormed, CircuitWellFormed,
      Gate.WellFormed]

@[simp]
theorem eraseZeroAnd_measurementCount
    (control indexBit target : Wire) :
    (eraseZeroAnd control indexBit target).measurementCount = 1 := by
  simp [eraseZeroAnd, AdaptiveCircuit.seq,
    measuredAndErase, measureResetWithCorrection,
    AdaptiveCircuit.measurementCount]

@[simp]
theorem eraseZeroAnd_tCount
    (control indexBit target : Wire) :
    (eraseZeroAnd control indexBit target).tCount = 0 := by
  simp [eraseZeroAnd, AdaptiveCircuit.seq,
    measuredAndErase, measureResetWithCorrection,
    AdaptiveCircuit.tCount, measuredAndCorrection, controlledZ,
    ShorECDLP.tCount, tCost]

end

end ShorECDLP.Paper2607_13816
