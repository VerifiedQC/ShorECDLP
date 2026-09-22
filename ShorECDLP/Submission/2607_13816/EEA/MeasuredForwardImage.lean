import ShorECDLP.Submission.«2607_13816».EEA.MeasuredScheduleCounts
import ShorECDLP.Submission.«2607_13816».EEA.TerminalEntry
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
attribute [local irreducible] indexedStepUnitary indexedStepEndRoutes
private theorem production_measured_inverse_actual (start count : Nat)
    (hlayout : IndexedScheduleLayout indexedStepProductionRegisters 256 start count)
    (hstart : 1 ≤ start) (hstop : start + count ≤ 1621)
    (state : BasisState)
    (hinput : IndexedScheduleAdaptiveInput indexedStepProductionRegisters 256 start count state) :
    run (indexedScheduleInverseUnitary indexedStepProductionRegisters 256 start count)
      (run (indexedScheduleUnitary indexedStepProductionRegisters 256 start count) state) = state ∧
    MeasuredScheduleInverseInput indexedStepProductionRegisters 256 start count
      (run (indexedScheduleUnitary indexedStepProductionRegisters 256 start count) state) := by
  induction hlayout generalizing state with
  | done start => exact ⟨rfl,trivial⟩
  | @step start count head tail ih =>
    let r := indexedStepProductionRegisters
    let routes := indexedStepEndRoutes r 256 start state
    have hroutes := secp256k1IndexedStepRoutesValid start hstart (by omega) state
    have hb : (endIterationWindowsAt 256 start).k4 ≤ routes.1 ∧
        routes.1 ≤ (endIterationWindowsAt 256 start).K4 ∧
        (endIterationWindowsAt 256 start).k5 ≤ routes.2 ∧
        routes.2 ≤ (endIterationWindowsAt 256 start).K5Decode 256 := hroutes
    have hhead := indexedStepInverseUnitary_after_forward r 256 start routes.1 routes.2
      ⟨hb.1,hb.2.1⟩ ⟨hb.2.2.1,hb.2.2.2⟩ state head hinput.1 hinput.2.1 (fun _ => rfl)
    have hready := indexedStepInverseAdaptiveInput_after_forward r 256 start routes.1 routes.2
      ⟨hb.1,hb.2.1⟩ ⟨hb.2.2.1,hb.2.2.2⟩ state head hinput.1 hinput.2.1 (fun _ => rfl)
    have htail := ih (by omega) (by omega)
      (run (indexedStepUnitary r 256 start) state) hinput.2.2
    constructor
    · simp only [indexedScheduleUnitary,indexedScheduleInverseUnitary,Classical.run_append]
      rw [htail.1]
      exact hhead
    · simp only [MeasuredScheduleInverseInput,indexedScheduleUnitary,Classical.run_append]
      refine ⟨htail.2, ?_⟩
      rw [htail.1]
      exact ⟨(indexedStepUnitary_correct r 256 start routes.1 routes.2
        ⟨hb.1,hb.2.1⟩ ⟨hb.2.2.1,hb.2.2.2⟩ state head hinput.1 hinput.2.1 (fun _ => rfl)).2, hready⟩


/-- Every clean canonical input establishes the measured inverse H and tail conditions. -/
theorem secp256k1MeasuredEEAReverse_input (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < ShorECDLP.p) :
    MeasuredScheduleInverseInput indexedStepProductionRegisters 256 1 1620
      (run (secp256k1EEAForwardUnitary indexedStepProductionRegisters)
        (eeaPreprocessIdealState state)) := by
  exact (production_measured_inverse_actual 1 1620 secp256k1ScheduleLayout_production
    (by decide) (by decide) (eeaPreprocessIdealState state)
    (secp256k1EEAForward_adaptiveInput state hclean hx hxp)).2

/-- The new forward schedule is coherent on the original preprocessed input domain. -/
theorem secp256k1MeasuredEEAForward_coherent_preprocessed :
    Quantum.CoherentlyImplementsOn (secp256k1MeasuredEEAForward indexedStepProductionRegisters)
      (Quantum.run (secp256k1EEAForwardUnitary indexedStepProductionRegisters))
      (fun state => ∃ s : BasisState,
        Clean (List.range' 0 263 ++ List.range' 519 61) s ∧
        0 < boolWordToNat (wireValues (List.range' 263 256) s) ∧
        boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p ∧
        state = eeaPreprocessIdealState s) := by
  have h := measuredIndexedSchedule_coherent indexedStepProductionRegisters 256 1
    secp256k1ScheduleLength secp256k1ScheduleLayout_production
  obtain ⟨coefficients, aligned, mass⟩ := h
  refine ⟨coefficients, ?_, mass⟩
  apply aligned.imp
  intro branch coefficient hb state hs
  obtain ⟨s, hc, hx, hxp, he⟩ := hs
  apply hb
  rw [he]
  exact secp256k1EEAForward_adaptiveInput s hc hx hxp

/-- The new reverse schedule is coherent on the original forward-image domain. -/
theorem secp256k1MeasuredEEAReverse_coherent_forward_image :
    Quantum.CoherentlyImplementsOn (secp256k1MeasuredEEAReverse indexedStepProductionRegisters)
      (Quantum.run (secp256k1EEAReverseUnitary indexedStepProductionRegisters))
      (fun state => ∃ s : BasisState,
        Clean (List.range' 0 263 ++ List.range' 519 61) s ∧
        0 < boolWordToNat (wireValues (List.range' 263 256) s) ∧
        boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p ∧
        state = run (secp256k1EEAForwardUnitary indexedStepProductionRegisters)
          (eeaPreprocessIdealState s)) := by
  have h := secp256k1MeasuredEEAReverse_coherent indexedStepProductionRegisters
    secp256k1ScheduleLayout_production
  obtain ⟨coefficients,aligned,mass⟩ := h
  refine ⟨coefficients,?_,mass⟩
  apply aligned.imp
  intro branch coefficient hb state hs
  obtain ⟨s,hc,hx,hxp,he⟩ := hs
  apply hb
  rw [he]
  exact secp256k1MeasuredEEAReverse_input s hc hx hxp

end ShorECDLP.Paper2607_13816
