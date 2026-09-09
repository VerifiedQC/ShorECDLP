import ShorECDLP.Submission.«2607_13816».EEA.InitialPacked
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout

/-! # First active production step after preprocessing -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
attribute [local irreducible] eeaPreprocessIdealState

private theorem first_all_ones (ws : List Wire) (s : BasisState)
    (h : wireAnd ws s = true) : boolWordToNat (wireValues ws s) = 2^ws.length - 1 := by
  induction ws with
  | nil => simp [wireValues]
  | cons w ws ih =>
    simp only [wireAnd, Bool.and_eq_true] at h
    have ht := ih h.2
    change boolWordToNat (List.map s ws) = 2^ws.length - 1 at ht
    simp only [wireValues, List.map_cons, boolWordToNat, h.1, Bool.toNat_true,
      List.length_cons, Nat.pow_succ]
    have hp := Nat.two_pow_pos ws.length
    omega

private theorem first_inputs (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < 2 ^ 256 - 2 ^ 32 - 977) :
    let after := eeaPreprocessIdealState state
    Clean indexedStepProductionRegisters.aux after ∧ after 1 = false ∧
    boolWordToNat (wireValues indexedStepProductionRegisters.lengthS after) = 511 ∧
    wireAnd indexedStepProductionRegisters.lengthRPrime after = false := by
  have h := eeaPreprocessIdealState_correct state hclean hx hxp
  have hd := eeaPreprocess_initial_divisor state hclean hx hxp
  dsimp only at h hd ⊢
  have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha : Clean indexedStepProductionRegisters.aux (eeaPreprocessIdealState state) := by
    intro w hw
    exact hc w (by simp only [List.mem_append]; exact Or.inr hw)
  have hp : eeaPreprocessIdealState state 1 = false := hc 1 (by simp)
  have hs : boolWordToNat (wireValues indexedStepProductionRegisters.lengthS
      (eeaPreprocessIdealState state)) = 511 := by
    change boolWordToNat (wireValues (List.range' 540 9) _) = 511
    rw [h.2.2.2.2.2.2.2.2.2.2.1, boolWordToNat_constantBits]
  refine ⟨ha, hp, hs, ?_⟩
  have hsize : (correctedInput (2 ^ 256 - 2 ^ 32 - 977)
      (boolWordToNat (wireValues (List.range' 263 256) state))).size ≤ 256 := by
    have hh := Nat.size_le_size (Nat.le_of_lt (correctedInput_lt hx hxp))
    exact hh.trans (Nat.size_le.mpr (by decide))
  have hw := congrArg boolWordToNat hd.2.2
  simp only [paperInitial, boolWordToNat_constantBits] at hw
  cases hh : wireAnd indexedStepProductionRegisters.lengthRPrime (eeaPreprocessIdealState state) with
  | false => rfl
  | true =>
    have hall := first_all_ones _ _ hh
    change boolWordToNat (wireValues (List.range' 549 9) (eeaPreprocessIdealState state)) = 511 at hall
    rw [hw] at hall
    have hlt : (correctedInput (2 ^ 256 - 2 ^ 32 - 977)
        (boolWordToNat (wireValues (List.range' 263 256) state))).size - 1 < 2^9 := by omega
    rw [Nat.mod_eq_of_lt hlt] at hall
    omega

/-- Preprocessing provides a concrete input for the first physical production step:
the shift counter becomes zero and the complete step preserves readiness and epoch encoding. -/
theorem eeaPreprocess_firstStep_correct (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < 2 ^ 256 - 2 ^ 32 - 977) :
    let r := indexedStepProductionRegisters
    let after := eeaPreprocessIdealState state
    boolWordToNat (wireValues r.lengthS (run (indexedStepShiftPrefix r 256 1) after)) = 0 ∧
    run (indexedStepUnitary r 256 1) after =
      phaseUpdateEpochState r.phaseUpdate r.shiftEpoch (run (indexedStepShiftPrefix r 256 1) after) ∧
    IndexedStepReady r (run (indexedStepUnitary r 256 1) after) ∧
    IndexedStepEpochEncoded r (run (indexedStepUnitary r 256 1) after) := by
  let r := indexedStepProductionRegisters
  let after := eeaPreprocessIdealState state
  obtain ⟨ha, hp, hs, hr⟩ := first_inputs state hclean hx hxp
  have hl : IndexedStepLayout r 256 1 := by
    have hh := secp256k1ScheduleLayout_production
    cases hh with
    | step head tail => exact head
  have hnext : (if after r.phase2 then
      (boolWordToNat (wireValues r.lengthS after) + 2^r.lengthS.length - 1) % 2^r.lengthS.length
    else (1 + boolWordToNat (wireValues r.lengthS after)) % 2^r.lengthS.length) = 0 := by
    change (if after 1 then
      (boolWordToNat (wireValues r.lengthS after) + 512 - 1) % 512
      else (1 + boolWordToNat (wireValues r.lengthS after)) % 512) = 0
    dsimp only [after, r]
    rw [hp, hs]
    decide
  refine ⟨?_, ?_⟩
  · exact (indexedStepShiftPrefix_counter r 256 1 after hl ha hr).trans hnext
  · exact indexedStepUnitary_active_correct r 256 1
      (endIterationWindowsAt 256 1).k4 (endIterationWindowsAt 256 1).k5
      (by decide) (by decide) after hl ha hr (by intro h; norm_num at h)
      (by intro h; norm_num at h)

end
end ShorECDLP.Paper2607_13816
