import ShorECDLP.Framework.Quantum.AdaptiveMeasurement
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerCoherent
import ShorECDLP.Submission.«2607_13816».EEA.WrapperLocality

/-!
# Figure 15 adaptive in-place schedules

These concrete programs follow the pinned wrapped quadratic source. The initial
256 X-measure/reset outcomes remain available across intervening adaptive EEA
and multiplication calls, and select the final Z corrections. The final bank
exchange uses actual three-CX swaps, as in the source. The arithmetic phase
reconstruction and aggregate resource certificates are separate obligations.
-/
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section

/-- The product is written to A; X controls and Y is the reusable addend. -/
def fig15MultiplyToWork : AdaptiveCircuit :=
  hornerMul (List.range' 263 256) (List.range' 580 256) (List.range' 7 256)
    secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559

/-- Recompute the old Y from X and A into the cleared data bank. -/
def fig15MultiplyToData : AdaptiveCircuit :=
  hornerMul (List.range' 263 256) (List.range' 7 256) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559

/-- Explicit source inverse of the recomputation call. -/
def fig15MultiplyToDataInverse : AdaptiveCircuit :=
  hornerMulInverse (List.range' 263 256) (List.range' 7 256) (List.range' 580 256)
    (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559

/-- The final source SWAP of the output and now-cleared work bank. -/
def fig15SwapOutput : Circuit :=
  (List.range 256).flatMap (fun i =>
    [.CX (580+i) (7+i), .CX (7+i) (580+i), .CX (580+i) (7+i)])

/-- Source division continuation: restore X, recompute Y for phase correction,
uncompute it, and swap the quotient into Y. -/
def fig15DivisionAfterReset (outcomes : List Bool) : AdaptiveCircuit :=
  (((secp256k1EEAReverseInDataBank.seq fig15MultiplyToData).seq
    (.unitary (registerZCorrection (List.range' 580 256) outcomes) .done)).seq
      fig15MultiplyToDataInverse).seq (.unitary fig15SwapOutput .done)

/-- Source multiplication continuation: invert X, recompute and phase-correct Y,
uncompute Y, restore X, and swap the product into Y. -/
def fig15MultiplicationAfterReset (outcomes : List Bool) : AdaptiveCircuit :=
  ((((secp256k1EEAForwardInDataBank.seq fig15MultiplyToData).seq
    (.unitary (registerZCorrection (List.range' 580 256) outcomes) .done)).seq
      fig15MultiplyToDataInverse).seq secp256k1EEAReverseInDataBank).seq
        (.unitary fig15SwapOutput .done)

/-- Literal complete Figure 15 division schedule at secp256k1 width. -/
def secp256k1InPlaceDivision : AdaptiveCircuit :=
  (secp256k1EEAForwardWrapper.seq fig15MultiplyToWork).seq
    (measureResetThen (List.range' 580 256) fig15DivisionAfterReset)

/-- Literal complete Figure 15 multiplication schedule at secp256k1 width. -/
def secp256k1InPlaceMultiplication : AdaptiveCircuit :=
  fig15MultiplyToWork.seq
    (measureResetThen (List.range' 580 256) fig15MultiplicationAfterReset)

private theorem figure15_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 580 256 ++ List.range' 7 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

private theorem figure15_data_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 7 256 ++ List.range' 580 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

attribute [local irreducible] hornerMul hornerMulInverse

private theorem figure15_multipliers_wellFormed :
    fig15MultiplyToWork.WellFormed ∧ fig15MultiplyToData.WellFormed ∧
      fig15MultiplyToDataInverse.WellFormed := by
  have ha : List.range' 7 256 = 7 :: List.range' 8 255 := rfl
  have hy : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  refine ⟨?_,?_,?_⟩
  · unfold fig15MultiplyToWork
    rw [ha]
    apply hornerMul_wellFormed
    · simp only [List.length_range',List.length_cons]
    · simp [secp256k1ReductionConstantBits]
    · rw [← ha]; exact figure15_layout
  · unfold fig15MultiplyToData
    rw [hy]
    apply hornerMul_wellFormed
    · simp only [List.length_range',List.length_cons]
    · simp [secp256k1ReductionConstantBits]
    · rw [← hy]; exact figure15_data_layout
  · unfold fig15MultiplyToDataInverse
    rw [hy]
    apply hornerMulInverse_wellFormed
    · simp only [List.length_range',List.length_cons]
    · simp only [List.length_cons,List.length_range',constantBits_length]
    · rw [← hy]; exact figure15_data_layout

private theorem figure15_swap_wellFormed : CircuitWellFormed fig15SwapOutput := by
  intro g hg
  simp only [fig15SwapOutput,List.mem_flatMap] at hg
  obtain ⟨i,hi,hg⟩ := hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;> norm_num [Gate.WellFormed,Nat.add_right_cancel_iff]

attribute [local irreducible] fig15MultiplyToWork fig15MultiplyToData fig15MultiplyToDataInverse
  secp256k1EEAForwardWrapper secp256k1EEAForwardInDataBank secp256k1EEAReverseInDataBank

private theorem figure15_unitary_wellFormed (c : Circuit) (h : CircuitWellFormed c) :
    (AdaptiveCircuit.unitary c .done).WellFormed := ⟨h,trivial⟩

private theorem division_continuation_wellFormed (outcomes : List Bool) :
    (fig15DivisionAfterReset outcomes).WellFormed := by
  exact (((secp256k1EEAInDataBank_wellFormed.2.seq figure15_multipliers_wellFormed.2.1).seq
    (figure15_unitary_wellFormed _ (registerZCorrection_wellFormed (List.range' 580 256) outcomes))).seq figure15_multipliers_wellFormed.2.2).seq
      (figure15_unitary_wellFormed _ figure15_swap_wellFormed)

private theorem multiplication_continuation_wellFormed (outcomes : List Bool) :
    (fig15MultiplicationAfterReset outcomes).WellFormed := by
  exact ((((secp256k1EEAInDataBank_wellFormed.1.seq figure15_multipliers_wellFormed.2.1).seq
    (figure15_unitary_wellFormed _ (registerZCorrection_wellFormed (List.range' 580 256) outcomes))).seq figure15_multipliers_wellFormed.2.2).seq
      secp256k1EEAInDataBank_wellFormed.2).seq (figure15_unitary_wellFormed _ figure15_swap_wellFormed)

/-- All gates and measurements in both complete source schedules are physically well formed. -/
theorem secp256k1InPlace_wellFormed :
    secp256k1InPlaceDivision.WellFormed ∧ secp256k1InPlaceMultiplication.WellFormed := by
  constructor
  · exact (secp256k1EEAForwardWrapper_wellFormed.seq figure15_multipliers_wellFormed.1).seq
      (measureResetThen_wellFormed _ _ (fun outcomes _ => division_continuation_wellFormed outcomes))
  · exact figure15_multipliers_wellFormed.1.seq
      (measureResetThen_wellFormed _ _ (fun outcomes _ => multiplication_continuation_wellFormed outcomes))

/-! ## Concrete division reconstruction and transcript phase -/
open Classical

def fig15WorkProductState : BasisState → BasisState :=
  hornerMulIdealState (List.range' 263 256) (List.range' 580 256) (List.range' 7 256)
    secp256k1ReductionConstantBits ShorECDLP.p 558 559

def fig15DataProductState : BasisState → BasisState :=
  hornerMulIdealState (List.range' 263 256) (List.range' 7 256) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 558 559

theorem fig15MultiplyToWork_coherent :
    CoherentlyImplementsOn fig15MultiplyToWork
      (Finsupp.lmapDomain ℂ ℂ fig15WorkProductState)
      (HornerInputValid (List.range' 580 256) (List.range' 7 256) ShorECDLP.p 558 560 561 559) := by
  have ha : List.range' 7 256 = 7 :: List.range' 8 255 := rfl
  unfold fig15MultiplyToWork fig15WorkProductState
  rw [ha]
  apply hornerMul_coherent
  · simp only [List.length_range',List.length_cons]
  · simp [secp256k1ReductionConstantBits]
  · rw [← ha]; exact figure15_layout
  · decide +kernel
  · decide +kernel
  · rw [secp256k1ReductionConstant_value]; decide +kernel

theorem fig15MultiplyToData_coherent :
    CoherentlyImplementsOn fig15MultiplyToData
      (Finsupp.lmapDomain ℂ ℂ fig15DataProductState)
      (HornerInputValid (List.range' 7 256) (List.range' 580 256) ShorECDLP.p 558 560 561 559) := by
  have hy : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  unfold fig15MultiplyToData fig15DataProductState
  rw [hy]
  apply hornerMul_coherent
  · simp only [List.length_range',List.length_cons]
  · simp [secp256k1ReductionConstantBits]
  · rw [← hy]; exact figure15_data_layout
  · decide +kernel
  · decide +kernel
  · rw [secp256k1ReductionConstant_value]; decide +kernel

theorem fig15MultiplyToDataInverse_coherent :
    CoherentlyImplementsOn fig15MultiplyToDataInverse
      (Finsupp.lmapDomain ℂ ℂ (hornerClearOutput (List.range' 580 256)))
      (fun s => ∃ original,
        HornerInputValid (List.range' 7 256) (List.range' 580 256) ShorECDLP.p 558 560 561 559 original ∧
        s = fig15DataProductState original) := by
  have hy : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  unfold fig15MultiplyToDataInverse fig15DataProductState
  rw [hy]
  apply hornerMulInverse_coherent
  · simp only [List.length_range',List.length_cons]
  · simp [secp256k1ReductionConstantBits]
  · simp only [List.length_range',List.length_cons,constantBits_length]
  · rw [← hy]; exact figure15_data_layout
  · decide +kernel
  · decide +kernel
  · rw [secp256k1ReductionConstant_value]; decide +kernel
  · rw [boolWordToNat_constantBits]; decide +kernel
private theorem clean_word_zero (ws : List Wire) (s : BasisState) (h : Clean ws s) :
    boolWordToNat (wireValues ws s) = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change boolWordToNat (s w :: wireValues ws s) = 0
    rw [boolWordToNat,h w (by simp),ih (by intro v hv; exact h v (by simp [hv]))]
    rfl

attribute [local irreducible] hornerMulIdealState

theorem fig15WorkProductState_correct (s : BasisState)
    (hs : HornerInputValid (List.range' 580 256) (List.range' 7 256) ShorECDLP.p 558 560 561 559 s) :
    boolWordToNat (wireValues (List.range' 7 256) (fig15WorkProductState s)) =
      (boolWordToNat (wireValues (List.range' 580 256) s) *
        boolWordToNat (wireValues (List.range' 263 256) s)) % ShorECDLP.p ∧
    ∀ w, w ∉ List.range' 7 256 → fig15WorkProductState s w = s w := by
  have ha : List.range' 7 256 = 7 :: List.range' 8 255 := rfl
  unfold fig15WorkProductState
  rw [ha]
  apply hornerMulIdealState_correct (r := 560) (t := 561)
  · simp only [List.length_range',List.length_cons]
  · simp [secp256k1ReductionConstantBits]
  · rw [← ha]; exact figure15_layout
  · exact hs.2.1
  · exact hs.2.2.2.2.1
  · decide +kernel
  · decide +kernel
  · exact hs.2.2.2.2.2
  · exact clean_word_zero _ s hs.1
  · rw [secp256k1ReductionConstant_value]; decide +kernel

theorem fig15DataProductState_correct (s : BasisState)
    (hs : HornerInputValid (List.range' 7 256) (List.range' 580 256) ShorECDLP.p 558 560 561 559 s) :
    boolWordToNat (wireValues (List.range' 580 256) (fig15DataProductState s)) =
      (boolWordToNat (wireValues (List.range' 7 256) s) *
        boolWordToNat (wireValues (List.range' 263 256) s)) % ShorECDLP.p ∧
    ∀ w, w ∉ List.range' 580 256 → fig15DataProductState s w = s w := by
  have hy : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  unfold fig15DataProductState
  rw [hy]
  apply hornerMulIdealState_correct (r := 560) (t := 561)
  · simp only [List.length_range',List.length_cons]
  · simp [secp256k1ReductionConstantBits]
  · rw [← hy]; exact figure15_data_layout
  · exact hs.2.1
  · exact hs.2.2.2.2.1
  · decide +kernel
  · decide +kernel
  · exact hs.2.2.2.2.2
  · exact clean_word_zero _ s hs.1
  · rw [secp256k1ReductionConstant_value]; decide +kernel
/-- Clean EEA workspace, nonzero canonical X and canonical data Y. -/
def Secp256k1InPlaceInputValid (s : BasisState) : Prop :=
  Secp256k1EEAInputValid s ∧ boolWordToNat (wireValues (List.range' 580 256) s) < ShorECDLP.p
private theorem fig15_initial_horner (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    HornerInputValid (List.range' 580 256) (List.range' 7 256) ShorECDLP.p 558 560 561 559 s := by
  refine ⟨?_,hs.1.1 558 (by decide +kernel),hs.1.1 560 (by decide +kernel),
    hs.1.1 561 (by decide +kernel),hs.1.1 559 (by decide +kernel),hs.2⟩
  intro w hw
  exact hs.1.1 w (by simp at hw ⊢; omega)
private theorem fig15_after_eea_horner (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    HornerInputValid (List.range' 580 256) (List.range' 7 256) ShorECDLP.p 558 560 561 559
      (secp256k1EEAOutputIdealState s) := by
  have ho := secp256k1EEAOutputIdealState_correct s hs.1.1 hs.1.2.1 hs.1.2.2
  have hword : wireValues (List.range' 580 256) (secp256k1EEAOutputIdealState s) =
      wireValues (List.range' 580 256) s := by
    apply List.map_congr_left
    intro w hw
    exact secp256k1EEAOutputIdealState_preservesOutside s w (by simp at hw; dsimp only [Wire] at *; omega)
  refine ⟨?_,ho.2.2.2.2 558 (by decide +kernel),ho.2.2.2.2 560 (by decide +kernel),
    ho.2.2.2.2 561 (by decide +kernel),ho.2.2.2.1,?_⟩
  · intro w hw
    exact ho.2.2.1 w (by simp at hw ⊢; omega)
  · rw [hword]; exact hs.2
private theorem coherent_strengthen {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State} {Valid Stronger : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid) (hsub : ∀ s, Stronger s → Valid s) :
    CoherentlyImplementsOn program ideal Stronger := by
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (hsub s hs)),hm⟩
private theorem basis_lift_ket (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by simp [ket]
attribute [local irreducible] secp256k1EEAOutputIdealState fig15WorkProductState

/-- The division prefix coherently writes the quotient product while preserving the future transcript input. -/
theorem fig15DivisionPrefix_coherent :
    CoherentlyImplementsOn (secp256k1EEAForwardWrapper.seq fig15MultiplyToWork)
      (Finsupp.lmapDomain ℂ ℂ (fun s => fig15WorkProductState (secp256k1EEAOutputIdealState s)))
      Secp256k1InPlaceInputValid := by
  have hf := coherent_strengthen secp256k1EEAForwardWrapper_coherent
    (Stronger := Secp256k1InPlaceInputValid) (fun s hs => hs.1)
  have hc := hf.seq fig15MultiplyToWork_coherent (by
    intro s hs
    rw [basis_lift_ket]
    exact supportedOn_ket _ _ (fig15_after_eea_horner s hs))
  apply hc.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,basis_lift_ket]
/-- The multiplication prefix uses the same product circuit on valid Figure 15 inputs. -/
theorem fig15MultiplicationPrefix_coherent :
    CoherentlyImplementsOn fig15MultiplyToWork
      (Finsupp.lmapDomain ℂ ℂ fig15WorkProductState) Secp256k1InPlaceInputValid :=
  coherent_strengthen fig15MultiplyToWork_coherent fig15_initial_horner
private theorem clear_outside (targets : List Wire) (s : BasisState) (w : Wire)
    (hw : w ∉ targets) : clearRegister targets s w = s w := by
  induction targets generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.mem_cons,not_or] at hw
    rw [clearRegister,ih _ hw.2]
    exact upd_other s a false hw.1
attribute [local irreducible] clearRegister
private theorem divisionReset_live (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    ∀ w, w < 580 →
      relabelBasis eeaWorkspaceExchange.symm
        (clearRegister (List.range' 580 256)
          (fig15WorkProductState (secp256k1EEAOutputIdealState s))) w =
      secp256k1EEAOutputIdealState s w := by
  have he := secp256k1EEAOutputIdealState_correct s hs.1.1 hs.1.2.1 hs.1.2.2
  have hm := fig15WorkProductState_correct _ (fig15_after_eea_horner s hs)
  intro w hw
  simp only [relabelBasis,Equiv.symm_symm]
  by_cases ha : 7 ≤ w ∧ w < 263
  · have hi : w - 7 < 256 := by dsimp only [Wire] at *; omega
    have heq : w = 7 + (w - 7) := by dsimp only [Wire] at *; omega
    have hwx : eeaWorkspaceExchange w = 580 + (w - 7) := by
      conv_lhs => rw [heq]
      exact eeaWorkspaceExchange_work _ hi
    have hmem : 580 + (w - 7) ∈ List.range' 580 256 :=
      List.mem_range'.mpr ⟨w-7,hi,by simp⟩
    rw [hwx,clearRegister_clean (List.range' 580 256) _ _ hmem]
    exact (he.2.2.1 w (by simp; dsimp only [Wire] at *; omega)).symm
  · have hy : ¬ (580 ≤ w ∧ w < 836) := by dsimp only [Wire] at *; omega
    rw [eeaWorkspaceExchange_frame w ha hy]
    rw [clear_outside _ _ w (by simp; dsimp only [Wire] at *; omega)]
    exact hm.2 w (by simpa using ha)

/-- After quotient accumulation and Y reset, the inverse borrowing Y has a valid live EEA image. -/
theorem fig15DivisionReset_inverseReady (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    Secp256k1EEAForwardLocalImage
      (relabelBasis eeaWorkspaceExchange.symm
        (clearRegister (List.range' 580 256)
          (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) :=
  ⟨s,hs.1,divisionReset_live s hs⟩

/-- Deterministic state immediately after the division continuation restores X using the Y workspace. -/
def fig15DivisionRestoredState (s : BasisState) : BasisState :=
  relabelBasis eeaWorkspaceExchange (secp256k1EEAReverseWrapperIdealState
    (relabelBasis eeaWorkspaceExchange.symm (clearRegister (List.range' 580 256)
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)))))
private theorem exchange_symm (w : Wire) : eeaWorkspaceExchange.symm w = eeaWorkspaceExchange w := rfl
attribute [local irreducible] secp256k1EEAReverseWrapperIdealState eeaWorkspaceExchange
/-- Restoration changes only A to the quotient and Y to zero; every other original wire is restored. -/
theorem fig15DivisionRestoredState_eq (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    fig15DivisionRestoredState s = fun w =>
      if w ∈ List.range' 7 256 then fig15WorkProductState (secp256k1EEAOutputIdealState s) w
      else if w ∈ List.range' 580 256 then false else s w := by
  have hr := secp256k1EEAReverseWrapper_output_localImage _ s hs.1 (divisionReset_live s hs)
  have hm := fig15WorkProductState_correct _ (fig15_after_eea_horner s hs)
  funext w
  unfold fig15DivisionRestoredState
  rw [hr]
  simp only [relabelBasis,Equiv.symm_symm,Equiv.apply_symm_apply]
  rw [exchange_symm]
  by_cases ha : w ∈ List.range' 7 256
  · have hb : 7 ≤ w ∧ w < 263 := by simpa using ha
    have hi : w-7 < 256 := by dsimp only [Wire] at *; omega
    have hwx : eeaWorkspaceExchange w = 580 + (w-7) := by
      have heq : w = 7+(w-7) := by dsimp only [Wire] at *; omega
      conv_lhs => rw [heq]
      exact eeaWorkspaceExchange_work _ hi
    rw [hwx,if_neg (by dsimp only [Wire] at *; omega),if_pos ha]
    exact clear_outside _ _ w (by simp; dsimp only [Wire] at *; omega)
  · rw [if_neg ha]
    by_cases hy : w ∈ List.range' 580 256
    · have hb : 580 ≤ w ∧ w < 836 := by simpa using hy
      have hi : w-580 < 256 := by dsimp only [Wire] at *; omega
      have hwx : eeaWorkspaceExchange w = 7 + (w-580) := by
        have heq : w = 580+(w-580) := by dsimp only [Wire] at *; omega
        conv_lhs => rw [heq]
        exact eeaWorkspaceExchange_data _ hi
      rw [hwx,if_pos (by dsimp only [Wire] at *; omega),if_pos hy]
      exact hs.1.1 _ (by simp; dsimp only [Wire] at *; omega)
    · rw [if_neg hy,eeaWorkspaceExchange_frame w (by simpa using ha) (by simpa using hy)]
      by_cases hw : w < 580
      · rw [if_pos hw]
      · rw [if_neg hw,clear_outside _ _ w hy,hm.2 w ha]
        exact secp256k1EEAOutputIdealState_preservesOutside s w (Nat.le_of_not_gt hw)
private theorem restored_A_word (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    wireValues (List.range' 7 256) (fig15DivisionRestoredState s) =
      wireValues (List.range' 7 256) (fig15WorkProductState (secp256k1EEAOutputIdealState s)) := by
  apply List.map_congr_left
  intro w hw
  simp only [fig15DivisionRestoredState_eq s hs,if_pos hw]
private theorem restored_X_word (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    wireValues (List.range' 263 256) (fig15DivisionRestoredState s) =
      wireValues (List.range' 263 256) s := by
  apply List.map_congr_left
  intro w hw
  have ha : w ∉ List.range' 7 256 := by simp at hw ⊢; omega
  have hy : w ∉ List.range' 580 256 := by simp at hw ⊢; omega
  simp only [fig15DivisionRestoredState_eq s hs,if_neg ha,if_neg hy]
private theorem restored_horner (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    HornerInputValid (List.range' 7 256) (List.range' 580 256) ShorECDLP.p 558 560 561 559
      (fig15DivisionRestoredState s) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    have ha : w ∉ List.range' 7 256 := by simp at hw ⊢; omega
    simp only [fig15DivisionRestoredState_eq s hs,if_neg ha,if_pos hw]
  · simpa [fig15DivisionRestoredState_eq s hs] using hs.1.1 558 (by decide +kernel)
  · simpa [fig15DivisionRestoredState_eq s hs] using hs.1.1 560 (by decide +kernel)
  · simpa [fig15DivisionRestoredState_eq s hs] using hs.1.1 561 (by decide +kernel)
  · simpa [fig15DivisionRestoredState_eq s hs] using hs.1.1 559 (by decide +kernel)
  · rw [restored_A_word s hs,(fig15WorkProductState_correct _ (fig15_after_eea_horner s hs)).1]
    exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
/-- Recomputing Y from the restored X and retained quotient exactly recovers the measured word. -/
theorem fig15DivisionRecompute_word (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    boolWordToNat (wireValues (List.range' 580 256)
      (fig15DataProductState (fig15DivisionRestoredState s))) =
      boolWordToNat (wireValues (List.range' 580 256) s) := by
  have he := secp256k1EEAOutputIdealState_correct s hs.1.1 hs.1.2.1 hs.1.2.2
  have hY : wireValues (List.range' 580 256) (secp256k1EEAOutputIdealState s) =
      wireValues (List.range' 580 256) s := by
    apply List.map_congr_left
    intro w hw
    exact secp256k1EEAOutputIdealState_preservesOutside s w
      (by simp at hw; dsimp only [Wire] at *; omega)
  rw [(fig15DataProductState_correct _ (restored_horner s hs)).1,restored_A_word s hs,
    restored_X_word s hs,(fig15WorkProductState_correct _ (fig15_after_eea_horner s hs)).1,hY,he.1]
  have hinv : (paperInverse ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s)) *
      boolWordToNat (wireValues (List.range' 263 256) s)) % ShorECDLP.p = 1 := by
    have h := he.2.1
    rw [he.1] at h
    have hv := congrArg ZMod.val h
    simpa only [← Nat.cast_mul,ZMod.val_natCast,ZMod.val_one] using hv
  rw [Nat.mod_mul_mod,Nat.mul_assoc,Nat.mul_mod _ (_ * _) _,hinv,Nat.mul_one,Nat.mod_mod]
  exact Nat.mod_eq_of_lt hs.2

/-- The recomputation restores every measured bit, not just its modular residue. -/
theorem fig15DivisionRecompute_bits (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    wireValues (List.range' 580 256) (fig15DataProductState (fig15DivisionRestoredState s)) =
      wireValues (List.range' 580 256) s :=
  boolWordToNat_injective_of_length (by simp only [wireValues,List.length_map])
    (fig15DivisionRecompute_word s hs)
private theorem phase_congr (targets : List Wire) (outcomes : List Bool) (s t : BasisState)
    (h : wireValues targets s = wireValues targets t) :
    registerXPhase targets outcomes s = registerXPhase targets outcomes t := by
  induction targets generalizing outcomes with
  | nil => rfl
  | cons w ws ih =>
    cases outcomes with
    | nil => rfl
    | cons b bs =>
      simp only [wireValues,List.map_cons,List.cons.injEq] at h
      simp only [registerXPhase,h.1,ih bs h.2]
/-- The actual selected Z correction reproduces the measurement sign for every transcript. -/
theorem fig15DivisionRecompute_phase (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    Quantum.run (registerZCorrection (List.range' 580 256) outcomes)
      (ket (fig15DataProductState (fig15DivisionRestoredState s))) =
      registerXPhase (List.range' 580 256) outcomes s •
        ket (fig15DataProductState (fig15DivisionRestoredState s)) := by
  rw [run_registerZCorrection_ket,phase_congr _ outcomes _ s (fig15DivisionRecompute_bits s hs)]

private theorem swap_three (a b : Wire) (hab : a ≠ b) (s : BasisState) :
    Classical.run [.CX a b,.CX b a,.CX a b] s =
      fun w => if w=a then s b else if w=b then s a else s w := by
  funext w
  by_cases ha : w=a
  · subst w
    cases hsa : s a <;> cases hsb : s b <;> simp [Classical.run,Classical.applyGate,upd,hab,Ne.symm hab,hsa,hsb]
  · by_cases hb : w=b
    · subst w
      simp [Classical.run,Classical.applyGate,upd,hab,Ne.symm hab]
    · simp [Classical.run,Classical.applyGate,upd,ha,hb]
private def swapPrefix (n : Nat) : Circuit :=
  (List.range n).flatMap fun i => [.CX (580+i) (7+i),.CX (7+i) (580+i),.CX (580+i) (7+i)]
private theorem swapPrefix_run (n : Nat) (hn : n ≤ 256) (s : BasisState) :
    Classical.run (swapPrefix n) s = fun w =>
      if 7 ≤ w ∧ w < 7+n then s (w+573)
      else if 580 ≤ w ∧ w < 580+n then s (w-573) else s w := by
  induction n with
  | zero =>
    funext w
    simp only [swapPrefix,List.range_zero,List.flatMap_nil,Classical.run_nil]
    dsimp only [Wire]
    split_ifs <;> first | omega | rfl
  | succ n ih =>
    have hh := ih (by omega)
    simp only [swapPrefix,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,Classical.run_append]
    rw [swap_three _ _ (by dsimp only [Wire]; omega),show Classical.run ((List.range n).flatMap
      (fun i => [.CX (580+i) (7+i),.CX (7+i) (580+i),.CX (580+i) (7+i)])) s = _ from hh]
    funext w
    dsimp only [Wire] at *
    split_ifs <;> first | omega | (apply congrArg s; dsimp only [Wire] at * <;> omega)
/-- The literal final source swaps exchange A and Y and preserve the complete remaining frame. -/
theorem fig15SwapOutput_run (s : BasisState) :
    Classical.run fig15SwapOutput s = fun w =>
      if w ∈ List.range' 7 256 then s (w+573)
      else if w ∈ List.range' 580 256 then s (w-573) else s w := by
  simpa only [swapPrefix,fig15SwapOutput,List.mem_range'_1] using swapPrefix_run 256 (by omega) s

end
end ShorECDLP.Paper2607_13816
