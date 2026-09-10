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

/-- State after multiplication has accumulated its product and borrowed Y for inversion. -/
def fig15MultiplicationInvertedState (s : BasisState) : BasisState :=
  relabelBasis eeaWorkspaceExchange (secp256k1EEAOutputIdealState
    (relabelBasis eeaWorkspaceExchange.symm
      (clearRegister (List.range' 580 256) (fig15WorkProductState s))))
private theorem multiplication_reset_input (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    Secp256k1EEAInputValid (relabelBasis eeaWorkspaceExchange.symm
      (clearRegister (List.range' 580 256) (fig15WorkProductState s))) := by
  have hm := fig15WorkProductState_correct s (fig15_initial_horner s hs)
  have hframe (w : Wire) (hw : w ∉ List.range' 7 256) (hy : w ∉ List.range' 580 256) :
      relabelBasis eeaWorkspaceExchange.symm
        (clearRegister (List.range' 580 256) (fig15WorkProductState s)) w = s w := by
    simp only [relabelBasis,Equiv.symm_symm,eeaWorkspaceExchange_frame w (by simpa using hw) (by simpa using hy)]
    rw [clear_outside _ _ w hy,hm.2 w hw]
  have hx : wireValues (List.range' 263 256)
      (relabelBasis eeaWorkspaceExchange.symm
        (clearRegister (List.range' 580 256) (fig15WorkProductState s))) =
      wireValues (List.range' 263 256) s := by
    apply List.map_congr_left
    intro w hw
    exact hframe w (by simp at hw ⊢; omega) (by simp at hw ⊢; omega)
  refine ⟨?_,?_,?_⟩
  · intro w hw
    by_cases ha : w ∈ List.range' 7 256
    · have hh : w = 7+(w-7) := by simp at ha; dsimp only [Wire] at *; omega
      have hi : w-7 <256 := by simp at ha; dsimp only [Wire] at *; omega
      simp only [relabelBasis,Equiv.symm_symm]
      have he : eeaWorkspaceExchange w = 580+(w-7) := by
        calc
          eeaWorkspaceExchange w = eeaWorkspaceExchange (7+(w-7)) := congrArg _ hh
          _ = _ := eeaWorkspaceExchange_work _ hi
      rw [he]
      exact clearRegister_clean (List.range' 580 256) _ (580+(w-7)) (by simp only [List.mem_range'_1]; dsimp only [Wire] at *; omega)
    · rw [hframe w ha (by simp at hw ⊢; dsimp only [Wire] at *; omega)]
      exact hs.1.1 w hw
  · rw [hx]; exact hs.1.2.1
  · rw [hx]; exact hs.1.2.2
private theorem multiplication_inverted_A (s : BasisState) (w : Wire)
    (hw : w ∈ List.range' 7 256) :
    fig15MultiplicationInvertedState s w = fig15WorkProductState s w := by
  have hi : w-7 <256 := by simp at hw; dsimp only [Wire] at *; omega
  have he : eeaWorkspaceExchange w = 580+(w-7) := by
    calc
      eeaWorkspaceExchange w = eeaWorkspaceExchange (7+(w-7)) := congrArg _ (by simp at hw; dsimp only [Wire] at *; omega)
      _ = _ := eeaWorkspaceExchange_work _ hi
  have hee : eeaWorkspaceExchange (eeaWorkspaceExchange w) = w := by
    rw [← exchange_symm]; exact eeaWorkspaceExchange.symm_apply_apply w
  simp only [fig15MultiplicationInvertedState,relabelBasis,exchange_symm]
  rw [secp256k1EEAOutputIdealState_preservesOutside _ _ (by rw [he]; dsimp only [Wire]; omega)]
  simp only [relabelBasis,Equiv.symm_symm,hee]
  exact clear_outside _ _ w (by simp at hw ⊢; omega)
private theorem multiplication_reset_X (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    wireValues (List.range' 263 256)
      (relabelBasis eeaWorkspaceExchange.symm
        (clearRegister (List.range' 580 256) (fig15WorkProductState s))) =
      wireValues (List.range' 263 256) s := by
  apply List.map_congr_left
  intro w hw
  have ha : w ∉ List.range' 7 256 := by simp at hw ⊢; omega
  have hy : w ∉ List.range' 580 256 := by simp at hw ⊢; omega
  simp only [relabelBasis,Equiv.symm_symm,eeaWorkspaceExchange_frame w (by simpa using ha) (by simpa using hy)]
  rw [clear_outside _ _ w hy]
  exact (fig15WorkProductState_correct s (fig15_initial_horner s hs)).2 w ha
private theorem multiplication_inverted_X (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    boolWordToNat (wireValues (List.range' 263 256) (fig15MultiplicationInvertedState s)) =
      paperInverse ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s)) := by
  have hv := multiplication_reset_input s hs
  have he := secp256k1EEAOutputIdealState_correct _ hv.1 hv.2.1 hv.2.2
  have hx : wireValues (List.range' 263 256) (fig15MultiplicationInvertedState s) =
      wireValues (List.range' 263 256) (secp256k1EEAOutputIdealState
        (relabelBasis eeaWorkspaceExchange.symm
          (clearRegister (List.range' 580 256) (fig15WorkProductState s)))) := by
    apply List.map_congr_left
    intro w hw
    simp only [fig15MultiplicationInvertedState,relabelBasis,exchange_symm]
    rw [eeaWorkspaceExchange_frame w (by simp at hw ⊢; dsimp only [Wire] at *; omega) (by simp at hw ⊢; dsimp only [Wire] at *; omega)]
  rw [hx,he.1,multiplication_reset_X s hs]
private theorem multiplication_inverted_horner (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    HornerInputValid (List.range' 7 256) (List.range' 580 256) ShorECDLP.p 558 560 561 559
      (fig15MultiplicationInvertedState s) := by
  have hv := multiplication_reset_input s hs
  have he := secp256k1EEAOutputIdealState_correct _ hv.1 hv.2.1 hv.2.2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    have hi : w-580 <256 := by simp at hw; dsimp only [Wire] at *; omega
    have hew : eeaWorkspaceExchange w = 7+(w-580) := by
      calc
        eeaWorkspaceExchange w = eeaWorkspaceExchange (580+(w-580)) := congrArg _ (by simp at hw; dsimp only [Wire] at *; omega)
        _ = _ := eeaWorkspaceExchange_data _ hi
    simp only [fig15MultiplicationInvertedState,relabelBasis,exchange_symm,hew]
    exact he.2.2.1 _ (by simp only [List.mem_range'_1]; dsimp only [Wire] at *; omega)
  · simpa only [fig15MultiplicationInvertedState,relabelBasis,exchange_symm,
      eeaWorkspaceExchange_frame 558 (by decide) (by decide)] using he.2.2.2.2 558 (by decide +kernel)
  · simpa only [fig15MultiplicationInvertedState,relabelBasis,exchange_symm,
      eeaWorkspaceExchange_frame 560 (by decide) (by decide)] using he.2.2.2.2 560 (by decide +kernel)
  · simpa only [fig15MultiplicationInvertedState,relabelBasis,exchange_symm,
      eeaWorkspaceExchange_frame 561 (by decide) (by decide)] using he.2.2.2.2 561 (by decide +kernel)
  · simpa only [fig15MultiplicationInvertedState,relabelBasis,exchange_symm,
      eeaWorkspaceExchange_frame 559 (by decide) (by decide)] using he.2.2.2.1
  · have ha : wireValues (List.range' 7 256) (fig15MultiplicationInvertedState s) =
        wireValues (List.range' 7 256) (fig15WorkProductState s) := by
      apply List.map_congr_left
      intro w hw
      exact multiplication_inverted_A s w hw
    rw [ha,(fig15WorkProductState_correct s (fig15_initial_horner s hs)).1]
    exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
/-- The product multiplied by the borrowed-bank inverse recovers the measured Y exactly. -/
theorem fig15MultiplicationRecompute_word (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    boolWordToNat (wireValues (List.range' 580 256)
      (fig15DataProductState (fig15MultiplicationInvertedState s))) =
      boolWordToNat (wireValues (List.range' 580 256) s) := by
  have hv := multiplication_reset_input s hs
  have he := secp256k1EEAOutputIdealState_correct _ hv.1 hv.2.1 hv.2.2
  have hinv : (boolWordToNat (wireValues (List.range' 263 256) s) *
      paperInverse ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))) % ShorECDLP.p = 1 := by
    have h := he.2.1
    rw [he.1,multiplication_reset_X s hs] at h
    have hh := congrArg ZMod.val h
    have hm : (paperInverse ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s)) *
        boolWordToNat (wireValues (List.range' 263 256) s)) % ShorECDLP.p = 1 := by
      simpa only [← Nat.cast_mul,ZMod.val_natCast,ZMod.val_one] using hh
    rwa [Nat.mul_comm] at hm
  have ha : wireValues (List.range' 7 256) (fig15MultiplicationInvertedState s) =
      wireValues (List.range' 7 256) (fig15WorkProductState s) := by
    apply List.map_congr_left
    intro w hw
    exact multiplication_inverted_A s w hw
  rw [(fig15DataProductState_correct _ (multiplication_inverted_horner s hs)).1,
    ha,(fig15WorkProductState_correct s (fig15_initial_horner s hs)).1,multiplication_inverted_X s hs,
    Nat.mod_mul_mod,Nat.mul_assoc,Nat.mul_mod _ (_*_) _,hinv,Nat.mul_one,Nat.mod_mod]
  exact Nat.mod_eq_of_lt hs.2
/-- Exact word reconstruction yields equality of every measured bit. -/
theorem fig15MultiplicationRecompute_bits (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    wireValues (List.range' 580 256) (fig15DataProductState (fig15MultiplicationInvertedState s)) =
      wireValues (List.range' 580 256) s :=
  boolWordToNat_injective_of_length (by simp only [wireValues,List.length_map])
    (fig15MultiplicationRecompute_word s hs)
/-- The actual correction produces the original measurement sign on every transcript. -/
theorem fig15MultiplicationRecompute_phase (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    Quantum.run (registerZCorrection (List.range' 580 256) outcomes)
      (ket (fig15DataProductState (fig15MultiplicationInvertedState s))) =
      registerXPhase (List.range' 580 256) outcomes s •
        ket (fig15DataProductState (fig15MultiplicationInvertedState s)) := by
  rw [run_registerZCorrection_ket,phase_congr _ outcomes _ s (fig15MultiplicationRecompute_bits s hs)]

private def divisionResetValid (t : BasisState) : Prop :=
  ∃ s, Secp256k1InPlaceInputValid s ∧
    t = clearRegister (List.range' 580 256) (fig15WorkProductState (secp256k1EEAOutputIdealState s))
private def divisionRestoreMap : State →ₗ[ℂ] State :=
  (relabelState eeaWorkspaceExchange).comp
    ((Finsupp.lmapDomain ℂ ℂ secp256k1EEAReverseWrapperIdealState).comp
      (relabelState eeaWorkspaceExchange.symm))
private def divisionRecomputeMap : State →ₗ[ℂ] State :=
  (Finsupp.lmapDomain ℂ ℂ fig15DataProductState).comp divisionRestoreMap
private def divisionCorrectMap (outcomes : List Bool) : State →ₗ[ℂ] State :=
  (Quantum.run (registerZCorrection (List.range' 580 256) outcomes)).comp divisionRecomputeMap
private def divisionUncomputeMap (outcomes : List Bool) : State →ₗ[ℂ] State :=
  (Finsupp.lmapDomain ℂ ℂ (hornerClearOutput (List.range' 580 256))).comp (divisionCorrectMap outcomes)
private theorem division_restore_ket (s : BasisState) :
    divisionRestoreMap (ket (clearRegister (List.range' 580 256)
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      ket (fig15DivisionRestoredState s) := by
  simp only [divisionRestoreMap,LinearMap.comp_apply,relabelState_ket,basis_lift_ket,
    fig15DivisionRestoredState]
private theorem division_recompute_ket (s : BasisState) :
    divisionRecomputeMap (ket (clearRegister (List.range' 580 256)
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      ket (fig15DataProductState (fig15DivisionRestoredState s)) := by
  simp only [divisionRecomputeMap,LinearMap.comp_apply,division_restore_ket,basis_lift_ket]
private theorem division_correct_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    divisionCorrectMap outcomes (ket (clearRegister (List.range' 580 256)
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      registerXPhase (List.range' 580 256) outcomes s •
        ket (fig15DataProductState (fig15DivisionRestoredState s)) := by
  simp only [divisionCorrectMap,LinearMap.comp_apply,division_recompute_ket,
    fig15DivisionRecompute_phase s hs]
private theorem supported_phase {Valid : BasisState → Prop} (s : BasisState)
    (c : ℂ) (hs : Valid s) : SupportedOn Valid (c • ket s) := by
  intro t ht
  have hts : s=t := by
    by_contra h
    apply ht
    simp only [Finsupp.smul_apply,ket_ne h,smul_zero]
  subst t
  exact hs
private theorem division_uncompute_state (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    hornerClearOutput (List.range' 580 256)
      (fig15DataProductState (fig15DivisionRestoredState s)) = fig15DivisionRestoredState s := by
  funext w
  by_cases hw : w ∈ List.range' 580 256
  · simp only [hornerClearOutput,if_pos hw]
    exact ((restored_horner s hs).1 w hw).symm
  · simp only [hornerClearOutput,if_neg hw]
    exact (fig15DataProductState_correct _ (restored_horner s hs)).2 w hw
private theorem division_uncompute_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    divisionUncomputeMap outcomes (ket (clearRegister (List.range' 580 256)
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      registerXPhase (List.range' 580 256) outcomes s • ket (fig15DivisionRestoredState s) := by
  simp only [divisionUncomputeMap,LinearMap.comp_apply,division_correct_ket s hs,
    map_smul,basis_lift_ket,division_uncompute_state s hs]
private theorem division_continuation_coherent (outcomes : List Bool) :
    CoherentlyImplementsOn (fig15DivisionAfterReset outcomes)
      ((Quantum.run fig15SwapOutput).comp (divisionUncomputeMap outcomes)) divisionResetValid := by
  have hr : CoherentlyImplementsOn secp256k1EEAReverseInDataBank divisionRestoreMap divisionResetValid := by
    apply coherent_strengthen secp256k1EEAReverseInDataBank_coherent_localImage
    rintro t ⟨s,hs,rfl⟩
    exact fig15DivisionReset_inverseReady s hs
  have hm := hr.seq fig15MultiplyToData_coherent (by
    rintro t ⟨s,hs,rfl⟩
    rw [division_restore_ket]
    exact supportedOn_ket _ _ (restored_horner s hs))
  have hz := hm.seq (CoherentlyImplementsOn.unitary
    (registerZCorrection (List.range' 580 256) outcomes) (fun _ => True)) (by
      intro t ht u hu; trivial)
  have hi := hz.seq fig15MultiplyToDataInverse_coherent (by
    rintro t ⟨s,hs,rfl⟩
    change SupportedOn _ (divisionCorrectMap outcomes _)
    rw [division_correct_ket s hs]
    exact supported_phase _ _ ⟨fig15DivisionRestoredState s,restored_horner s hs,rfl⟩)
  exact hi.seq (CoherentlyImplementsOn.unitary fig15SwapOutput (fun _ => True))
    (by intro t ht u hu; trivial)
private def divisionPreparedValid (t : BasisState) : Prop :=
  ∃ s, Secp256k1InPlaceInputValid s ∧ t = fig15WorkProductState (secp256k1EEAOutputIdealState s)
private def divisionPreparedOutput (t : BasisState) : BasisState :=
  Classical.run fig15SwapOutput (relabelBasis eeaWorkspaceExchange
    (secp256k1EEAReverseWrapperIdealState (relabelBasis eeaWorkspaceExchange.symm
      (clearRegister (List.range' 580 256) t))))
private theorem division_prepared_phase (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    registerXPhase (List.range' 580 256) outcomes
      (fig15WorkProductState (secp256k1EEAOutputIdealState s)) =
      registerXPhase (List.range' 580 256) outcomes s := by
  apply phase_congr
  apply List.map_congr_left
  intro w hw
  rw [(fig15WorkProductState_correct _ (fig15_after_eea_horner s hs)).2 w (by simp at hw ⊢; omega)]
  exact secp256k1EEAOutputIdealState_preservesOutside s w (by simp at hw; dsimp only [Wire] at *; omega)
private def divisionWitness : BasisState := fun w => decide (w = 263)
private theorem divisionWitness_valid : Secp256k1InPlaceInputValid divisionWitness := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro w hw
    simp only [List.mem_append,List.mem_range'_1] at hw
    simp only [divisionWitness, decide_eq_false_iff_not]
    dsimp only [Wire] at *
    omega
  · decide +kernel
  · decide +kernel
  · decide +kernel
private theorem division_swap_hp : Classical.HPFree fig15SwapOutput := by
  intro g hg
  simp only [fig15SwapOutput,List.mem_flatMap] at hg
  obtain ⟨i,hi,hg⟩ := hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;> trivial
attribute [local irreducible] Classical.run Quantum.run relabelBasis measureResetThen fig15DivisionAfterReset
  divisionPreparedOutput divisionUncomputeMap
private theorem division_prepared_output (s : BasisState) :
    divisionPreparedOutput (fig15WorkProductState (secp256k1EEAOutputIdealState s)) =
      Classical.run fig15SwapOutput (fig15DivisionRestoredState s) := by
  delta divisionPreparedOutput fig15DivisionRestoredState
  exact Eq.refl _
private theorem division_final_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    ((Quantum.run fig15SwapOutput).comp (divisionUncomputeMap outcomes))
      (ket (clearRegister (List.range' 580 256) (fig15WorkProductState (secp256k1EEAOutputIdealState s)))) =
      registerXPhase (List.range' 580 256) outcomes s •
        ket (divisionPreparedOutput (fig15WorkProductState (secp256k1EEAOutputIdealState s))) := by
  rw [LinearMap.comp_apply,division_uncompute_ket s hs,map_smul,
    run_ket_agrees_classical _ _ division_swap_hp,division_prepared_output]
private theorem division_reset_correct (outcomes : List Bool) (t : BasisState)
    (ht : divisionPreparedValid t) :
    divisionResetValid (clearRegister (List.range' 580 256) t) ∧
    ((Quantum.run fig15SwapOutput).comp (divisionUncomputeMap outcomes))
      (ket (clearRegister (List.range' 580 256) t)) =
      registerXPhase (List.range' 580 256) outcomes t • ket (divisionPreparedOutput t) := by
  obtain ⟨s,hs,rfl⟩ := ht
  refine ⟨⟨s,hs,rfl⟩,?_⟩
  rw [division_prepared_phase s hs]
  exact division_final_ket s hs outcomes
private theorem division_reset_coherent :
    CoherentlyImplementsOn (measureResetThen (List.range' 580 256) fig15DivisionAfterReset)
      (Finsupp.lmapDomain ℂ ℂ divisionPreparedOutput) divisionPreparedValid :=
  measureResetThen_coherent (List.range' 580 256) fig15DivisionAfterReset
    (fun outcomes => (Quantum.run fig15SwapOutput).comp (divisionUncomputeMap outcomes))
    (fun _ => divisionResetValid) divisionPreparedValid divisionPreparedOutput List.nodup_range'
    (fun outcomes _ => division_continuation_wellFormed outcomes)
    division_continuation_coherent (fun outcomes _ t ht => division_reset_correct outcomes t ht)
    (fig15WorkProductState (secp256k1EEAOutputIdealState divisionWitness))
    ⟨divisionWitness,divisionWitness_valid,rfl⟩
/-- Complete ideal output of the literal Figure 15 division, including its final bank swap. -/
def fig15DivisionOutputState (s : BasisState) : BasisState :=
  Classical.run fig15SwapOutput (fig15DivisionRestoredState s)
/-- Every transcript of the actual full division implements one common linear map,
with normalized coefficients independent of the valid input. -/
theorem secp256k1InPlaceDivision_coherent :
    CoherentlyImplementsOn secp256k1InPlaceDivision
      (Finsupp.lmapDomain ℂ ℂ fig15DivisionOutputState) Secp256k1InPlaceInputValid := by
  have h := fig15DivisionPrefix_coherent.seq division_reset_coherent (by
    intro s hs
    rw [basis_lift_ket]
    exact supportedOn_ket _ _ ⟨s,hs,rfl⟩)
  apply h.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,basis_lift_ket]
  delta divisionPreparedOutput fig15DivisionOutputState fig15DivisionRestoredState
  rfl
/-- Division changes only Y: the work bank is restored to its original clean value. -/
theorem fig15DivisionOutputState_eq (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    fig15DivisionOutputState s = fun w =>
      if w ∈ List.range' 580 256 then
        fig15WorkProductState (secp256k1EEAOutputIdealState s) (w-573)
      else s w := by
  funext w
  rw [fig15DivisionOutputState,fig15SwapOutput_run]
  by_cases ha : w ∈ List.range' 7 256
  · have hy : w ∉ List.range' 580 256 := by simp at ha ⊢; omega
    have hy' : w+573 ∈ List.range' 580 256 := by simp at ha ⊢; dsimp only [Wire] at *; omega
    have ha' : w+573 ∉ List.range' 7 256 := by simp
    simp only [if_pos ha,if_neg hy,fig15DivisionRestoredState_eq s hs,if_neg ha',if_pos hy']
    exact (hs.1.1 w (by simp at ha ⊢; omega)).symm
  · by_cases hy : w ∈ List.range' 580 256
    · have ha' : w-573 ∈ List.range' 7 256 := by simp at hy ⊢; dsimp only [Wire] at *; omega
      simp only [if_neg ha,if_pos hy,fig15DivisionRestoredState_eq s hs,if_pos ha']
    · simp only [if_neg ha,if_neg hy,fig15DivisionRestoredState_eq s hs]
/-- The concrete output register contains Y/X modulo the secp256k1 prime. -/
theorem fig15DivisionOutputState_word (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    boolWordToNat (wireValues (List.range' 580 256) (fig15DivisionOutputState s)) =
      (boolWordToNat (wireValues (List.range' 580 256) s) *
        paperInverse ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))) % ShorECDLP.p := by
  have hbits : wireValues (List.range' 580 256) (fig15DivisionOutputState s) =
      wireValues (List.range' 7 256) (fig15WorkProductState (secp256k1EEAOutputIdealState s)) := by
    have hmap : List.map (fun w : Nat => w-573) (List.range' 580 256) = List.range' 7 256 :=
      List.map_sub_range' (by omega) 256
    simp only [wireValues]
    rw [← hmap,List.map_map]
    apply List.map_congr_left
    intro w hw
    simp only [fig15DivisionOutputState_eq s hs,if_pos hw,Function.comp_apply]
  rw [hbits,(fig15WorkProductState_correct _ (fig15_after_eea_horner s hs)).1]
  have hY : wireValues (List.range' 580 256) (secp256k1EEAOutputIdealState s) =
      wireValues (List.range' 580 256) s := by
    apply List.map_congr_left
    intro w hw
    exact secp256k1EEAOutputIdealState_preservesOutside s w (by simp at hw; dsimp only [Wire] at *; omega)
  rw [hY,(secp256k1EEAOutputIdealState_correct s hs.1.1 hs.1.2.1 hs.1.2.2).1]

private def multiplicationResetValid (t : BasisState) : Prop :=
  ∃ s, Secp256k1InPlaceInputValid s ∧ t = clearRegister (List.range' 580 256) (fig15WorkProductState s)
private def multiplicationInvertMap : State →ₗ[ℂ] State :=
  (relabelState eeaWorkspaceExchange).comp
    ((Finsupp.lmapDomain ℂ ℂ secp256k1EEAOutputIdealState).comp (relabelState eeaWorkspaceExchange.symm))
private def multiplicationRecomputeMap : State →ₗ[ℂ] State :=
  (Finsupp.lmapDomain ℂ ℂ fig15DataProductState).comp multiplicationInvertMap
private def multiplicationCorrectMap (outcomes : List Bool) : State →ₗ[ℂ] State :=
  (Quantum.run (registerZCorrection (List.range' 580 256) outcomes)).comp multiplicationRecomputeMap
private def multiplicationUncomputeMap (outcomes : List Bool) : State →ₗ[ℂ] State :=
  (Finsupp.lmapDomain ℂ ℂ (hornerClearOutput (List.range' 580 256))).comp (multiplicationCorrectMap outcomes)
private def multiplicationRestoreMap (outcomes : List Bool) : State →ₗ[ℂ] State :=
  divisionRestoreMap.comp (multiplicationUncomputeMap outcomes)
private theorem multiplication_invert_ket (s : BasisState) :
    multiplicationInvertMap (ket (clearRegister (List.range' 580 256) (fig15WorkProductState s))) =
      ket (fig15MultiplicationInvertedState s) := by
  simp only [multiplicationInvertMap,LinearMap.comp_apply,relabelState_ket,basis_lift_ket,
    fig15MultiplicationInvertedState]
private theorem multiplication_recompute_ket (s : BasisState) :
    multiplicationRecomputeMap (ket (clearRegister (List.range' 580 256) (fig15WorkProductState s))) =
      ket (fig15DataProductState (fig15MultiplicationInvertedState s)) := by
  simp only [multiplicationRecomputeMap,LinearMap.comp_apply,multiplication_invert_ket,basis_lift_ket]
private theorem multiplication_correct_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    multiplicationCorrectMap outcomes (ket (clearRegister (List.range' 580 256) (fig15WorkProductState s))) =
      registerXPhase (List.range' 580 256) outcomes s •
        ket (fig15DataProductState (fig15MultiplicationInvertedState s)) := by
  simp only [multiplicationCorrectMap,LinearMap.comp_apply,multiplication_recompute_ket,
    fig15MultiplicationRecompute_phase s hs]
private theorem multiplication_uncompute_state (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    hornerClearOutput (List.range' 580 256)
      (fig15DataProductState (fig15MultiplicationInvertedState s)) = fig15MultiplicationInvertedState s := by
  funext w
  by_cases hw : w ∈ List.range' 580 256
  · simp only [hornerClearOutput,if_pos hw]
    exact ((multiplication_inverted_horner s hs).1 w hw).symm
  · simp only [hornerClearOutput,if_neg hw]
    exact (fig15DataProductState_correct _ (multiplication_inverted_horner s hs)).2 w hw
private theorem multiplication_uncompute_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    multiplicationUncomputeMap outcomes (ket (clearRegister (List.range' 580 256) (fig15WorkProductState s))) =
      registerXPhase (List.range' 580 256) outcomes s • ket (fig15MultiplicationInvertedState s) := by
  simp only [multiplicationUncomputeMap,LinearMap.comp_apply,multiplication_correct_ket s hs,
    map_smul,basis_lift_ket,multiplication_uncompute_state s hs]
private theorem bank_relabel_cancel (e : Wire ≃ Wire) (s : BasisState) :
    relabelBasis e.symm (relabelBasis e s) = s := by
  funext w
  simp only [relabelBasis,Equiv.symm_symm,Equiv.symm_apply_apply]
private theorem multiplication_inverse_ready (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    Secp256k1EEAForwardLocalImage (relabelBasis eeaWorkspaceExchange.symm (fig15MultiplicationInvertedState s)) := by
  rw [fig15MultiplicationInvertedState,bank_relabel_cancel]
  exact ⟨_,multiplication_reset_input s hs,fun _ _ => rfl⟩
private theorem multiplication_inverse_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    divisionRestoreMap (ket (fig15MultiplicationInvertedState s)) =
      ket (clearRegister (List.range' 580 256) (fig15WorkProductState s)) := by
  simp only [divisionRestoreMap,LinearMap.comp_apply,relabelState_ket,basis_lift_ket]
  rw [fig15MultiplicationInvertedState,bank_relabel_cancel,
    secp256k1EEAReverseWrapper_output _ (multiplication_reset_input s hs)]
  have hc := bank_relabel_cancel eeaWorkspaceExchange.symm
    (clearRegister (List.range' 580 256) (fig15WorkProductState s))
  simpa only [Equiv.symm_symm] using congrArg ket hc
private theorem multiplication_restore_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    multiplicationRestoreMap outcomes (ket (clearRegister (List.range' 580 256) (fig15WorkProductState s))) =
      registerXPhase (List.range' 580 256) outcomes s •
        ket (clearRegister (List.range' 580 256) (fig15WorkProductState s)) := by
  simp only [multiplicationRestoreMap,LinearMap.comp_apply,multiplication_uncompute_ket s hs,
    map_smul,multiplication_inverse_ket s hs]
private theorem multiplication_continuation_coherent (outcomes : List Bool) :
    CoherentlyImplementsOn (fig15MultiplicationAfterReset outcomes)
      ((Quantum.run fig15SwapOutput).comp (multiplicationRestoreMap outcomes)) multiplicationResetValid := by
  have hf : CoherentlyImplementsOn secp256k1EEAForwardInDataBank multiplicationInvertMap multiplicationResetValid := by
    apply coherent_strengthen secp256k1EEAForwardInDataBank_coherent
    rintro t ⟨s,hs,rfl⟩
    exact multiplication_reset_input s hs
  have hm := hf.seq fig15MultiplyToData_coherent (by
    rintro t ⟨s,hs,rfl⟩
    rw [multiplication_invert_ket]
    exact supportedOn_ket _ _ (multiplication_inverted_horner s hs))
  have hz := hm.seq (CoherentlyImplementsOn.unitary
    (registerZCorrection (List.range' 580 256) outcomes) (fun _ => True)) (by
      intro t ht u hu; trivial)
  have hi := hz.seq fig15MultiplyToDataInverse_coherent (by
    rintro t ⟨s,hs,rfl⟩
    change SupportedOn _ (multiplicationCorrectMap outcomes _)
    rw [multiplication_correct_ket s hs]
    exact supported_phase _ _ ⟨fig15MultiplicationInvertedState s,multiplication_inverted_horner s hs,rfl⟩)
  have hr := hi.seq secp256k1EEAReverseInDataBank_coherent_localImage (by
    rintro t ⟨s,hs,rfl⟩
    change SupportedOn _ (multiplicationUncomputeMap outcomes _)
    rw [multiplication_uncompute_ket s hs]
    exact supported_phase _ _ (multiplication_inverse_ready s hs))
  exact hr.seq (CoherentlyImplementsOn.unitary fig15SwapOutput (fun _ => True))
    (by intro t ht u hu; trivial)
private def multiplicationPreparedValid (t : BasisState) : Prop :=
  ∃ s, Secp256k1InPlaceInputValid s ∧ t = fig15WorkProductState s
private def multiplicationPreparedOutput (t : BasisState) : BasisState :=
  Classical.run fig15SwapOutput (clearRegister (List.range' 580 256) t)
private theorem multiplication_prepared_phase (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    registerXPhase (List.range' 580 256) outcomes (fig15WorkProductState s) =
      registerXPhase (List.range' 580 256) outcomes s := by
  apply phase_congr
  apply List.map_congr_left
  intro w hw
  exact (fig15WorkProductState_correct s (fig15_initial_horner s hs)).2 w (by simp at hw ⊢; omega)
attribute [local irreducible] fig15MultiplicationAfterReset multiplicationPreparedOutput
private theorem multiplication_final_ket (s : BasisState) (hs : Secp256k1InPlaceInputValid s)
    (outcomes : List Bool) :
    ((Quantum.run fig15SwapOutput).comp (multiplicationRestoreMap outcomes))
      (ket (clearRegister (List.range' 580 256) (fig15WorkProductState s))) =
      registerXPhase (List.range' 580 256) outcomes s •
        ket (multiplicationPreparedOutput (fig15WorkProductState s)) := by
  rw [LinearMap.comp_apply,multiplication_restore_ket s hs,map_smul,
    run_ket_agrees_classical _ _ division_swap_hp,multiplicationPreparedOutput]
private theorem multiplication_reset_correct (outcomes : List Bool) (t : BasisState)
    (ht : multiplicationPreparedValid t) :
    multiplicationResetValid (clearRegister (List.range' 580 256) t) ∧
    ((Quantum.run fig15SwapOutput).comp (multiplicationRestoreMap outcomes))
      (ket (clearRegister (List.range' 580 256) t)) =
      registerXPhase (List.range' 580 256) outcomes t • ket (multiplicationPreparedOutput t) := by
  obtain ⟨s,hs,rfl⟩ := ht
  refine ⟨⟨s,hs,rfl⟩,?_⟩
  rw [multiplication_prepared_phase s hs]
  exact multiplication_final_ket s hs outcomes
private theorem multiplication_reset_coherent :
    CoherentlyImplementsOn (measureResetThen (List.range' 580 256) fig15MultiplicationAfterReset)
      (Finsupp.lmapDomain ℂ ℂ multiplicationPreparedOutput) multiplicationPreparedValid :=
  measureResetThen_coherent (List.range' 580 256) fig15MultiplicationAfterReset
    (fun outcomes => (Quantum.run fig15SwapOutput).comp (multiplicationRestoreMap outcomes))
    (fun _ => multiplicationResetValid) multiplicationPreparedValid multiplicationPreparedOutput List.nodup_range'
    (fun outcomes _ => multiplication_continuation_wellFormed outcomes)
    multiplication_continuation_coherent (fun outcomes _ t ht => multiplication_reset_correct outcomes t ht)
    (fig15WorkProductState divisionWitness) ⟨divisionWitness,divisionWitness_valid,rfl⟩
/-- Complete ideal output of the literal Figure 15 multiplication. -/
def fig15MultiplicationOutputState (s : BasisState) : BasisState :=
  multiplicationPreparedOutput (fig15WorkProductState s)
/-- All actual multiplication transcripts implement the same linear output map
with normalized coefficients independent of the valid input. -/
theorem secp256k1InPlaceMultiplication_coherent :
    CoherentlyImplementsOn secp256k1InPlaceMultiplication
      (Finsupp.lmapDomain ℂ ℂ fig15MultiplicationOutputState) Secp256k1InPlaceInputValid := by
  have h := fig15MultiplicationPrefix_coherent.seq multiplication_reset_coherent (by
    intro s hs
    rw [basis_lift_ket]
    exact supportedOn_ket _ _ ⟨s,hs,rfl⟩)
  apply h.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,basis_lift_ket]
  rfl
/-- Multiplication changes only Y; all work and the original X are restored. -/
theorem fig15MultiplicationOutputState_eq (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    fig15MultiplicationOutputState s = fun w =>
      if w ∈ List.range' 580 256 then fig15WorkProductState s (w-573) else s w := by
  funext w
  rw [fig15MultiplicationOutputState,multiplicationPreparedOutput,fig15SwapOutput_run]
  have hm := fig15WorkProductState_correct s (fig15_initial_horner s hs)
  by_cases ha : w ∈ List.range' 7 256
  · have hy : w ∉ List.range' 580 256 := by simp at ha ⊢; omega
    have hy' : w+573 ∈ List.range' 580 256 := by simp at ha ⊢; dsimp only [Wire] at *; omega
    simp only [if_pos ha,if_neg hy]
    rw [clearRegister_clean _ _ _ hy']
    exact (hs.1.1 w (by simp at ha ⊢; omega)).symm
  · by_cases hy : w ∈ List.range' 580 256
    · have hn : w-573 ∉ List.range' 580 256 := by simp at hy ⊢; dsimp only [Wire] at *; omega
      simp only [if_neg ha,if_pos hy]
      exact clear_outside _ _ _ hn
    · simp only [if_neg ha,if_neg hy]
      rw [clear_outside _ _ _ hy]
      exact hm.2 w ha
/-- The actual multiplication output contains the canonical product in Y. -/
theorem fig15MultiplicationOutputState_word (s : BasisState) (hs : Secp256k1InPlaceInputValid s) :
    boolWordToNat (wireValues (List.range' 580 256) (fig15MultiplicationOutputState s)) =
      (boolWordToNat (wireValues (List.range' 580 256) s) *
        boolWordToNat (wireValues (List.range' 263 256) s)) % ShorECDLP.p := by
  have hbits : wireValues (List.range' 580 256) (fig15MultiplicationOutputState s) =
      wireValues (List.range' 7 256) (fig15WorkProductState s) := by
    have hmap : List.map (fun w : Nat => w-573) (List.range' 580 256) = List.range' 7 256 :=
      List.map_sub_range' (by omega) 256
    simp only [wireValues]
    rw [← hmap,List.map_map]
    apply List.map_congr_left
    intro w hw
    simp only [fig15MultiplicationOutputState_eq s hs,if_pos hw,Function.comp_apply]
  rw [hbits,(fig15WorkProductState_correct s (fig15_initial_horner s hs)).1]

end
end ShorECDLP.Paper2607_13816
