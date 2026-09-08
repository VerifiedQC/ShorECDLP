import ShorECDLP.Submission.«2607_13816».EEA.PreprocessResources
import ShorECDLP.Submission.«2607_13816».EEA.Model
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep

/-! # The concrete initial EEA encoding -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

private theorem initial_word_append (a b : List Bool) :
    boolWordToNat (a ++ b) = boolWordToNat a + 2 ^ a.length * boolWordToNat b := by
  induction a with
  | nil => simp
  | cons bit bits ih =>
    simp only [List.cons_append, boolWordToNat_cons, ih, List.length_cons, pow_succ]
    ring

/-- The source's first-set-bit scan is the ordinary binary length, including zero. -/
theorem bigEndianWord_size (bits : List Bool) :
    (boolWordToNat bits.reverse).size = bits.length - bits.findIdx id := by
  induction bits with
  | nil => simp
  | cons b bs ih =>
    have hb := boolWordToNat_lt_pow_two bs.reverse
    simp only [List.length_reverse] at hb
    cases b with
    | false =>
      simpa [List.reverse_cons, initial_word_append, List.findIdx_cons] using ih
    | true =>
      have hv : boolWordToNat (true :: bs).reverse = boolWordToNat bs.reverse + 2 ^ bs.length := by
        simp [List.reverse_cons, initial_word_append]
      have hlo : bs.length < (boolWordToNat (true :: bs).reverse).size :=
        Nat.lt_size.mpr (by rw [hv]; omega)
      have hhi : (boolWordToNat (true :: bs).reverse).size ≤ bs.length + 1 :=
        Nat.size_le.mpr (by rw [hv, pow_succ]; omega)
      simp only [List.findIdx_cons, id_eq, Bool.cond_true, List.length_cons, Nat.sub_zero]
      omega

/-- Numeric interpretation of the length initializer's exact source scan. -/
theorem lengthInitialize_size_correct (input targets : List Wire) (flag : Wire) (scratches : List Wire)
    (known : Nat) (state : BasisState) (hnd : targets.Nodup)
    (hlayout : ComputeControlLayout input flag scratches)
    (htargets : ∀ wire ∈ targets, wire ∉ input ∧ wire ≠ flag ∧ wire ∉ scratches)
    (hknown : wireValues scratches state = constantBits scratches.length known)
    (hflag : state flag = false) :
    wireValues targets (run (lengthInitialize input targets flag scratches known) state) =
      xorConstantBits (wireValues targets state)
        (if boolWordToNat (wireValues input state).reverse = 0 then 2 ^ targets.length - 1
         else (boolWordToNat (wireValues input state).reverse).size - 1) ∧
    ∀ wire, wire ∉ targets → run (lengthInitialize input targets flag scratches known) state wire = state wire := by
  have h := lengthInitialize_correct input targets flag scratches known state hnd hlayout htargets hknown hflag
  have hs := bigEndianWord_size (wireValues input state)
  simp only [wireValues, List.length_map, List.findIdx_map, Function.comp_def, id_eq] at hs
  change (boolWordToNat (wireValues input state).reverse).size = input.length - input.findIdx state at hs
  have hle := List.findIdx_le_length (p := state) (xs := input)
  have hz : boolWordToNat (wireValues input state).reverse = 0 ↔ input.findIdx state = input.length := by
    rw [← Nat.size_eq_zero, hs]
    omega
  refine ⟨h.1.trans ?_, h.2⟩
  congr 1
  by_cases he : input.findIdx state = input.length
  · rw [if_neg (by omega), if_pos (hz.mpr he)]
  · rw [if_pos (by omega), if_neg (fun h => he (hz.mp h)), hs]

private theorem initial_scan_encoding (input : List Wire) (state : BasisState)
    (hpos : 0 < boolWordToNat (wireValues input state).reverse) :
    (if input.findIdx state < input.length then input.length - 1 - input.findIdx state
     else 2 ^ 9 - 1) = (boolWordToNat (wireValues input state).reverse).size - 1 := by
  have hs := bigEndianWord_size (wireValues input state)
  simp only [wireValues, List.length_map, List.findIdx_map, Function.comp_def, id_eq] at hs
  change (boolWordToNat (wireValues input state).reverse).size = input.length - input.findIdx state at hs
  have hz : (boolWordToNat (wireValues input state).reverse).size ≠ 0 := by
    intro hz
    exact (Nat.ne_of_gt hpos) (Nat.size_eq_zero.mp hz)
  rw [if_pos (by omega), hs]
  omega

private theorem initial_corrected_min (p x : Nat) (hx : x < p) :
    correctedInput p x = min x (p - x) := by
  unfold correctedInput
  split_ifs with h
  · rw [min_eq_right (by omega)]
  · rw [min_eq_left (by omega)]

attribute [local irreducible] eeaPreprocessIdealState

/-- The actual initialized divisor, parity bit and encoded divisor length agree with
`paperInitial`. Length metadata stores the binary length minus one. -/
theorem eeaPreprocess_initial_divisor (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < 2 ^ 256 - 2 ^ 32 - 977) :
    let after := eeaPreprocessIdealState state
    let initial := paperInitial (2 ^ 256 - 2 ^ 32 - 977)
      (boolWordToNat (wireValues (List.range' 263 256) state))
    boolWordToNat (wireValues (List.range' 266 256).reverse after) = initial.rPrime ∧
    after 2 = initial.iter ∧
    wireValues (List.range' 549 9) after = constantBits 9 (initial.lRPrime - 1) := by
  have h := eeaPreprocessIdealState_correct state hclean hx hxp
  dsimp only at h ⊢
  have hd := h.1.trans (initial_corrected_min _ _ hxp).symm
  have hs := initial_scan_encoding (List.range' 266 256) (eeaPreprocessIdealState state)
    (by simpa only [wireValues, List.map_reverse] using h.2.1)
  simp only [List.length_range', Nat.reduceSub, Nat.reducePow] at hs
  have hsize : (boolWordToNat (wireValues (List.range' 266 256)
      (eeaPreprocessIdealState state)).reverse).size =
      (correctedInput (2 ^ 256 - 2 ^ 32 - 977)
        (boolWordToNat (wireValues (List.range' 263 256) state))).size := by
    rw [show (wireValues (List.range' 266 256) (eeaPreprocessIdealState state)).reverse =
      wireValues (List.range' 266 256).reverse (eeaPreprocessIdealState state) by
        simp only [wireValues, List.map_reverse], hd]
  simp only [paperInitial]
  refine ⟨hd, ?_, ?_⟩
  · change _ = decide (_ / 2 < _)
    rw [h.2.2.2.1]
    congr 1
  · change _ = constantBits 9 ((correctedInput _ _).size - 1)
    rw [h.2.2.2.2.2.2.2.2.2.2.2.1, hs, hsize]

private theorem initial_ready_of_banks (after : BasisState)
    (haux : Clean (List.range' 558 22) after)
    (hword : wireValues (List.range' 531 9) after = constantBits 9 511) :
    IndexedStepReady indexedStepProductionRegisters after ∧
    IndexedStepEpochEncoded indexedStepProductionRegisters after := by
  constructor
  · intro w hw
    apply haux w
    have hsub : ∀ w ∈ indexedStepProductionRegisters.sharedScratch, w ∈ List.range' 558 22 := by
      decide
    exact hsub w hw
  · unfold IndexedStepEpochEncoded
    split
    · have hq := congrArg (fun bits : List Bool => bits.headD false) hword
      change after 531 = true
      simpa only [wireValues, List.range'_succ, List.map_cons, List.headD_cons,
        constantBits, List.range_succ_eq_map, List.map_cons, List.headD_cons] using hq
    · change after 559 = false
      exact haux 559 (by decide)

/-- The preprocessing prefix establishes the scratch and borrowed-epoch premises
for the first production step. Preservation and routing over subsequent steps remain separate. -/
theorem eeaPreprocess_initial_ready (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < 2 ^ 256 - 2 ^ 32 - 977) :
    IndexedStepReady indexedStepProductionRegisters (eeaPreprocessIdealState state) ∧
    IndexedStepEpochEncoded indexedStepProductionRegisters (eeaPreprocessIdealState state) := by
  have h := eeaPreprocessIdealState_correct state hclean hx hxp
  dsimp only at h
  have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have haux : Clean (List.range' 558 22) (eeaPreprocessIdealState state) := by
    intro w hw
    exact hc w (by simp only [List.mem_append]; exact Or.inr hw)
  exact initial_ready_of_banks _ haux h.2.2.2.2.2.2.2.2.2.1

end
end ShorECDLP.Paper2607_13816
