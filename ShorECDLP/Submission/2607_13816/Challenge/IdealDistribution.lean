import ShorECDLP.Submission.«2607_13816».Challenge.WindowBranchSum
import ShorECDLP.Submission.«2607_13816».Challenge.ActualPair
import ShorECDLP.Submission.«2607_13816».Window.StreamSamplingSuccess
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1
noncomputable section
attribute [local irreducible] fourierOutcomes

def axisInputWords : Nat → List (List (List Bool))
  | 0 => [[]]
  | n+1 => (fourierOutcomes 16).flatMap (fun input =>
      (axisInputWords n).map (fun rest => input :: rest))

def axisInputEnd (Q : Point) : List (OddWindow × List Bool) → List (List Bool) → Point → Point
  | (w, _) :: windows, input :: inputs, P =>
      axisInputEnd Q windows inputs (P + windowDigitPoint Q w (boolWordToNat input))
  | _, _, P => P

def axisInputWeight : List (OddWindow × List Bool) → List Bool → List (List Bool) → ℂ
  | (_, output) :: windows, prior, input :: inputs =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) *
        fourierBitAmplitude .inverse input.reverse prior output *
          axisInputWeight windows (output.reverse ++ prior) inputs
  | _, _, _ => 1

private theorem flat_sum {A B : Type} [AddCommMonoid B] (xs : List A) (f : A → List B) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

theorem pointAxisKernel_inputs (Q : Point) (s : BasisState)
    (windows : List (OddWindow × List Bool)) (prior : List Bool) (P : Point) :
    pointAxisKernel Q s windows prior P =
      ((axisInputWords windows.length).map (fun inputs =>
        axisInputWeight windows prior inputs • ket (pointWrite (axisInputEnd Q windows inputs P) s))).sum := by
  induction windows generalizing prior P with
  | nil => simp [pointAxisKernel, axisInputWords, axisInputWeight, axisInputEnd]
  | cons w windows ih =>
    simp only [pointAxisKernel, List.length_cons, axisInputWords, List.map_flatMap,
      List.map_map, Function.comp_def, axisInputWeight, axisInputEnd, flat_sum]
    simp_rw [ih]
    simp only [smul_smul, List.smul_sum, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro input hi
    congr 1
    apply List.map_congr_left
    intro inputs his
    rw [mul_assoc]
def axisInputPairs (windows : List (OddWindow × List Bool)) (inputs : List (List Bool)) :
    List (List Bool × List Bool) :=
  (windows.zip inputs).map (fun p => (p.2.reverse, p.1.2))

theorem axisInputWeight_amplitude (windows : List (OddWindow × List Bool))
    (prior : List Bool) (inputs : List (List Bool)) (hl : inputs.length = windows.length) :
    axisInputWeight windows prior inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (16 * windows.length)) *
        windowFourierAmplitude .inverse (axisInputPairs windows inputs) prior := by
  induction windows generalizing prior inputs with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs
    simp [axisInputWeight, axisInputPairs, windowFourierAmplitude]
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      have ht : inputs.length = windows.length := by simpa using hl
      simp only [axisInputWeight, axisInputPairs, List.zip_cons_cons, List.map_cons,
        windowFourierAmplitude, List.length_cons]
      rw [ih _ inputs ht]
      change _ = _ * (fourierBitAmplitude .inverse input.reverse prior w.2 *
        windowFourierAmplitude .inverse (axisInputPairs windows inputs) (w.2.reverse ++ prior))
      rw [show 16 * (windows.length + 1) = 16 + 16 * windows.length by omega, pow_add]
      ring

theorem axisInputPairs_lengths (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool))
    (ho : ∀ w ∈ windows, w.2.length = 16) (hi : ∀ input ∈ inputs, input.length = 16) :
    ∀ pair ∈ axisInputPairs windows inputs, pair.2.length = pair.1.length := by
  intro pair hp
  unfold axisInputPairs at hp
  obtain ⟨p, hzip, he⟩ := List.mem_map.mp hp
  subst pair
  have hw := List.of_mem_zip hzip
  simp only [List.length_reverse]
  rw [ho p.1 hw.1, hi p.2 hw.2]

/-- The coefficient of a whole input path has the exact full-axis kernel,
including both Hadamard preparation and Fourier normalization. -/
theorem axisInputWeight_kernel (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length)
    (ho : ∀ w ∈ windows, w.2.length = 16) (hi : ∀ input ∈ inputs, input.length = 16) :
    axisInputWeight windows List.nil inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (16 * windows.length)) *
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ ((axisInputPairs windows inputs).map Prod.fst).flatten.length) *
        dyadicFourierKernel .inverse ((axisInputPairs windows inputs).map Prod.fst).flatten.length
          (fourierWordMSB ((axisInputPairs windows inputs).map Prod.fst).flatten)
          (fourierWordLSB ((axisInputPairs windows inputs).map Prod.snd).flatten) := by
  rw [axisInputWeight_amplitude windows List.nil inputs hl,
    windowFourierAmplitude_kernel .inverse _ (axisInputPairs_lengths windows inputs ho hi)]
  ring

theorem fourierOutcomes_reverse_perm (n : Nat) :
    ((fourierOutcomes n).map List.reverse).Perm (fourierOutcomes n) := by
  apply (List.perm_ext_iff_of_nodup
    ((fourierOutcomes_nodup n).map List.reverse_injective) (fourierOutcomes_nodup n)).mpr
  intro bits
  simp only [List.mem_map, fourierOutcomes_mem]
  constructor
  · rintro ⟨xs, hx, rfl⟩
    simpa only [List.length_reverse] using hx
  · intro hb
    exact ⟨bits.reverse, by simpa using hb, List.reverse_reverse bits⟩

theorem fourierOutcomes_append (n m : Nat) : fourierOutcomes (n + m) =
    (fourierOutcomes n).flatMap (fun a => (fourierOutcomes m).map (fun b => a ++ b)) := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [Nat.succ_add, fourierOutcomes, ih, List.flatMap_append, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def, List.cons_append]

theorem axisInputWords_flatten (n : Nat) :
    (axisInputWords n).map List.flatten = fourierOutcomes (16 * n) := by
  induction n with
  | zero => simp [axisInputWords, fourierOutcomes]
  | succ n ih =>
    rw [show 16 * (n + 1) = 16 + 16 * n by omega, fourierOutcomes_append]
    simp only [axisInputWords, List.map_flatMap, List.map_map, Function.comp_def, List.flatten_cons]
    apply congrArg (List.flatMap · (fourierOutcomes 16))
    funext input
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map (input ++ ·)) ih

theorem axisInputWords_mem (n : Nat) (inputs : List (List Bool)) :
    inputs ∈ axisInputWords n ↔ inputs.length = n ∧ ∀ bits ∈ inputs, bits.length = 16 := by
  induction n generalizing inputs with
  | zero => cases inputs <;> simp [axisInputWords]
  | succ n ih =>
    cases inputs with
    | nil => simp [axisInputWords, List.mem_flatMap]
    | cons input inputs =>
      simp [axisInputWords, List.mem_flatMap, List.mem_map, List.cons.injEq,
        fourierOutcomes_mem, ih, and_assoc, and_left_comm, and_comm]

theorem axisInputWords_reverse_perm (n : Nat) :
    ((axisInputWords n).map (List.map List.reverse)).Perm (axisInputWords n) := by
  induction n with
  | zero => simp [axisInputWords]
  | succ n ih =>
    simp only [axisInputWords]
    have he : ((fourierOutcomes 16).flatMap (fun input =>
        (axisInputWords n).map (fun rest => input :: rest))).map (List.map List.reverse) =
      ((fourierOutcomes 16).map List.reverse).flatMap (fun input =>
        ((axisInputWords n).map (List.map List.reverse)).map (fun rest => input :: rest)) := by
      simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, List.map_cons]
    rw [he]
    exact (fourierOutcomes_reverse_perm 16).flatMap (fun input _ => ih.map (input :: ·))

/-- Reversing each physical input window gives every full MSB-first input word
exactly once, so regrouping the coherent sum does not change multiplicity. -/
theorem axisInputWords_msb_perm (n : Nat) :
    ((axisInputWords n).map (fun inputs => (inputs.map List.reverse).flatten)).Perm
      (fourierOutcomes (16 * n)) := by
  have hp := (axisInputWords_reverse_perm n).map List.flatten
  simpa only [List.map_map, Function.comp_def, axisInputWords_flatten] using hp

theorem axisInputEnd_sum (Q : Point) (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (P : Point) :
    axisInputEnd Q windows inputs P = P +
      ((windows.zip inputs).map (fun p => windowDigitPoint Q p.1.1 (boolWordToNat p.2))).sum := by
  induction windows generalizing inputs P with
  | nil => simp [axisInputEnd]
  | cons w windows ih =>
    cases inputs with
    | nil => simp [axisInputEnd]
    | cons input inputs =>
      simp only [axisInputEnd, List.zip_cons_cons, List.map_cons, List.sum_cons, ih]
      exact add_assoc _ _ _

theorem axisInputPairs_fst (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length) :
    (axisInputPairs windows inputs).map Prod.fst = inputs.map List.reverse := by
  induction windows generalizing inputs with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [axisInputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

theorem axisInputPairs_snd (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length) :
    (axisInputPairs windows inputs).map Prod.snd = windows.map Prod.snd := by
  induction windows generalizing inputs with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [axisInputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

/-- A path has one preparation factor and one Fourier factor per input bit. -/
theorem axisInputWeight_full_kernel (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length)
    (ho : ∀ w ∈ windows, w.2.length = 16) (hi : ∀ input ∈ inputs, input.length = 16) :
    axisInputWeight windows List.nil inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (32 * windows.length)) *
        dyadicFourierKernel .inverse (16 * windows.length)
          (fourierWordMSB (inputs.map List.reverse).flatten)
          (fourierWordLSB (windows.map Prod.snd).flatten) := by
  have hlen : (inputs.map List.reverse).flatten.length = 16 * windows.length := by
    rw [fixed_windows_flatten_length 16 _]
    · simp only [List.length_map, hl]
    · intro bits hb
      obtain ⟨input, hm, he⟩ := List.mem_map.mp hb
      subst bits
      simpa only [List.length_reverse] using hi input hm
  rw [axisInputWeight_kernel windows inputs hl ho hi,
    axisInputPairs_fst windows inputs hl, axisInputPairs_snd windows inputs hl, hlen,
    ← pow_add, show 16 * windows.length + 16 * windows.length = 32 * windows.length by omega]

def descendingOddValue : List Nat → Int
  | [] => 0
  | d :: ds => signedTableOdd 32768 d * 65536 ^ ds.length + descendingOddValue ds

private theorem signedValue_append (xs ys : List Int) :
    signedWindowValue 65536 (xs ++ ys) =
      signedWindowValue 65536 xs + (65536 : Int) ^ xs.length * signedWindowValue 65536 ys := by
  induction xs with
  | nil => simp [signedWindowValue]
  | cons x xs ih =>
    simp only [List.cons_append, signedWindowValue, List.length_cons, ih, pow_succ]
    ring

theorem descendingOddValue_reverse (digits : List Nat) :
    descendingOddValue digits = signedWindowValue 65536 (digits.reverse.map (signedTableOdd 32768)) := by
  induction digits with
  | nil => rfl
  | cons d ds ih =>
    simp only [descendingOddValue, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, signedValue_append, List.length_map, List.length_reverse,
      signedWindowValue, ih]
    ring

/-- Each chronological window uses the descending power belonging to its
remaining suffix. This proposition concerns only fixed labels and weights. -/
def DescendingAxisWeights (Q P : Point) : List (OddWindow × List Bool) → Prop
  | [] => True
  | (w, _) :: windows =>
      (∀ digit, windowDigitPoint Q w digit =
        signedTableOdd 32768 digit • (65536 ^ windows.length • signedWindowHalfPoint P order)) ∧
      DescendingAxisWeights Q P windows

theorem axisInputEnd_weighted (Q P : Point) (windows : List (OddWindow × List Bool))
    (hw : DescendingAxisWeights Q P windows) (inputs : List (List Bool))
    (hl : inputs.length = windows.length) (A : Point) :
    axisInputEnd Q windows inputs A =
      A + descendingOddValue (inputs.map boolWordToNat) • signedWindowHalfPoint P order := by
  induction windows generalizing inputs A with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs
    simp [axisInputEnd, descendingOddValue]
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      have ht : inputs.length = windows.length := by simpa using hl
      simp only [axisInputEnd]
      rw [ih hw.2 inputs ht, hw.1]
      simp only [List.map_cons, descendingOddValue, List.length_map, ht, add_zsmul]
      rw [mul_zsmul, show (65536 : Int) ^ windows.length = ((65536 ^ windows.length : Nat) : Int) by norm_cast, natCast_zsmul]
      exact add_assoc _ _ _

def DescendingLabelWeights (Q P : Point) : List OddWindow → Prop
  | [] => True
  | w :: windows =>
      (∀ digit, windowDigitPoint Q w digit =
        signedTableOdd 32768 digit • (65536 ^ windows.length • signedWindowHalfPoint P order)) ∧
      DescendingLabelWeights Q P windows

theorem descendingLabelWeights_zip (Q P : Point) (windows : List OddWindow)
    (hw : DescendingLabelWeights Q P windows) (outputs : List (List Bool))
    (hl : outputs.length = windows.length) : DescendingAxisWeights Q P (windows.zip outputs) := by
  induction windows generalizing outputs with
  | nil => simp [DescendingAxisWeights]
  | cons w windows ih =>
    cases outputs with
    | nil => simp at hl
    | cons output outputs =>
      have ht : outputs.length = windows.length := by simpa using hl
      simp only [List.zip_cons_cons, DescendingAxisWeights, List.length_zip, ht, min_self]
      exact ⟨hw.1, ih hw.2 outputs ht⟩

theorem left_labels_weights (Q : Point) : DescendingLabelWeights Q G leftOddIndices := by
  norm_num [leftOddIndices, List.ofFn_succ, DescendingLabelWeights, windowDigitPoint, pow_mul]

theorem right_labels_weights (Q : Point) : DescendingLabelWeights Q Q rightOddIndices := by
  norm_num [rightOddIndices, List.ofFn_succ, DescendingLabelWeights, windowDigitPoint, pow_mul]

theorem left_axis_input_end (Q : Point) (outputs inputs : List (List Bool))
    (ho : outputs.length = 15) (hi : inputs.length = 15) (A : Point) :
    axisInputEnd Q (leftOddIndices.zip outputs) inputs A =
      A + descendingOddValue (inputs.map boolWordToNat) • signedWindowHalfPoint G order := by
  apply axisInputEnd_weighted
  · apply descendingLabelWeights_zip Q G _ (left_labels_weights Q) outputs
    simpa only [leftOddIndices, List.length_ofFn] using ho
  · simpa only [List.length_zip, leftOddIndices, List.length_ofFn, ho, min_self] using hi

theorem right_axis_input_end (Q : Point) (outputs inputs : List (List Bool))
    (ho : outputs.length = 13) (hi : inputs.length = 13) (A : Point) :
    axisInputEnd Q (rightOddIndices.zip outputs) inputs A =
      A + descendingOddValue (inputs.map boolWordToNat) • signedWindowHalfPoint Q order := by
  apply axisInputEnd_weighted
  · apply descendingLabelWeights_zip Q Q _ (right_labels_weights Q) outputs
    simpa only [rightOddIndices, List.length_ofFn] using ho
  · simpa only [List.length_zip, rightOddIndices, List.length_ofFn, ho, min_self] using hi

theorem actual_two_axes_input_end (Q : Point) (hQ : order • Q = 0)
    (first : List Bool) (left right outputsL outputsR : List (List Bool))
    (hl : left.length = 15) (hr : right.length = 13)
    (hol : outputsL.length = 15) (hor : outputsR.length = 13) :
    axisInputEnd Q (rightOddIndices.zip outputsR) right
      (axisInputEnd Q (leftOddIndices.zip outputsL) left
        (axisWindowOffset G 16 + axisWindowOffset Q 13 +
          signedTableOdd 32768 (boolWordToNat first) •
            ((2 ^ (16 * 15)) • signedWindowHalfPoint G order))) =
      windowValue 65536 ((first :: left).map boolWordToNat).reverse • G +
        windowValue 65536 (right.map boolWordToNat).reverse • Q := by
  rw [right_axis_input_end Q outputsR right hor hr,
    left_axis_input_end Q outputsL left hol hl]
  have hgroup := two_axis_signed_digits Q hQ
    ((first :: left).map boolWordToNat).reverse (right.map boolWordToNat).reverse
    (by simp only [List.length_reverse, List.length_map, List.length_cons, hl])
    (by simp only [List.length_reverse, List.length_map, hr])
  rw [← descendingOddValue_reverse, ← descendingOddValue_reverse] at hgroup
  rw [← hgroup]
  simp only [List.map_cons, descendingOddValue, List.length_map, hl, add_zsmul, mul_zsmul]
  rw [show (65536 : Int) ^ 15 = ((65536 ^ 15 : Nat) : Int) by norm_cast, natCast_zsmul,
    show 2 ^ (16 * 15) = 65536 ^ 15 by decide +kernel]
  abel

/-- The actual two-axis branch is one coherent sum over all three input
blocks: the direct first load, the remaining left windows, and the right axis. -/
theorem actual_two_axes_state_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (firstOutput : List Bool) (left right : List (OddWindow × List Bool))
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    actualAxisBranch Q right List.nil
      (actualAxisBranch Q left firstOutput.reverse
        (fourierBranch .inverse streamAddress.reverse List.nil firstOutput
          (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
            (Quantum.run (streamAddress.map Gate.H) (ket s))))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun firstInput =>
          fourierBitAmplitude .inverse firstInput.reverse List.nil firstOutput •
            ((axisInputWords left.length).map (fun inputsL =>
              axisInputWeight left firstOutput.reverse inputsL •
                ((axisInputWords right.length).map (fun inputsR =>
                  axisInputWeight right List.nil inputsR •
                    ket (pointWrite
                      (axisInputEnd Q right inputsR
                        (axisInputEnd Q left inputsL
                          (axisWindowOffset G 16 + axisWindowOffset Q 13 +
                            signedTableOdd 32768 (boolWordToNat firstInput) •
                              ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)))) s))).sum)).sum)).sum := by
  rw [actual_first_point_sum Q List.nil firstOutput s hz]
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def,
    actualAxisBranch_point Q hQ hn s hs hz]
  simp_rw [pointAxisKernel_inputs]
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def,
    actualAxisBranch_point Q hQ hn s hs hz, pointAxisKernel_inputs]

def inputScalarWord (inputs : List (List Bool)) : List Bool :=
  (inputs.map List.reverse).flatten.reverse

theorem inputScalarWord_perm (n : Nat) :
    ((axisInputWords n).map inputScalarWord).Perm (fourierOutcomes (16 * n)) := by
  have hp := (axisInputWords_msb_perm n).map List.reverse
  simpa only [List.map_map, Function.comp_def, inputScalarWord] using
    hp.trans (fourierOutcomes_reverse_perm (16 * n))

theorem inputScalarWord_value (inputs : List (List Bool))
    (hi : ∀ bits ∈ inputs, bits.length = 16) :
    boolWordToNat (inputScalarWord inputs) =
      windowValue 65536 (inputs.map boolWordToNat).reverse := by
  rw [← fourierWordMSB_reverse]
  simp only [inputScalarWord, List.reverse_reverse]
  have h := input_windows_value 16 (inputs.map List.reverse) (by
    intro bits hb
    obtain ⟨input, hm, he⟩ := List.mem_map.mp hb
    subst bits
    simpa only [List.length_reverse] using hi input hm)
  simpa only [List.map_map, Function.comp_def, fourierWordMSB_reverse] using h

theorem two_axis_input_kernel (left right : List (OddWindow × List Bool))
    (inputsL inputsR : List (List Bool)) (hl : left.length = 16) (hr : right.length = 13)
    (hil : inputsL.length = left.length) (hir : inputsR.length = right.length)
    (hol : ∀ w ∈ left, w.2.length = 16) (hor : ∀ w ∈ right, w.2.length = 16)
    (hbl : ∀ bits ∈ inputsL, bits.length = 16) (hbr : ∀ bits ∈ inputsR, bits.length = 16) :
    axisInputWeight left List.nil inputsL * axisInputWeight right List.nil inputsR =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928) *
        dyadicFourierKernel .inverse 256 (boolWordToNat (inputScalarWord inputsL))
          (fourierWordLSB (left.map Prod.snd).flatten) *
        dyadicFourierKernel .inverse 208 (boolWordToNat (inputScalarWord inputsR))
          (fourierWordLSB (right.map Prod.snd).flatten) := by
  rw [axisInputWeight_full_kernel left inputsL hil hol hbl,
    axisInputWeight_full_kernel right inputsR hir hor hbr, hl, hr]
  have hw (inputs : List (List Bool)) :
      fourierWordMSB (inputs.map List.reverse).flatten = boolWordToNat (inputScalarWord inputs) := by
    simpa only [inputScalarWord, List.reverse_reverse] using
      fourierWordMSB_reverse (inputScalarWord inputs)
  rw [hw, hw, show (928 : Nat) = 32 * 16 + 32 * 13 by decide, pow_add]
  ring

theorem axisInputWords_sum_succ {A : Type} [AddCommMonoid A] (n : Nat)
    (f : List (List Bool) → A) :
    ((axisInputWords (n + 1)).map f).sum =
      ((fourierOutcomes 16).map (fun input =>
        ((axisInputWords n).map (fun inputs => f (input :: inputs))).sum)).sum := by
  simp only [axisInputWords, List.map_flatMap, List.map_map, Function.comp_def, flat_sum]

def twoAxisInputState (Q : Point) (s : BasisState) (x y : List Bool) : State :=
  ((axisInputWords 16).map (fun inputsL =>
    ((axisInputWords 13).map (fun inputsR =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928 *
        dyadicFourierKernel .inverse 256 (boolWordToNat (inputScalarWord inputsL)) (fourierWordLSB x) *
        dyadicFourierKernel .inverse 208 (boolWordToNat (inputScalarWord inputsR)) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat (inputScalarWord inputsL) • G +
        boolWordToNat (inputScalarWord inputsR) • Q) s))).sum)).sum

theorem actual_two_axes_input_state (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (firstOutput : List Bool) (outputsL outputsR : List (List Bool))
    (ho0 : firstOutput.length = 16) (hol : outputsL.length = 15) (hor : outputsR.length = 13)
    (hbl : ∀ bits ∈ outputsL, bits.length = 16) (hbr : ∀ bits ∈ outputsR, bits.length = 16)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    actualAxisBranch Q (rightOddIndices.zip outputsR) List.nil
      (actualAxisBranch Q (leftOddIndices.zip outputsL) firstOutput.reverse
        (fourierBranch .inverse streamAddress.reverse List.nil firstOutput
          (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
            (Quantum.run (streamAddress.map Gate.H) (ket s))))) =
      twoAxisInputState Q s (firstOutput :: outputsL).flatten outputsR.flatten := by
  have hll : (leftOddIndices.zip outputsL).length = 15 := by
    simp only [List.length_zip, leftOddIndices, List.length_ofFn, hol, min_self]
  have hrl : (rightOddIndices.zip outputsR).length = 13 := by
    simp only [List.length_zip, rightOddIndices, List.length_ofFn, hor, min_self]
  rw [actual_two_axes_state_sum Q hQ hn firstOutput _ _ s hs hz, hll, hrl,
    twoAxisInputState, axisInputWords_sum_succ 15]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro firstInput hf
  apply congrArg List.sum
  apply List.map_congr_left
  intro inputsL hlm
  apply congrArg List.sum
  apply List.map_congr_left
  intro inputsR hrm
  have hf' := (fourierOutcomes_mem 16 firstInput).mp hf
  have hl' := (axisInputWords_mem 15 inputsL).mp hlm
  have hr' := (axisInputWords_mem 13 inputsR).mp hrm
  have hli : ∀ bits ∈ firstInput :: inputsL, bits.length = 16 := by
    intro bits hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hf'
    · exact hl'.2 bits hb
  rw [actual_two_axes_input_end Q hQ firstInput inputsL inputsR outputsL outputsR
    hl'.1 hr'.1 hol hor,
    ← inputScalarWord_value (firstInput :: inputsL) hli,
    ← inputScalarWord_value inputsR hr'.2]
  apply congrArg (fun c : ℂ => c • ket (pointWrite
    (boolWordToNat (inputScalarWord (firstInput :: inputsL)) • G +
      boolWordToNat (inputScalarWord inputsR) • Q) s))
  let left : List (OddWindow × List Bool) := (.left ⟨0, by decide⟩, firstOutput) :: leftOddIndices.zip outputsL
  have hcoef := two_axis_input_kernel left (rightOddIndices.zip outputsR)
    (firstInput :: inputsL) inputsR (by simp only [left, List.length_cons, hll]) hrl
    (by simp only [left, List.length_cons, hll, hl'.1]) (hr'.1.trans hrl.symm)
    (by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ho0
      · exact hbl w.2 (List.of_mem_zip hw).2)
    (fun w hw => hbr w.2 (List.of_mem_zip hw).2) hli hr'.2
  have hls : (leftOddIndices.zip outputsL).map Prod.snd = outputsL :=
    List.map_snd_zip (by simp only [leftOddIndices, List.length_ofFn, hol, le_refl])
  have hrs : (rightOddIndices.zip outputsR).map Prod.snd = outputsR :=
    List.map_snd_zip (by simp only [rightOddIndices, List.length_ofFn, hor, le_refl])
  simpa only [left, axisInputWeight, List.map_cons, hls, hrs, List.nil_append, List.append_nil,
    mul_assoc] using hcoef

theorem inputScalarWord_sum {A : Type} [AddCommMonoid A] (n : Nat) (f : List Bool → A) :
    ((axisInputWords n).map (fun inputs => f (inputScalarWord inputs))).sum =
      ((fourierOutcomes (16 * n)).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using ((inputScalarWord_perm n).map f).sum_eq

def idealPointState (Q : Point) (s : BasisState) (x y : List Bool) : State :=
  ((fourierOutcomes 256).map (fun a =>
    ((fourierOutcomes 208).map (fun b =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928 *
        dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x) *
        dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) s))).sum)).sum

theorem twoAxisInputState_ideal (Q : Point) (s : BasisState) (x y : List Bool) :
    twoAxisInputState Q s x y = idealPointState Q s x y := by
  let f (a b : List Bool) : State :=
    (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928 *
      dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x) *
      dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) s)
  change ((axisInputWords 16).map (fun inputs =>
    ((axisInputWords 13).map (fun other => f (inputScalarWord inputs) (inputScalarWord other))).sum)).sum =
    ((fourierOutcomes 256).map (fun a => ((fourierOutcomes 208).map (f a)).sum)).sum
  simp_rw [inputScalarWord_sum (A := State) 13]
  exact inputScalarWord_sum (A := State) 16 (fun a => ((fourierOutcomes 208).map (f a)).sum)

theorem stream_kernel_idealPointState (Q : Point) (x y : List Bool) :
    measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) y
      (measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls G Q))) x
        (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput G Q) (streamPreparedEntry G Q))) =
      idealPointState Q (scalarRootFlip zeroBasisState) x y := by
  rw [streamFourierKernel_point_sum]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul, idealPointState]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  apply congrArg (fun c : ℂ => c • ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q)
    (scalarRootFlip zeroBasisState)))
  rw [show (928 : Nat) = 464 + 464 by decide, pow_add]
  ring

theorem windowOutputPaths_zip (windows : List OddWindow) :
    windowOutputPaths windows = (axisInputWords windows.length).map (windows.zip ·) := by
  induction windows with
  | nil => rfl
  | cons w windows ih =>
    simp only [windowOutputPaths, List.length_cons, axisInputWords, List.map_flatMap,
      List.map_map, Function.comp_def, List.zip_cons_cons, ih]

/-- Expose both chronological output paths while preserving the terminal event. -/
theorem selectedIdealTwoAxes_paths_mass (Q : Point) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) (ψ : State) :
    (selectedIdealTwoAxes Q left right terminal).bornMass ψ =
      ((fourierOutcomes 16).map (fun first =>
        ((windowOutputPaths left).map (fun lp =>
          ((windowOutputPaths right).map (fun rp =>
            (terminal ((lp.map Prod.snd).flatten.reverse ++ first.reverse)
              (rp.map Prod.snd).flatten.reverse).bornMass
                (actualAxisBranch Q rp List.nil (actualAxisBranch Q lp first.reverse
                  (fourierBranch .inverse streamAddress.reverse List.nil first
                    (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
                      (Quantum.run (streamAddress.map Gate.H) ψ))))))).sum)).sum)).sum := by
  have he : (selectedIdealTwoAxes Q left right terminal).bornMass ψ =
      (fourierContinuationInstrument List.nil (fun bits =>
        selectedIdealAxis Q left bits.reverse (fun lhs =>
          selectedIdealAxis Q right List.nil (terminal lhs)))).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
    simp only [selectedIdealTwoAxes, Instrument.bornMass, List.map_map, Function.comp_def,
      InstrumentBranch.seq, LinearMap.comp_apply]
  rw [he, fourierContinuationInstrument_mass]
  simp_rw [selectedIdealAxis_paths_mass]
  simp only [List.append_nil]

theorem selectedIdealTwoAxes_word_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (terminal : List Bool → List Bool → Instrument)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices terminal).bornMass (ket s) =
      ((axisInputWords 16).map (fun outputsL =>
        ((axisInputWords 13).map (fun outputsR =>
          (terminal outputsL.flatten.reverse outputsR.flatten.reverse).bornMass
            (idealPointState Q s outputsL.flatten outputsR.flatten))).sum)).sum := by
  rw [selectedIdealTwoAxes_paths_mass, windowOutputPaths_zip, windowOutputPaths_zip]
  simp only [show leftOddIndices.length = 15 by simp [leftOddIndices],
    show rightOddIndices.length = 13 by simp [rightOddIndices], List.map_map, Function.comp_def]
  rw [axisInputWords_sum_succ (A := ℝ) 15]
  apply congrArg List.sum
  apply List.map_congr_left
  intro firstOutput hf
  apply congrArg List.sum
  apply List.map_congr_left
  intro outputsL hlm
  apply congrArg List.sum
  apply List.map_congr_left
  intro outputsR hrm
  have hf' := (fourierOutcomes_mem 16 firstOutput).mp hf
  have hl' := (axisInputWords_mem 15 outputsL).mp hlm
  have hr' := (axisInputWords_mem 13 outputsR).mp hrm
  have hls : (leftOddIndices.zip outputsL).map Prod.snd = outputsL :=
    List.map_snd_zip (by simp only [leftOddIndices, List.length_ofFn, hl'.1, le_refl])
  have hrs : (rightOddIndices.zip outputsR).map Prod.snd = outputsR :=
    List.map_snd_zip (by simp only [rightOddIndices, List.length_ofFn, hr'.1, le_refl])
  rw [hls, hrs, actual_two_axes_input_state Q hQ hn firstOutput outputsL outputsR
    hf' hl'.1 hr'.1 hl'.2 hr'.2 s hs hz, twoAxisInputState_ideal]
  simp only [List.flatten_cons, List.reverse_append]

theorem outputWords_sum {A : Type} [AddCommMonoid A] (n : Nat) (f : List Bool → A) :
    ((axisInputWords n).map (fun outputs => f outputs.flatten)).sum =
      ((fourierOutcomes (16 * n)).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun xs => (xs.map f).sum) (axisInputWords_flatten n)

/-- Exact output distribution of the full corrected 256/208-bit streaming
computation, expressed against an arbitrary output-dependent terminal instrument. -/
theorem selectedIdealTwoAxes_output_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (terminal : List Bool → List Bool → Instrument)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices terminal).bornMass (ket s) =
      ((fourierOutcomes 256).map (fun lhs =>
        ((fourierOutcomes 208).map (fun rhs =>
          (terminal lhs.reverse rhs.reverse).bornMass (idealPointState Q s lhs rhs))).sum)).sum := by
  rw [selectedIdealTwoAxes_word_mass Q hQ hn terminal s hs hz]
  let f (lhs rhs : List Bool) : ℝ :=
    (terminal lhs.reverse rhs.reverse).bornMass (idealPointState Q s lhs rhs)
  change ((axisInputWords 16).map (fun outputs =>
    ((axisInputWords 13).map (fun other => f outputs.flatten other.flatten)).sum)).sum =
    ((fourierOutcomes 256).map (fun lhs => ((fourierOutcomes 208).map (f lhs)).sum)).sum
  simp_rw [outputWords_sum (A := ℝ) 13]
  exact outputWords_sum (A := ℝ) 16 (fun lhs => ((fourierOutcomes 208).map (f lhs)).sum)

private theorem unitary_prefix_mass (c : Circuit) (tail : AdaptiveCircuit) (ψ : State) :
    (AdaptiveCircuit.unitary c tail).run.bornMass ψ = tail.run.bornMass (Quantum.run c ψ) := by
  simp only [AdaptiveCircuit.run, Instrument.bornMass, List.map_map, Function.comp_def]
  rfl

theorem actual_terminal_mass (ψ : State) :
    (AdaptiveCircuit.unitary [.X 836]
      (measureResetWithCorrection batchedResetWires (fun _ => []))).run.bornMass ψ = normSq ψ := by
  calc
    _ = (measureResetWithCorrection batchedResetWires (fun _ => [])).run.bornMass
        (Quantum.run [.X 836] ψ) := unitary_prefix_mass _ _ _
    _ = normSq (Quantum.run [.X 836] ψ) := resetRegister_mass _ _
    _ = normSq ψ := normSq_run _ (by simp [CircuitWellFormed, Gate.WellFormed]) ψ

/-- The complete corrected streaming computation has exactly the ideal 256/208
Fourier event distribution, for any Boolean acceptance predicate. -/
theorem selectedIdealTwoAxes_event_eq (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (accept : Nat → Nat → Bool) :
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then
        (AdaptiveCircuit.unitary [.X 836]
          (measureResetWithCorrection batchedResetWires (fun _ => []))).run
      else [])).bornMass (ket (zeroBasisState[836 ↦ true])) =
      reducedRawIdealFourierEventMass G Q (fun xy =>
        accept (fourierWordLSB xy.1) (fourierWordLSB xy.2)) := by
  rw [selectedIdealTwoAxes_output_mass Q hQ hn _ _ firstWindowInput_start
    (by
      intro v hv
      have hb : 855 ≤ v := by simpa [streamAddress, List.mem_range'_1] using (And.left (by
        simpa [streamAddress, List.mem_range'_1] using hv : 855 ≤ v ∧ v < 855 + 16))
      simp [upd, zeroBasisState, show v ≠ 836 by dsimp only [Wire] at *; omega])]
  rw [← streamIdealFourierEventMass_eq G Q G_ne_zero hn generator_nsmul_eq_zero hQ]
  unfold streamFourierKernelEventMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro lhs hl
  apply congrArg List.sum
  apply List.map_congr_left
  intro rhs hr
  simp only [List.reverse_reverse]
  split_ifs
  · rw [actual_terminal_mass, stream_kernel_idealPointState]
    rfl
  · rfl

end
end ShorECDLP.Paper2607_13816.ChallengeMigration
