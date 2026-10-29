import ShorECDLP.Submission.«2607_13816».Window.StreamKernel
import ShorECDLP.Submission.«2607_13816».Window.ScalarWindows

namespace ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Chronological outputs from later windows have the higher binary weights. -/
theorem fourierWordLSB_append (xs ys : List Bool) :
    fourierWordLSB (xs ++ ys) = fourierWordLSB xs + 2 ^ xs.length * fourierWordLSB ys := by
  induction xs with
  | nil => simp [fourierWordLSB]
  | cons b xs ih =>
    simp only [List.cons_append, fourierWordLSB, List.length_cons, ih, pow_succ]
    ring

/-- Reversing the newest-first feedback history restores chronological output. -/
theorem fourierWordLSB_updated_history (bits prior : List Bool) :
    fourierWordLSB (bits.reverse ++ prior).reverse =
      fourierWordLSB prior.reverse + 2 ^ prior.length * fourierWordLSB bits := by
  rw [List.reverse_append, List.reverse_reverse, fourierWordLSB_append, List.length_reverse]

/-- Input words use the opposite convention: the first window is most significant. -/
theorem fourierWordMSB_append (xs ys : List Bool) :
    fourierWordMSB (xs ++ ys) = fourierWordMSB xs * 2 ^ ys.length + fourierWordMSB ys := by
  induction xs with
  | nil => simp [fourierWordMSB]
  | cons b xs ih =>
    simp only [List.cons_append, fourierWordMSB, List.length_append, ih, pow_add]
    ring

-- Both sides of the signed-address boundary, including both extreme addresses.
example : [0, 32767, 32768, 65535].map (signedTableOdd 32768) =
    [-65535, -1, 1, 65535] := by decide +kernel

-- Two radix-65536 input windows. The fixed offset cancels both centered digits.
example : ([0, 32767, 32768, 65535] : List Nat).all (fun a =>
    [0, 32767, 32768, 65535].all (fun b =>
      65535 * (65536 + 1) + signedTableOdd 32768 a * 65536 +
        signedTableOdd 32768 b == 2 * ((a : Int) * 65536 + b))) = true := by
  decide +kernel

example : fourierWordLSB (List.replicate 16 false ++ true :: List.replicate 15 false) =
    65536 := by decide +kernel

/-- The offset cancellation holds for every pair of input digits, including the
sign boundary. Multiplication by a half-point turns the right side into the
ordinary unsigned two-window scalar. -/
theorem two_window_signed_offset (a b : Nat) :
    65535 * (65536 + 1) + signedTableOdd 32768 a * 65536 + signedTableOdd 32768 b =
      2 * ((a : Int) * 65536 + b) := by
  rw [signedTableOdd_value, signedTableOdd_value]
  ring

/-- Splitting a Fourier word at a window boundary retains all feedback phases. -/
theorem fourierBitAmplitude_append (dir : PhaseDir) (xs ys prior bs cs : List Bool)
    (hl : bs.length = xs.length) :
    fourierBitAmplitude dir (xs ++ ys) prior (bs ++ cs) =
      fourierBitAmplitude dir xs prior bs *
        fourierBitAmplitude dir ys (bs.reverse ++ prior) cs := by
  induction xs generalizing prior bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.mp hl
    subst bs
    simp [fourierBitAmplitude]
  | cons a xs ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.cons_append, fourierBitAmplitude]
      rw [ih (b :: prior) bs (by simpa using hl)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      ring

/-- Actual feedback order for any number of complete windows. -/
theorem window_history_fold (windows : List (List Bool)) (prior : List Bool) :
    windows.foldl (fun history bits => bits.reverse ++ history) prior =
      windows.flatten.reverse ++ prior := by
  induction windows generalizing prior with
  | nil => simp
  | cons bits windows ih =>
    simp only [List.foldl_cons, ih, List.flatten_cons, List.reverse_append, List.append_assoc]

/-- Product of the individual window amplitudes, with the actual newest-first
history carried from one window to the next. -/
noncomputable def windowFourierAmplitude (dir : PhaseDir) :
    List (List Bool × List Bool) → List Bool → ℂ
  | [], _ => 1
  | (input, output) :: windows, prior =>
      fourierBitAmplitude dir input prior output *
        windowFourierAmplitude dir windows (output.reverse ++ prior)

theorem windowFourierAmplitude_flatten (dir : PhaseDir)
    (windows : List (List Bool × List Bool)) (prior : List Bool)
    (hl : ∀ w ∈ windows, w.2.length = w.1.length) :
    windowFourierAmplitude dir windows prior =
      fourierBitAmplitude dir (windows.map Prod.fst).flatten prior
        (windows.map Prod.snd).flatten := by
  induction windows generalizing prior with
  | nil => simp [windowFourierAmplitude, fourierBitAmplitude]
  | cons w windows ih =>
    simp only [windowFourierAmplitude, List.map_cons, List.flatten_cons]
    rw [fourierBitAmplitude_append dir _ _ _ _ _ (hl w (by simp)),
      ih _ (fun v hv => hl v (List.mem_cons_of_mem w hv))]

/-- The entire axis has one Fourier kernel; window feedback introduces no
extra phase when the axis starts with empty history. -/
theorem windowFourierAmplitude_kernel (dir : PhaseDir)
    (windows : List (List Bool × List Bool))
    (hl : ∀ w ∈ windows, w.2.length = w.1.length) :
    windowFourierAmplitude dir windows List.nil =
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ (windows.map Prod.fst).flatten.length) *
        dyadicFourierKernel dir (windows.map Prod.fst).flatten.length
          (fourierWordMSB (windows.map Prod.fst).flatten)
          (fourierWordLSB (windows.map Prod.snd).flatten) := by
  have he : (windows.map Prod.snd).flatten.length =
      (windows.map Prod.fst).flatten.length := by
    induction windows with
    | nil => rfl
    | cons w windows ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      rw [hl w (by simp), ih (fun v hv => hl v (List.mem_cons_of_mem w hv))]
  rw [windowFourierAmplitude_flatten dir windows List.nil hl,
    fourierBitAmplitude_eq dir _ List.nil _ he]
  simp [fourierHistoryPhase, fourierHistoryAngle]

/-- All centered odd digits, including the first mixed-table digit, reconstruct
an unsigned scalar after its fixed initial offset is added. -/
theorem signed_odd_digits_reconstruct (digits : List Nat) :
    signedWindowValue 65536 (digits.map (signedTableOdd 32768)) +
      (65535 * radixGeometric digits.length : Nat) =
      2 * (windowValue 65536 digits : Int) := by
  induction digits with
  | nil => simp [signedWindowValue, windowValue, radixGeometric]
  | cons d ds ih =>
    simp only [List.map_cons, List.length_cons, signedWindowValue,
      windowValue, radixGeometric, signedTableOdd_value]
    push_cast at ih ⊢
    linear_combination 65536 * ih

/-- Group-level reconstruction uses only the subgroup order, and imposes no
exceptional-point exclusion on the accumulator. -/
theorem signed_odd_digits_point {A : Type} [AddCommGroup A]
    (P : A) (r : Nat) (hr : Odd r) (hP : r • P = 0) (digits : List Nat) :
    signedWindowValue 65536 (digits.map (signedTableOdd 32768)) •
        signedWindowHalfPoint P r +
      (65535 * radixGeometric digits.length) • signedWindowHalfPoint P r =
        windowValue 65536 digits • P := by
  rw [← natCast_zsmul (signedWindowHalfPoint P r) (65535 * radixGeometric digits.length),
    ← add_zsmul, signed_odd_digits_reconstruct]
  rw [show 2 * (windowValue 65536 digits : Int) =
    (windowValue 65536 digits : Int) + (windowValue 65536 digits : Int) by ring,
    add_zsmul, natCast_zsmul, ← nsmul_add,
    signedWindowHalfPoint_double P r hr hP]

/-- A fixed-width list of windows retains leading zero windows. -/
theorem fixed_windows_flatten_length (w : Nat) (windows : List (List Bool))
    (hw : ∀ bits ∈ windows, bits.length = w) :
    windows.flatten.length = w * windows.length := by
  induction windows with
  | nil => simp
  | cons bits windows ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hw bits (by simp), ih (fun bs hb => hw bs (List.mem_cons_of_mem bits hb))]
    ring

/-- Chronological window outputs are the little-endian radix digits of the
integer accepted by the decoder. -/
theorem output_windows_value (w : Nat) (windows : List (List Bool))
    (hw : ∀ bits ∈ windows, bits.length = w) :
    fourierWordLSB windows.flatten = windowValue (2 ^ w) (windows.map fourierWordLSB) := by
  induction windows with
  | nil => rfl
  | cons bits windows ih =>
    simp only [List.flatten_cons, List.map_cons, windowValue, fourierWordLSB_append]
    rw [hw bits (by simp), ih (fun bs hb => hw bs (List.mem_cons_of_mem bits hb))]

private theorem windowValue_append (base : Nat) (xs ys : List Nat) :
    windowValue base (xs ++ ys) = windowValue base xs + base ^ xs.length * windowValue base ys := by
  induction xs with
  | nil => simp [windowValue]
  | cons x xs ih =>
    simp only [List.cons_append, windowValue, List.length_cons, ih, pow_succ]
    ring

/-- Input windows run in descending significance, opposite to emitted output
weights. This is the unsigned scalar reconstructed by the signed point tables. -/
theorem input_windows_value (w : Nat) (windows : List (List Bool))
    (hw : ∀ bits ∈ windows, bits.length = w) :
    fourierWordMSB windows.flatten =
      windowValue (2 ^ w) (windows.map fourierWordMSB).reverse := by
  induction windows with
  | nil => rfl
  | cons bits windows ih =>
    have ht := fun bs hb => hw bs (List.mem_cons_of_mem bits hb)
    simp only [List.flatten_cons, List.map_cons, List.reverse_cons,
      fourierWordMSB_append, windowValue_append, List.length_reverse, List.length_map,
      windowValue]
    rw [ih ht, fixed_windows_flatten_length w windows ht, pow_mul]
    ring

end ShorECDLP.Paper2607_13816.ChallengeMigration
