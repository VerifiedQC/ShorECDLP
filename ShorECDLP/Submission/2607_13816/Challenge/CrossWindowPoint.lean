import ShorECDLP.Submission.«2607_13816».Challenge.FirstValidity
import ShorECDLP.Submission.«2607_13816».Challenge.CrossWindowWeights
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1

/-- The sign bit and the unsigned value agree even at the two central digits. -/
theorem reused_window_digit_low (s : BasisState) :
    windowRawDigit 0 s < 32768 ↔ s 870 = false := by
  have hb := boolWordToNat_lt_pow_two (wireValues (windowAddressBits 0) s)
  simp only [wireValues, List.length_map, windowAddressBits, List.length_range'] at hb
  change boolWordToNat (wireValues (windowAddressBits 0) s) < 32768 at hb
  cases hh : s 870 <;> simp_all [windowRawDigit, windowBankStart]

/-- Actual signed table selection gives a centered odd scalar at its fixed
power-of-two weight. No accumulator point is excluded. -/
theorem reused_window_selected_odd (P : Point) (j : Nat) (s : BasisState) :
    (if s 870 then oddWindowPoint P j (signedTableAddress 32768 (windowRawDigit 0 s))
      else -oddWindowPoint P j (signedTableAddress 32768 (windowRawDigit 0 s))) =
    signedTableOdd 32768 (windowRawDigit 0 s) •
      ((2 ^ (16 * j)) • signedWindowHalfPoint P order) := by
  have ha := signedTableAddress_bound 32768 (windowRawDigit 0 s) (windowRawDigit_bound 0 s)
  simp only [oddWindowPoint, Nat.mod_eq_of_lt ha, signedTableOdd]
  cases hs : s 870
  · rw [if_neg (by decide), if_pos ((reused_window_digit_low s).mpr hs)]
    simp only [neg_zsmul, natCast_zsmul]
  · rw [if_pos rfl, if_neg (by intro h; have hh := (reused_window_digit_low s).mp h; simp [hs] at hh)]
    simp only [natCast_zsmul]

/-- The corrected actual left window has precisely its scalar digit action. -/
theorem actual_left_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (j : Fin 15) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualBatchedWindowState Q (.left j) s =
      pointWrite (P + signedTableOdd 32768 (windowRawDigit 0 s) •
        ((2 ^ (16 * j.val)) • signedWindowHalfPoint G order)) s := by
  rw [actualBatchedWindowState_selected Q hQ hn (.left j) s hs P hP]
  simp only [windowPoint, reused_window_selected_odd]

/-- The corrected actual right window has precisely its scalar digit action. -/
theorem actual_right_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (j : Fin 13) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualBatchedWindowState Q (.right j) s =
      pointWrite (P + signedTableOdd 32768 (windowRawDigit 0 s) •
        ((2 ^ (16 * j.val)) • signedWindowHalfPoint Q order)) s := by
  rw [actualBatchedWindowState_selected Q hQ hn (.right j) s hs P hP]
  simp only [windowPoint, reused_window_selected_odd]
/-- The mixed first table obeys the same centered odd-digit formula as the
later tables, including any row whose resulting point is infinity. -/
theorem actual_first_window_digit (Q : Point) (s : BasisState) :
    actualFirstWindowState Q s =
      pointWrite (axisWindowOffset G 16 + axisWindowOffset Q 13 +
        signedTableOdd 32768 (windowRawDigit 0 s) •
          ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)) s := by
  have ha : tableAddressValue (List.range' 855 16) s = windowRawDigit 0 s := by
    simp [tableAddressValue, windowRawDigit, windowAddressBits, windowBankStart,
      List.range', wireValues, boolWordToNat]
    omega
  have hd : (2 ^ (16 * 15)) • signedWindowHalfPoint G order +
      (2 ^ (16 * 15)) • signedWindowHalfPoint G order = (2 ^ (16 * 15)) • G := by
    rw [← nsmul_add, signedWindowHalfPoint_double G order (by decide +kernel)
      generator_nsmul_eq_zero]
  have he := signedTable_point ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)
    32768 (windowRawDigit 0 s)
  rw [hd] at he
  have hh : signedWindowHalfPoint ((2 ^ (16 * 15)) • G) order =
      (2 ^ (16 * 15)) • signedWindowHalfPoint G order := by
    exact smul_comm ((order + 1) / 2) (2 ^ (16 * 15)) G
  simp only [actualFirstWindowState, firstWindowTable, ha, hh]
  rw [sub_eq_iff_eq_add.mp he]
  rfl

/-- Once the actual signed digits have been accumulated, the two initial
 offsets cancel exactly. This is an exact group identity, without a loss term. -/
theorem two_axis_signed_digits (Q : Point) (hQ : order • Q = 0)
    (left right : List Nat) (hl : left.length = 16) (hr : right.length = 13) :
    axisWindowOffset G 16 + axisWindowOffset Q 13 +
      signedWindowValue 65536 (left.map (signedTableOdd 32768)) •
        signedWindowHalfPoint G order +
      signedWindowValue 65536 (right.map (signedTableOdd 32768)) •
        signedWindowHalfPoint Q order =
      windowValue 65536 left • G + windowValue 65536 right • Q := by
  have hleft := signed_odd_digits_point G order (by decide +kernel)
    generator_nsmul_eq_zero left
  have hright := signed_odd_digits_point Q order (by decide +kernel) hQ right
  rw [hl] at hleft
  rw [hr] at hright
  change _ + axisWindowOffset G 16 = _ at hleft
  change _ + axisWindowOffset Q 13 = _ at hright
  rw [← hleft, ← hright]
  abel

/-- In bit-word form, the signed tables reconstruct exactly the two integers
used as input exponents by the 256/208 Fourier kernels. -/
theorem two_axis_input_words (Q : Point) (hQ : order • Q = 0)
    (left right : List (List Bool)) (hl : left.length = 16) (hr : right.length = 13)
    (hlw : ∀ bits ∈ left, bits.length = 16) (hrw : ∀ bits ∈ right, bits.length = 16) :
    axisWindowOffset G 16 + axisWindowOffset Q 13 +
      signedWindowValue 65536 ((left.map fourierWordMSB).reverse.map (signedTableOdd 32768)) •
        signedWindowHalfPoint G order +
      signedWindowValue 65536 ((right.map fourierWordMSB).reverse.map (signedTableOdd 32768)) •
        signedWindowHalfPoint Q order =
      fourierWordMSB left.flatten • G + fourierWordMSB right.flatten • Q := by
  rw [input_windows_value 16 left hlw, input_windows_value 16 right hrw]
  exact two_axis_signed_digits Q hQ _ _ (by simpa using hl) (by simpa using hr)

end ShorECDLP.Paper2607_13816.ChallengeMigration
