import ShorECDLP.Submission.«2607_13816».EEA.RangeSlices

/-! # Arithmetic extraction of packed iteration-end ranges -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem extract_append (xs ys : List Bool) :
    boolWordToNat (xs ++ ys) = boolWordToNat xs + 2^xs.length * boolWordToNat ys := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.cons_append, boolWordToNat_cons, List.length_cons, ih, Nat.pow_succ]
    ring

private theorem extract_split (bits : List Bool) (count : Nat) (h : count ≤ bits.length) :
    boolWordToNat bits = boolWordToNat (bits.take count) +
      2^count * boolWordToNat (bits.drop count) := by
  have he := extract_append (bits.take count) (bits.drop count)
  simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left h] using he

private theorem extract_take (bits : List Bool) (count : Nat) (h : count ≤ bits.length) :
    boolWordToNat (bits.take count) = boolWordToNat bits % 2^count := by
  have hb := boolWordToNat_lt_pow_two (bits.take count)
  rw [List.length_take, Nat.min_eq_left h] at hb
  rw [extract_split bits count h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

private theorem extract_drop (bits : List Bool) (count : Nat) (h : count ≤ bits.length) :
    boolWordToNat (bits.drop count) = boolWordToNat bits / 2^count := by
  have hb := boolWordToNat_lt_pow_two (bits.take count)
  rw [List.length_take, Nat.min_eq_left h] at hb
  rw [extract_split bits count h, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hb, Nat.zero_add]

/-- A fitting little-endian slice is division followed by reduction modulo its width. -/
theorem boolWordToNat_slice (bits : List Bool) (start count : Nat)
    (hfit : start + count ≤ bits.length) :
    boolWordToNat ((bits.drop start).take count) =
      (boolWordToNat bits / 2^start) % 2^count := by
  rw [extract_take _ count (by simp only [List.length_drop]; omega),
    extract_drop bits start (by omega)]

/-- Reversal changes the extraction offset to the omitted suffix length. -/
theorem boolWordToNat_reverse_slice (bits : List Bool) (start count : Nat)
    (hfit : start + count ≤ bits.length) :
    boolWordToNat ((bits.drop start).take count).reverse =
      (boolWordToNat bits.reverse / 2^(bits.length-start-count)) % 2^count := by
  rw [List.reverse_take, List.length_drop, List.reverse_drop, List.drop_take]
  rw [show bits.length - start - (bits.length - start - count) = count by omega]
  apply boolWordToNat_slice
  simp only [List.length_reverse]
  omega

/-- The upper iteration mask extracts precisely the selected binary field. -/
theorem endIterationUpperRangeBits_extract (work : List Bool) (k K boundary : Nat)
    (hk : 1 ≤ k) (hb : k ≤ boundary ∧ boundary ≤ K) (hfit : K ≤ work.length) :
    boolWordToNat (endIterationUpperRangeBits true boundary (zeroMapLabels k K) work) =
      (boolWordToNat work / 2^(k-1)) % 2^(boundary-k+1) := by
  rw [endIterationUpperRangeBits_value work k K boundary hk hb hfit,
    boolWordToNat_slice work _ _ (by omega)]

/-- The lower iteration mask extracts from the full big-endian packed word. -/
theorem endIterationLowerRangeBits_extract (work : List Bool) (k K boundary : Nat)
    (hk : 1 ≤ k) (hb : k ≤ boundary ∧ boundary ≤ K) (hfit : K ≤ work.length) :
    boolWordToNat (endIterationLowerRangeBits true boundary (zeroMapLabels k K) work).reverse =
      (boolWordToNat work.reverse / 2^(work.length-K)) % 2^(K-boundary+1) := by
  rw [endIterationLowerRangeBits_value work k K boundary hk hb hfit,
    boolWordToNat_reverse_slice work _ _ (by omega)]
  congr 3
  omega

end ShorECDLP.Paper2607_13816
