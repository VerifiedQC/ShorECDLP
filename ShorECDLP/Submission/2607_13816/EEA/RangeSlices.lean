import ShorECDLP.Submission.«2607_13816».EEA.LengthBitLength

/-! # Contiguous work slices selected by the iteration-end range masks -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem range_source_slice (work : List Bool) (start count : Nat)
    (hstart : 1 ≤ start) (hfit : start - 1 + count ≤ work.length) :
    (List.range' start count).map (fun label => work.getD (label - 1) false) =
      (work.drop (start - 1)).take count := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range', List.length_take, List.length_drop]
    omega
  · intro i hi hj
    have hi' : i < count := by simpa using hi
    simp only [List.getElem_map, List.getElem_range'_1, List.getElem_take, List.getElem_drop]
    rw [List.getD_eq_getElem _ _ (by omega)]
    congr 1
    omega

/-- The upper range is the selected contiguous slice followed by zero mask bits. -/
theorem endIterationUpperRangeBits_slice (work : List Bool) (k K boundary : Nat)
    (hk : 1 ≤ k) (hb : k ≤ boundary ∧ boundary ≤ K) (hfit : K ≤ work.length) :
    endIterationUpperRangeBits true boundary (zeroMapLabels k K) work =
      (work.drop (k - 1)).take (boundary - k + 1) ++ List.replicate (K - boundary) false := by
  have hsplit : List.range' k (K + 1 - k) =
      List.range' k (boundary - k + 1) ++ List.range' (boundary + 1) (K - boundary) := by
    rw [show boundary + 1 = k + (boundary - k + 1) by omega, List.range'_append_1]
    congr 1
    omega
  have hfirst : (List.range' k (boundary - k + 1)).map
      (fun label => true && decide (label ≤ boundary) && work.getD (label - 1) false) =
      (List.range' k (boundary - k + 1)).map (fun label => work.getD (label - 1) false) := by
    apply List.map_congr_left
    intro label hm
    simp only [List.mem_range'] at hm
    have hle : label ≤ boundary := by omega
    simp [hle]
  have hlast : (List.range' (boundary + 1) (K - boundary)).map
      (fun label => true && decide (label ≤ boundary) && work.getD (label - 1) false) =
      List.replicate (K - boundary) false := by
    calc
      _ = (List.range' (boundary + 1) (K - boundary)).map (fun _ => false) := by
        apply List.map_congr_left
        intro label hm
        simp only [List.mem_range'] at hm
        have hn : ¬label ≤ boundary := by omega
        simp [hn]
      _ = _ := by simp
  rw [endIterationUpperRangeBits, zeroMapLabels_eq_range', hsplit, List.map_append, hfirst, hlast,
    range_source_slice work k _ hk (by omega)]

/-- The lower range is zero mask bits followed by the selected contiguous slice. -/
theorem endIterationLowerRangeBits_slice (work : List Bool) (k K boundary : Nat)
    (hk : 1 ≤ k) (hb : k ≤ boundary ∧ boundary ≤ K) (hfit : K ≤ work.length) :
    endIterationLowerRangeBits true boundary (zeroMapLabels k K) work =
      List.replicate (boundary - k) false ++
        (work.drop (boundary - 1)).take (K - boundary + 1) := by
  have hsplit : List.range' k (K + 1 - k) =
      List.range' k (boundary - k) ++ List.range' boundary (K - boundary + 1) := by
    have h : List.range' k (boundary - k) ++
        List.range' (k + (boundary - k)) (K - boundary + 1) =
        List.range' k (boundary - k + (K - boundary + 1)) := List.range'_append_1
    simpa only [show k + (boundary - k) = boundary by omega,
      show boundary - k + (K - boundary + 1) = K + 1 - k by omega] using h.symm
  have hfirst : (List.range' k (boundary - k)).map
      (fun label => true && decide (boundary ≤ label) && work.getD (label - 1) false) =
      List.replicate (boundary - k) false := by
    calc
      _ = (List.range' k (boundary - k)).map (fun _ => false) := by
        apply List.map_congr_left
        intro label hm
        simp only [List.mem_range'] at hm
        have hn : ¬boundary ≤ label := by omega
        simp [hn]
      _ = _ := by simp
  have hlast : (List.range' boundary (K - boundary + 1)).map
      (fun label => true && decide (boundary ≤ label) && work.getD (label - 1) false) =
      (List.range' boundary (K - boundary + 1)).map (fun label => work.getD (label - 1) false) := by
    apply List.map_congr_left
    intro label hm
    simp only [List.mem_range'] at hm
    have hle : boundary ≤ label := by omega
    simp [hle]
  rw [endIterationLowerRangeBits, zeroMapLabels_eq_range', hsplit, List.map_append, hfirst, hlast,
    range_source_slice work boundary _ (by omega) (by omega)]

private theorem range_zero_tail (bits : List Bool) (count : Nat) :
    boolWordToNat (bits ++ List.replicate count false) = boolWordToNat bits := by
  induction bits with
  | nil =>
    simp only [List.nil_append, boolWordToNat_nil]
    induction count with
    | zero => rfl
    | succ count ih => simp [List.replicate_succ, ih]
  | cons b bits ih => simp [boolWordToNat, ih]

/-- The upper mask preserves exactly the little-endian value of its selected slice. -/
theorem endIterationUpperRangeBits_value (work : List Bool) (k K boundary : Nat)
    (hk : 1 ≤ k) (hb : k ≤ boundary ∧ boundary ≤ K) (hfit : K ≤ work.length) :
    boolWordToNat (endIterationUpperRangeBits true boundary (zeroMapLabels k K) work) =
      boolWordToNat ((work.drop (k - 1)).take (boundary - k + 1)) := by
  rw [endIterationUpperRangeBits_slice work k K boundary hk hb hfit, range_zero_tail]

/-- The lower mask preserves exactly the big-endian value of its selected slice. -/
theorem endIterationLowerRangeBits_value (work : List Bool) (k K boundary : Nat)
    (hk : 1 ≤ k) (hb : k ≤ boundary ∧ boundary ≤ K) (hfit : K ≤ work.length) :
    boolWordToNat (endIterationLowerRangeBits true boundary (zeroMapLabels k K) work).reverse =
      boolWordToNat ((work.drop (boundary - 1)).take (K - boundary + 1)).reverse := by
  rw [endIterationLowerRangeBits_slice work k K boundary hk hb hfit,
    List.reverse_append, List.reverse_replicate, range_zero_tail]

end ShorECDLP.Paper2607_13816
