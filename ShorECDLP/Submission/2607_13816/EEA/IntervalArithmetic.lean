import ShorECDLP.Submission.«2607_13816».EEA.IntervalWordBody
/-! # Selected-slice arithmetic of the actual interval body -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem range_mask (n L R : Nat) (enabled : Bool) (ho : L ≤ R) (hr : R < n) :
    (List.range n).map (fun j => enabled && decide (L ≤ j ∧ j ≤ R)) =
      List.replicate L false ++ List.replicate (R-L+1) enabled ++ List.replicate (n-R-1) false := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_append,List.length_replicate]
    omega
  · intro i hi hj
    have hin : i < n := by simpa using hi
    simp only [List.getElem_map,List.getElem_range]
    by_cases hp : i < L
    · simp [List.length_replicate, hp, show ¬ L ≤ i by omega]
    · by_cases hm : i < L+(R-L+1)
      · have hlo : L ≤ i := by omega
        have hhi : i ≤ R := by omega
        simp [List.getElem_append, List.length_replicate, hlo, hhi]
        omega
      · have hhi : ¬ i ≤ R := by omega
        simp [List.getElem_append, List.length_replicate, hp, hhi]
        omega


private theorem split_word (xs : List Bool) (L m : Nat) :
    xs.take L ++ (xs.drop L).take m ++ xs.drop (L+m) = xs := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

private theorem expected_range_words (mode : RippleMode) (enabled : Bool) (ts ads : List Bool)
    (L R : Nat) (carry : Bool) (hlen : ts.length = ads.length)
    (ho : L ≤ R) (hr : R < ts.length) :
    maskedRippleExpectedWords mode
      ((List.range ts.length).map (fun j => enabled && decide (L ≤ j ∧ j ≤ R))) ts ads carry =
      (ts.take L ++ (uniformRippleExpectedWords mode enabled ((ts.drop L).take (R-L+1))
        ((ads.drop L).take (R-L+1)) carry).1 ++ ts.drop (R+1),
       (uniformRippleExpectedWords mode enabled ((ts.drop L).take (R-L+1))
        ((ads.drop L).take (R-L+1)) carry).2) := by
  let m := R-L+1
  have hl : L ≤ ts.length := by omega
  have hla : L ≤ ads.length := by omega
  have hm : m ≤ ts.length-L := by dsimp [m]; omega
  have hma : m ≤ ads.length-L := by omega
  have hp : (ts.take L).length = L := List.length_take_of_le hl
  have hpa : (ads.take L).length = L := List.length_take_of_le hla
  have hmid : ((ts.drop L).take m).length = m := by simp [List.length_take, List.length_drop, Nat.min_eq_left hm]
  have hmida : ((ads.drop L).take m).length = m := by simp [List.length_take, List.length_drop, Nat.min_eq_left hma]
  have hv := maskedRippleWords_interval mode enabled (ts.take L) ((ts.drop L).take m)
    (ts.drop (L+m)) (ads.take L) ((ads.drop L).take m) (ads.drop (L+m)) carry
    (hp.trans hpa.symm) (hmid.trans hmida.symm) (by simp [hlen])
  dsimp only at hv
  rw [split_word, split_word, hp, hmid] at hv
  have hpost : (ts.drop (L+m)).length = ts.length-R-1 := by simp only [List.length_drop]; dsimp [m]; omega
  rw [hpost, ← range_mask ts.length L R enabled ho hr] at hv
  have hf := maskedRippleWords_fusion mode
    ((List.range ts.length).map (fun j => enabled && decide (L ≤ j ∧ j ≤ R)))
    ts ads carry (by simp) hlen
  apply Prod.ext
  · have he := congrArg (fun x : List Bool × List Bool × Bool => x.1) (hf.1.symm.trans hv.1)
    simpa only [show L+m = R+1 by dsimp [m]; omega] using he
  · exact hf.2.symm.trans hv.2

private theorem expected_range_value (mode : RippleMode) (ts ads : List Bool)
    (L R : Nat) (carry : Bool) (hlen : ts.length = ads.length)
    (ho : L ≤ R) (hr : R < ts.length) :
    let expected := maskedRippleExpectedWords mode
      ((List.range ts.length).map (fun j => true && decide (L ≤ j ∧ j ≤ R))) ts ads carry
    boolWordToNat (((expected.1.drop L).take (R-L+1)).reverse) =
      (match mode with
      | .add => boolWordToNat (((ts.drop L).take (R-L+1)).reverse) +
          boolWordToNat (((ads.drop L).take (R-L+1)).reverse) + carry.toNat
      | .sub => boolWordToNat (((ts.drop L).take (R-L+1)).reverse) + 2^(R-L+1) -
          boolWordToNat (((ads.drop L).take (R-L+1)).reverse) - carry.toNat) % 2^(R-L+1) := by
  have hl : L ≤ ts.length := by omega
  have hpre : (ts.take L).length = L := List.length_take_of_le hl
  have hmiddle : ((ts.drop L).take (R-L+1)).length = R-L+1 := by
    simp only [List.length_take,List.length_drop]
    omega
  have hmid : ((ts.drop L).take (R-L+1)).length = ((ads.drop L).take (R-L+1)).length := by
    simp [hlen]
  dsimp only
  rw [expected_range_words mode true ts ads L R carry hlen ho hr]
  simp only [List.append_assoc,List.drop_append,hpre,Nat.sub_self,List.drop_zero,
    List.drop_take,List.take_zero,List.nil_append,List.take_append,
    uniformRippleExpectedWords_length,hmiddle,List.append_nil]
  rw [List.take_of_length_le (show (uniformRippleExpectedWords mode true ((ts.drop L).take (R-L+1))
    ((ads.drop L).take (R-L+1)) carry).1.length ≤ R-L+1 by simp only [uniformRippleExpectedWords_length,hmiddle]; rfl)]
  cases mode
  · simpa only [hmiddle] using uniformRippleExpectedWords_add_mod _ _ carry hmid
  · simpa only [hmiddle] using uniformRippleExpectedWords_sub_mod _ _ carry hmid

/-- With its control enabled, the actual interval body adds/subtracts the selected
slice modulo its width, including the incoming carry/borrow. Lists of physical
lanes are most-significant-bit first, hence the reversal for `boolWordToNat`. -/
theorem run_intervalAddSubBody_value (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout r k K target)
    (hc : Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (ha : state (r.accumulator k K) = false)
    (hr : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K)
    (ho : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state))
    (he : state r.control = true) :
    let L := boolWordToNat (wireValues r.lengthQ state)
    let width := boolWordToNat (wireValues r.lengthS state) - L + 1
    let ts := (List.range (intervalLaneCount k K)).map (r.targetAt target)
    let ads := (List.range (intervalLaneCount k K)).map (r.addendAt target)
    let value := fun ws s => boolWordToNat ((((wireValues ws s).drop L).take width).reverse)
    value ts (run (intervalAddSubBodyUnitary r k K mode signUpdate target) state) =
      (match mode with
      | .add => value ts state + value ads state + (state (r.carry k K)).toNat
      | .sub => value ts state + 2^width - value ads state - (state (r.carry k K)).toNat) % 2^width := by
  have hw := congrArg (fun x : List Bool × List Bool × Bool => x.1)
    (run_intervalAddSubBody_words r k K mode signUpdate target state h hc ha hr ho).1
  dsimp only at hw ⊢
  rw [hw]
  rw [he]
  have hv := expected_range_value mode
    (wireValues ((List.range (intervalLaneCount k K)).map (r.targetAt target)) state)
    (wireValues ((List.range (intervalLaneCount k K)).map (r.addendAt target)) state)
    (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state))
    (state (r.carry k K)) (by simp [wireValues]) ho (by
      simp only [wireValues, List.length_map, List.length_range]
      simp only [wireValues, intervalTopRelative, intervalLaneCount] at hr ⊢
      omega)
  simpa only [wireValues, List.length_map, List.length_range] using hv





/-- The actual body changes only the selected target slice. The complete target
word retains its prefix and suffix; addend/carry are restored and sign uses the
selected arithmetic's outgoing carry/borrow. -/
theorem run_intervalAddSubBody_slices (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout r k K target)
    (hc : Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (ha : state (r.accumulator k K) = false)
    (hr : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K)
    (ho : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state)) :
    let L := boolWordToNat (wireValues r.lengthQ state)
    let R := boolWordToNat (wireValues r.lengthS state)
    let ts := (List.range (intervalLaneCount k K)).map (r.targetAt target)
    let ads := (List.range (intervalLaneCount k K)).map (r.addendAt target)
    let before := wireValues ts state
    let addend := wireValues ads state
    let result := uniformRippleExpectedWords mode (state r.control)
      ((before.drop L).take (R-L+1)) ((addend.drop L).take (R-L+1)) (state (r.carry k K))
    let final := run (intervalAddSubBodyUnitary r k K mode signUpdate target) state
    (wireValues ts final, wireValues ads final, final (r.carry k K)) =
      (before.take L ++ result.1 ++ before.drop (R+1), addend, state (r.carry k K)) ∧
    final r.sign = (if signUpdate then state r.sign ^^ result.2 else state r.sign) := by
  have hb := run_intervalAddSubBody_words r k K mode signUpdate target state h hc ha hr ho
  have hx := expected_range_words mode (state r.control)
    (wireValues ((List.range (intervalLaneCount k K)).map (r.targetAt target)) state)
    (wireValues ((List.range (intervalLaneCount k K)).map (r.addendAt target)) state)
    (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state))
    (state (r.carry k K)) (by simp [wireValues]) ho (by
      simp only [wireValues,List.length_map,List.length_range]
      simp only [wireValues,intervalTopRelative,intervalLaneCount] at hr ⊢
      omega)
  simp only [wireValues,List.length_map,List.length_range] at hx
  dsimp only at hb ⊢
  simp only [wireValues] at hb ⊢
  rw [hx] at hb
  exact hb
end ShorECDLP.Paper2607_13816
