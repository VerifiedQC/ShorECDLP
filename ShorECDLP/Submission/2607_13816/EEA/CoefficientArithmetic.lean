import ShorECDLP.Submission.«2607_13816».EEA.CoefficientComposition

/-!
# Arithmetic of the prepared coefficient prefix

The source scans select the inclusive physical window `k..boundary`. Its little-endian
low prefix performs uniform ripple arithmetic; the high suffix is unchanged. The
boundary-in-range hypothesis remains explicit until the reachable-state proof.
-/

namespace ShorECDLP.Paper2607_13816
open Classical

private theorem prefix_mask (k n B : Nat) (enabled : Bool) (hk : k ≤ B) (hB : B < k+n) :
    (List.range' k n).map (fun j => enabled && decide (j ≤ B)) =
      List.replicate (B-k+1) enabled ++ List.replicate (n-(B-k+1)) false := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range',List.length_append,List.length_replicate]
    omega
  · intro i hi hj
    have hin : i < n := by simpa only [List.length_map,List.length_range'] using hi
    simp only [List.getElem_map,List.getElem_range',Nat.one_mul]
    by_cases hm : i < B-k+1
    · have hp : k+i ≤ B := by omega
      simp [List.length_replicate,hm,hp]
    · have hp : ¬ k+i ≤ B := by omega
      simp [List.getElem_append,List.length_replicate,hm,hp]

private theorem expected_suffix (mode : RippleMode) (enabled : Bool)
    (pre middle apre amid : List Bool) (carry : Bool)
    (hp : pre.length = apre.length) (hm : middle.length = amid.length) :
    maskedRippleExpectedWords mode (List.replicate pre.length false ++ List.replicate middle.length enabled)
      (pre++middle) (apre++amid) carry =
      (pre++(uniformRippleExpectedWords mode enabled middle amid carry).1,
        (uniformRippleExpectedWords mode enabled middle amid carry).2) := by
  have hf := maskedRippleWords_fusion mode
    (List.replicate pre.length false ++ List.replicate middle.length enabled)
    (pre++middle) (apre++amid) carry (by simp) (by simp [hp,hm])
  have hi := maskedRippleWords_interval mode enabled pre middle ([] : List Bool) apre amid ([] : List Bool) carry hp hm rfl
  simp only [List.length_nil,List.replicate_zero,List.append_nil] at hi
  dsimp only at hf hi
  apply Prod.ext
  · exact congrArg (fun x : List Bool × List Bool × Bool => x.1) (hf.1.symm.trans hi.1)
  · exact hf.2.symm.trans hi.2

private theorem expected_prefix (mode : RippleMode) (enabled : Bool)
    (ts ads : List Bool) (m : Nat) (hlen : ts.length = ads.length) (hm : m ≤ ts.length) :
    maskedRippleExpectedWords mode (List.replicate (ts.length-m) false ++ List.replicate m enabled)
      ts.reverse ads.reverse false =
      ((ts.drop m).reverse ++ (uniformRippleExpectedWords mode enabled (ts.take m).reverse (ads.take m).reverse false).1,
        (uniformRippleExpectedWords mode enabled (ts.take m).reverse (ads.take m).reverse false).2) := by
  have he := expected_suffix mode enabled (ts.drop m).reverse (ts.take m).reverse
    (ads.drop m).reverse (ads.take m).reverse false (by simp [hlen]) (by simp [hlen])
  have hsplit (xs : List Bool) : (xs.drop m).reverse ++ (xs.take m).reverse = xs.reverse := by
    rw [← List.reverse_append,List.take_append_drop]
  simpa only [List.length_reverse,List.length_drop,List.length_take,Nat.min_eq_left hm,hsplit] using he

private theorem mapped_lanes (ws : List Wire) (k count : Nat) (hl : ws.length = count) :
    (List.range' k count).map (fun j => ws.getD (j-k) (ws.getD 0 0)) = ws := by
  apply List.ext_getElem
  · simp [hl]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range',Nat.one_mul,Nat.add_sub_cancel_left]
    exact List.getD_eq_getElem _ _ hj

private theorem target_lanes (r : CoefficientPrefixRegisters) (k K : Nat)
    (target : CoefficientTarget) (h : CoefficientPrefixLayout r k K) :
    (List.range' k (K-k+1)).map (r.targetAt target k) =
      (match target with | .work1 => r.work1 | .work2 => r.work2) := by
  cases target
  · exact mapped_lanes r.work1 k _ h.work1_length
  · exact mapped_lanes r.work2 k _ h.work2_length
private theorem addend_lanes (r : CoefficientPrefixRegisters) (k K : Nat)
    (target : CoefficientTarget) (h : CoefficientPrefixLayout r k K) :
    (List.range' k (K-k+1)).map (r.addendAt target k) =
      (match target with | .work1 => r.work2 | .work2 => r.work1) := by
  cases target
  · exact mapped_lanes r.work2 k _ h.work2_length
  · exact mapped_lanes r.work1 k _ h.work1_length

private theorem reverse_values (ws : List Wire) (s : BasisState) :
    wireValues ws.reverse s = (wireValues ws s).reverse := List.map_reverse

/-- The complete coefficient circuit changes exactly its little-endian prefix.
The high suffix is preserved; sign receives only the selected prefix's carry/borrow. -/
theorem run_coefficientPrefixUnitary_prefix (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K) (hc : CoefficientPrefixReady r s)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K) :
    let ts := match target with | .work1 => r.work1 | .work2 => r.work2
    let ads := match target with | .work1 => r.work2 | .work2 => r.work1
    let m := boolWordToNat (wireValues r.boundary s)-k+1
    let expected := uniformRippleExpectedWords mode (s r.control)
      ((wireValues ts s).take m).reverse ((wireValues ads s).take m).reverse false
    let final := run (coefficientPrefixUnitary r k K mode signUpdate target) s
    wireValues ts final = expected.1.reverse ++ (wireValues ts s).drop m ∧
      wireValues ads final = wireValues ads s ∧
      final r.sign = (s r.sign ^^ (signUpdate && expected.2)) ∧
      CoefficientPrefixReady r final ∧ AgreesOutside (r.sign :: r.work1 ++ r.work2) final s := by
  let ts := match target with | .work1 => r.work1 | .work2 => r.work2
  let ads := match target with | .work1 => r.work2 | .work2 => r.work1
  let B := boolWordToNat (wireValues r.boundary s)
  let m := B-k+1
  have hT : ts.length = K-k+1 := by cases target <;> first | exact h.work1_length | exact h.work2_length
  have hA : ads.length = K-k+1 := by cases target <;> first | exact h.work1_length | exact h.work2_length
  have hb : k ≤ B ∧ B < k+(K-k+1) := by
    simp only [quotientSwapLabels,List.mem_range'] at hv
    have := h.k_le_K
    dsimp [B]
    omega
  have hm : m ≤ (wireValues ts s).length := by simp only [wireValues,List.length_map,hT]; dsimp [m]; omega
  have hlen : (wireValues ts s).length = (wireValues ads s).length := by simp only [wireValues,List.length_map,hT,hA]
  have hh := run_coefficientPrefixUnitary_words r k K mode signUpdate target s h hc hv
  dsimp only at hh
  simp only [List.map_reverse,target_lanes r k K target h,addend_lanes r k K target h,reverse_values] at hh
  rw [prefix_mask k (K-k+1) B (s r.control) hb.1 hb.2,List.reverse_append,List.reverse_replicate,List.reverse_replicate] at hh
  have he := expected_prefix mode (s r.control) (wireValues ts s) (wireValues ads s) m hlen hm
  have he' : maskedRippleExpectedWords mode
      (List.replicate (K-k+1-m) false ++ List.replicate m (s r.control))
      (wireValues ts s).reverse (wireValues ads s).reverse false =
      (((wireValues ts s).drop m).reverse ++
        (uniformRippleExpectedWords mode (s r.control) ((wireValues ts s).take m).reverse ((wireValues ads s).take m).reverse false).1,
        (uniformRippleExpectedWords mode (s r.control) ((wireValues ts s).take m).reverse ((wireValues ads s).take m).reverse false).2) := by
    simpa only [wireValues,List.length_map,hT] using he
  change (wireValues ts (run (coefficientPrefixUnitary r k K mode signUpdate target) s)).reverse = _ ∧
    (wireValues ads (run (coefficientPrefixUnitary r k K mode signUpdate target) s)).reverse = (wireValues ads s).reverse ∧ _ at hh
  rw [he'] at hh
  refine ⟨?_,List.reverse_injective hh.2.1,hh.2.2.1,hh.2.2.2⟩
  have ht := congrArg List.reverse hh.1
  simpa only [List.reverse_reverse,List.reverse_append] using ht
/-- With control enabled, the selected low prefix performs modular addition or
subtraction at its own width, and every higher target bit is preserved. -/
theorem run_coefficientPrefixUnitary_value (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K) (hc : CoefficientPrefixReady r s)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K)
    (hen : s r.control = true) :
    let ts := match target with | .work1 => r.work1 | .work2 => r.work2
    let ads := match target with | .work1 => r.work2 | .work2 => r.work1
    let m := boolWordToNat (wireValues r.boundary s)-k+1
    let x := boolWordToNat ((wireValues ts s).take m)
    let y := boolWordToNat ((wireValues ads s).take m)
    let final := run (coefficientPrefixUnitary r k K mode signUpdate target) s
    boolWordToNat ((wireValues ts final).take m) =
      (match mode with | .add => (x+y) % 2^m | .sub => (x+2^m-y) % 2^m) ∧
      (wireValues ts final).drop m = (wireValues ts s).drop m := by
  let ts := match target with | .work1 => r.work1 | .work2 => r.work2
  let ads := match target with | .work1 => r.work2 | .work2 => r.work1
  let m := boolWordToNat (wireValues r.boundary s)-k+1
  have hT : ts.length = K-k+1 := by cases target <;> first | exact h.work1_length | exact h.work2_length
  have hA : ads.length = K-k+1 := by cases target <;> first | exact h.work1_length | exact h.work2_length
  have hm : m ≤ (wireValues ts s).length := by
    simp only [quotientSwapLabels,List.mem_range'] at hv
    simp only [wireValues,List.length_map,hT]
    dsimp [m]
    omega
  have hlen : ((wireValues ts s).take m).reverse.length = ((wireValues ads s).take m).reverse.length := by
    simp only [List.length_reverse,List.length_take,wireValues,List.length_map,hT,hA]
  have htlen : ((wireValues ts s).take m).reverse.length = m := by
    simp only [List.length_reverse,List.length_take,Nat.min_eq_left hm]
  have hp := (run_coefficientPrefixUnitary_prefix r k K mode signUpdate target s h hc hv).1
  change wireValues ts _ = _ at hp
  rw [hen] at hp
  let expected := uniformRippleExpectedWords mode true ((wireValues ts s).take m).reverse
    ((wireValues ads s).take m).reverse false
  have helen : expected.1.reverse.length = m := by
    simp only [expected,List.length_reverse,uniformRippleExpectedWords_length,htlen]
  change boolWordToNat ((wireValues ts _).take m) = _ ∧ (wireValues ts _).drop m = _
  rw [hp]
  change boolWordToNat ((expected.1.reverse ++ (wireValues ts s).drop m).take m) = _ ∧
    (expected.1.reverse ++ (wireValues ts s).drop m).drop m = _
  rw [← helen,List.take_left,List.drop_left]
  rw [helen]
  refine ⟨?_,rfl⟩
  cases mode with
  | add =>
    have ha := uniformRippleExpectedWords_add_mod ((wireValues ts s).take m).reverse
      ((wireValues ads s).take m).reverse false hlen
    simpa only [expected,List.reverse_reverse,htlen,Bool.toNat_false,Nat.add_zero] using ha
  | sub =>
    have ha := uniformRippleExpectedWords_sub_mod ((wireValues ts s).take m).reverse
      ((wireValues ads s).take m).reverse false hlen
    simpa only [expected,List.reverse_reverse,htlen,Bool.toNat_false,Nat.sub_zero] using ha
end ShorECDLP.Paper2607_13816
