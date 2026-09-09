import ShorECDLP.Submission.«2607_13816».EEA.TBoundaryArithmetic

/-! # Numeric coefficient update of the complete Block E circuit -/
namespace ShorECDLP.Paper2607_13816
open Classical

private theorem coefficient_pair_values (ts ads : List Bool) (subEnable addEnable : Bool)
    (hlen : ts.length = ads.length) :
    let sub := uniformRippleExpectedWords .sub subEnable ts ads false
    let add := uniformRippleExpectedWords .add addEnable sub.1 ads false
    let modulus := 2^ts.length
    let x := boolWordToNat ads.reverse
    let y := boolWordToNat ts.reverse
    let middle := if subEnable then (y+modulus-x)%modulus else y
    boolWordToNat add.1.reverse = (if addEnable then (middle+x)%modulus else middle) ∧
      add.2 = (addEnable && decide (modulus ≤ middle+x)) := by
  let sub := uniformRippleExpectedWords .sub subEnable ts ads false
  have hv : boolWordToNat sub.1.reverse =
      (if subEnable then (boolWordToNat ts.reverse+2^ts.length-boolWordToNat ads.reverse)%2^ts.length
      else boolWordToNat ts.reverse) := by
    cases subEnable with
    | false => simp only [sub,uniformRippleExpectedWords_disabled,Bool.false_eq_true,if_false]
    | true => simpa only [sub,Bool.toNat_false,Nat.sub_zero,if_true]
        using uniformRippleExpectedWords_sub_mod ts ads false hlen
  have hl : sub.1.length = ts.length := uniformRippleExpectedWords_length _ _ _ _ _
  dsimp only
  change boolWordToNat (uniformRippleExpectedWords .add addEnable sub.1 ads false).1.reverse = _ ∧
    (uniformRippleExpectedWords .add addEnable sub.1 ads false).2 = _
  cases addEnable with
  | false => simpa only [uniformRippleExpectedWords_disabled,Bool.false_eq_true,if_false,Bool.false_and]
      using And.intro hv (Eq.refl false)
  | true =>
    have ha := uniformRippleExpectedWords_add_mod sub.1 ads false (hl.trans hlen)
    have hc := uniformRippleExpectedWords_add_carry sub.1 ads false (hl.trans hlen)
    simpa only [hl,hv,Bool.toNat_false,Nat.add_zero,if_true,Bool.true_and]
      using And.intro ha hc

/-- Complete Block E updates the selected coefficient prefix modulo its own
width. The sign records the phase flip and the overflow of the final addition. -/
theorem blockEForward_coefficient_value (r : IndexedStepRegisters) (n index : Nat)
    (window : ActiveWindow) (s : BasisState) (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hr : IndexedStepReady r s)
    (hv : boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
      (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
      (wireValues r.tBoundary.lengthSLow s) n).1 ∈ quotientSwapLabels window.start window.stop) :
    let cr := r.coefficient window
    let B := boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
      (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
      (wireValues r.tBoundary.lengthSLow s) n).1
    let m := B-window.start+1
    let modulus := 2^m
    let x := boolWordToNat ((wireValues cr.work1 s).take m)
    let y := boolWordToNat ((wireValues cr.work2 s).take m)
    let subEnable := s r.phase1 && !(!s r.phase2 && s r.sign)
    let middle := if subEnable then (y+modulus-x)%modulus else y
    let final := run (blockEForward r n window) s
    boolWordToNat ((wireValues cr.work2 final).take m) =
        (if s r.phase1 then (middle+x)%modulus else middle) ∧
      (wireValues cr.work2 final).drop m = (wireValues cr.work2 s).drop m ∧
      wireValues cr.work1 final = wireValues cr.work1 s ∧
      final r.sign = ((s r.sign ^^ s r.phase1) ^^
        (s r.phase1 && decide (modulus ≤ middle+x))) ∧
      IndexedStepReady r final ∧
      AgreesOutside (r.sign :: cr.work1 ++ cr.work2) final s := by
  let cr := r.coefficient window
  let B := boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
    (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
    (wireValues r.tBoundary.lengthSLow s) n).1
  let m := B-window.start+1
  let ts := wireValues cr.work2 s
  let ads := wireValues cr.work1 s
  let sub := uniformRippleExpectedWords .sub (s r.phase1 && !(!s r.phase2 && s r.sign))
    (ts.take m).reverse (ads.take m).reverse false
  let add := uniformRippleExpectedWords .add (s r.phase1) sub.1 (ads.take m).reverse false
  let final := run (blockEForward r n window) s
  have hl : CoefficientPrefixLayout cr window.start window.stop := by subst window; exact h.coefficient
  have hm : m ≤ ts.length := by
    have hv' := hv
    simp only [quotientSwapLabels,List.mem_range'] at hv'
    simp only [ts,wireValues,List.length_map,hl.work2_length]
    dsimp [m,B]
    omega
  have hlen : (ts.take m).reverse.length = (ads.take m).reverse.length := by
    simp only [List.length_reverse,List.length_take,ts,ads,wireValues,List.length_map,
      hl.work1_length,hl.work2_length]
  have htlen : (ts.take m).reverse.length = m := by
    simp only [List.length_reverse,List.length_take,Nat.min_eq_left hm]
  have hslen : sub.1.reverse.length = m := by
    simp only [sub,List.length_reverse,uniformRippleExpectedWords_length,htlen]
  have halen : add.1.reverse.length = m := by
    simp only [add,List.length_reverse,uniformRippleExpectedWords_length]
    simpa only [List.length_reverse] using hslen
  have htake : (sub.1.reverse ++ ts.drop m).take m = sub.1.reverse := by
    rw [← hslen]; simp
  have hdrop : (sub.1.reverse ++ ts.drop m).drop m = ts.drop m := by
    rw [← hslen]; simp
  have hf := blockEForward_words r n index window s h hw hr hv
  have hout := hf.1
  change wireValues cr.work2 final =
    (uniformRippleExpectedWords .add (s r.phase1)
      ((sub.1.reverse ++ ts.drop m).take m).reverse (ads.take m).reverse false).1.reverse ++
      (sub.1.reverse ++ ts.drop m).drop m at hout
  rw [htake,hdrop,List.reverse_reverse] at hout
  change wireValues cr.work2 final = add.1.reverse ++ ts.drop m at hout
  have hsign := hf.2.2.1
  change final r.sign = ((s r.sign ^^ s r.phase1) ^^
    (uniformRippleExpectedWords .add (s r.phase1)
      ((sub.1.reverse ++ ts.drop m).take m).reverse (ads.take m).reverse false).2) at hsign
  rw [htake,List.reverse_reverse] at hsign
  change final r.sign = ((s r.sign ^^ s r.phase1) ^^ add.2) at hsign
  have hnum := coefficient_pair_values (ts.take m).reverse (ads.take m).reverse
    (s r.phase1 && !(!s r.phase2 && s r.sign)) (s r.phase1) hlen
  simp only [List.reverse_reverse,htlen] at hnum
  have htakeout : (wireValues cr.work2 final).take m = add.1.reverse := by
    rw [hout,← halen]; simp
  have hdropout : (wireValues cr.work2 final).drop m = ts.drop m := by
    rw [hout,← halen]; simp
  dsimp only
  change boolWordToNat ((wireValues cr.work2 final).take m) = _ ∧
    (wireValues cr.work2 final).drop m = _ ∧ _
  refine ⟨?_,?_,hf.2.1,?_,hf.2.2.2⟩
  · rw [htakeout]
    exact hnum.1
  · exact hdropout
  · change final r.sign = _
    rw [hsign]
    exact congrArg (fun b => (s r.sign ^^ s r.phase1) ^^ b) hnum.2

/-- The complete output word has a canonical coefficient prefix and its original high fields. -/
theorem blockEForward_coefficient_packed (r : IndexedStepRegisters) (n index : Nat)
    (window : ActiveWindow) (s : BasisState) (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hr : IndexedStepReady r s)
    (hv : boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
      (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
      (wireValues r.tBoundary.lengthSLow s) n).1 ∈ quotientSwapLabels window.start window.stop) :
    let cr := r.coefficient window
    let B := boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
      (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
      (wireValues r.tBoundary.lengthSLow s) n).1
    let m := B-window.start+1
    let modulus := 2^m
    let x := boolWordToNat ((wireValues cr.work1 s).take m)
    let y := boolWordToNat ((wireValues cr.work2 s).take m)
    let subEnable := s r.phase1 && !(!s r.phase2 && s r.sign)
    let middle := if subEnable then (y+modulus-x)%modulus else y
    let final := run (blockEForward r n window) s
    wireValues cr.work2 final =
        constantBits m (if s r.phase1 then (middle+x)%modulus else middle) ++
          (wireValues cr.work2 s).drop m ∧
      wireValues cr.work1 final = wireValues cr.work1 s ∧
      final r.sign = ((s r.sign ^^ s r.phase1) ^^
        (s r.phase1 && decide (modulus ≤ middle+x))) ∧
      IndexedStepReady r final ∧
      AgreesOutside (r.sign :: cr.work1 ++ cr.work2) final s := by
  let cr := r.coefficient window
  let B := boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
    (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
    (wireValues r.tBoundary.lengthSLow s) n).1
  let m := B-window.start+1
  let final := run (blockEForward r n window) s
  have hl : CoefficientPrefixLayout cr window.start window.stop := by subst window; exact h.coefficient
  have hm : m ≤ cr.work2.length := by
    have hv' := hv
    simp only [quotientSwapLabels,List.mem_range'] at hv'
    rw [hl.work2_length]
    dsimp [m,B]
    omega
  have hlen : ((wireValues cr.work2 final).take m).length = m := by
    simp only [List.length_take,wireValues,List.length_map,Nat.min_eq_left hm]
  have hf := blockEForward_coefficient_value r n index window s h hw hr hv
  dsimp only at hf ⊢
  refine ⟨?_,hf.2.2⟩
  have hvalue := hf.1
  change boolWordToNat ((wireValues cr.work2 final).take m) = _ at hvalue
  have hb := boolWordToNat_lt_pow_two ((wireValues cr.work2 final).take m)
  rw [hlen,hvalue] at hb
  have hprefix := boolWordToNat_injective_of_length
    (show ((wireValues cr.work2 final).take m).length = (constantBits m _).length by simp only [hlen,constantBits_length])
    (by rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt hb]; exact hvalue)
  change wireValues cr.work2 final = _
  rw [← List.take_append_drop m (wireValues cr.work2 final),hprefix]
  have hdrop := hf.2.1
  change (wireValues cr.work2 final).drop m = (wireValues cr.work2 s).drop m at hdrop
  rw [hdrop]

private theorem bank_window_frame (ws : List Wire) (start width : Nat)
    (before after : BasisState) (hn : ws.Nodup)
    (hf : ∀ w ∈ ws, w ∉ (ws.drop start).take width → after w = before w) :
    wireValues ws after = (wireValues ws before).take start ++
      wireValues ((ws.drop start).take width) after ++
      (wireValues ws before).drop (start+width) := by
  have hpre : (wireValues ws after).take start = (wireValues ws before).take start := by
    rw [wireValues,wireValues,← List.map_take,← List.map_take]
    apply List.map_congr_left
    intro w hm
    apply hf w (List.mem_of_mem_take hm)
    intro hw
    exact (List.disjoint_left.mp (List.disjoint_take_drop hn (Nat.le_refl start))) hm
      (List.mem_of_mem_take hw)
  have hpost : (wireValues ws after).drop (start+width) = (wireValues ws before).drop (start+width) := by
    rw [wireValues,wireValues,← List.map_drop,← List.map_drop]
    apply List.map_congr_left
    intro w hm
    apply hf w (List.mem_of_mem_drop hm)
    intro hw
    have hd : (ws.drop start).Nodup := hn.sublist (List.drop_sublist _ _)
    have hm' : w ∈ (ws.drop start).drop width := by simpa only [List.drop_drop] using hm
    exact (List.disjoint_left.mp (List.disjoint_take_drop hd (Nat.le_refl width))) hw hm'
  calc
    wireValues ws after = (wireValues ws after).take start ++
        (((wireValues ws after).drop start).take width ++
          ((wireValues ws after).drop start).drop width) := by simp only [List.take_append_drop]
    _ = _ := by
      rw [List.drop_drop,hpre,hpost]
      simp only [wireValues,List.map_take,List.map_drop,List.append_assoc]

private theorem coefficient_bank_geometry (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) :
    r.work1.Nodup ∧ r.work2.Nodup ∧
      (∀ w ∈ r.work1, w ≠ r.sign ∧ w ∉ r.work2) ∧
      (∀ w ∈ r.work2, w ≠ r.sign ∧ w ∉ r.work1) := by
  have hn : ([r.phase1,r.phase2,r.iter,r.sign] ++ (r.work1 ++ (r.work2 ++
      (r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux)))).Nodup := by
    simpa only [IndexedStepRegisters.allWires,List.append_assoc] using h.physical
  have htail := (List.nodup_append.mp hn).2.1
  have h1 := (List.nodup_append.mp htail).1
  have h2 := (List.nodup_append.mp (List.nodup_append.mp htail).2.1).1
  have hd := (List.nodup_append.mp htail).2.2
  have hs := (List.nodup_append.mp hn).2.2
  refine ⟨h1,h2,?_,?_⟩
  · intro w hw
    refine ⟨Ne.symm (hs r.sign (by simp) w (by simp [hw])),?_⟩
    intro hw2
    exact hd w hw w (by simp [hw2]) rfl
  · intro w hw
    refine ⟨Ne.symm (hs r.sign (by simp) w (by simp [hw])),?_⟩
    intro hw1
    exact hd w hw1 w (by simp [hw]) rfl

/-- Complete physical work banks after the coefficient update, including all neighboring fields. -/
theorem blockEForward_workBanks (r : IndexedStepRegisters) (n index : Nat)
    (window : ActiveWindow) (s : BasisState) (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hr : IndexedStepReady r s)
    (hv : boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
      (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
      (wireValues r.tBoundary.lengthSLow s) n).1 ∈ quotientSwapLabels window.start window.stop) :
    let cr := r.coefficient window
    let B := boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
      (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
      (wireValues r.tBoundary.lengthSLow s) n).1
    let m := B-window.start+1
    let modulus := 2^m
    let x := boolWordToNat ((wireValues cr.work1 s).take m)
    let y := boolWordToNat ((wireValues cr.work2 s).take m)
    let subEnable := s r.phase1 && !(!s r.phase2 && s r.sign)
    let middle := if subEnable then (y+modulus-x)%modulus else y
    let final := run (blockEForward r n window) s
    wireValues r.work2 final =
        (wireValues r.work2 s).take (window.start-1) ++ constantBits m (if s r.phase1 then (middle+x)%modulus else middle) ++
          (wireValues r.work2 s).drop (window.start-1+m) ∧
      wireValues r.work1 final = wireValues r.work1 s ∧
      final r.sign = ((s r.sign ^^ s r.phase1) ^^
        (s r.phase1 && decide (modulus ≤ middle+x))) ∧
      IndexedStepReady r final ∧
      AgreesOutside (r.sign :: cr.work1 ++ cr.work2) final s := by
  let cr := r.coefficient window
  let offset := window.start-1
  let width := window.stop-window.start+1
  let B := boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
    (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
    (wireValues r.tBoundary.lengthSLow s) n).1
  let m := B-window.start+1
  let final := run (blockEForward r n window) s
  have hg := coefficient_bank_geometry r n index h
  have hf := blockEForward_coefficient_packed r n index window s h hw hr hv
  have hframe := hf.2.2.2.2
  have h1 := bank_window_frame r.work1 offset width s final hg.1 (by
    intro w hm hn
    apply hframe w
    have hs := (hg.2.2.1 w hm).1
    have hnot : w ∉ cr.work2 := fun hh => (hg.2.2.1 w hm).2
      (List.mem_of_mem_drop (List.mem_of_mem_take hh))
    change w ∉ cr.work1 at hn
    simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using And.intro hs (And.intro hn hnot))
  have h2 := bank_window_frame r.work2 offset width s final hg.2.1 (by
    intro w hm hn
    apply hframe w
    have hs := (hg.2.2.2 w hm).1
    have hnot : w ∉ cr.work1 := fun hh => (hg.2.2.2 w hm).2
      (List.mem_of_mem_drop (List.mem_of_mem_take hh))
    change w ∉ cr.work2 at hn
    simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using And.intro hs (And.intro hnot hn))
  change wireValues r.work1 final = (wireValues r.work1 s).take offset ++
    wireValues cr.work1 final ++ (wireValues r.work1 s).drop (offset+width) at h1
  change wireValues r.work2 final = (wireValues r.work2 s).take offset ++
    wireValues cr.work2 final ++ (wireValues r.work2 s).drop (offset+width) at h2
  have hadd := hf.2.1
  change wireValues cr.work1 final = wireValues cr.work1 s at hadd
  rw [hadd] at h1
  have h1full : wireValues r.work1 final = wireValues r.work1 s := by
    have hslice : wireValues cr.work1 s = ((wireValues r.work1 s).drop offset).take width := by
      simp only [cr,IndexedStepRegisters.coefficient,IndexedStepRegisters.windowSlice,
        wireValues,List.map_take,List.map_drop]
      rfl
    have hd : (wireValues r.work1 s).drop (offset+width) =
        ((wireValues r.work1 s).drop offset).drop width := by simp only [List.drop_drop]
    simpa only [hslice,hd,List.append_assoc,List.take_append_drop] using h1
  have hl : CoefficientPrefixLayout cr window.start window.stop := by subst window; exact h.coefficient
  have hm : m ≤ (wireValues cr.work2 s).length := by
    have hv' := hv
    simp only [quotientSwapLabels,List.mem_range'] at hv'
    simp only [wireValues,List.length_map,hl.work2_length]
    dsimp [m,B]
    omega
  have hrest : (wireValues cr.work2 s).drop m ++ (wireValues r.work2 s).drop (offset+width) =
      (wireValues r.work2 s).drop (offset+m) := by
    change (List.map s ((r.work2.drop offset).take width)).drop m ++
      (List.map s r.work2).drop (offset+width) = _
    have hm' : m ≤ (((List.map s r.work2).drop offset).take width).length := by
      simpa only [cr,IndexedStepRegisters.coefficient,IndexedStepRegisters.windowSlice,
        wireValues,List.map_take,List.map_drop] using hm
    have hd : (List.map s r.work2).drop (offset+width) =
        ((List.map s r.work2).drop offset).drop width := by simp only [List.drop_drop]
    simp only [List.map_take,List.map_drop]
    rw [hd,← List.drop_append_of_le_length hm',List.take_append_drop,List.drop_drop]
    rfl
  have hp := hf.1
  change wireValues cr.work2 final = constantBits m _ ++ (wireValues cr.work2 s).drop m at hp
  rw [hp] at h2
  dsimp only
  refine ⟨?_,h1full,hf.2.2⟩
  change wireValues r.work2 final = _
  simpa only [List.append_assoc,hrest] using h2

end ShorECDLP.Paper2607_13816
