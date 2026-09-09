import ShorECDLP.Submission.«2607_13816».EEA.CoefficientWords

/-! # Complete prepared coefficient-prefix word and sign semantics -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem prefixFold_frame (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B : Nat)
    (h : CoefficientPrefixLayout r k K) (labels : List Nat)
    (hl : ∀ j ∈ labels, k ≤ j ∧ j ≤ K) (s : BasisState) :
    AgreesOutside (r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2)
      (labels.foldl (fun s j => coefficientFirstPrefixCell r k K mode target enabled B j s) s) s := by
  induction labels generalizing s with
  | nil => intro w hw; rfl
  | cons j labels ih =>
    have hj := hl j (by simp)
    have ht1 : r.work1At k j ∈ r.work1 := by
      unfold CoefficientPrefixRegisters.work1At CoefficientPrefixRegisters.laneAt
      rw [List.getD_eq_getElem _ _ (by rw [h.work1_length]; omega)]
      exact List.getElem_mem _
    have ht2 : r.work2At k j ∈ r.work2 := by
      unfold CoefficientPrefixRegisters.work2At CoefficientPrefixRegisters.laneAt
      rw [List.getD_eq_getElem _ _ (by rw [h.work2_length]; omega)]
      exact List.getElem_mem _
    intro w hw
    rw [List.foldl_cons,ih (fun j hj => hl j (by simp [hj])) _ w hw]
    have hn : w ≠ r.accumulator k K ∧ w ≠ r.carry k K ∧ w ∉ r.work1 ∧ w ∉ r.work2 := by
      simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using hw
    have h1 : w ≠ r.work1At k j := fun he => hn.2.2.1 (he ▸ ht1)
    have h2 : w ≠ r.work2At k j := fun he => hn.2.2.2 (he ▸ ht2)
    cases target <;> simp [coefficientFirstPrefixCell,CoefficientPrefixRegisters.targetAt,
      CoefficientPrefixRegisters.addendAt,writeRippleCell,upd,hn.1,hn.2.1,h1,h2]

private theorem first_frame (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K)
    (hc : Clean (r.path k K) s) (hcell : s (r.cellScratch k K) = false)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K)
    (ha : s (r.accumulator k K) = s r.control) :
    AgreesOutside (r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2)
      (run (unaryActionUnitary .inc (coefficientPrefixFirstLeaf r k K mode target)
        (coefficientPrefixTree r k K) r.control (r.path k K)) s) s := by
  rw [(run_coefficientPrefixFirstTraversal_scan r k K mode target s h hc hcell hv ha).1]
  apply prefixFold_frame r k K mode target (s r.control) _ h
  intro j hj
  simp only [List.mem_range'] at hj
  have := h.k_le_K
  omega


private theorem prefixSecondFold_frame (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B : Nat)
    (h : CoefficientPrefixLayout r k K) (labels : List Nat)
    (hl : ∀ j ∈ labels, k ≤ j ∧ j ≤ K) (s : BasisState) :
    AgreesOutside (r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2)
      (labels.foldl (fun s j => coefficientSecondPrefixCell r k K mode target enabled B j s) s) s := by
  induction labels generalizing s with
  | nil => intro w hw; rfl
  | cons j labels ih =>
    have hj := hl j (by simp)
    have ht1 : r.work1At k j ∈ r.work1 := by
      unfold CoefficientPrefixRegisters.work1At CoefficientPrefixRegisters.laneAt
      rw [List.getD_eq_getElem _ _ (by rw [h.work1_length]; omega)]
      exact List.getElem_mem _
    have ht2 : r.work2At k j ∈ r.work2 := by
      unfold CoefficientPrefixRegisters.work2At CoefficientPrefixRegisters.laneAt
      rw [List.getD_eq_getElem _ _ (by rw [h.work2_length]; omega)]
      exact List.getElem_mem _
    intro w hw
    rw [List.foldl_cons,ih (fun j hj => hl j (by simp [hj])) _ w hw]
    have hn : w ≠ r.accumulator k K ∧ w ≠ r.carry k K ∧ w ∉ r.work1 ∧ w ∉ r.work2 := by
      simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using hw
    have h1 : w ≠ r.work1At k j := fun he => hn.2.2.1 (he ▸ ht1)
    have h2 : w ≠ r.work2At k j := fun he => hn.2.2.2 (he ▸ ht2)
    cases target <;> simp [coefficientSecondPrefixCell,CoefficientPrefixRegisters.targetAt,
      CoefficientPrefixRegisters.addendAt,writeRippleCell,upd,hn.1,hn.2.1,h1,h2]

private theorem second_frame (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K)
    (hc : Clean (r.path k K) s) (hcell : s (r.cellScratch k K) = false)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K)
    (ha : s (r.accumulator k K) = false) :
    AgreesOutside (r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2)
      (run (unaryActionUnitary .dec (coefficientPrefixSecondLeaf r k K mode target)
        (coefficientPrefixTree r k K) r.control (r.path k K)) s) s := by
  rw [(run_coefficientPrefixSecondTraversal_scan r k K mode target s h hc hcell hv ha).1]
  apply prefixSecondFold_frame r k K mode target (s r.control) _ h
  intro j hj
  simp only [List.mem_reverse,List.mem_range'] at hj
  have := h.k_le_K
  omega


private theorem scratch_slot (r : CoefficientPrefixRegisters) (k K i : Nat)
    (h : CoefficientPrefixLayout r k K) (hi : i < r.scratch.length)
    (hc : i ≠ r.scratchBase k K) (ha : i ≠ r.scratchBase k K+1) :
    r.scratch.getD i 0 ∉ r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2 := by
  let pre := [r.control,r.sign] ++ r.work1 ++ r.work2 ++ r.boundary
  have hp : (pre ++ r.scratch).Nodup := by
    simpa only [pre,CoefficientPrefixRegisters.allWires,List.append_assoc] using h.physical
  have hh := List.nodup_append.mp hp
  have haidx : r.scratchBase k K+1 < r.scratch.length := by rw [h.scratch_length]; omega
  have hcidx : r.scratchBase k K < r.scratch.length := by rw [h.scratch_length]; omega
  have hm : r.scratch.getD i 0 ∈ r.scratch := by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hna : r.scratch.getD i 0 ≠ r.accumulator k K := by
    unfold CoefficientPrefixRegisters.accumulator
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ haidx]
    exact fun he => ha (hh.2.1.getElem_inj_iff.mp he)
  have hnc : r.scratch.getD i 0 ≠ r.carry k K := by
    unfold CoefficientPrefixRegisters.carry
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hcidx]
    exact fun he => hc (hh.2.1.getElem_inj_iff.mp he)
  have hnw : r.scratch.getD i 0 ∉ r.work1 ++ r.work2 := by
    intro hw
    exact hh.2.2 _ (by simp only [pre,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; tauto) _ hm rfl
  simpa only [List.mem_cons,List.mem_append,not_or,and_assoc] using
    (show r.scratch.getD i 0 ≠ r.accumulator k K ∧ r.scratch.getD i 0 ≠ r.carry k K ∧
      r.scratch.getD i 0 ∉ r.work1 ++ r.work2 from ⟨hna,hnc,hnw⟩)

private theorem path_outside (r : CoefficientPrefixRegisters) (k K : Nat)
    (h : CoefficientPrefixLayout r k K) (w : Wire) (hw : w ∈ r.path k K) :
    w ∉ r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2 := by
  change w ∈ r.scratch.take (quotientSwapUnaryDepth k K) at hw
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hw
  have hib : i < min (quotientSwapUnaryDepth k K) r.scratch.length := by
    simpa only [List.length_take] using hi
  have hin : i < r.scratch.length := lt_of_lt_of_le hib (Nat.min_le_right _ _)
  have hid : i < quotientSwapUnaryDepth k K := lt_of_lt_of_le hib (Nat.min_le_left _ _)
  have hbase : quotientSwapUnaryDepth k K ≤ r.scratchBase k K := Nat.le_max_left _ _
  have hslot := scratch_slot r k K i h hin (by omega) (by omega)
  have he' : r.scratch.getD i 0 = w := by
    rw [List.getD_eq_getElem _ _ hin]
    simpa only [List.getElem_take] using he
  exact he' ▸ hslot

private theorem cell_outside (r : CoefficientPrefixRegisters) (k K : Nat)
    (h : CoefficientPrefixLayout r k K) :
    r.cellScratch k K ∉ r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2 := by
  exact scratch_slot r k K (r.scratchBase k K+2) h (by rw [h.scratch_length]; omega) (by omega) (by omega)

private theorem fixed_outside (r : CoefficientPrefixRegisters) (k K : Nat)
    (h : CoefficientPrefixLayout r k K) (w : Wire) (hw : w ∈ r.control :: r.sign :: r.boundary) :
    w ∉ r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2 := by
  let banks := r.work1 ++ r.work2
  let pre := [r.control,r.sign] ++ banks ++ r.boundary
  have hp : (pre ++ r.scratch).Nodup := by
    simpa only [pre,banks,CoefficientPrefixRegisters.allWires,List.append_assoc] using h.physical
  have hh := List.nodup_append.mp hp
  have hwpre : w ∈ pre := by simp only [pre,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; tauto
  have hs : ∀ x ∈ r.scratch, w ≠ x := fun x hx => hh.2.2 w hwpre x hx
  have hmacc : r.accumulator k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.accumulator
    rw [List.getD_eq_getElem _ _ (by rw [h.scratch_length]; omega)]
    exact List.getElem_mem _
  have hmcarry : r.carry k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.carry
    rw [List.getD_eq_getElem _ _ (by rw [h.scratch_length]; omega)]
    exact List.getElem_mem _
  have hb : w ∉ banks := by
    have hf : ([r.control,r.sign] ++ (banks ++ r.boundary)).Nodup := by
      simpa only [pre,List.append_assoc] using hh.1
    have hf' := List.nodup_append.mp hf
    intro hwb
    simp only [List.mem_cons] at hw
    rcases hw with hctl | hsign | hbound
    · subst w; exact hf'.2.2 _ (by simp) _ (List.mem_append_left _ hwb) rfl
    · subst w; exact hf'.2.2 _ (by simp) _ (List.mem_append_left _ hwb) rfl
    · exact (List.nodup_append.mp hf'.2.1).2.2 _ hwb _ hbound rfl
  simpa only [banks,List.mem_cons,List.mem_append,not_or,and_assoc] using
    (show w ≠ r.accumulator k K ∧ w ≠ r.carry k K ∧ w ∉ banks from ⟨hs _ hmacc,hs _ hmcarry,hb⟩)


private theorem not_sign (r : CoefficientPrefixRegisters) (k K : Nat)
    (h : CoefficientPrefixLayout r k K) (w : Wire)
    (hw : w ∈ r.control :: r.work1 ++ r.work2 ++ r.boundary ++ r.scratch) : w ≠ r.sign := by
  have hp : (r.control :: r.sign :: (r.work1 ++ r.work2 ++ r.boundary ++ r.scratch)).Nodup := by
    simpa only [CoefficientPrefixRegisters.allWires,List.cons_append,List.nil_append,List.append_assoc] using h.physical
  have hctl := (List.nodup_cons.mp hp).1
  have hsign := (List.nodup_cons.mp (List.nodup_cons.mp hp).2).1
  simp only [List.mem_cons,List.mem_append,or_assoc] at hw
  intro he
  subst w
  rcases hw with hctl' | h1 | h2 | hb | hs
  · exact hctl (by simp [hctl'])
  · exact hsign (by simp [h1])
  · exact hsign (by simp [h2])
  · exact hsign (by simp [hb])
  · exact hsign (by simp [hs])

private theorem first_pathCell (r : CoefficientPrefixRegisters) (k K : Nat)
    (h : CoefficientPrefixLayout r k K) (s t : BasisState)
    (hf : AgreesOutside (r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2) t s)
    (hc : Clean (r.path k K) s) (hcell : s (r.cellScratch k K) = false) :
    Clean (r.path k K) t ∧ t (r.cellScratch k K) = false := by
  constructor
  · intro w hw
    exact (hf w (path_outside r k K h w hw)).trans (hc w hw)
  · exact (hf _ (cell_outside r k K h)).trans hcell


private theorem lane_mem (r : CoefficientPrefixRegisters) (k K j : Nat)
    (h : CoefficientPrefixLayout r k K) (hj : j ∈ (List.range' k (K-k+1)).reverse)
    (target : CoefficientTarget) :
    r.targetAt target k j ∈ r.work1 ++ r.work2 ∧ r.addendAt target k j ∈ r.work1 ++ r.work2 := by
  have hb : k ≤ j ∧ j ≤ K := by simp only [List.mem_reverse,List.mem_range'] at hj; have := h.k_le_K; omega
  have h1 : r.work1At k j ∈ r.work1 := by
    unfold CoefficientPrefixRegisters.work1At CoefficientPrefixRegisters.laneAt
    rw [List.getD_eq_getElem _ _ (by rw [h.work1_length]; omega)]
    exact List.getElem_mem _
  have h2 : r.work2At k j ∈ r.work2 := by
    unfold CoefficientPrefixRegisters.work2At CoefficientPrefixRegisters.laneAt
    rw [List.getD_eq_getElem _ _ (by rw [h.work2_length]; omega)]
    exact List.getElem_mem _
  cases target <;> simp [CoefficientPrefixRegisters.targetAt,CoefficientPrefixRegisters.addendAt,h1,h2]

set_option maxHeartbeats 2000000 in
private theorem scan_pair (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K)
    (hc : Clean (r.path k K) s) (hcell : s (r.cellScratch k K) = false)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K)
    (ha : s (r.accumulator k K) = s r.control) :
    let labels := (List.range' k (K-k+1)).reverse
    let ts := labels.map (r.targetAt target k)
    let ads := labels.map (r.addendAt target k)
    let B := boolWordToNat (wireValues r.boundary s)
    let expected := maskedRippleExpectedWords mode (labels.map (fun j => s r.control && decide (j ≤ B)))
      (wireValues ts s) (wireValues ads s) (s (r.carry k K))
    let first := run (unaryActionUnitary .inc (coefficientPrefixFirstLeaf r k K mode target)
      (coefficientPrefixTree r k K) r.control (r.path k K)) s
    let signed := if signUpdate then first[r.sign ↦ first r.sign ^^ first (r.carry k K)] else first
    let final := run (unaryActionUnitary .dec (coefficientPrefixSecondLeaf r k K mode target)
      (coefficientPrefixTree r k K) r.control (r.path k K)) signed
    (wireValues ts final,wireValues ads final,final (r.carry k K)) = (expected.1,wireValues ads s,s (r.carry k K)) ∧
      final r.sign = (s r.sign ^^ (signUpdate && expected.2)) ∧ final (r.accumulator k K) = s r.control := by
  let labels := (List.range' k (K-k+1)).reverse
  let ts := labels.map (r.targetAt target k)
  let ads := labels.map (r.addendAt target k)
  let B := boolWordToNat (wireValues r.boundary s)
  let es := labels.map (fun j => s r.control && decide (j ≤ B))
  let first := run (unaryActionUnitary .inc (coefficientPrefixFirstLeaf r k K mode target)
      (coefficientPrefixTree r k K) r.control (r.path k K)) s
  let signed := if signUpdate then first[r.sign ↦ first r.sign ^^ first (r.carry k K)] else first
  let final := run (unaryActionUnitary .dec (coefficientPrefixSecondLeaf r k K mode target)
      (coefficientPrefixTree r k K) r.control (r.path k K)) signed
  have hf := first_frame r k K mode target s h hc hcell hv ha
  have hfp := first_pathCell r k K h s first hf hc hcell
  have hfa : first (r.accumulator k K) = false :=
    (run_coefficientPrefixFirstTraversal_scan r k K mode target s h hc hcell hv ha).2
  have hsig : ∀ w, w ≠ r.sign → signed w = first w := by
    intro w hw; cases signUpdate <;> simp [signed,upd,hw]
  have hfixed : ∀ w ∈ r.control :: r.boundary, signed w = s w := by
    intro w hw
    rw [hsig w (not_sign r k K h w (by simp only [List.mem_cons,List.mem_append] at *; tauto))]
    exact hf w (fixed_outside r k K h w (by simp only [List.mem_cons] at *; tauto))
  have hctl : signed r.control = s r.control := hfixed _ (by simp)
  have hbound : wireValues r.boundary signed = wireValues r.boundary s := by
    apply List.map_congr_left; intro w hw; exact hfixed w (by simp [hw])
  have hsv : boolWordToNat (wireValues r.boundary signed) ∈ quotientSwapLabels k K := hbound ▸ hv
  have hsp : Clean (r.path k K) signed := by
    intro w hw
    have hws : w ∈ r.scratch := List.mem_of_mem_take (show w ∈ r.scratch.take (quotientSwapUnaryDepth k K) from hw)
    rw [hsig w (not_sign r k K h w (by simp [hws]))]
    exact hfp.1 w hw
  have hcellmem : r.cellScratch k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.cellScratch
    rw [List.getD_eq_getElem _ _ (by rw [h.scratch_length]; omega)]
    exact List.getElem_mem _
  have hsc : signed (r.cellScratch k K) = false := by
    rw [hsig _ (not_sign r k K h _ (by simp [hcellmem]))]; exact hfp.2
  have hsn : r.sign ≠ r.accumulator k K ∧ r.sign ≠ r.carry k K := by
    have hh := fixed_outside r k K h r.sign (by simp)
    simp only [List.mem_cons,List.mem_append,not_or,and_assoc] at hh
    exact ⟨hh.1,hh.2.1⟩
  have hsa : signed (r.accumulator k K) = false := by rw [hsig _ (Ne.symm hsn.1)]; exact hfa
  have hwords : wireValues ts signed = wireValues ts first ∧ wireValues ads signed = wireValues ads first := by
    constructor
    all_goals
      apply List.map_congr_left
      intro w hw
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
      apply hsig
      apply not_sign r k K h
    · have hm := (lane_mem r k K j h hj target).1
      simp only [List.mem_cons,List.mem_append] at *; tauto
    · have hm := (lane_mem r k K j h hj target).2
      simp only [List.mem_cons,List.mem_append] at *; tauto
  have hcarry : signed (r.carry k K) = first (r.carry k K) := hsig _ (Ne.symm hsn.2)
  have hw1 := run_coefficientPrefixFirstTraversal_words r k K mode target s h hc hcell hv ha
  have hw2 := run_coefficientPrefixSecondTraversal_words r k K mode target signed h hsp hsc hsv hsa
  change (wireValues ts first,wireValues ads first,first (r.carry k K)) =
    maskedRippleFirstWords mode es (wireValues ts s) (wireValues ads s) (s (r.carry k K)) at hw1
  change (wireValues ts final,wireValues ads final,final (r.carry k K)) =
    maskedRippleSecondWords mode (labels.map (fun j => signed r.control && decide (j ≤ boolWordToNat (wireValues r.boundary signed))))
      (wireValues ts signed) (wireValues ads signed) (signed (r.carry k K)) at hw2
  rw [hctl,hbound,hwords.1,hwords.2,hcarry] at hw2
  have ht := congrArg (fun x : List Bool × List Bool × Bool => x.1) hw1
  have had := congrArg (fun x : List Bool × List Bool × Bool => x.2.1) hw1
  have hca := congrArg (fun x : List Bool × List Bool × Bool => x.2.2) hw1
  dsimp only at ht had hca
  rw [ht,had,hca] at hw2
  have hfu := maskedRippleWords_fusion mode es (wireValues ts s) (wireValues ads s) (s (r.carry k K))
    (by simp [es,ts,wireValues]) (by simp [ts,ads,wireValues])
  dsimp only at hfu
  rw [hfu.1] at hw2
  refine ⟨hw2,?_,?_⟩
  · have hs2 := second_frame r k K mode target signed h hsp hsc hsv hsa r.sign (fixed_outside r k K h _ (by simp))
    have hs1 := hf r.sign (fixed_outside r k K h _ (by simp))
    change first r.sign = s r.sign at hs1
    change final r.sign = signed r.sign at hs2
    change final r.sign = (s r.sign ^^ (signUpdate && (maskedRippleExpectedWords mode es (wireValues ts s) (wireValues ads s) (s (r.carry k K))).2))
    rw [hs2]
    cases signUpdate <;> simp [signed,hs1,hca,hfu.2]
  · exact (run_coefficientPrefixSecondTraversal_scan r k K mode target signed h hsp hsc hsv hsa).2.trans hctl


private theorem acc_separation (r : CoefficientPrefixRegisters) (k K : Nat)
    (h : CoefficientPrefixLayout r k K) :
    r.carry k K ≠ r.accumulator k K ∧ ∀ w ∈ r.work1 ++ r.work2, w ≠ r.accumulator k K := by
  let pre := [r.control,r.sign] ++ r.work1 ++ r.work2 ++ r.boundary
  have hp : (pre ++ r.scratch).Nodup := by
    simpa only [pre,CoefficientPrefixRegisters.allWires,List.append_assoc] using h.physical
  have hh := List.nodup_append.mp hp
  have haidx : r.scratchBase k K+1 < r.scratch.length := by rw [h.scratch_length]; omega
  have hcidx : r.scratchBase k K < r.scratch.length := by rw [h.scratch_length]; omega
  constructor
  · unfold CoefficientPrefixRegisters.accumulator CoefficientPrefixRegisters.carry
    rw [List.getD_eq_getElem _ _ haidx,List.getD_eq_getElem _ _ hcidx]
    intro he
    have := hh.2.1.getElem_inj_iff.mp he
    omega
  · intro w hw
    apply hh.2.2 w (by simp only [pre,List.mem_append] at *; tauto)
    unfold CoefficientPrefixRegisters.accumulator
    rw [List.getD_eq_getElem _ _ haidx]
    exact List.getElem_mem _

set_option maxHeartbeats 2000000 in
/-- The complete prepared coefficient prefix computes its masked arithmetic word,
restores the addend and scratch, and optionally XORs the arithmetic carry into sign. -/
theorem run_coefficientPrefixUnitary_words (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K) (hc : CoefficientPrefixReady r s)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K) :
    let labels := (List.range' k (K-k+1)).reverse
    let ts := labels.map (r.targetAt target k)
    let ads := labels.map (r.addendAt target k)
    let expected := maskedRippleExpectedWords mode
      (labels.map (fun j => s r.control && decide (j ≤ boolWordToNat (wireValues r.boundary s))))
      (wireValues ts s) (wireValues ads s) false
    let final := run (coefficientPrefixUnitary r k K mode signUpdate target) s
    wireValues ts final = expected.1 ∧ wireValues ads final = wireValues ads s ∧
      final r.sign = (s r.sign ^^ (signUpdate && expected.2)) ∧
      CoefficientPrefixReady r final ∧ AgreesOutside (r.sign :: r.work1 ++ r.work2) final s := by
  let labels := (List.range' k (K-k+1)).reverse
  let ts := labels.map (r.targetAt target k)
  let ads := labels.map (r.addendAt target k)
  let seeded := s[r.accumulator k K ↦ s r.control]
  let first := run (unaryActionUnitary .inc (coefficientPrefixFirstLeaf r k K mode target)
    (coefficientPrefixTree r k K) r.control (r.path k K)) seeded
  let signed := if signUpdate then first[r.sign ↦ first r.sign ^^ first (r.carry k K)] else first
  let second := run (unaryActionUnitary .dec (coefficientPrefixSecondLeaf r k K mode target)
    (coefficientPrefixTree r k K) r.control (r.path k K)) signed
  have ham : r.accumulator k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.accumulator
    rw [List.getD_eq_getElem _ _ (by rw [h.scratch_length]; omega)]
    exact List.getElem_mem _
  have hcm : r.carry k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.carry
    rw [List.getD_eq_getElem _ _ (by rw [h.scratch_length]; omega)]
    exact List.getElem_mem _
  have hcellm : r.cellScratch k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.cellScratch
    rw [List.getD_eq_getElem _ _ (by rw [h.scratch_length]; omega)]
    exact List.getElem_mem _
  have hna : ∀ w, w ∉ r.accumulator k K :: r.carry k K :: r.work1 ++ r.work2 → w ≠ r.accumulator k K := by
    intro w hw he; apply hw; simp [he]
  have hfixed : ∀ w ∈ r.control :: r.sign :: r.boundary, seeded w = s w := by
    intro w hw
    simp only [seeded,upd,hna w (fixed_outside r k K h w hw),if_false]
  have hctl : seeded r.control = s r.control := hfixed _ (by simp)
  have hsign : seeded r.sign = s r.sign := hfixed _ (by simp)
  have hbound : wireValues r.boundary seeded = wireValues r.boundary s := by
    apply List.map_congr_left; intro w hw; exact hfixed w (by simp [hw])
  have hpath : Clean (r.path k K) seeded := by
    intro w hw
    rw [show seeded w = s w by simp only [seeded,upd,hna w (path_outside r k K h w hw),if_false]]
    exact hc w (List.mem_of_mem_take (show w ∈ r.scratch.take (quotientSwapUnaryDepth k K) from hw))
  have hcell : seeded (r.cellScratch k K) = false := by
    simp only [seeded,upd,hna _ (cell_outside r k K h),if_false]
    exact hc _ hcellm
  have hac : seeded (r.accumulator k K) = seeded r.control := by simp [seeded,hctl]
  have hv' : boolWordToNat (wireValues r.boundary seeded) ∈ quotientSwapLabels k K := hbound ▸ hv
  have hsep := acc_separation r k K h
  have hcarry : seeded (r.carry k K) = false := by simp only [seeded,upd,hsep.1,if_false]; exact hc _ hcm
  have hwords : wireValues ts seeded = wireValues ts s ∧ wireValues ads seeded = wireValues ads s := by
    constructor
    all_goals
      apply List.map_congr_left
      intro w hw
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    · simp only [seeded,upd,hsep.2 _ (lane_mem r k K j h hj target).1,if_false]
    · simp only [seeded,upd,hsep.2 _ (lane_mem r k K j h hj target).2,if_false]
  have hp := scan_pair r k K mode signUpdate target seeded h hpath hcell hv' hac
  change (wireValues ts second,wireValues ads second,second (r.carry k K)) =
      ((maskedRippleExpectedWords mode
        (labels.map (fun j => seeded r.control && decide (j ≤ boolWordToNat (wireValues r.boundary seeded))))
        (wireValues ts seeded) (wireValues ads seeded) (seeded (r.carry k K))).1,wireValues ads seeded,seeded (r.carry k K)) ∧
    second r.sign = (seeded r.sign ^^ (signUpdate && (maskedRippleExpectedWords mode
        (labels.map (fun j => seeded r.control && decide (j ≤ boolWordToNat (wireValues r.boundary seeded))))
        (wireValues ts seeded) (wireValues ads seeded) (seeded (r.carry k K))).2)) ∧
      second (r.accumulator k K) = seeded r.control at hp
  rw [hctl,hsign,hbound,hwords.1,hwords.2,hcarry] at hp
  have hseed : run [.CX r.control (r.accumulator k K)] s = seeded := by
    simp only [run,List.foldl,applyGate,seeded,hc _ ham,Bool.false_xor]
  have hshape : run (coefficientPrefixUnitary r k K mode signUpdate target) s =
      run [.CX r.control (r.accumulator k K)] second := by
    have hsg : run (coefficientPrefixSignCircuit r k K signUpdate) first = signed := by cases signUpdate <;> rfl
    simp only [coefficientPrefixUnitary,run_append,hseed]
    change run [.CX r.control (r.accumulator k K)]
      (run (unaryActionUnitary .dec (coefficientPrefixSecondLeaf r k K mode target)
        (coefficientPrefixTree r k K) r.control (r.path k K))
          (run (coefficientPrefixSignCircuit r k K signUpdate) first)) = _
    rw [hsg]
  have hfinal : ∀ w, w ≠ r.accumulator k K →
      run (coefficientPrefixUnitary r k K mode signUpdate target) s w = second w := by
    intro w hw; rw [hshape]; simp only [run,List.foldl,applyGate,upd,hw,if_false]
  have hfinalWords : wireValues ts (run (coefficientPrefixUnitary r k K mode signUpdate target) s) = wireValues ts second ∧
      wireValues ads (run (coefficientPrefixUnitary r k K mode signUpdate target) s) = wireValues ads second := by
    constructor
    all_goals
      apply List.map_congr_left
      intro w hw
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    · exact hfinal _ (hsep.2 _ (lane_mem r k K j h hj target).1)
    · exact hfinal _ (hsep.2 _ (lane_mem r k K j h hj target).2)
  refine ⟨hfinalWords.1.trans (congrArg Prod.fst hp.1),hfinalWords.2.trans (congrArg (fun x => x.2.1) hp.1),?_,
    coefficientPrefixUnitary_clean r mode signUpdate target s h hc,
    coefficientPrefixUnitary_frame r mode signUpdate target s h⟩
  exact (hfinal _ (hna _ (fixed_outside r k K h r.sign (by simp)))).trans hp.2.1
end ShorECDLP.Paper2607_13816
