import ShorECDLP.Submission.«2607_13816».EEA.CoefficientScan
import ShorECDLP.Submission.«2607_13816».EEA.MaskedState

/-! # Coefficient prefix folds execute the masked word passes -/
namespace ShorECDLP.Paper2607_13816
open Classical

private def sameExceptAcc (acc : Wire) (s t : BasisState) : Prop :=
  ∀ w, w ≠ acc → s w = t w

private theorem first_cell (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B j : Nat)
    (s u : BasisState)
    (h : sameExceptAcc (r.accumulator k K) s u)
    (ht : (r.targetAt target k j) ≠ (r.accumulator k K))
    (ha : (r.addendAt target k j) ≠ (r.accumulator k K))
    (hc : (r.carry k K) ≠ (r.accumulator k K)) :
    sameExceptAcc (r.accumulator k K) (coefficientFirstPrefixCell r k K mode target enabled B j s)
      (writeRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) (rippleFirstBits mode (enabled && decide (j ≤ B))
        (readRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) u)) u) := by
  have hr : readRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) s = readRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) u := by
    simp [readRippleCell, h (r.targetAt target k j) ht, h (r.addendAt target k j) ha, h (r.carry k K) hc]
  intro w hw
  simp only [coefficientFirstPrefixCell]
  rw [hr]
  simp [writeRippleCell, upd, hw, h w hw]

private theorem second_cell (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B j : Nat)
    (s u : BasisState)
    (h : sameExceptAcc (r.accumulator k K) s u)
    (ht : (r.targetAt target k j) ≠ (r.accumulator k K))
    (ha : (r.addendAt target k j) ≠ (r.accumulator k K))
    (hc : (r.carry k K) ≠ (r.accumulator k K)) :
    sameExceptAcc (r.accumulator k K) (coefficientSecondPrefixCell r k K mode target enabled B j s)
      (writeRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) (rippleSecondBits mode (enabled && decide (j ≤ B))
        (readRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) u)) u) := by
  have hr : readRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) s = readRippleCell (r.targetAt target k j) (r.addendAt target k j) (r.carry k K) u := by
    simp [readRippleCell, h (r.targetAt target k j) ht, h (r.addendAt target k j) ha, h (r.carry k K) hc]
  intro w hw
  simp only [coefficientSecondPrefixCell]
  rw [hr]
  simp [writeRippleCell, upd, hw, h w hw]

private theorem first_fold (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B : Nat) (labels : List Nat) (s u : BasisState)
    (h : sameExceptAcc (r.accumulator k K) s u)
    (ht : ∀ j ∈ labels, (r.targetAt target k) j ≠ (r.accumulator k K)) (ha : ∀ j ∈ labels, (r.addendAt target k) j ≠ (r.accumulator k K))
   
    (hc : (r.carry k K) ≠ (r.accumulator k K)) :
    sameExceptAcc (r.accumulator k K)
      (labels.reverse.foldl (fun state j => coefficientFirstPrefixCell r k K mode target enabled B j state) s)
      (maskedRippleFirstState mode (labels.map (fun j => enabled && decide (j ≤ B)))
        (labels.map (r.targetAt target k)) (labels.map (r.addendAt target k)) (r.carry k K) u) := by
  induction labels generalizing s u with
  | nil => exact h
  | cons j labels ih =>
    have hf := ih s u h (fun j hj => ht j (by simp [hj])) (fun j hj => ha j (by simp [hj]))
    have hcell := first_cell r k K mode target enabled B j _ _ hf
      (ht j (by simp)) (ha j (by simp)) hc
    simpa only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_cons, maskedRippleFirstState] using hcell

private theorem second_fold (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool) (B : Nat) (labels : List Nat) (s u : BasisState)
    (h : sameExceptAcc (r.accumulator k K) s u)
    (ht : ∀ j ∈ labels, (r.targetAt target k) j ≠ (r.accumulator k K)) (ha : ∀ j ∈ labels, (r.addendAt target k) j ≠ (r.accumulator k K))
   
    (hc : (r.carry k K) ≠ (r.accumulator k K)) :
    sameExceptAcc (r.accumulator k K)
      (labels.foldl (fun state j => coefficientSecondPrefixCell r k K mode target enabled B j state) s)
      (maskedRippleSecondState mode (labels.map (fun j => enabled && decide (j ≤ B)))
        (labels.map (r.targetAt target k)) (labels.map (r.addendAt target k)) (r.carry k K) u) := by
  induction labels generalizing s u with
  | nil => exact h
  | cons j labels ih =>
    have hcell := second_cell r k K mode target enabled B j s u h
      (ht j (by simp)) (ha j (by simp)) hc
    have hf := ih _ _ hcell (fun j hj => ht j (by simp [hj])) (fun j hj => ha j (by simp [hj]))
    simpa only [List.foldl_cons, List.map_cons, maskedRippleSecondState] using hf


private theorem layout_roles (acc carry : Wire) (targetAt addendAt : Nat → Wire) (labels : List Nat)
    (hnd : (acc :: carry :: (labels.map targetAt ++ labels.map addendAt)).Nodup) :
    (∀ j ∈ labels, targetAt j ≠ acc) ∧ (∀ j ∈ labels, addendAt j ≠ acc) ∧ carry ≠ acc := by
  have hn := (List.nodup_cons.mp hnd).1
  refine ⟨?_, ?_, ?_⟩
  · intro j hj he
    have hm : targetAt j ∈ labels.map targetAt := List.mem_map_of_mem hj
    apply hn
    simp [← he, hm]
  · intro j hj he
    have hm : addendAt j ∈ labels.map addendAt := List.mem_map_of_mem hj
    apply hn
    simp [← he, hm]
  · intro he
    apply hn
    simp [← he]

private theorem frame_values (acc : Wire) (ws : List Wire) (s u : BasisState)
    (h : sameExceptAcc acc s u) (hw : ∀ w ∈ ws, w ≠ acc) :
    wireValues ws s = wireValues ws u := by
  apply List.map_congr_left
  intro w hm
  exact h w (hw w hm)



/-- The numeric inclusive first scan reads as the corresponding masked word pass.
Its accumulator writes do not affect the target/addend words or carry. -/
theorem coefficientFirstPrefixFold_words (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool)
    (B : Nat) (labels : List Nat) (state : BasisState)
    (hnd : ((r.accumulator k K) :: (r.carry k K) :: (labels.map (r.targetAt target k) ++ labels.map (r.addendAt target k))).Nodup) :
    let final := labels.reverse.foldl (fun s j => coefficientFirstPrefixCell r k K mode target enabled B j s) state
    (wireValues (labels.map (r.targetAt target k)) final, wireValues (labels.map (r.addendAt target k)) final, final (r.carry k K)) =
      maskedRippleFirstWords mode (labels.map (fun j => enabled && decide (j ≤ B)))
        (wireValues (labels.map (r.targetAt target k)) state) (wireValues (labels.map (r.addendAt target k)) state) (state (r.carry k K)) := by
  obtain ⟨ht,ha,hc⟩ := layout_roles (r.accumulator k K) (r.carry k K) (r.targetAt target k) (r.addendAt target k) labels hnd
  have hf := first_fold r k K mode target enabled B labels state state
    (fun _ _ => rfl) ht ha hc
  have ht' : ∀ w ∈ labels.map (r.targetAt target k), w ≠ (r.accumulator k K) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ht j hj
  have ha' : ∀ w ∈ labels.map (r.addendAt target k), w ≠ (r.accumulator k K) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ha j hj
  have hT := frame_values (r.accumulator k K) (labels.map (r.targetAt target k)) _ _ hf ht'
  have hA := frame_values (r.accumulator k K) (labels.map (r.addendAt target k)) _ _ hf ha'
  have hC := hf (r.carry k K) hc
  dsimp only
  rw [hT, hA, hC]
  exact maskedRippleFirstState_words mode _ _ _ (r.carry k K) state (List.nodup_cons.mp hnd).2
    (by simp) (by simp)

/-- The numeric inclusive second scan reads as the corresponding masked word pass.
Its accumulator writes do not affect the target/addend words or carry. -/
theorem coefficientSecondPrefixFold_words (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool)
    (B : Nat) (labels : List Nat) (state : BasisState)
    (hnd : ((r.accumulator k K) :: (r.carry k K) :: (labels.map (r.targetAt target k) ++ labels.map (r.addendAt target k))).Nodup) :
    let final := labels.foldl (fun s j => coefficientSecondPrefixCell r k K mode target enabled B j s) state
    (wireValues (labels.map (r.targetAt target k)) final, wireValues (labels.map (r.addendAt target k)) final, final (r.carry k K)) =
      maskedRippleSecondWords mode (labels.map (fun j => enabled && decide (j ≤ B)))
        (wireValues (labels.map (r.targetAt target k)) state) (wireValues (labels.map (r.addendAt target k)) state) (state (r.carry k K)) := by
  obtain ⟨ht,ha,hc⟩ := layout_roles (r.accumulator k K) (r.carry k K) (r.targetAt target k) (r.addendAt target k) labels hnd
  have hf := second_fold r k K mode target enabled B labels state state
    (fun _ _ => rfl) ht ha hc
  have ht' : ∀ w ∈ labels.map (r.targetAt target k), w ≠ (r.accumulator k K) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ht j hj
  have ha' : ∀ w ∈ labels.map (r.addendAt target k), w ≠ (r.accumulator k K) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ha j hj
  have hT := frame_values (r.accumulator k K) (labels.map (r.targetAt target k)) _ _ hf ht'
  have hA := frame_values (r.accumulator k K) (labels.map (r.addendAt target k)) _ _ hf ha'
  have hC := hf (r.carry k K) hc
  dsimp only
  rw [hT, hA, hC]
  exact maskedRippleSecondState_words mode _ _ _ (r.carry k K) state (List.nodup_cons.mp hnd).2
    (by simp) (by simp)

/-- The two numeric inclusive folds fuse to the masked arithmetic word, restoring
all wires outside the target list except their explicit accumulator updates. -/
theorem coefficientPrefixPair_fusion (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (enabled : Bool)
    (B : Nat) (labels : List Nat) (state : BasisState)
    (hnd : ((r.accumulator k K) :: (r.carry k K) :: (labels.map (r.targetAt target k) ++ labels.map (r.addendAt target k))).Nodup) :
    let first := labels.reverse.foldl (fun s j => coefficientFirstPrefixCell r k K mode target enabled B j s) state
    let final := labels.foldl (fun s j => coefficientSecondPrefixCell r k K mode target enabled B j s) first
    (wireValues (labels.map (r.targetAt target k)) final, wireValues (labels.map (r.addendAt target k)) final, final (r.carry k K)) =
      ((maskedRippleExpectedWords mode (labels.map (fun j => enabled && decide (j ≤ B)))
        (wireValues (labels.map (r.targetAt target k)) state) (wireValues (labels.map (r.addendAt target k)) state) (state (r.carry k K))).1,
        wireValues (labels.map (r.addendAt target k)) state, state (r.carry k K)) ∧
      (∀ w, w ∉ (r.accumulator k K) :: labels.map (r.targetAt target k) → final w = state w) := by
  obtain ⟨ht,ha,hc⟩ := layout_roles (r.accumulator k K) (r.carry k K) (r.targetAt target k) (r.addendAt target k) labels hnd
  have hf := first_fold r k K mode target enabled B labels state state
    (fun _ _ => rfl) ht ha hc
  have hs := second_fold r k K mode target enabled B labels _ _ hf ht ha hc
  have hm := maskedRippleState_fusion mode (labels.map (fun j => enabled && decide (j ≤ B)))
    (labels.map (r.targetAt target k)) (labels.map (r.addendAt target k)) (r.carry k K) state (List.nodup_cons.mp hnd).2 (by simp) (by simp)
  have ht' : ∀ w ∈ labels.map (r.targetAt target k), w ≠ (r.accumulator k K) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ht j hj
  have ha' : ∀ w ∈ labels.map (r.addendAt target k), w ≠ (r.accumulator k K) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ha j hj
  have hT := frame_values (r.accumulator k K) (labels.map (r.targetAt target k)) _ _ hs ht'
  have hA := frame_values (r.accumulator k K) (labels.map (r.addendAt target k)) _ _ hs ha'
  have hC := hs (r.carry k K) hc
  dsimp only
  constructor
  · rw [hT, hA, hC]
    exact hm.1
  · intro w hw
    have hw' : w ≠ (r.accumulator k K) ∧ w ∉ labels.map (r.targetAt target k) := by simpa only [List.mem_cons, not_or] using hw
    exact (hs w hw'.1).trans (hm.2 w hw'.2)



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

private theorem word_layout (r : CoefficientPrefixRegisters) (k K : Nat)
    (target : CoefficientTarget) (h : CoefficientPrefixLayout r k K) :
    (r.accumulator k K :: r.carry k K ::
      (((List.range' k (K-k+1)).reverse.map (r.targetAt target k)) ++
       ((List.range' k (K-k+1)).reverse.map (r.addendAt target k)))).Nodup := by
  have hp : (r.work1 ++ (r.work2 ++ (r.boundary ++ r.scratch))).Nodup :=
    (List.nodup_append.mp h.physical).2.1
  have h1 := List.nodup_append.mp hp
  have h2 := List.nodup_append.mp h1.2.1
  have hscr := (List.nodup_append.mp h2.2.1).2.1
  have haidx : r.scratchBase k K+1 < r.scratch.length := by rw [h.scratch_length]; omega
  have hcidx : r.scratchBase k K < r.scratch.length := by rw [h.scratch_length]; omega
  have ham : r.accumulator k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.accumulator
    rw [List.getD_eq_getElem _ _ haidx]
    exact List.getElem_mem _
  have hcm : r.carry k K ∈ r.scratch := by
    unfold CoefficientPrefixRegisters.carry
    rw [List.getD_eq_getElem _ _ hcidx]
    exact List.getElem_mem _
  have hac : r.accumulator k K ≠ r.carry k K := by
    unfold CoefficientPrefixRegisters.accumulator CoefficientPrefixRegisters.carry
    rw [List.getD_eq_getElem _ _ haidx,List.getD_eq_getElem _ _ hcidx]
    intro he
    have := hscr.getElem_inj_iff.mp he
    omega
  have hs1 : ∀ w ∈ r.scratch, w ∉ r.work1 := by
    intro w hw hm
    exact h1.2.2 w hm w (List.mem_append_right _ (List.mem_append_right _ hw)) rfl
  have hs2 : ∀ w ∈ r.scratch, w ∉ r.work2 := by
    intro w hw hm
    exact h2.2.2 w hm w (List.mem_append_right _ hw) rfl
  have h12 : List.Disjoint r.work1 r.work2 := by
    intro w hw1 hw2
    exact h1.2.2 w hw1 w (List.mem_append_left _ hw2) rfl
  rw [List.map_reverse,List.map_reverse,target_lanes r k K target h,addend_lanes r k K target h]
  cases target <;> simp only [List.nodup_cons,List.mem_cons,List.mem_append,List.mem_reverse,not_or]
  · exact ⟨⟨hac,hs1 _ ham,hs2 _ ham⟩,⟨hs1 _ hcm,hs2 _ hcm⟩,
      List.nodup_append.mpr ⟨List.nodup_reverse.mpr h1.1,List.nodup_reverse.mpr h2.1,fun a ha b hb he => h12 (List.mem_reverse.mp ha) (he ▸ List.mem_reverse.mp hb)⟩⟩
  · exact ⟨⟨hac,hs2 _ ham,hs1 _ ham⟩,⟨hs2 _ hcm,hs1 _ hcm⟩,
      List.nodup_append.mpr ⟨List.nodup_reverse.mpr h2.1,List.nodup_reverse.mpr h1.1,fun a ha b hb he => h12 (List.mem_reverse.mp hb) (he ▸ List.mem_reverse.mp ha)⟩⟩

/-- The actual increasing coefficient scan computes the masked first word pass.
The returned lists are most-significant-bit first, reversing the physical coefficient lanes. -/
theorem run_coefficientPrefixFirstTraversal_words (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K)
    (hc : Clean (r.path k K) s) (hcell : s (r.cellScratch k K) = false)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K)
    (ha : s (r.accumulator k K) = s r.control) :
    let labels := (List.range' k (K-k+1)).reverse
    let ts := labels.map (r.targetAt target k)
    let ads := labels.map (r.addendAt target k)
    let B := boolWordToNat (wireValues r.boundary s)
    let final := run (unaryActionUnitary .inc (coefficientPrefixFirstLeaf r k K mode target)
      (coefficientPrefixTree r k K) r.control (r.path k K)) s
    (wireValues ts final,wireValues ads final,final (r.carry k K)) =
      maskedRippleFirstWords mode (labels.map (fun j => s r.control && decide (j ≤ B)))
        (wireValues ts s) (wireValues ads s) (s (r.carry k K)) := by
  have hs := (run_coefficientPrefixFirstTraversal_scan r k K mode target s h hc hcell hv ha).1
  dsimp only at hs ⊢
  rw [hs]
  have hh := coefficientFirstPrefixFold_words r k K mode target (s r.control)
    (boolWordToNat (wireValues r.boundary s)) (List.range' k (K-k+1)).reverse s (word_layout r k K target h)
  simpa only [List.reverse_reverse] using hh

/-- The actual decreasing coefficient scan computes the masked second word pass. -/
theorem run_coefficientPrefixSecondTraversal_words (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (s : BasisState)
    (h : CoefficientPrefixLayout r k K)
    (hc : Clean (r.path k K) s) (hcell : s (r.cellScratch k K) = false)
    (hv : boolWordToNat (wireValues r.boundary s) ∈ quotientSwapLabels k K)
    (ha : s (r.accumulator k K) = false) :
    let labels := (List.range' k (K-k+1)).reverse
    let ts := labels.map (r.targetAt target k)
    let ads := labels.map (r.addendAt target k)
    let B := boolWordToNat (wireValues r.boundary s)
    let final := run (unaryActionUnitary .dec (coefficientPrefixSecondLeaf r k K mode target)
      (coefficientPrefixTree r k K) r.control (r.path k K)) s
    (wireValues ts final,wireValues ads final,final (r.carry k K)) =
      maskedRippleSecondWords mode (labels.map (fun j => s r.control && decide (j ≤ B)))
        (wireValues ts s) (wireValues ads s) (s (r.carry k K)) := by
  have hs := (run_coefficientPrefixSecondTraversal_scan r k K mode target s h hc hcell hv ha).1
  dsimp only at hs ⊢
  rw [hs]
  exact coefficientSecondPrefixFold_words r k K mode target (s r.control)
    (boolWordToNat (wireValues r.boundary s)) (List.range' k (K-k+1)).reverse s (word_layout r k K target h)
end ShorECDLP.Paper2607_13816
