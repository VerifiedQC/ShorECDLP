import ShorECDLP.Submission.«2607_13816».EEA.IntervalScan
import ShorECDLP.Submission.«2607_13816».EEA.MaskedState

/-! # Numeric inclusive-cell folds execute the masked word passes -/
namespace ShorECDLP.Paper2607_13816
open Classical

private def sameExceptAcc (acc : Wire) (s t : BasisState) : Prop :=
  ∀ w, w ≠ acc → s w = t w

private theorem first_cell (mode : RippleMode) (enabled : Bool) (acc t a c L R j : Nat)
    (s u : BasisState) (h : sameExceptAcc acc s u) (ht : t ≠ acc) (ha : a ≠ acc) (hc : c ≠ acc) :
    sameExceptAcc acc (intervalFirstInclusiveCell mode enabled acc t a c L R j s)
      (writeRippleCell t a c (rippleFirstBits mode (enabled && decide (L ≤ j ∧ j ≤ R))
        (readRippleCell t a c u)) u) := by
  have hr : readRippleCell t a c s = readRippleCell t a c u := by
    simp [readRippleCell, h t ht, h a ha, h c hc]
  intro w hw
  simp only [intervalFirstInclusiveCell]
  rw [hr]
  simp [writeRippleCell, upd, hw, h w hw]

private theorem second_cell (mode : RippleMode) (enabled : Bool) (acc t a c L R j : Nat)
    (s u : BasisState) (h : sameExceptAcc acc s u) (ht : t ≠ acc) (ha : a ≠ acc) (hc : c ≠ acc) :
    sameExceptAcc acc (intervalSecondInclusiveCell mode enabled acc t a c L R j s)
      (writeRippleCell t a c (rippleSecondBits mode (enabled && decide (L ≤ j ∧ j ≤ R))
        (readRippleCell t a c u)) u) := by
  have hr : readRippleCell t a c s = readRippleCell t a c u := by
    simp [readRippleCell, h t ht, h a ha, h c hc]
  intro w hw
  simp only [intervalSecondInclusiveCell]
  rw [hr]
  simp [writeRippleCell, upd, hw, h w hw]

private theorem first_fold (mode : RippleMode) (enabled : Bool) (acc carry L R : Nat)
    (targetAt addendAt : Nat → Wire) (labels : List Nat) (s u : BasisState)
    (h : sameExceptAcc acc s u)
    (ht : ∀ j ∈ labels, targetAt j ≠ acc) (ha : ∀ j ∈ labels, addendAt j ≠ acc)
    (hc : carry ≠ acc) :
    sameExceptAcc acc
      (labels.reverse.foldl (fun state j => intervalFirstInclusiveCell mode enabled acc
        (targetAt j) (addendAt j) carry L R j state) s)
      (maskedRippleFirstState mode (labels.map (fun j => enabled && decide (L ≤ j ∧ j ≤ R)))
        (labels.map targetAt) (labels.map addendAt) carry u) := by
  induction labels generalizing s u with
  | nil => exact h
  | cons j labels ih =>
    have hf := ih s u h (fun j hj => ht j (by simp [hj])) (fun j hj => ha j (by simp [hj]))
    have hcell := first_cell mode enabled acc (targetAt j) (addendAt j) carry L R j _ _ hf
      (ht j (by simp)) (ha j (by simp)) hc
    simpa only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_cons, maskedRippleFirstState] using hcell

private theorem second_fold (mode : RippleMode) (enabled : Bool) (acc carry L R : Nat)
    (targetAt addendAt : Nat → Wire) (labels : List Nat) (s u : BasisState)
    (h : sameExceptAcc acc s u)
    (ht : ∀ j ∈ labels, targetAt j ≠ acc) (ha : ∀ j ∈ labels, addendAt j ≠ acc)
    (hc : carry ≠ acc) :
    sameExceptAcc acc
      (labels.foldl (fun state j => intervalSecondInclusiveCell mode enabled acc
        (targetAt j) (addendAt j) carry L R j state) s)
      (maskedRippleSecondState mode (labels.map (fun j => enabled && decide (L ≤ j ∧ j ≤ R)))
        (labels.map targetAt) (labels.map addendAt) carry u) := by
  induction labels generalizing s u with
  | nil => exact h
  | cons j labels ih =>
    have hcell := second_cell mode enabled acc (targetAt j) (addendAt j) carry L R j s u h
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
theorem intervalFirstInclusiveFold_words (mode : RippleMode) (enabled : Bool)
    (acc carry L R : Nat) (targetAt addendAt : Nat → Wire) (labels : List Nat) (state : BasisState)
    (hnd : (acc :: carry :: (labels.map targetAt ++ labels.map addendAt)).Nodup) :
    let final := labels.reverse.foldl (fun s j => intervalFirstInclusiveCell mode enabled acc
      (targetAt j) (addendAt j) carry L R j s) state
    (wireValues (labels.map targetAt) final, wireValues (labels.map addendAt) final, final carry) =
      maskedRippleFirstWords mode (labels.map (fun j => enabled && decide (L ≤ j ∧ j ≤ R)))
        (wireValues (labels.map targetAt) state) (wireValues (labels.map addendAt) state) (state carry) := by
  obtain ⟨ht,ha,hc⟩ := layout_roles acc carry targetAt addendAt labels hnd
  have hf := first_fold mode enabled acc carry L R targetAt addendAt labels state state
    (fun _ _ => rfl) ht ha hc
  have ht' : ∀ w ∈ labels.map targetAt, w ≠ acc := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ht j hj
  have ha' : ∀ w ∈ labels.map addendAt, w ≠ acc := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ha j hj
  have hT := frame_values acc (labels.map targetAt) _ _ hf ht'
  have hA := frame_values acc (labels.map addendAt) _ _ hf ha'
  have hC := hf carry hc
  dsimp only
  rw [hT, hA, hC]
  exact maskedRippleFirstState_words mode _ _ _ carry state (List.nodup_cons.mp hnd).2
    (by simp) (by simp)

/-- The numeric inclusive second scan reads as the corresponding masked word pass.
Its accumulator writes do not affect the target/addend words or carry. -/
theorem intervalSecondInclusiveFold_words (mode : RippleMode) (enabled : Bool)
    (acc carry L R : Nat) (targetAt addendAt : Nat → Wire) (labels : List Nat) (state : BasisState)
    (hnd : (acc :: carry :: (labels.map targetAt ++ labels.map addendAt)).Nodup) :
    let final := labels.foldl (fun s j => intervalSecondInclusiveCell mode enabled acc
      (targetAt j) (addendAt j) carry L R j s) state
    (wireValues (labels.map targetAt) final, wireValues (labels.map addendAt) final, final carry) =
      maskedRippleSecondWords mode (labels.map (fun j => enabled && decide (L ≤ j ∧ j ≤ R)))
        (wireValues (labels.map targetAt) state) (wireValues (labels.map addendAt) state) (state carry) := by
  obtain ⟨ht,ha,hc⟩ := layout_roles acc carry targetAt addendAt labels hnd
  have hf := second_fold mode enabled acc carry L R targetAt addendAt labels state state
    (fun _ _ => rfl) ht ha hc
  have ht' : ∀ w ∈ labels.map targetAt, w ≠ acc := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ht j hj
  have ha' : ∀ w ∈ labels.map addendAt, w ≠ acc := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ha j hj
  have hT := frame_values acc (labels.map targetAt) _ _ hf ht'
  have hA := frame_values acc (labels.map addendAt) _ _ hf ha'
  have hC := hf carry hc
  dsimp only
  rw [hT, hA, hC]
  exact maskedRippleSecondState_words mode _ _ _ carry state (List.nodup_cons.mp hnd).2
    (by simp) (by simp)

/-- The two numeric inclusive folds fuse to the masked arithmetic word, restoring
all wires outside the target list except their explicit accumulator updates. -/
theorem intervalInclusivePair_fusion (mode : RippleMode) (enabled : Bool)
    (acc carry L R : Nat) (targetAt addendAt : Nat → Wire) (labels : List Nat) (state : BasisState)
    (hnd : (acc :: carry :: (labels.map targetAt ++ labels.map addendAt)).Nodup) :
    let first := labels.reverse.foldl (fun s j => intervalFirstInclusiveCell mode enabled acc
      (targetAt j) (addendAt j) carry L R j s) state
    let final := labels.foldl (fun s j => intervalSecondInclusiveCell mode enabled acc
      (targetAt j) (addendAt j) carry L R j s) first
    (wireValues (labels.map targetAt) final, wireValues (labels.map addendAt) final, final carry) =
      ((maskedRippleExpectedWords mode (labels.map (fun j => enabled && decide (L ≤ j ∧ j ≤ R)))
        (wireValues (labels.map targetAt) state) (wireValues (labels.map addendAt) state) (state carry)).1,
        wireValues (labels.map addendAt) state, state carry) ∧
      (∀ w, w ∉ acc :: labels.map targetAt → final w = state w) := by
  obtain ⟨ht,ha,hc⟩ := layout_roles acc carry targetAt addendAt labels hnd
  have hf := first_fold mode enabled acc carry L R targetAt addendAt labels state state
    (fun _ _ => rfl) ht ha hc
  have hs := second_fold mode enabled acc carry L R targetAt addendAt labels _ _ hf ht ha hc
  have hm := maskedRippleState_fusion mode (labels.map (fun j => enabled && decide (L ≤ j ∧ j ≤ R)))
    (labels.map targetAt) (labels.map addendAt) carry state (List.nodup_cons.mp hnd).2 (by simp) (by simp)
  have ht' : ∀ w ∈ labels.map targetAt, w ≠ acc := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ht j hj
  have ha' : ∀ w ∈ labels.map addendAt, w ≠ acc := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact ha j hj
  have hT := frame_values acc (labels.map targetAt) _ _ hs ht'
  have hA := frame_values acc (labels.map addendAt) _ _ hs ha'
  have hC := hs carry hc
  dsimp only
  constructor
  · rw [hT, hA, hC]
    exact hm.1
  · intro w hw
    have hw' : w ≠ acc ∧ w ∉ labels.map targetAt := by simpa only [List.mem_cons, not_or] using hw
    exact (hs w hw'.1).trans (hm.2 w hw'.2)

end ShorECDLP.Paper2607_13816
