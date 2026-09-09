import ShorECDLP.Submission.«2607_13816».EEA.IntervalArithmetic
/-! # Arithmetic of the complete interval including endpoint transformations -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem endpoint_outside (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) (w : Wire)
    (hw : w ∈ r.control :: r.sign :: (r.work1 ++ r.work2)) :
    w ∉ intervalEndpointSupport r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) := by
  intro hm
  have htail : w ∈ r.lengthT ++ (r.lengthQ ++ (r.lengthS ++ r.scratch)) := by
    simp only [intervalEndpointSupport, List.mem_append, List.mem_singleton] at hm
    rcases hm with ((((he | he) | he) | he) | he)
    · simp [List.mem_of_mem_take he]
    · subst w; simp [intervalCarry_mem_scratch r k K target h]
    · simp [he]
    · simp [he]
    · simp [he]
  have hp := h.physical
  rw [IntervalRegisters.allWires] at hp
  have hcontrol := List.nodup_append.mp hp
  have hw1 := List.nodup_append.mp hcontrol.2.1
  have hw2 := List.nodup_append.mp hw1.2.1
  rcases List.mem_cons.mp hw with he | hw
  · subst w
    exact hcontrol.2.2 r.control (by simp) r.control (by simp [htail]) rfl
  rcases List.mem_cons.mp hw with he | hw
  · subst w
    exact hcontrol.2.2 r.sign (by simp) r.sign (by simp [htail]) rfl
  rcases List.mem_append.mp hw with hw | hw
  · exact hw1.2.2 w hw w (List.mem_append_right _ htail) rfl
  · exact hw2.2.2 w hw w htail rfl

private theorem target_mem (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) (j : Nat) (hj : j < intervalLaneCount k K) :
    r.targetAt target j ∈ r.control :: r.sign :: (r.work1 ++ r.work2) := by
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  cases target with
  | work1 =>
    apply List.mem_append_left
    change r.work1.getD j 0 ∈ r.work1
    rw [List.getD_eq_getElem r.work1 0 (by rw [h.work1_length]; exact hj)]
    exact List.getElem_mem _
  | work2 =>
    apply List.mem_append_right
    change r.work2.getD j 0 ∈ r.work2
    rw [List.getD_eq_getElem r.work2 0 (by rw [h.work2_length]; exact hj)]
    exact List.getElem_mem _

private theorem endpoint_words (r : IntervalRegisters) (n k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) (state : BasisState) (restore : Bool)
    (ws : List Wire) (hm : ∀ w ∈ ws, w ∈ r.control :: r.sign :: (r.work1 ++ r.work2)) :
    wireValues ws
      (run (if restore then restoreIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k
        else prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k) state) =
    wireValues ws state := by
  apply List.map_congr_left
  intro w hw
  have hout := endpoint_outside r k K target h w (hm w hw)
  cases restore
  · exact (prepareIntervalEndpoints_usesOnly r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k).preservesOutside state hout
  · exact (restoreIntervalEndpoints_usesOnly r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k).preservesOutside state hout

private theorem addend_mem (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) (j : Nat) (hj : j < intervalLaneCount k K) :
    r.addendAt target j ∈ r.control :: r.sign :: (r.work1 ++ r.work2) := by
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  cases target with
  | work1 =>
    apply List.mem_append_right
    change r.work2.getD j 0 ∈ r.work2
    rw [List.getD_eq_getElem r.work2 0 (by rw [h.work2_length]; exact hj)]
    exact List.getElem_mem _
  | work2 =>
    apply List.mem_append_left
    change r.work1.getD j 0 ∈ r.work1
    rw [List.getD_eq_getElem r.work1 0 (by rw [h.work1_length]; exact hj)]
    exact List.getElem_mem _

/-- The complete interval performs selected-slice arithmetic after preparing its
endpoints. Endpoint restoration leaves both data banks untouched; ready scratch
provides a zero arithmetic carry. Prepared endpoints are explicitly bounded. -/
theorem run_intervalAddSubUnitary_value (r : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout r k K target) (hready : IntervalReady r state)
    (he : state r.control = true)
    (hvalues : let p := run (prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS
        r.endpointScratch (r.carry k K) n k) state
      boolWordToNat (wireValues r.lengthS p) ≤ intervalTopRelative k K ∧
        boolWordToNat (wireValues r.lengthQ p) ≤ boolWordToNat (wireValues r.lengthS p)) :
    let p := run (prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k) state
    let L := boolWordToNat (wireValues r.lengthQ p)
    let width := boolWordToNat (wireValues r.lengthS p) - L + 1
    let ts := (List.range (intervalLaneCount k K)).map (r.targetAt target)
    let ads := (List.range (intervalLaneCount k K)).map (r.addendAt target)
    let value := fun ws s => boolWordToNat ((((wireValues ws s).drop L).take width).reverse)
    value ts (run (intervalAddSubUnitary r n k K mode signUpdate target) state) =
      (match mode with
      | .add => value ts state + value ads state
      | .sub => value ts state + 2^width - value ads state) % 2^width := by
  let p := run (prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k) state
  let b := run (intervalAddSubBodyUnitary r k K mode signUpdate target) p
  let ts := (List.range (intervalLaneCount k K)).map (r.targetAt target)
  let ads := (List.range (intervalLaneCount k K)).map (r.addendAt target)
  have hts : ∀ w ∈ ts, w ∈ r.control :: r.sign :: (r.work1 ++ r.work2) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact target_mem r k K target h j (List.mem_range.mp hj)
  have hads : ∀ w ∈ ads, w ∈ r.control :: r.sign :: (r.work1 ++ r.work2) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact addend_mem r k K target h j (List.mem_range.mp hj)
  have ht := endpoint_words r n k K target h state false ts hts
  have had := endpoint_words r n k K target h state false ads hads
  have hout := endpoint_words r n k K target h b true ts hts
  have hc : Clean r.scratch p := intervalPrepare_cleanScratch r n k K target state h hready
  have hcp : p r.control = true := by
    exact ((prepareIntervalEndpoints_usesOnly r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k).preservesOutside state
      (endpoint_outside r k K target h _ (by simp))).trans he
  have hb := run_intervalAddSubBody_value r k K mode signUpdate target p h
    (fun w hw => hc w (intervalTopScratch_mem_scratch r k K target h w hw))
    (hc _ (intervalAccumulator_mem_scratch r k K target h)) hvalues.1 hvalues.2 hcp
  have hcarry := hc _ (intervalCarry_mem_scratch r k K target h)
  have hshape : run (intervalAddSubUnitary r n k K mode signUpdate target) state =
      run (restoreIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k) b := by
    simp only [intervalAddSubUnitary, intervalAddSubBodyUnitary, p, b, Classical.run_append]
  simp only [Bool.false_eq_true, reduceIte] at ht had hout
  dsimp only at hb ⊢
  rw [hshape, hout]
  rw [ht, had, hcarry] at hb
  simpa only [Bool.toNat_false, Nat.add_zero, Nat.sub_zero] using hb
end ShorECDLP.Paper2607_13816
