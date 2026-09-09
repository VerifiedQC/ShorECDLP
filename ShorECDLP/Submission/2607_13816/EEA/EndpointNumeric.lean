import ShorECDLP.Submission.«2607_13816».EEA.IntervalComplete
import ShorECDLP.Submission.«2607_13816».EEA.EndpointArithmetic

/-! # Complete interval arithmetic in logical length coordinates -/
namespace ShorECDLP.Paper2607_13816
open Classical

private theorem logicalEndpoints (r : IntervalRegisters) (n k K T Q shift : Nat)
    (target : IntervalTarget) (state : BasisState) (h : IntervalLayout r k K target)
    (hready : IntervalReady r state)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length Q)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : k ≤ T+Q+2) (hleftHigh : T+Q+2-k < 2^r.lengthQ.length)
    (hrightLow : shift+k ≤ n+3) (hrightHigh : n+3-shift-k < 2^r.lengthS.length) :
    let p := run (prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) n k) state
    boolWordToNat (wireValues r.lengthQ p) = T+Q+2-k ∧
      boolWordToNat (wireValues r.lengthS p) = n+3-shift-k := by
  have hw : intervalEndpointWidth r ≤ r.scratch.length := by
    calc
      _ ≤ intervalScratchBase r k K := Nat.le_max_right _ _
      _ ≤ intervalScratchBase r k K + 3 := by omega
      _ = _ := h.scratch_length.symm
  have hqWidth : r.lengthQ.length ≤ r.endpointScratch.length := by
    simp only [IntervalRegisters.endpointScratch, List.length_take]
    exact Nat.le_min.mpr ⟨Nat.le_max_left _ _, (Nat.le_max_left _ _).trans hw⟩
  have hsWidth : r.lengthS.length ≤ r.endpointScratch.length := by
    simp only [IntervalRegisters.endpointScratch, List.length_take]
    exact Nat.le_min.mpr ⟨Nat.le_max_right _ _, (Nat.le_max_right _ _).trans hw⟩
  have hc : Clean (r.endpointScratch ++ [r.carry k K]) state := by
    intro w hw
    apply hready w
    rcases List.mem_append.mp hw with hw | hw
    · exact List.mem_of_mem_take hw
    · simp only [List.mem_singleton] at hw
      subst w
      exact intervalCarry_mem_scratch r k K target h
  have hp := prepareIntervalEndpoints_arithmetic r.lengthT r.lengthQ r.lengthS r.endpointScratch
    (r.carry k K) n k T Q shift state h.lengthT_eq_lengthQ hqWidth hsWidth
    (by have hp := h.lengthT_two_le; rw [h.lengthT_eq_lengthQ] at hp; omega) (by have := h.lengthS_two_le; omega) h.endpoints hc
    ht hq hs hleftLow hleftHigh hrightLow hrightHigh
  exact ⟨hp.2.1,hp.2.2.1⟩

/-- The complete interval uses the source logical endpoints when the stored words
encode truth-minus-one lengths. This reuses the existing modular endpoint proof,
including wrapped encodings of zero logical lengths. -/
theorem run_intervalAddSubUnitary_logicalValues (r : IntervalRegisters) (n k K T Q shift : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout r k K target) (hready : IntervalReady r state) (he : state r.control = true)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length Q)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : k ≤ T+Q+2) (hleftHigh : T+Q+2-k < 2^r.lengthQ.length)
    (hrightLow : shift+k ≤ n+3) (hrightHigh : n+3-shift-k < 2^r.lengthS.length)
    (hrange : n+3-shift-k ≤ intervalTopRelative k K)
    (horder : T+Q+2-k ≤ n+3-shift-k) :
    let L := T+Q+2-k
    let width := n+3-shift-k-L+1
    let ts := (List.range (intervalLaneCount k K)).map (r.targetAt target)
    let ads := (List.range (intervalLaneCount k K)).map (r.addendAt target)
    let value := fun ws s => boolWordToNat ((((wireValues ws s).drop L).take width).reverse)
    value ts (run (intervalAddSubUnitary r n k K mode signUpdate target) state) =
      (match mode with
      | .add => value ts state + value ads state
      | .sub => value ts state + 2^width - value ads state) % 2^width := by
  have hp := logicalEndpoints r n k K T Q shift target state h hready ht hq hs
    hleftLow hleftHigh hrightLow hrightHigh
  have hb := run_intervalAddSubUnitary_value r n k K mode signUpdate target state h hready he
    (by dsimp only; rw [hp.1, hp.2]; exact ⟨hrange,horder⟩)
  dsimp only at hb ⊢
  simpa only [hp.1,hp.2] using hb

/-- The actual interval sign records unsigned borrow in logical length coordinates. -/
theorem run_intervalAddSubUnitary_logicalBorrow (r : IntervalRegisters) (n k K T Q shift : Nat)
    (target : IntervalTarget) (state : BasisState)
    (h : IntervalLayout r k K target) (hready : IntervalReady r state) (he : state r.control = true)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length Q)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : k ≤ T+Q+2) (hleftHigh : T+Q+2-k < 2^r.lengthQ.length)
    (hrightLow : shift+k ≤ n+3) (hrightHigh : n+3-shift-k < 2^r.lengthS.length)
    (hrange : n+3-shift-k ≤ intervalTopRelative k K)
    (horder : T+Q+2-k ≤ n+3-shift-k) :
    let L := T+Q+2-k
    let width := n+3-shift-k-L+1
    let ts := (List.range (intervalLaneCount k K)).map (r.targetAt target)
    let ads := (List.range (intervalLaneCount k K)).map (r.addendAt target)
    let value := fun ws => boolWordToNat ((((wireValues ws state).drop L).take width).reverse)
    run (intervalAddSubUnitary r n k K .sub true target) state r.sign =
      (state r.sign ^^ decide (value ts < value ads)) := by
  have hp := logicalEndpoints r n k K T Q shift target state h hready ht hq hs
    hleftLow hleftHigh hrightLow hrightHigh
  have hb := run_intervalAddSubUnitary_sub_borrow r n k K target state h hready he
    (by dsimp only; rw [hp.1,hp.2]; exact ⟨hrange,horder⟩)
  dsimp only at hb ⊢
  simpa only [hp.1,hp.2] using hb

end ShorECDLP.Paper2607_13816
