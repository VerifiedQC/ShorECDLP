import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedCandidates
import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedPeak
namespace ShorECDLP.Paper2607_13816
/-- Include the endpoint `N` only when its physical Fourier encoding is zero. -/
def wrappedNumeratorCandidates (r precision value : Nat) : Finset Nat :=
  numeratorCandidates r precision value ∪
    if value=0 then numeratorCandidates r precision (2^precision) else ∅

theorem reducedPeak_mem_candidates (r precision : Nat) (k : Fin r) :
    k.val ∈ wrappedNumeratorCandidates r precision (reducedPeak r precision k).val := by
  have hraw := nearNumerator_mem_candidates _ _ _ _ (reducedPeakRaw_near r precision k)
  have hle := reducedPeakRaw_le r precision k
  by_cases heq : reducedPeakRaw r precision k = 2^precision
  · apply Finset.mem_union.mpr
    right
    simpa [reducedPeak, heq] using hraw
  · apply Finset.mem_union.mpr
    left
    simpa [reducedPeak, Nat.mod_eq_of_lt (by omega : reducedPeakRaw r precision k < 2^precision)] using hraw

theorem wrappedNumeratorCandidates_card (r precision value : Nat) :
    (wrappedNumeratorCandidates r precision value).card ≤ 2*(r/2^precision+2) := by
  unfold wrappedNumeratorCandidates
  apply (Finset.card_union_le _ _).trans
  have h₁ := numeratorCandidates_card r precision value
  split_ifs
  · have h₂ := numeratorCandidates_card r precision (2^precision)
    omega
  · simp only [Finset.card_empty, Nat.add_zero]
    omega

theorem secp_wrappedNumeratorCandidates_card (value : Nat) :
    (wrappedNumeratorCandidates ShorECDLP.order 208 value).card ≤ 2^49+2 := by
  exact (wrappedNumeratorCandidates_card _ _ _).trans (by decide +kernel)

noncomputable section
/-- Finite classical candidates; a later verification step must check the public point. -/
def reducedShiftCandidates (r n m : Nat) (out : Fin (2^n) × Fin (2^m)) : Finset (ZMod r) :=
  (wrappedNumeratorCandidates r m out.2.val).image
    (fun (l : Nat) => (l : ZMod r) * (ShorECDLP.Quantum.OrderFinding.nearestNumerator r n out.1.val : ZMod r)⁻¹)

theorem reducedShiftCandidates_card (r n m : Nat) (out : Fin (2^n) × Fin (2^m)) :
    (reducedShiftCandidates r n m out).card ≤ 2*(r/2^m+2) := by
  exact (Finset.card_image_le).trans (wrappedNumeratorCandidates_card _ _ _)

theorem reducedShiftCandidates_correct (r n m d : Nat) [Fact (Nat.Prime r)]
    (hn : r<2^n) (k : Fin r) (hk : (k.val : ZMod r) ≠ 0) :
    (d : ZMod r) ∈ reducedShiftCandidates r n m
      (paperPeak r n hn k, reducedPeak r m ⟨(d*k.val)%r, Nat.mod_lt _ (by have := k.isLt; omega)⟩) := by
  unfold reducedShiftCandidates
  apply Finset.mem_image.mpr
  refine ⟨(d*k.val)%r, reducedPeak_mem_candidates _ _ _, ?_⟩
  simp only [paperPeak_round]
  simp [Nat.cast_mul, hk]
end
end ShorECDLP.Paper2607_13816
