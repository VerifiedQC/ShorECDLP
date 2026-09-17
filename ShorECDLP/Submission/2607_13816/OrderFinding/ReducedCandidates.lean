import ShorECDLP.Submission.«2607_13816».OrderFinding.Postprocess
import Mathlib.Order.Interval.Finset.Nat
namespace ShorECDLP.Paper2607_13816
/-- Integer candidates consistent with an unwrapped half-bin observation. -/
def numeratorCandidates (r precision value : Nat) : Finset Nat :=
  Finset.Icc ((2*r*value-r)/(2*2^precision)) ((2*r*value+r)/(2*2^precision))

theorem nearNumerator_mem_candidates (r precision k value : Nat)
    (h : NearNumerator r precision k value) :
    k ∈ numeratorCandidates r precision value := by
  have hN : 0 < 2*2^precision := by positivity
  apply Finset.mem_Icc.mpr
  constructor
  · apply Nat.div_le_of_le_mul
    have := h.2
    omega
  · apply (Nat.le_div_iff_mul_le hN).mpr
    simpa [Nat.mul_comm] using h.1

theorem numeratorCandidates_card (r precision value : Nat) :
    (numeratorCandidates r precision value).card ≤ r / 2^precision + 2 := by
  let N := 2^precision
  let a := 2*r*value
  have hN : 0 < N := by dsimp [N]; positivity
  have hlo := Nat.lt_mul_div_succ (a-r) (by omega : 0<2*N)
  have hhi := Nat.div_mul_le_self (a+r) (2*N)
  have hr := Nat.lt_mul_div_succ r hN
  have hsub : a ≤ (a-r)+r := by omega
  have hwidth : (a+r)/(2*N) ≤ (a-r)/(2*N) + r/N + 1 := by
    nlinarith
  simp only [numeratorCandidates, Nat.card_Icc]
  change (a+r)/(2*N) + 1 - (a-r)/(2*N) ≤ r/N+2
  exact Nat.sub_le_of_le_add (by omega)

/-- The 208-bit second register leaves at most 2^48+1 numerator candidates. -/
theorem secp_numeratorCandidates_card (value : Nat) :
    (numeratorCandidates ShorECDLP.order 208 value).card ≤ 2^48+1 := by
  exact (numeratorCandidates_card _ _ _).trans (by decide +kernel)

/-- Every near second-register sample includes the actual logarithm after division. -/
theorem nearNumerator_shift_mem (r precision d k value : Nat) [Fact (Nat.Prime r)]
    (hk : (k : ZMod r) ≠ 0)
    (h : NearNumerator r precision ((d*k)%r) value) :
    (d : ZMod r) ∈ (numeratorCandidates r precision value).image
      (fun (l : Nat) => (l : ZMod r) / (k : ZMod r)) := by
  apply Finset.mem_image.mpr
  refine ⟨(d*k)%r, nearNumerator_mem_candidates _ _ _ _ h, ?_⟩
  simp [Nat.cast_mul, hk]
end ShorECDLP.Paper2607_13816
