import ShorECDLP.Math.Bitcoin
import ShorECDLP.Math.BitcoinPrimes
import Mathlib.Tactic.Linarith
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Quantum.OrderFinding
/-- Exact integer form of a sample within half a Fourier bin of numerator `k/r`. -/
def NearNumerator (r precision k value : Nat) : Prop :=
  2 * 2^precision * k ≤ 2*r*value+r ∧ 2*r*value ≤ 2*2^precision*k+r

theorem nearNumerator_round (r precision k value : Nat) (hr : r<2^precision)
    (h : NearNumerator r precision k value) : nearestNumerator r precision value=k := by
  unfold nearestNumerator
  apply Nat.div_eq_of_lt_le
  · have := h.1; nlinarith
  · have := h.2; nlinarith

/-- Two sufficiently close samples recover the discrete logarithm when the first character is nonzero. -/
theorem paperPostprocess_correct (r precision d k : Nat) (hr : Nat.Prime r)
    (hprecision : r<2^precision) (hk : (k:ZMod r) ≠ 0)
    (out : Fin (2^precision) × Fin (2^precision))
    (ha : NearNumerator r precision k out.1.val)
    (hb : NearNumerator r precision ((d*k)%r) out.2.val) :
    orderFindingPostprocess r precision hr out=some (d:ZMod r) := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  unfold orderFindingPostprocess
  rw [nearNumerator_round r precision k out.1.val hprecision ha,
    nearNumerator_round r precision ((d*k)%r) out.2.val hprecision hb]
  simp only [hk, if_false]
  congr 1
  simp [Nat.cast_mul, hk]
/-- The paper's `n+1` exponent precision at the 256-bit specialization. -/
def paperExponentPrecision : Nat := 257

theorem paperExponentPrecision_order : ShorECDLP.order<2^paperExponentPrecision := by
  decide +kernel
/-- Nearest Fourier-bin sample, computed using integers only. -/
def paperPeak (r precision : Nat) (hprecision : r<2^precision) (k : Fin r) : Fin (2^precision) :=
  ⟨(2*2^precision*k.val+r)/(2*r), by
    have hk := k.isLt
    apply (Nat.div_lt_iff_lt_mul (by omega : 0<2*r)).2
    have hn : 0<2^precision := by positivity
    nlinarith⟩

theorem paperPeak_near (r precision : Nat) (hprecision : r<2^precision) (k : Fin r) :
    NearNumerator r precision k.val (paperPeak r precision hprecision k).val := by
  have hr : 0<2*r := by have := k.isLt; omega
  have h₁ := Nat.div_mul_le_self (2*2^precision*k.val+r) (2*r)
  have h₂ := Nat.lt_mul_div_succ (2*2^precision*k.val+r) hr
  unfold NearNumerator paperPeak
  constructor <;> nlinarith

theorem paperPeak_round (r precision : Nat) (hprecision : r<2^precision) (k : Fin r) :
    nearestNumerator r precision (paperPeak r precision hprecision k).val=k.val :=
  nearNumerator_round _ _ _ _ hprecision (paperPeak_near _ _ _ _)

theorem paperPeak_injective (r precision : Nat) (hprecision : r<2^precision) :
    Function.Injective (paperPeak r precision hprecision) := by
  intro k l h
  apply Fin.ext
  have he := congrArg (fun a : Fin (2^precision) => nearestNumerator r precision a.val) h
  simpa only [paperPeak_round] using he
end ShorECDLP.Paper2607_13816
