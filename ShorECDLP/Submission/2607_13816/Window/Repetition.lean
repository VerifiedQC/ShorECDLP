import ShorECDLP.Submission.«2607_13816».Window.Secp
import ShorECDLP.Framework.Repetition
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1 Quantum.PhaseEstimation Quantum.OrderFinding
open scoped BigOperators
noncomputable section
theorem secpSuccessBound_numeric :
    (163:ℝ)/1000 ≤ (((order-1:Nat):ℝ)/(order:ℝ))*((4:ℝ)/Real.pi^2)^2 := by
  have ho : (1000:ℝ)≤order := by exact_mod_cast (show 1000≤order by decide +kernel)
  have hop : (0:ℝ)<order := by linarith
  have hc : ((order-1:Nat):ℝ)=(order:ℝ)-1 := by
    rw [Nat.cast_sub (by have := order_prime.two_le; omega),Nat.cast_one]
  have hr : (999:ℝ)/1000 ≤ ((order-1:Nat):ℝ)/(order:ℝ) := by
    rw [hc]
    apply (le_div_iff₀ hop).mpr
    linarith
  have hpi := Real.pi_lt_d4
  have hpp := Real.pi_pos
  have hp2 : Real.pi^2 < (3.1416:ℝ)^2 := by nlinarith
  have hp : (81:ℝ)/200 ≤ 4/Real.pi^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hpp)).mpr
    nlinarith
  have hpn : (0:ℝ)≤4/Real.pi^2 := by positivity
  have hpq : ((81:ℝ)/200)^2 ≤ (4/Real.pi^2)^2 := by nlinarith
  have h := mul_le_mul hr hpq (by positivity) (by positivity)
  norm_num at h ⊢
  linarith
private theorem output_nonneg (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G)
    (out : Fin (2^257) × Fin (2^257)) : 0≤secpWindowOutputMass Q hrQ out := by
  unfold secpWindowOutputMass
  split
  · split <;> norm_num
  · rw [windowTrialFiniteOutputMass_eq order_prime G Q _ _ _ _ generator_order d hQd]
    exact paperPairMass_nonneg order 257 d out
theorem selectedMass_le_total {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p]
    (mass : α → ℝ) (hn : ∀ a, 0≤mass a) :
    (∑ a, if p a then mass a else 0) ≤ ∑ a, mass a := by
  apply Finset.sum_le_sum
  intro a ha
  split
  · exact le_rfl
  · exact hn a

theorem secpWindowSuccessMass_le_one (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    secpWindowSuccessMass Q hrQ d≤1 :=
  (selectedMass_le_total (fun out => secpWindowPostprocess Q out=some (d:ZMod order))
    (secpWindowOutputMass Q hrQ) (output_nonneg Q hrQ d hQd)).trans_eq
      (secpWindowOutputMass_total Q hrQ d hQd)
/-- At least 16.3 percent success in one concrete run. -/
theorem secpWindowSuccessMass_numeric (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (163:ℝ)/1000≤secpWindowSuccessMass Q hrQ d :=
  secpSuccessBound_numeric.trans (secpWindowSuccessMass_lower Q hrQ d hQd)
/-- Twenty-six independent measured runs exceed 99 percent success. -/
theorem secpWindowRetrySuccess (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (99:ℝ)/100 ≤ independentRetrySuccessProbability (secpWindowSuccessMass Q hrQ d) 26 := by
  have h := independentRetrySuccessProbability_mono 26 (secpWindowSuccessMass_le_one Q hrQ d hQd)
    (secpWindowSuccessMass_numeric Q hrQ d hQd)
  have hn : (99:ℝ)/100 ≤ independentRetrySuccessProbability ((163:ℝ)/1000) 26 := by
    norm_num [independentRetrySuccessProbability]
  exact hn.trans h
end
end ShorECDLP.Paper2607_13816
