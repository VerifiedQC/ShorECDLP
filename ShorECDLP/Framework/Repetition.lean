import ShorECDLP.Framework.CostModel
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Independent measured repetition

This file contains only the classical run-measure-retry model and its
aggregate T-count.  It is independent of ECDLP and of any particular circuit.
-/

namespace ShorECDLP

/--
Success probability of `trials` independent measured runs, accepting when at
least one run succeeds.  Independence makes the all-fail probability the
product `(1 - p)^trials`.
-/
def independentRetrySuccessProbability (p : Real) (trials : Nat) : Real :=
  1 - (1 - p) ^ trials

@[simp]
theorem independentRetrySuccessProbability_zero (p : Real) :
    independentRetrySuccessProbability p 0 = 0 := by
  simp [independentRetrySuccessProbability]

/--
Operational recurrence for independent run-measure-retry: the next run
succeeds with probability `p`; on failure, the remaining runs are attempted.
-/
theorem independentRetrySuccessProbability_succ (p : Real) (trials : Nat) :
    independentRetrySuccessProbability p (trials + 1) =
      p + (1 - p) * independentRetrySuccessProbability p trials := by
  simp [independentRetrySuccessProbability, pow_succ]
  ring

/-- Increasing a valid single-run lower bound can only improve retry success. -/
theorem independentRetrySuccessProbability_mono
    (trials : Nat) {p q : Real}
    (hq_le_one : q ≤ 1)
    (hpq : p ≤ q) :
    independentRetrySuccessProbability p trials ≤
      independentRetrySuccessProbability q trials := by
  have hq_failure_nonneg : 0 ≤ 1 - q := by linarith
  have hfailure : 1 - q ≤ 1 - p := by linarith
  have hpow : (1 - q) ^ trials ≤ (1 - p) ^ trials :=
    pow_le_pow_left₀ hq_failure_nonneg hfailure trials
  unfold independentRetrySuccessProbability
  linarith

/-- Aggregate T-count of sequential measured trials. -/
def repeatedTCount (trial : Circuit) (trials : Nat) : Nat :=
  trials * tCount trial

end ShorECDLP
