import ShorECDLP.Framework.CostModel
import ShorECDLP.Framework.Quantum.InnerProduct

import Mathlib.Algebra.Field.ZMod

/-!
# ECDLP submission contract

This file is the public, implementation-independent boundary for an ECDLP
resource submission.  It defines the canonical two-register measurement and
postprocessing probability, independent measured retries, their aggregate
T-count, and one same-program contract joining the final success and cost
claims.

The contract deliberately contains no curve, arithmetic circuit, oracle, or
register allocation.  A submission supplies one exact `trial` circuit.  Both
the measured success probability and `tCount` are computed from that same
term, so the two claims cannot drift apart.
-/

namespace ShorECDLP

open scoped BigOperators

/-- An injective fixed-width representation of mathematical group elements. -/
structure PointEncoding (G : Type*) (w : Nat) where
  encode : G → Fin (2 ^ w)
  injective : Function.Injective encode

/-- The classical ECDLP oracle function `(a,b,R) ↦ R + aP + bQ`. -/
def ecdlpFunction {G : Type*} [AddCommGroup G]
    (P Q : G) (a b : Nat) : G :=
  a • P + b • Q

namespace Quantum.OrderFinding

noncomputable section

/-- Born probability of measuring the two named registers as `(a,b)`. -/
def jointRegisterProbability
    (aReg bReg : List Wire)
    (a b : Nat)
    (psi : State) : Real := by
  classical
  exact
    ∑ s ∈ psi.support,
      if regValue aReg s = a ∧ regValue bReg s = b
      then Complex.normSq (psi s)
      else 0

/-- Round a `precision`-bit phase sample to its nearest numerator modulo `r`. -/
def nearestNumerator (r precision value : Nat) : Nat :=
  (2 * r * value + 2 ^ precision) / (2 * 2 ^ precision)

/-- Canonical classical recovery from one pair of ECDLP Fourier samples. -/
noncomputable def orderFindingPostprocess
    (r precision : Nat)
    (hr : Nat.Prime r)
    (out : Fin (2 ^ precision) × Fin (2 ^ precision)) :
    Option (ZMod r) := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  let k : ZMod r := nearestNumerator r precision out.1.val
  let l : ZMod r := nearestNumerator r precision out.2.val
  exact if k = 0 then none else some (l / k)

/--
Born probability that measurement followed by the canonical ECDLP
postprocessing recovers `d`.
-/
noncomputable def orderFindingSuccessProbability
    (r precision d : Nat)
    (hr : Nat.Prime r)
    (aReg bReg : List Wire)
    (psi : State) : Real :=
  ∑ a : Fin (2 ^ precision),
    ∑ b : Fin (2 ^ precision),
      if orderFindingPostprocess r precision hr (a, b) =
          some (d : ZMod r)
      then
        jointRegisterProbability aReg bReg a.val b.val psi
      else 0

/-- Mathematical ECDLP instance used by the abstract order-finding proof. -/
structure ECDLPSetting
    {G : Type*} [AddCommGroup G]
    (P Q : G) (r d : Nat) : Prop where
  prime_order : Nat.Prime r
  order_P : addOrderOf P = r
  Q_eq : Q = d • P

/-- Register initialization required by one order-finding trial. -/
structure OrderFindingSetup
    {G : Type*} [AddCommGroup G]
    {w : Nat}
    (enc : PointEncoding G w)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (precision : Nat)
    (s : BasisState) : Prop where
  a_width : aReg.length = precision
  b_width : bReg.length = precision
  a_zero : regValue aReg s = 0
  b_zero : regValue bReg s = 0
  point_zero : regValue pointReg s = (enc.encode (0 : G)).val
  oracleWork_zero : Clean oracleWork s
  ancilla_zero : s qftAncilla = false
  ancilla_fresh :
    qftAncilla ∉ aReg ++ bReg ++ pointReg ++ oracleWork

private theorem regValue_lt_two_pow
    (ws : List Wire) (s : BasisState) :
    regValue ws s < 2 ^ ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      rw [regValue_cons, List.length_cons, Nat.pow_succ]
      by_cases h : s w <;> simp [h] <;> omega

private theorem normSq_eq_support_sum (psi : State) :
    normSq psi = ∑ s ∈ psi.support, Complex.normSq (psi s) := by
  classical
  have hinner :
      inner psi psi =
        ((∑ s ∈ psi.support, Complex.normSq (psi s) : Real) : Complex) := by
    unfold inner
    change
      (∑ s ∈ psi.support,
        (starRingEnd Complex) (psi s) * psi s) =
      ((∑ s ∈ psi.support, Complex.normSq (psi s) : Real) : Complex)
    push_cast
    apply Finset.sum_congr rfl
    intro s _
    exact (Complex.normSq_eq_conj_mul_self).symm
  unfold normSq
  rw [hinner]
  simp

private theorem jointRegisterProbability_sum_eq_normSq
    (aReg bReg : List Wire)
    (precision : Nat)
    (ha : aReg.length = precision)
    (hb : bReg.length = precision)
    (psi : State) :
    (∑ a : Fin (2 ^ precision),
      ∑ b : Fin (2 ^ precision),
        jointRegisterProbability aReg bReg a.val b.val psi) = normSq psi := by
  classical
  rw [normSq_eq_support_sum]
  unfold jointRegisterProbability
  calc
    (∑ a : Fin (2 ^ precision),
        ∑ b : Fin (2 ^ precision),
          ∑ s ∈ psi.support,
            if regValue aReg s = a.val ∧ regValue bReg s = b.val
            then Complex.normSq (psi s) else 0) =
      ∑ a : Fin (2 ^ precision),
        ∑ s ∈ psi.support,
          ∑ b : Fin (2 ^ precision),
            if regValue aReg s = a.val ∧ regValue bReg s = b.val
            then Complex.normSq (psi s) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ s ∈ psi.support,
        ∑ a : Fin (2 ^ precision),
          ∑ b : Fin (2 ^ precision),
            if regValue aReg s = a.val ∧ regValue bReg s = b.val
            then Complex.normSq (psi s) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s ∈ psi.support, Complex.normSq (psi s) := by
      apply Finset.sum_congr rfl
      intro s _
      let a : Fin (2 ^ precision) :=
        ⟨regValue aReg s,
          by simpa [ha] using regValue_lt_two_pow aReg s⟩
      let b : Fin (2 ^ precision) :=
        ⟨regValue bReg s,
          by simpa [hb] using regValue_lt_two_pow bReg s⟩
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp [a, b]
        · intro b' _ hne
          have hbval : regValue bReg s ≠ b'.val := by
            intro h
            exact hne (Fin.ext h.symm)
          simp [hbval]
        · simp
      · intro a' _ hne
        have haval : regValue aReg s ≠ a'.val := by
          intro h
          exact hne (Fin.ext h.symm)
        simp [haval]
      · simp

/-- A joint-register Born probability is nonnegative. -/
theorem jointRegisterProbability_nonneg
    (aReg bReg : List Wire) (a b : Nat) (psi : State) :
    0 ≤ jointRegisterProbability aReg bReg a b psi := by
  classical
  unfold jointRegisterProbability
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- The successful outcomes carry at most the state's total Born mass. -/
theorem orderFindingSuccessProbability_le_normSq
    (r precision d : Nat)
    (hr : Nat.Prime r)
    (aReg bReg : List Wire)
    (ha : aReg.length = precision)
    (hb : bReg.length = precision)
    (psi : State) :
    orderFindingSuccessProbability r precision d hr aReg bReg psi ≤
      normSq psi := by
  calc
    orderFindingSuccessProbability r precision d hr aReg bReg psi ≤
        ∑ a : Fin (2 ^ precision),
          ∑ b : Fin (2 ^ precision),
            jointRegisterProbability aReg bReg a.val b.val psi := by
      unfold orderFindingSuccessProbability
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      split_ifs
      · exact le_rfl
      · exact jointRegisterProbability_nonneg _ _ _ _ _
    _ = normSq psi :=
      jointRegisterProbability_sum_eq_normSq aReg bReg precision ha hb psi

end

end Quantum.OrderFinding

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

/--
Public same-program ECDLP submission format.  `successful` measures the exact
`trial` supplied here, and `counted` charges repetitions of that identical
circuit.
-/
structure ECDLPSubmission
    (trial : Circuit)
    (input : BasisState)
    (aReg bReg : List Wire)
    (order precision secret : Nat)
    (primeOrder : Nat.Prime order)
    (trials : Nat)
    (targetSuccess : Real)
    (exactTCount : Nat) : Prop where
  normalized :
    Quantum.normSq (Quantum.run trial (Quantum.ket input)) = 1
  successful :
    targetSuccess ≤
      independentRetrySuccessProbability
        (Quantum.OrderFinding.orderFindingSuccessProbability
          order precision secret primeOrder aReg bReg
          (Quantum.run trial (Quantum.ket input)))
        trials
  counted : repeatedTCount trial trials = exactTCount

end ShorECDLP
