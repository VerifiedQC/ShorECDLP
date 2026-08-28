import ShorECDLP.Framework.Quantum.Measurement
import ShorECDLP.Framework.Repetition
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Bitcoin ECDLP problem specification

This file contains the secp256k1 group order and the canonical two-register
ECDLP postprocessing probability used by the submission contract.  It
contains no submitted circuit or resource number.
-/

namespace ShorECDLP

/-- The secp256k1 group order `n` (number of points on the curve). -/
def order : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

namespace Quantum.OrderFinding

open scoped BigOperators

noncomputable section

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

end ShorECDLP
