import ShorECDLP.Math.BitcoinCurve
import Mathlib.Algebra.Field.ZMod

/-!
# Bitcoin ECDLP problem specification

This file contains the canonical classical postprocessing used to interpret
two-register Bitcoin ECDLP measurement outcomes.  It contains no point
encoding, submitted circuit, or resource number.
-/

namespace ShorECDLP

namespace Quantum.OrderFinding

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

end

end Quantum.OrderFinding

end ShorECDLP
