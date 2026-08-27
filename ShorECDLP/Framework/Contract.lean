import ShorECDLP.Framework.Repetition
import ShorECDLP.Submission.Correctness.Trial

/-!
# Bitcoin ECDLP submission contract

This file contains only the closed public claim for the Bitcoin curve.  The
joint-measurement semantics and independent-repetition model live in their
own Framework modules; generic ECDLP and order-finding definitions live under
`Submission/OrderFinding`.

There are no configurable contract parameters.  The proposition fixes
secp256k1, 256-bit phase registers, 26 independent measured trials, a 99%
success target, and the exact aggregate T-count.  It quantifies internally
over the public key and every valid wire placement, and both claims reference
the same exact `ecdlpTrial` term.
-/

namespace ShorECDLP.Secp256k1

/--
The complete Bitcoin ECDLP claim: the concrete secp256k1 trial is normalized,
26 independent measured runs recover the discrete logarithm with probability
at least 99%, and those same 26 trials cost exactly
21,888,426,033,809,920 T gates.
-/
def BitcoinECDLPSubmission : Prop :=
  ∀ [Fact (Nat.Prime p)] [Fact (Nat.Prime order)]
    {d : Nat} (Q : Point)
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (input : BasisState),
    pointReg.length = pointWidth →
    (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup →
    addOrderOf G = order →
    Q = d • G →
    Q ≠ 0 →
    Quantum.OrderFinding.OrderFindingSetup pointEncoding
      aReg bReg pointReg (scalarMulWork workStart)
      qftAncilla 256 input →
    let trial :=
      ecdlpTrial aReg bReg pointReg workStart qftAncilla Q
    Quantum.normSq (Quantum.run trial (Quantum.ket input)) = 1 ∧
      (99 / 100 : Real) ≤
        independentRetrySuccessProbability
          (Quantum.OrderFinding.orderFindingSuccessProbability
            order 256 d (Fact.out : Nat.Prime order) aReg bReg
            (Quantum.run trial (Quantum.ket input)))
          26 ∧
      repeatedTCount trial 26 = 21888426033809920

end ShorECDLP.Secp256k1
