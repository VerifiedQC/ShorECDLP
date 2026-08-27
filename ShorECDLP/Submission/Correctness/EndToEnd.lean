import ShorECDLP.Submission.EllipticCurve.ECDLPOracle
import ShorECDLP.Submission.OrderFinding.Main

/-!
# Conditional secp256k1 order-finding theorem

This module applies the already-proved two-register order-finding theorem to
the concrete two-ScalarMul ECDLP oracle.  The result keeps the two remaining
secp256k1 group facts visible: primality of `order` and the statement that the
standard generator has that additive order.

This is the concrete single-run correctness bridge.  It does not yet add an
operational measurement/repetition circuit or a same-program aggregate
resource theorem.
-/

namespace ShorECDLP
namespace Secp256k1

variable [Fact (Nat.Prime p)] [Fact (Nat.Prime order)]

/--
The concrete secp256k1 oracle satisfies the conditional ECDLP order-finding
success bound.  The generator-order equality and the relation `Q = d • G`
remain explicit hypotheses.
-/
theorem orderFinding_correct
    {d precision : Nat}
    (Q : Point)
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (s : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup)
    (horderG : addOrderOf G = order)
    (hQ : Q = d • G)
    (hsetup :
      Quantum.OrderFinding.OrderFindingSetup pointEncoding
        aReg bReg pointReg (scalarMulWork workStart)
        qftAncilla precision s)
    (hprecision : order ≤ 2 ^ precision) :
    ((order - 1 : ℝ) / order) *
        ((4 : ℝ) / Real.pi ^ 2) ^ 2 ≤
      Quantum.OrderFinding.orderFindingSuccessProbability
        order precision d (Fact.out : Nat.Prime order)
        aReg bReg
        (Quantum.OrderFinding.orderFinding
          aReg bReg qftAncilla
          (Quantum.run
            (ecdlpOracle aReg bReg pointReg workStart G Q))
          (Quantum.ket s)) := by
  let hsetting :
      Quantum.OrderFinding.ECDLPSetting G Q order d :=
    { prime_order := (Fact.out : Nat.Prime order)
      order_P := horderG
      Q_eq := hQ }

  have hspec := ecdlpOracle_spec
    aReg bReg pointReg workStart G Q hpointLength hnodup

  have hresult := Quantum.OrderFinding.orderFinding_correct
    pointEncoding
    (Quantum.run (ecdlpOracle aReg bReg pointReg workStart G Q))
    G Q aReg bReg pointReg (scalarMulWork workStart)
    qftAncilla s hsetting hspec hsetup hprecision

  simpa [hsetting] using hresult

end Secp256k1
end ShorECDLP
