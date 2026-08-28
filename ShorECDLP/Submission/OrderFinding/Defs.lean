import ShorECDLP.Submission.OrderFinding.OracleSpec
import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Defs
import ShorECDLP.Framework.Bitcoin

namespace ShorECDLP.Quantum.OrderFinding

noncomputable section

open PhaseEstimation

def orderFinding
    (aReg bReg : List Wire)
    (qftAncilla : Wire)
    (oracle : State →ₗ[ℂ] State) :
    State →ₗ[ℂ] State :=
  (run (iqft bReg qftAncilla)).comp
    ((run (iqft aReg qftAncilla)).comp
      (oracle.comp
        (run (hadamards (aReg ++ bReg)))))

end

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

end ShorECDLP.Quantum.OrderFinding
