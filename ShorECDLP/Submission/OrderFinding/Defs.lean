import ShorECDLP.Submission.OrderFinding.OracleSpec
import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Defs
import ShorECDLP.Framework.Bitcoin
import ShorECDLP.Framework.Quantum.Measurement

namespace ShorECDLP.Quantum.OrderFinding

noncomputable section

open PhaseEstimation
open scoped BigOperators

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

end ShorECDLP.Quantum.OrderFinding
