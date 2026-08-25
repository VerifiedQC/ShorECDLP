import ShorECDLP.Submission.OrderFinding.OracleSpec
import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Defs
import Mathlib.Algebra.Field.ZMod

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

def jointRegisterProbability
    (aReg bReg : List Wire)
    (a b : Nat)
    (psi : State) : ℝ := by
  classical
  exact
    ∑ s ∈ psi.support,
      if regValue aReg s = a ∧ regValue bReg s = b
      then Complex.normSq (psi s)
      else 0

end

def nearestNumerator (r precision value : ℕ) : ℕ :=
  (2 * r * value + 2 ^ precision) / (2 * 2 ^ precision)

noncomputable def orderFindingPostprocess
    (r precision : ℕ)
    (hr : Nat.Prime r)
    (out : Fin (2 ^ precision) × Fin (2 ^ precision)) :
    Option (ZMod r) := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  let k : ZMod r := nearestNumerator r precision out.1.val
  let l : ZMod r := nearestNumerator r precision out.2.val
  exact if k = 0 then none else some (l / k)

noncomputable def orderFindingSuccessProbability
    (r precision d : ℕ)
    (hr : Nat.Prime r)
    (aReg bReg : List Wire)
    (ψ : State) : ℝ :=
  ∑ a : Fin (2 ^ precision),
    ∑ b : Fin (2 ^ precision),
      if orderFindingPostprocess r precision hr (a, b) =
          some (d : ZMod r)
      then
        jointRegisterProbability
          aReg bReg a.val b.val ψ
      else 0

structure ECDLPSetting
    {G : Type*} [AddCommGroup G]
    (P Q : G) (r d : ℕ) : Prop where
  prime_order : Nat.Prime r
  order_P : addOrderOf P = r
  Q_eq : Q = d • P

structure OrderFindingSetup
    {G : Type*} [AddCommGroup G]
    {w : ℕ}
    (enc : PointEncoding G w)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (precision : ℕ)
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
