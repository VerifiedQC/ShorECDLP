import ShorECDLP.Submission.EllipticCurve.ECDLPOracle
import ShorECDLP.Submission.OrderFinding.Defs

/-!
# Concrete Bitcoin ECDLP trial

This file names only the exact one-run secp256k1 circuit.  Its correctness,
repetition policy, and resource certificate live in separate modules.
-/

namespace ShorECDLP.Secp256k1

variable [Fact (Nat.Prime p)]

open Quantum.PhaseEstimation

/-- One exact secp256k1 ECDLP order-finding trial. -/
def ecdlpTrial
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (Q : Point) : Circuit :=
  hadamards (aReg ++ bReg) ++
    ecdlpOracle aReg bReg pointReg workStart G Q ++
    Quantum.iqft aReg qftAncilla ++
    Quantum.iqft bReg qftAncilla

/-- The named trial is definitionally the circuit form of `orderFinding`. -/
theorem ecdlpTrial_run
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (Q : Point) (s : BasisState) :
    Quantum.run (ecdlpTrial
        aReg bReg pointReg workStart qftAncilla Q) (Quantum.ket s) =
      Quantum.OrderFinding.orderFinding
        aReg bReg qftAncilla
        (Quantum.run
          (ecdlpOracle aReg bReg pointReg workStart G Q))
        (Quantum.ket s) := by
  simp [ecdlpTrial, Quantum.OrderFinding.orderFinding,
    Quantum.run_append, LinearMap.comp_apply]

end ShorECDLP.Secp256k1
