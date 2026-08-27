import ShorECDLP.Submission.OrderFinding.OracleSpec
import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Defs

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

end ShorECDLP.Quantum.OrderFinding
