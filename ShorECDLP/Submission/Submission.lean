import ShorECDLP.Submission.Correctness.EndToEnd

/-!
# Concrete Bitcoin ECDLP submission

This file contains only the final record value required by
`Framework.Contract`.  Its circuit and supporting proofs are defined in the
submission modules it imports.
-/

namespace ShorECDLP
namespace Secp256k1

variable [Fact (Nat.Prime p)] [Fact (Nat.Prime order)]

/-- The concrete circuit family and certificates submitted to the Framework contract. -/
noncomputable def bitcoinECDLPSubmission
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (haLength : aReg.length = 256)
    (hbLength : bReg.length = 256)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup)
    (horderG : addOrderOf G = order)
    (hancillaFresh :
      qftAncilla ∉
        aReg ++ bReg ++ pointReg ++ scalarMulWork workStart) :
    BitcoinECDLPSubmission (Fact.out : Nat.Prime order) aReg bReg where
  program := fun Q =>
    ecdlpTrial aReg bReg pointReg workStart qftAncilla Q
  singleRunSuccessLowerBound := 41 / 250
  correct := by
    intro Q d hQ _hQnonzero
    let hsetup :
        Quantum.OrderFinding.OrderFindingSetup pointEncoding
          aReg bReg pointReg (scalarMulWork workStart)
          qftAncilla 256 zeroBasisState :=
      { a_width := haLength
        b_width := hbLength
        a_zero := regValue_zeroBasisState aReg
        b_zero := regValue_zeroBasisState bReg
        point_zero := by
          simp only [regValue_zeroBasisState, pointEncoding_encode_val,
            encodeNat_zero]
        oracleWork_zero := by simp [Clean]
        ancilla_zero := zeroBasisState_apply qftAncilla
        ancilla_fresh := hancillaFresh }
    exact bitcoinECDLPTrial_correct (d := d) Q aReg bReg pointReg workStart
      qftAncilla hpointLength hnodup horderG hQ hsetup
  gateCount := 841862539761920
  gateCount_correct := by
    intro Q d hQ hQnonzero
    exact ecdlpTrial_tCount Q aReg bReg pointReg workStart
      qftAncilla haLength hbLength hpointLength horderG hQ hQnonzero
  trialCount := 26
  trialCount_correct := bitcoinECDLP_correct

end Secp256k1
end ShorECDLP
