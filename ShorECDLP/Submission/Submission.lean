import ShorECDLP.Submission.Correctness.EndToEnd

/-!
# Concrete Bitcoin ECDLP submission

This file contains only the final record value required by
`Framework.Contract`.  Its circuit, fixed wire layout, and supporting proofs
are defined in the submission modules it imports.
-/

namespace ShorECDLP
namespace Secp256k1

/--
The closed Bitcoin ECDLP submission.  Its public registers, point register,
workspace, and QFT ancilla are fixed by the submission, so callers supply no
layout or initialization premises.
-/
noncomputable def bitcoinECDLPSubmission :
    BitcoinECDLPSubmission order_prime bitcoinAReg bitcoinBReg := by
  obtain ⟨haLength, hbLength, hpointLength, hnodup, hancillaFresh⟩ :=
    bitcoinWireLayout
  exact
    { program := fun Q =>
        ecdlpTrial bitcoinAReg bitcoinBReg bitcoinPointReg
          bitcoinWorkStart bitcoinQFTAncilla Q
      singleRunSuccessLowerBound := 41 / 250
      correct := by
        intro Q d hQ _hQnonzero
        let hsetup :
            Quantum.OrderFinding.OrderFindingSetup pointEncoding
              bitcoinAReg bitcoinBReg bitcoinPointReg
              (scalarMulWork bitcoinWorkStart)
              bitcoinQFTAncilla 256 zeroBasisState :=
          { a_width := haLength
            b_width := hbLength
            a_zero := regValue_zeroBasisState bitcoinAReg
            b_zero := regValue_zeroBasisState bitcoinBReg
            point_zero := by
              simp only [regValue_zeroBasisState, pointEncoding_encode_val,
                encodeNat_zero]
            oracleWork_zero := by simp [Clean]
            ancilla_zero := zeroBasisState_apply bitcoinQFTAncilla
            ancilla_fresh := hancillaFresh }
        exact bitcoinECDLPTrial_correct (d := d) Q
          bitcoinAReg bitcoinBReg bitcoinPointReg
          bitcoinWorkStart bitcoinQFTAncilla
          hpointLength hnodup hQ hsetup
      gateCount := 841862539761920
      gateCount_correct := by
        intro Q d hQ hQnonzero
        exact ecdlpTrial_tCount Q
          bitcoinAReg bitcoinBReg bitcoinPointReg
          bitcoinWorkStart bitcoinQFTAncilla
          haLength hbLength hpointLength hQ hQnonzero
      trialCount := 26
      trialCount_correct := bitcoinECDLP_correct }

end Secp256k1
end ShorECDLP
