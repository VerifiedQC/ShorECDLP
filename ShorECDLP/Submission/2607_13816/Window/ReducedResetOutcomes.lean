import ShorECDLP.Submission.«2607_13816».Window.ReducedTotal
import ShorECDLP.Submission.«2607_13816».Window.ReducedReset
import ShorECDLP.Submission.«2607_13816».Window.ResetOutcomes
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Decode only the original trial prefix, excluding reset measurements. -/
def resetReducedWindowDecode (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (List Bool × List Bool) := do
  let rest ← consumeAdaptiveHistory (reducedSecpWindowProgram Q hrQ) hist
  reducedSecpWindowDecode Q hrQ (hist.take (hist.length-rest.length))
private theorem reset_decode_seq (Q : Point) (hrQ : order • Q=0)
    (before after : InstrumentBranch) (hb : before∈(reducedSecpWindowProgram Q hrQ).run) :
    resetReducedWindowDecode Q hrQ (before.seq after).history=reducedSecpWindowDecode Q hrQ before.history := by
  simp only [resetReducedWindowDecode,InstrumentBranch.seq,consumeAdaptiveHistory_run _ before hb,
    Option.bind,Bind.bind,List.length_append,Nat.add_sub_cancel_right,List.take_left]
theorem resetReducedWindowOutputMass_physical (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^256) × Fin (2^208)) :
    Instrument.bornMass ((resetReducedWindowTrial Q hrQ).run.filter
      (fun b => resetReducedWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2))) (ket zeroBasisState)=
      reducedSecpWindowOutputMass Q hrQ out := by
  rw [resetReducedWindowTrial,AdaptiveCircuit.run_seq]
  rw [instrumentFilter_seq_first _ _ (fun b => reducedSecpWindowDecode Q hrQ b.history==
    some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2)) _ (by
      intro b hb a _; rw [reset_decode_seq Q hrQ b a hb])]
  rw [reducedResetProgram,instrumentMass_seq_preserving _ _ _ (resetRegister_mass reducedResetWires)]
  exact reducedSecpWindowOutputMass_physical Q hrQ out

theorem resetReducedWindowTrial_total (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass (resetReducedWindowTrial Q hrQ).run (ket zeroBasisState)=1 := by
  rw [resetReducedWindowTrial,AdaptiveCircuit.run_seq,reducedResetProgram,instrumentMass_seq_preserving _ _ _ (resetRegister_mass reducedResetWires)]
  exact reducedSecpWindowProgram_total Q hrQ d hQd
end
end ShorECDLP.Paper2607_13816
