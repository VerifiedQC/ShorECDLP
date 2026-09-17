import ShorECDLP.Submission.«2607_13816».Window.DirectTotal
import ShorECDLP.Submission.«2607_13816».Window.DirectReset
import ShorECDLP.Submission.«2607_13816».Window.ResetOutcomes
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Decode only the original trial prefix, excluding reset measurements. -/
def resetDirectWindowDecode (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (List Bool × List Bool) := do
  let rest ← consumeAdaptiveHistory (directSecpWindowProgram Q hrQ) hist
  directSecpWindowDecode Q hrQ (hist.take (hist.length-rest.length))
private theorem reset_decode_seq (Q : Point) (hrQ : order • Q=0)
    (before after : InstrumentBranch) (hb : before∈(directSecpWindowProgram Q hrQ).run) :
    resetDirectWindowDecode Q hrQ (before.seq after).history=directSecpWindowDecode Q hrQ before.history := by
  simp only [resetDirectWindowDecode,InstrumentBranch.seq,consumeAdaptiveHistory_run _ before hb,
    Option.bind,Bind.bind,List.length_append,Nat.add_sub_cancel_right,List.take_left]
theorem resetDirectWindowOutputMass_physical (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^257) × Fin (2^257)) :
    Instrument.bornMass ((resetDirectWindowTrial Q hrQ).run.filter
      (fun b => resetDirectWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))) (ket zeroBasisState)=
      secpWindowOutputMass Q hrQ out := by
  rw [resetDirectWindowTrial,AdaptiveCircuit.run_seq]
  rw [instrumentFilter_seq_first _ _ (fun b => directSecpWindowDecode Q hrQ b.history==
    some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2)) _ (by
      intro b hb a _; rw [reset_decode_seq Q hrQ b a hb])]
  rw [windowResetProgram,instrumentMass_seq_preserving _ _ _ (resetRegister_mass windowResetWires)]
  exact directSecpWindowOutputMass_physical Q hrQ out

theorem resetDirectWindowTrial_total (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass (resetDirectWindowTrial Q hrQ).run (ket zeroBasisState)=1 := by
  rw [resetDirectWindowTrial,AdaptiveCircuit.run_seq,windowResetProgram,instrumentMass_seq_preserving _ _ _ (resetRegister_mass windowResetWires)]
  exact directSecpWindowProgram_total Q hrQ d hQd
end
end ShorECDLP.Paper2607_13816
