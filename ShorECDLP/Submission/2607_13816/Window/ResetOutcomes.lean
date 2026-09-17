import ShorECDLP.Submission.«2607_13816».Window.Total
import ShorECDLP.Submission.«2607_13816».Window.Reset
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Decode only the original trial prefix, excluding reset measurements. -/
def resetWindowDecode (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (List Bool × List Bool) := do
  let rest ← consumeAdaptiveHistory (secpWindowProgram Q hrQ) hist
  secpWindowDecode Q hrQ (hist.take (hist.length-rest.length))
private theorem reset_decode_seq (Q : Point) (hrQ : order • Q=0)
    (before after : InstrumentBranch) (hb : before∈(secpWindowProgram Q hrQ).run) :
    resetWindowDecode Q hrQ (before.seq after).history=secpWindowDecode Q hrQ before.history := by
  simp only [resetWindowDecode,InstrumentBranch.seq,consumeAdaptiveHistory_run _ before hb,
    Option.bind,Bind.bind,List.length_append,Nat.add_sub_cancel_right,List.take_left]
private theorem reset_wellFormed (ws : List Wire) :
    (measureResetWithCorrection ws (fun _ => [])).WellFormed := by
  induction ws with
  | nil => exact ⟨by simp [CircuitWellFormed],True.intro⟩
  | cons w ws ih => exact ⟨ih,ih⟩
theorem resetRegister_mass (ws : List Wire) (ψ : State) :
    Instrument.bornMass (measureResetWithCorrection ws (fun _ => [])).run ψ=normSq ψ :=
  AdaptiveCircuit.run_preservesBornMass _ (reset_wellFormed ws) ψ
theorem instrumentMass_seq_preserving (I J : Instrument) (ψ : State)
    (hJ : ∀ φ, Instrument.bornMass J φ=normSq φ) :
    Instrument.bornMass (Instrument.seq I J) ψ=Instrument.bornMass I ψ := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    have he : Instrument.bornMass (J.map b.seq) ψ=normSq (b.kraus ψ) := by
      simpa only [Instrument.bornMass,List.map_map,InstrumentBranch.seq,LinearMap.comp_apply] using hJ (b.kraus ψ)
    simpa only [Instrument.seq,List.flatMap_cons,Instrument.bornMass,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons] using congrArg₂ (·+·) he ih
theorem instrumentFilter_seq_first (I J : Instrument) (p z : InstrumentBranch → Bool)
    (hz : ∀ b∈I, ∀ a∈J, z (b.seq a)=p b) :
    (Instrument.seq I J).filter z=Instrument.seq (I.filter p) J := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    have hm : (J.map b.seq).filter z=if p b then J.map b.seq else [] := by
      rw [List.filter_map]
      have he : J.filter (z ∘ b.seq)=J.filter (fun _ => p b) := by
        apply List.filter_congr
        intro a ha
        exact hz b (by simp) a ha
      rw [he]
      cases p b <;> simp
    have ht := ih (fun a ha c hc => hz a (by simp [ha]) c hc)
    unfold Instrument.seq at ht
    cases hp : p b <;> simp [Instrument.seq,List.filter_append,hm,hp,ht]
theorem resetWindowOutputMass_physical (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^257) × Fin (2^257)) :
    Instrument.bornMass ((resetWindowTrial Q hrQ).run.filter
      (fun b => resetWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))) (ket zeroBasisState)=
      secpWindowOutputMass Q hrQ out := by
  rw [resetWindowTrial,AdaptiveCircuit.run_seq]
  rw [instrumentFilter_seq_first _ _ (fun b => secpWindowDecode Q hrQ b.history==
    some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2)) _ (by
      intro b hb a _; rw [reset_decode_seq Q hrQ b a hb])]
  rw [windowResetProgram,instrumentMass_seq_preserving _ _ _ (resetRegister_mass windowResetWires)]
  exact secpWindowOutputMass_physical Q hrQ out

theorem resetWindowTrial_total (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass (resetWindowTrial Q hrQ).run (ket zeroBasisState)=1 := by
  rw [resetWindowTrial,AdaptiveCircuit.run_seq,windowResetProgram,instrumentMass_seq_preserving _ _ _ (resetRegister_mass windowResetWires)]
  exact secpWindowProgram_total Q hrQ d hQd
end
end ShorECDLP.Paper2607_13816
