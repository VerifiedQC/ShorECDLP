import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceCorrections
import ShorECDLP.Framework.Quantum.Relabel
namespace ShorECDLP.Paper2607_13816
def CorrectionFragment.relabel (e : Wire ≃ Wire) : CorrectionFragment → CorrectionFragment
  | .ordinary g => .ordinary (g.map (Gate.relabel e))
  | .selected g => .selected (g.map (Gate.relabel e))
private theorem correctionBlockErase_relabel (e : Wire ≃ Wire) (fs : List CorrectionFragment) :
    correctionBlockErase (fs.map (CorrectionFragment.relabel e))=
      (correctionBlockErase fs).map (Gate.relabel e) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp [correctionBlockErase,CorrectionFragment.relabel,CorrectionFragment.erase] at *
    all_goals exact ih
private theorem correctionBlockEvents_relabel (e : Wire ≃ Wire) (fs : List CorrectionFragment) :
    correctionBlockEvents (fs.map (CorrectionFragment.relabel e))=correctionBlockEvents fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp [correctionBlockEvents,CorrectionFragment.relabel,CorrectionFragment.events] at *
    all_goals exact ih
def CorrectionProgram.relabel (e : Wire ≃ Wire) : CorrectionProgram → CorrectionProgram
  | .done => .done
  | .unitary fs next => .unitary (fs.map (CorrectionFragment.relabel e)) (next.relabel e)
  | .reset w a b => .reset (e w) (a.relabel e) (b.relabel e)
theorem CorrectionProgram.erase_relabel (e : Wire ≃ Wire) (p : CorrectionProgram) :
    (p.relabel e).erase=p.erase.relabel e := by
  induction p with
  | done => rfl
  | unitary fs p ih => simp [relabel,erase,Quantum.AdaptiveCircuit.relabel,correctionBlockErase_relabel,ih]
  | reset w a b iha ihb => simp [relabel,erase,Quantum.AdaptiveCircuit.relabel,iha,ihb]
theorem CorrectionProgram.events_relabel (e : Wire ≃ Wire) (p : CorrectionProgram) :
    (p.relabel e).events=p.events := by
  induction p with
  | done => rfl
  | unitary fs p ih => simp [relabel,events,correctionBlockEvents_relabel,ih]
  | reset w a b iha ihb => simp [relabel,events,iha,ihb]
end ShorECDLP.Paper2607_13816
