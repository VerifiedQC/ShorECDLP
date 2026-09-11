import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceCorrections
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantControl
namespace ShorECDLP.Paper2607_13816
/-- Eliminate a fixed control without losing the provenance of selected corrections. -/
def CorrectionFragment.constantControl (q : Wire) : CorrectionFragment → CorrectionFragment
  | .ordinary g => .ordinary (g.map (constantControlGate q))
  | .selected g => .selected (g.map (constantControlGate q))
private theorem correctionBlockErase_constantControl (q : Wire) (fs : List CorrectionFragment) :
    correctionBlockErase (fs.map (CorrectionFragment.constantControl q))=
      (correctionBlockErase fs).map (constantControlGate q) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp [correctionBlockErase,CorrectionFragment.constantControl,CorrectionFragment.erase] at *
    all_goals exact ih
private theorem correctionBlockEvents_constantControl (q : Wire) (fs : List CorrectionFragment) :
    correctionBlockEvents (fs.map (CorrectionFragment.constantControl q))=correctionBlockEvents fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp [correctionBlockEvents,CorrectionFragment.constantControl,CorrectionFragment.events] at *
    all_goals exact ih
def CorrectionProgram.constantControl (q : Wire) : CorrectionProgram → CorrectionProgram
  | .done => .done
  | .unitary fs next => .unitary (fs.map (CorrectionFragment.constantControl q)) (next.constantControl q)
  | .reset w a b => .reset w (a.constantControl q) (b.constantControl q)
theorem CorrectionProgram.erase_constantControl (q : Wire) (p : CorrectionProgram) :
    (p.constantControl q).erase=constantControlProgram q p.erase := by
  induction p with
  | done => rfl
  | unitary fs p ih => simp [constantControl,erase,constantControlProgram,correctionBlockErase_constantControl,ih]
  | reset w a b iha ihb => simp [constantControl,erase,constantControlProgram,iha,ihb]
theorem CorrectionProgram.events_constantControl (q : Wire) (p : CorrectionProgram) :
    (p.constantControl q).events=p.events := by
  induction p with
  | done => rfl
  | unitary fs p ih => simp [constantControl,events,correctionBlockEvents_constantControl,ih]
  | reset w a b iha ihb => simp [constantControl,events,iha,ihb]
end ShorECDLP.Paper2607_13816
