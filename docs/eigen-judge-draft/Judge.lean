-- PROTECTED. Organizer-owned judge for the ShorECDLP challenge (Eigen-style shell).
-- Editable path for entrants: ShorECDLP/Submission/Entrant/ only.
-- The entrant module must define, in namespace `ShorECDLP.Entrant`:
--   entry       : ShorECDLP.Challenge.StraightEntry
--   layout      : ShorECDLP.Challenge.DecodeLayout
--   bounds      : ShorECDLP.Challenge.Bounds
--   certificate : ShorECDLP.Challenge.Certificate officialLimits layout entry bounds
-- Every type below is written with `_root_.` so an entrant namespace cannot shadow it.
import ShorECDLP.Challenge.Official
import ShorECDLP.Submission.Entrant.Main

namespace ShorECDLP.Judge

/-- Organizer limits. Fixed here, outside every editable path. Values TBD (owner/Eigen). -/
abbrev officialLimits := _root_.ShorECDLP.Challenge.officialLimits

def check_entry : _root_.ShorECDLP.Challenge.StraightEntry := _root_.ShorECDLP.Entrant.entry
def check_layout : _root_.ShorECDLP.Challenge.DecodeLayout := _root_.ShorECDLP.Entrant.layout
def check_bounds : _root_.ShorECDLP.Challenge.Bounds := _root_.ShorECDLP.Entrant.bounds

/-- The single acceptance statement. If this elaborates, the entry is admitted. -/
theorem check_certificate :
    _root_.ShorECDLP.Challenge.Certificate officialLimits check_layout check_entry check_bounds :=
  _root_.ShorECDLP.Entrant.certificate

/-- Score = declared T-model bound of the whole program (lower is better). -/
def score : Nat := _root_.ShorECDLP.Challenge.declaredScore check_bounds
def qubits : Nat := check_bounds.qubits

end ShorECDLP.Judge

#print axioms ShorECDLP.Judge.check_certificate
#eval ShorECDLP.Judge.score
#eval ShorECDLP.Judge.qubits
