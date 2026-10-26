import ShorECDLP.Challenge.Official
import ShorECDLP.Submission.Entrant.Main

/-! PROTECTED judge. Binds the entrant's four names to fully `_root_`-qualified
protected types, so an entrant namespace cannot shadow them. If this module
elaborates and its axioms are within the allowlist, the entry is admitted. -/

namespace ShorECDLP.Judge
noncomputable section

def check_entry : _root_.ShorECDLP.Challenge.StraightEntry := _root_.ShorECDLP.Entrant.entry
def check_layout : _root_.ShorECDLP.Challenge.DecodeLayout := _root_.ShorECDLP.Entrant.layout
def check_bounds : _root_.ShorECDLP.Challenge.Bounds := _root_.ShorECDLP.Entrant.bounds

/-- The single acceptance statement, against the protected organizer limits. -/
theorem check_certificate :
    _root_.ShorECDLP.Challenge.Certificate _root_.ShorECDLP.Challenge.officialLimits
      check_layout check_entry check_bounds :=
  _root_.ShorECDLP.Entrant.certificate

end

/-- Score: declared T-model bound of the whole program (lower is better). -/
def score : Nat := _root_.ShorECDLP.Challenge.declaredScore _root_.ShorECDLP.Entrant.bounds
def qubits : Nat := _root_.ShorECDLP.Entrant.bounds.qubits
def measurements : Nat := _root_.ShorECDLP.Entrant.bounds.measurements

end ShorECDLP.Judge
