import ShorECDLP.Challenge.Official
import ShorECDLP.Challenge.ExtendedContract

/-! Protected acceptance predicates. This module never imports entrant code.
The external trusted judge constructs applications of these constants as Expr
and checks them with the kernel, without elaborating syntax after importing an
entrant. Qualified names alone do not defend against imported macros. -/
namespace ShorECDLP.Judge
open Challenge

def acceptance (e : StraightEntry) (layout : DecodeLayout) (bounds : Bounds) : Prop :=
  Certificate officialLimits layout e bounds

def extendedAcceptance (e : StraightEntry) (layout : DecodeLayout)
    (bounds : Bounds) (extra : ExtendedBounds) : Prop :=
  ExtendedCertificate officialLimits layout e bounds extra

theorem derive_diagnostics {e : StraightEntry} {layout : DecodeLayout} {bounds : Bounds}
    (h : acceptance e layout bounds) :
    extendedAcceptance e layout bounds ⟨bounds.tModel / 7, officialLimits.gateSlots⟩ :=
  h.extend

end ShorECDLP.Judge
