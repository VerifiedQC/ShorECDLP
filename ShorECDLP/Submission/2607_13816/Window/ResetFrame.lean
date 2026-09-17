import ShorECDLP.Framework.Quantum.AdaptiveFrame
import ShorECDLP.Submission.«2607_13816».Window.Reset

namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Starting from zero, the reset trial returns each branch to the same zero basis state. -/
theorem resetWindowTrial_zero_support (Q : Point) (hrQ : order • Q=0)
    (b : InstrumentBranch) (hb : b∈(resetWindowTrial Q hrQ).run) :
    SupportedOn (fun s => s=zeroBasisState) (b.kraus (ket zeroBasisState)) := by
  intro s hs
  funext w
  by_cases hw : w∈windowResetWires
  · exact resetWindowTrial_clean Q hrQ b hb (ket zeroBasisState) s hs w hw
  · have hn : w∉(resetWindowTrial Q hrQ).wires := fun h => hw (resetWindowTrial_support Q hrQ h)
    exact AdaptiveCircuit.branch_frame (resetWindowTrial Q hrQ) w false hn b hb
      (ket zeroBasisState) (supportedOn_ket _ _ rfl) s hs
theorem supportedZero_scalar (ψ : State)
    (hψ : SupportedOn (fun s => s=zeroBasisState) ψ) :
    ψ=ψ zeroBasisState • ket zeroBasisState := by
  classical
  ext s
  by_cases he : s=zeroBasisState
  · subst s; simp [ket]
  · have hz : ψ s=0 := by by_contra h; exact he (hψ s h)
    simp [ket,he,hz]
theorem resetWindowTrial_zero_branch (Q : Point) (hrQ : order • Q=0)
    (b : InstrumentBranch) (hb : b∈(resetWindowTrial Q hrQ).run) :
    b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  supportedZero_scalar _ (resetWindowTrial_zero_support Q hrQ b hb)
end
end ShorECDLP.Paper2607_13816
