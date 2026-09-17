import ShorECDLP.Submission.«2607_13816».Window.DirectSuccess
import ShorECDLP.Submission.«2607_13816».Window.Secp
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
open scoped BigOperators
noncomputable section
private theorem generator_nonzero : G≠0 := by
  intro h
  have hg := generator_order
  rw [h,addOrderOf_zero] at hg
  have hp := order_prime.two_le
  omega

def directSecpWindowProgram (Q : Point) (hrQ : order • Q=0) : AdaptiveCircuit := by
  classical
  exact if hQ : Q=0 then .done else
    directWindowTrialProgram G Q generator_nonzero hQ generator_nsmul_eq_zero hrQ

def directSecpWindowDecode (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (List Bool × List Bool) := by
  classical
  exact if hQ : Q=0 then secpWindowDecode Q hrQ hist else
    decodeDirectWindowTrial G Q generator_nonzero hQ generator_nsmul_eq_zero hrQ hist

theorem directSecpWindowProgram_qubitCount (Q : Point) (hrQ : order • Q=0) :
    (directSecpWindowProgram Q hrQ).qubitCount≤1383 := by
  by_cases hQ : Q=0
  · simp [directSecpWindowProgram,hQ,AdaptiveCircuit.qubitCount,AdaptiveCircuit.wires]
  · simpa only [directSecpWindowProgram,dif_neg hQ] using
      directWindowTrialProgram_qubitCount G Q generator_nonzero hQ generator_nsmul_eq_zero hrQ

/-- The new program's complete transcript has the baseline output distribution. -/
theorem directSecpWindowOutputMass_physical (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^257) × Fin (2^257)) :
    Instrument.bornMass ((directSecpWindowProgram Q hrQ).run.filter
      (fun b => directSecpWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))) (ket zeroBasisState)=
      secpWindowOutputMass Q hrQ out := by
  by_cases hQ : Q=0
  · simpa only [directSecpWindowProgram,directSecpWindowDecode,secpWindowProgram,dif_pos hQ] using
      secpWindowOutputMass_physical Q hrQ out
  · simp only [directSecpWindowProgram,directSecpWindowDecode,secpWindowOutputMass,dif_neg hQ]
    exact directWindowTrialOutputMass_eq G Q generator_nonzero hQ generator_nsmul_eq_zero hrQ _ _
      (paperOutcomeBits_length _ _) (paperOutcomeBits_length _ _)

/-- Success is computed by filtering the new physical circuit's actual transcripts. -/
def directSecpWindowSuccessMass (Q : Point) (hrQ : order • Q=0) (d : Nat) : ℝ :=
  ∑ out : Fin (2^257) × Fin (2^257),
    if secpWindowPostprocess Q out=some (d:ZMod order) then
      Instrument.bornMass ((directSecpWindowProgram Q hrQ).run.filter
        (fun b => directSecpWindowDecode Q hrQ b.history==
          some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))) (ket zeroBasisState)
    else 0

theorem directSecpWindowSuccessMass_eq (Q : Point) (hrQ : order • Q=0) (d : Nat) :
    directSecpWindowSuccessMass Q hrQ d=secpWindowSuccessMass Q hrQ d := by
  simp only [directSecpWindowSuccessMass,secpWindowSuccessMass,directSecpWindowOutputMass_physical]

theorem directSecpWindow_success_certificate (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    (∑ out : Fin (2^257) × Fin (2^257),
      Instrument.bornMass ((directSecpWindowProgram Q hrQ).run.filter
        (fun b => directSecpWindowDecode Q hrQ b.history==
          some (paperOutcomeBits 257 out.1,paperOutcomeBits 257 out.2))) (ket zeroBasisState))=1 ∧
    (((order-1:Nat):ℝ)/(order:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ directSecpWindowSuccessMass Q hrQ d ∧
    (directSecpWindowProgram Q hrQ).qubitCount≤1383 := by
  refine ⟨?_,?_,directSecpWindowProgram_qubitCount Q hrQ⟩
  · simp only [directSecpWindowOutputMass_physical]
    exact secpWindowOutputMass_total Q hrQ d hQd
  · rw [directSecpWindowSuccessMass_eq]
    exact secpWindowSuccessMass_lower Q hrQ d hQd
end
end ShorECDLP.Paper2607_13816
