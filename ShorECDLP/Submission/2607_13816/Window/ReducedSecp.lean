import ShorECDLP.Submission.«2607_13816».Window.ReducedSuccess
import ShorECDLP.Submission.«2607_13816».Window.Secp
import ShorECDLP.Math.EllipticCurve.GeneratorOrder
import Mathlib.Analysis.Real.Pi.Bounds
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1 Quantum.PhaseEstimation Quantum.OrderFinding
open scoped BigOperators
noncomputable section
/-- The zero public point needs no quantum gates. -/
def reducedSecpWindowProgram (Q : Point) (hrQ : order • Q=0) : AdaptiveCircuit := by
  classical
  exact if hQ : Q=0 then .done else
    reducedWindowTrialProgram G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ
/-- Public-input classical postprocessing, including the zero-point case. -/
def reducedSecpWindowPostprocess (Q : Point) (out : Fin (2^256) × Fin (2^208)) : Option (ZMod order) := by
  classical
  exact if Q=0 then some 0 else reducedVerifiedCandidate Q out
/-- Distribution of decoded output pairs; zero input uses the deterministic pair (0,0). -/
def reducedSecpWindowOutputMass (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^256) × Fin (2^208)) : ℝ := by
  classical
  exact if hQ : Q=0 then if out=(0,0) then 1 else 0 else
    reducedWindowTrialFiniteOutputMass G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ out
/-- Success event of the public-input program and its classical postprocessor. -/
def reducedSecpWindowSuccessMass (Q : Point) (hrQ : order • Q=0) (d : Nat) : ℝ :=
  ∑ out : Fin (2^256) × Fin (2^208),
    if reducedSecpWindowPostprocess Q out=some (d:ZMod order) then reducedSecpWindowOutputMass Q hrQ out else 0

theorem reducedSecpWindow_zero_success (Q : Point) (hrQ : order • Q=0) (hQ : Q=0)
    (d : Nat) (hQd : Q=d • G) : reducedSecpWindowSuccessMass Q hrQ d=1 := by
  have hd := secpWindow_zero_input d (hQd.symm.trans hQ)
  simp only [reducedSecpWindowSuccessMass,reducedSecpWindowPostprocess,reducedSecpWindowOutputMass,hd,
    dif_pos hQ,if_pos hQ,ite_true,Finset.sum_ite_eq',Finset.mem_univ]
theorem reducedSecpWindow_nonzero_success (Q : Point) (hQ : Q≠0) (hrQ : order • Q=0) (d : Nat) :
    reducedSecpWindowSuccessMass Q hrQ d=
      reducedPhysicalVerifiedMass Q secpGenerator_ne_zero hQ hrQ d := by
  simp only [reducedSecpWindowSuccessMass,reducedSecpWindowPostprocess,reducedSecpWindowOutputMass,if_neg hQ,dif_neg hQ,
    reducedPhysicalVerifiedMass]
theorem reducedSecpWindowProgram_qubitCount (Q : Point) (hrQ : order • Q=0) :
    (reducedSecpWindowProgram Q hrQ).qubitCount≤1303 := by
  by_cases hQ : Q=0
  · simp [reducedSecpWindowProgram,hQ,AdaptiveCircuit.qubitCount,AdaptiveCircuit.wires]
  · simpa only [reducedSecpWindowProgram,dif_neg hQ] using
      reducedWindowTrialProgram_qubitCount G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ
theorem reducedSecpWindowProgram_zero (hrQ : order • (0:Point)=0) : reducedSecpWindowProgram 0 hrQ=.done := by
  simp [reducedSecpWindowProgram]
theorem reducedSecpWindowProgram_nonzero (Q : Point) (hrQ : order • Q=0) (hQ : Q≠0) :
    reducedSecpWindowProgram Q hrQ=reducedWindowTrialProgram G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ := by
  simp only [reducedSecpWindowProgram,dif_neg hQ]
theorem reducedSecpWindowOutputMass_total (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    ∑ out : Fin (2^256) × Fin (2^208), reducedSecpWindowOutputMass Q hrQ out=1 := by
  by_cases hQ : Q=0
  · simp only [reducedSecpWindowOutputMass,dif_pos hQ,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · simp only [reducedSecpWindowOutputMass,dif_neg hQ]
    exact reducedWindowTrialFiniteOutputMass_total order_prime G Q secpGenerator_ne_zero hQ
      generator_nsmul_eq_zero hrQ generator_order d hQd
/-- The classical zero case and quantum nonzero case satisfy one concrete success bound. -/
theorem reducedSecpWindowSuccessMass_lower (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (((order-1:Nat):ℝ)/(order:ℝ))*((4:ℝ)/Real.pi^2)^2 ≤ reducedSecpWindowSuccessMass Q hrQ d := by
  by_cases hQ : Q=0
  · exact secpSuccessBound_le_one.trans_eq (reducedSecpWindow_zero_success Q hrQ hQ d hQd).symm
  · exact (reducedPhysicalVerifiedMass_lower Q secpGenerator_ne_zero hQ hrQ d hQd).trans_eq (reducedSecpWindow_nonzero_success Q hQ hrQ d).symm
/-- Decode the public-input program's actual transcript; the gate-free case emits the classical zero pair. -/
def reducedSecpWindowDecode (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (List Bool × List Bool) := by
  classical
  exact if hQ : Q=0 then
    if hist=[] then some (paperOutcomeBits 256 0,paperOutcomeBits 208 0) else none
  else decodeReducedWindowTrial G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ hist
/-- The distribution is obtained by filtering the actual public-input adaptive program. -/
theorem reducedSecpWindowOutputMass_physical (Q : Point) (hrQ : order • Q=0)
    (out : Fin (2^256) × Fin (2^208)) :
    Instrument.bornMass ((reducedSecpWindowProgram Q hrQ).run.filter
      (fun b => reducedSecpWindowDecode Q hrQ b.history==
        some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2))) (ket zeroBasisState)=
      reducedSecpWindowOutputMass Q hrQ out := by
  by_cases hQ : Q=0
  · simp only [reducedSecpWindowProgram,dif_pos hQ,reducedSecpWindowOutputMass]
    rw [doneFiltered_mass (fun hist => reducedSecpWindowDecode Q hrQ hist==
      some (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2))]
    simp only [reducedSecpWindowDecode,dif_pos hQ,ite_true,beq_iff_eq,Option.some.injEq,zeroOutcomeBits_pair]
  · simp only [reducedSecpWindowProgram,reducedSecpWindowDecode,reducedSecpWindowOutputMass,dif_neg hQ]
    rfl
theorem reducedSecpWindowPostprocess_sound (Q : Point) (d : Nat) (hQd : Q=d • G)
    (out : Fin (2^256) × Fin (2^208)) (c : ZMod order)
    (hc : reducedSecpWindowPostprocess Q out=some c) : c=(d:ZMod order) := by
  by_cases hQ : Q=0
  · have hd := secpWindow_zero_input d (hQd.symm.trans hQ)
    simp only [reducedSecpWindowPostprocess,if_pos hQ,Option.some.injEq] at hc
    exact hc.symm.trans hd.symm
  · exact reducedVerifiedCandidate_sound Q d hQd out c (by
      simpa only [reducedSecpWindowPostprocess,if_neg hQ] using hc)

end
end ShorECDLP.Paper2607_13816
