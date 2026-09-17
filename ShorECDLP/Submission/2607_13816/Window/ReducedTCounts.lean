import ShorECDLP.Submission.«2607_13816».Window.ReducedPrimitives
import ShorECDLP.Submission.«2607_13816».Window.TrialTCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
private theorem scalar_phase (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    (reducedScalarPrimitives P Q hP hQ hrP hrQ).phase=0 := by
  simp only [reducedScalarPrimitives,physicalPointLookupPrimitives,PrimitiveResources.add,
    preparedSchedulePrimitives_phase_zero,zero_add]
attribute [local irreducible] primitiveResources
private theorem prepared_resources (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    primitiveResources (reducedPreparedScalarProgram P Q hP hQ hrP hrQ)=
      (⟨0,464,0,0,0,0⟩ : PrimitiveResources).add
        (((⟨1,0,0,0,0,0⟩ : PrimitiveResources).add
          (reducedScalarPrimitives P Q hP hQ hrP hrQ)).add ⟨1,0,0,0,0,0⟩) := by
  have hx : primitiveResources (.unitary [.X 836] .done)=⟨1,0,0,0,0,0⟩ := by
    unfold primitiveResources
    rfl
  rw [reducedPreparedScalarProgram,primitiveResources_seq,reducedPhasePrepare_primitive,
    reducedScalarComputeProgram,primitiveResources_seq,primitiveResources_seq,hx,
    reducedScalarProgram_primitive]

private theorem t_seq (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b

theorem reducedWindowTrialProgram_tCount_exact (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    (reducedWindowTrialProgram P Q hP hQ hrP hrQ).tCount=
      7*(reducedScalarPrimitives P Q hP hQ hrP hrQ).toffoli+54168 := by
  have hp : (primitiveResources (reducedPreparedScalarProgram P Q hP hQ hrP hrQ)).phase=0 := by
    rw [prepared_resources]
    simp only [PrimitiveResources.add,scalar_phase,zero_add,add_zero]
  rw [reducedWindowTrialProgram,t_seq,primitiveResources_T_of_no_phase _ hp,
    prepared_resources,reducedFourierProgram_tCount_exact]
  simp only [PrimitiveResources.add,zero_add,add_zero]

theorem reducedSecpWindowProgram_tCount_exact (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) :
    (reducedSecpWindowProgram Q hrQ).tCount=
      7*(reducedSecpWindowPrimitives Q hrQ).toffoli+(reducedSecpWindowPrimitives Q hrQ).phase := by
  classical
  unfold reducedSecpWindowProgram reducedSecpWindowPrimitives
  split
  · rfl
  · rw [reducedWindowTrialProgram_tCount_exact]
    simp only [reducedWindowTrialPrimitives,PrimitiveResources.add,
      scalar_phase,zero_add,add_zero]

theorem reducedSecpWindowRepeatedProgram_tCount_exact (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) :
    (reducedSecpWindowRepeatedProgram Q hrQ).tCount=
      7*(reducedRepeatedWindowPrimitives Q hrQ).toffoli+(reducedRepeatedWindowPrimitives Q hrQ).phase := by
  rw [(reducedSecpWindowRepeatedProgram_resources Q hrQ).1,reducedSecpWindowProgram_tCount_exact]
  simp only [reducedRepeatedWindowPrimitives,scalePrimitives,PrimitiveResources.add,add_zero]
  omega
end
end ShorECDLP.Paper2607_13816
