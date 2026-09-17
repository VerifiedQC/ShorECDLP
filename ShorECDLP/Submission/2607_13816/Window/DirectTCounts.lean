import ShorECDLP.Submission.«2607_13816».Window.DirectPrimitives
import ShorECDLP.Submission.«2607_13816».Window.TrialTCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
private theorem scalar_phase (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    (directScalarPrimitives P Q hP hQ hrP hrQ).phase=0 := by
  simp only [directScalarPrimitives,physicalPointLookupPrimitives,PrimitiveResources.add,
    preparedSchedulePrimitives_phase_zero,zero_add]
attribute [local irreducible] primitiveResources
private theorem prepared_resources (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    primitiveResources (directPreparedScalarProgram P Q hP hQ hrP hrQ)=
      (⟨0,514,0,0,0,0⟩ : PrimitiveResources).add
        (((⟨1,0,0,0,0,0⟩ : PrimitiveResources).add
          (directScalarPrimitives P Q hP hQ hrP hrQ)).add ⟨1,0,0,0,0,0⟩) := by
  have hx : primitiveResources (.unitary [.X 836] .done)=⟨1,0,0,0,0,0⟩ := by
    unfold primitiveResources
    rfl
  rw [directPreparedScalarProgram,primitiveResources_seq,scalarPhasePrepare_primitive,
    directScalarComputeProgram,primitiveResources_seq,primitiveResources_seq,hx,
    directScalarProgram_primitive]

private theorem t_seq (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b

theorem directWindowTrialProgram_tCount_exact (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    (directWindowTrialProgram P Q hP hQ hrP hrQ).tCount=
      7*(directScalarPrimitives P Q hP hQ hrP hrQ).toffoli+65792 := by
  have hp : (primitiveResources (directPreparedScalarProgram P Q hP hQ hrP hrQ)).phase=0 := by
    rw [prepared_resources]
    simp only [PrimitiveResources.add,scalar_phase,zero_add,add_zero]
  rw [directWindowTrialProgram,t_seq,primitiveResources_T_of_no_phase _ hp,
    prepared_resources,scalarFourierProgram_tCount_exact]
  simp only [PrimitiveResources.add,zero_add,add_zero]

theorem directSecpWindowProgram_tCount_exact (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) :
    (directSecpWindowProgram Q hrQ).tCount=
      7*(directSecpWindowPrimitives Q hrQ).toffoli+(directSecpWindowPrimitives Q hrQ).phase := by
  classical
  unfold directSecpWindowProgram directSecpWindowPrimitives
  split
  · rfl
  · rw [directWindowTrialProgram_tCount_exact]
    simp only [directWindowTrialPrimitives,PrimitiveResources.add,
      scalar_phase,zero_add,add_zero]

theorem directSecpWindowRepeatedProgram_tCount_exact (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) :
    (directSecpWindowRepeatedProgram Q hrQ).tCount=
      7*(directRepeatedWindowPrimitives Q hrQ).toffoli+(directRepeatedWindowPrimitives Q hrQ).phase := by
  rw [(directSecpWindowRepeatedProgram_resources Q hrQ).1,directSecpWindowProgram_tCount_exact]
  simp only [directRepeatedWindowPrimitives,scalePrimitives,PrimitiveResources.add,add_zero]
  omega
end
end ShorECDLP.Paper2607_13816
