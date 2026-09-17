import ShorECDLP.Submission.«2607_13816».Window.DirectRepetition
import ShorECDLP.Submission.«2607_13816».Window.TrialPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section

def physicalPointLookupPrimitives (table : Nat → Point) : PrimitiveResources :=
  ⟨262140,131070,
    (tableAddressTree (List.range' 855 16) 0 1).leafCostSum
      (fun a _ => (pointTableMask table a).length) 836 (List.range' 519 16)+196605,
    65535,0,65535⟩

theorem physicalPointLookup_primitive (table : Nat → Point) :
    primitiveResources (physicalPointLookup table)=physicalPointLookupPrimitives table := by
  rw [physicalPointLookup,directPointLookup,tableLookupProgram_primitive _ _ _ _
    (by simp) (by decide +kernel)]
  rfl

def directScalarPrimitives (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : PrimitiveResources :=
  ((physicalPointLookupPrimitives (firstWindowTable (axisWindowOffset P 17+axisWindowOffset Q 17) P)).add
    (preparedSchedulePrimitives (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
      (fun k => oddWindowTable_valid P hP hrP (k-0)) 16 1)).add
    (preparedSchedulePrimitives (fun k => oddWindowX Q (k-17)) (fun k => oddWindowY Q (k-17))
      (fun k => oddWindowTable_valid Q hQ hrQ (k-17)) 17 17)

theorem directScalarProgram_primitive (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    primitiveResources (directScalarProgram P Q hP hQ hrP hrQ)=directScalarPrimitives P Q hP hQ hrP hrQ := by
  rw [directScalarProgram,primitiveResources_seq,primitiveResources_seq,physicalPointLookup_primitive,
    axisWindowProgram,preparedWindowSchedule_primitive,preparedWindowSchedule_primitive]
  rfl

def directWindowTrialPrimitives (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : PrimitiveResources :=
  ((⟨0,514,0,0,0,0⟩ : PrimitiveResources).add
    (((⟨1,0,0,0,0,0⟩ : PrimitiveResources).add
      (directScalarPrimitives P Q hP hQ hrP hrQ)).add ⟨1,0,0,0,0,0⟩)).add
    ⟨0,0,0,0,65792,514⟩

theorem directWindowTrialProgram_primitive (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    primitiveResources (directWindowTrialProgram P Q hP hQ hrP hrQ)=directWindowTrialPrimitives P Q hP hQ hrP hrQ := by
  have hx : primitiveResources (.unitary [.X 836] .done)=⟨1,0,0,0,0,0⟩ := by
    unfold primitiveResources
    rfl
  rw [directWindowTrialProgram,primitiveResources_seq,directPreparedScalarProgram,primitiveResources_seq,
    scalarPhasePrepare_primitive,directScalarComputeProgram,primitiveResources_seq,
    primitiveResources_seq,hx,directScalarProgram_primitive,scalarFourierProgram_primitive_exact]
  rfl

private theorem generator_nonzero : G≠0 := by
  intro h
  have hg := generator_order
  rw [h,addOrderOf_zero] at hg
  have hp := order_prime.two_le
  omega

def directSecpWindowPrimitives (Q : Point) (hrQ : order • Q=0) : PrimitiveResources := by
  classical
  exact if hQ : Q=0 then ⟨0,0,0,0,0,0⟩ else
    directWindowTrialPrimitives G Q generator_nonzero hQ generator_nsmul_eq_zero hrQ

theorem directSecpWindowProgram_primitive (Q : Point) (hrQ : order • Q=0) :
    primitiveResources (directSecpWindowProgram Q hrQ)=directSecpWindowPrimitives Q hrQ := by
  by_cases hQ : Q=0
  · simp only [directSecpWindowProgram,directSecpWindowPrimitives,dif_pos hQ]
    rfl
  · simp only [directSecpWindowProgram,directSecpWindowPrimitives,dif_neg hQ]
    exact directWindowTrialProgram_primitive _ _ _ _ _ _

def directRepeatedWindowPrimitives (Q : Point) (hrQ : order • Q=0) : PrimitiveResources :=
  scalePrimitives 26 ((directSecpWindowPrimitives Q hrQ).add ⟨0,0,0,0,0,1383⟩)

theorem directSecpWindowRepeatedProgram_primitive (Q : Point) (hrQ : order • Q=0) :
    primitiveResources (directSecpWindowRepeatedProgram Q hrQ)=directRepeatedWindowPrimitives Q hrQ := by
  rw [directSecpWindowRepeatedProgram,repeatWindowProgram_primitive,resetDirectWindowTrial,
    primitiveResources_seq,directSecpWindowProgram_primitive,windowResetProgram_primitive]
  rfl
end
end ShorECDLP.Paper2607_13816
