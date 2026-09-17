import ShorECDLP.Submission.«2607_13816».Window.ReducedTrial
import ShorECDLP.Submission.«2607_13816».Window.DirectPrimitives
import ShorECDLP.Submission.«2607_13816».Window.ReducedRepetition
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
theorem reducedFourierProgram_tCount_exact : reducedFourierProgram.tCount=54168 := by
  have h := modularGateCount_seq tCost
    (semiclassicalFourier .inverse reducedFourierLeft List.nil)
    (semiclassicalFourier .inverse reducedFourierRight List.nil)
  simp only [gidneyGateCount_tCount,semiclassicalFourier_tCount_exact,reducedFourierLeft,reducedFourierRight,
    List.length_reverse,List.length_range',List.count_nil] at h
  have hl : fourierPhaseCount 256 0=32640 := by decide +kernel
  have hr : fourierPhaseCount 208 0=21528 := by decide +kernel
  rw [hl,hr] at h
  exact h
private theorem scalar_cost (cost : Gate → Nat) (v : Nat)
    (hc : ∀ dir k w, cost (.P dir k w)=v) :
    gidneyGateCount cost reducedFourierProgram=v*reducedFourierProgram.tCount := by
  rw [reducedFourierProgram,modularGateCount_seq]
  simp only [semiclassicalFourier_gateCount cost v hc]
  have h := modularGateCount_seq tCost
    (semiclassicalFourier .inverse reducedFourierLeft List.nil)
    (semiclassicalFourier .inverse reducedFourierRight List.nil)
  simp only [gidneyGateCount_tCount] at h
  exact (mul_add _ _ _).symm.trans (congrArg (fun z : Nat => v*z) h.symm)
theorem reducedPhasePrepare_primitive :
    primitiveResources (.unitary reducedPhasePrepare .done)=⟨0,464,0,0,0,0⟩ := by
  change primitiveResources (.unitary (reducedPhaseWires.map Gate.H) .done)=_
  rw [hadamards_primitiveResources]
  simp [reducedPhaseWires]

private theorem fourier_resources_of_cost (a : AdaptiveCircuit)
    (hc : ∀ (cost : Gate → Nat) (v : Nat), (∀ dir k w, cost (.P dir k w)=v) →
      gidneyGateCount cost a=v*a.tCount)
    (ht : a.tCount=54168) (hm : a.measurementCount=464) :
    primitiveResources a=⟨0,0,0,0,54168,464⟩ := by
  have hz (cost : Gate → Nat) (h : ∀ dir k w, cost (.P dir k w)=0) :
      gidneyGateCount cost a=0 := by simpa only [zero_mul] using hc cost 0 h
  have hp : gidneyGateCount primitivePhaseCost a=54168 := by
    simpa only [one_mul,ht] using hc primitivePhaseCost 1 (by intros; rfl)
  unfold primitiveResources gidneyCnotCount gidneyToffoliCount
  rw [hz _ (by intros; rfl),hz _ (by intros; rfl),hz _ (by intros; rfl),
    hz _ (by intros; rfl),hp,hm]

theorem reducedFourierProgram_primitive_exact :
    primitiveResources reducedFourierProgram=⟨0,0,0,0,54168,464⟩ :=
  fourier_resources_of_cost _ scalar_cost reducedFourierProgram_tCount_exact reducedFourierProgram_measurements

def reducedScalarPrimitives (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : PrimitiveResources :=
  ((physicalPointLookupPrimitives (firstWindowTable (axisWindowOffset P 16+axisWindowOffset Q 13) P)).add
    (preparedSchedulePrimitives (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
      (fun k => oddWindowTable_valid P hP hrP (k-0)) 15 1)).add
    (preparedSchedulePrimitives (fun k => oddWindowX Q (k-17)) (fun k => oddWindowY Q (k-17))
      (fun k => oddWindowTable_valid Q hQ hrQ (k-17)) 13 17)

theorem reducedScalarProgram_primitive (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    primitiveResources (reducedScalarProgram P Q hP hQ hrP hrQ)=reducedScalarPrimitives P Q hP hQ hrP hrQ := by
  rw [reducedScalarProgram,primitiveResources_seq,primitiveResources_seq,physicalPointLookup_primitive,
    axisWindowProgram,preparedWindowSchedule_primitive,preparedWindowSchedule_primitive]
  rfl

def reducedWindowTrialPrimitives (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : PrimitiveResources :=
  ((⟨0,464,0,0,0,0⟩ : PrimitiveResources).add
    (((⟨1,0,0,0,0,0⟩ : PrimitiveResources).add
      (reducedScalarPrimitives P Q hP hQ hrP hrQ)).add ⟨1,0,0,0,0,0⟩)).add
    ⟨0,0,0,0,54168,464⟩

theorem reducedWindowTrialProgram_primitive (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    primitiveResources (reducedWindowTrialProgram P Q hP hQ hrP hrQ)=reducedWindowTrialPrimitives P Q hP hQ hrP hrQ := by
  have hx : primitiveResources (.unitary [.X 836] .done)=⟨1,0,0,0,0,0⟩ := by
    unfold primitiveResources
    rfl
  rw [reducedWindowTrialProgram,primitiveResources_seq,reducedPreparedScalarProgram,primitiveResources_seq,
    reducedPhasePrepare_primitive,reducedScalarComputeProgram,primitiveResources_seq,
    primitiveResources_seq,hx,reducedScalarProgram_primitive,reducedFourierProgram_primitive_exact]
  rfl
theorem reducedResetProgram_primitive :
    primitiveResources reducedResetProgram=⟨0,0,0,0,0,1303⟩ := by
  rw [reducedResetProgram,resetRegister_primitiveResources]
  simp [reducedResetWires,reducedPhaseWires]

def reducedSecpWindowPrimitives (Q : Point) (hrQ : order • Q=0) : PrimitiveResources := by
  classical
  exact if hQ : Q=0 then ⟨0,0,0,0,0,0⟩ else
    reducedWindowTrialPrimitives G Q secpGenerator_ne_zero hQ generator_nsmul_eq_zero hrQ

theorem reducedSecpWindowProgram_primitive (Q : Point) (hrQ : order • Q=0) :
    primitiveResources (reducedSecpWindowProgram Q hrQ)=reducedSecpWindowPrimitives Q hrQ := by
  by_cases hQ : Q=0
  · simp only [reducedSecpWindowProgram,reducedSecpWindowPrimitives,dif_pos hQ]
    rfl
  · simp only [reducedSecpWindowProgram,reducedSecpWindowPrimitives,dif_neg hQ]
    exact reducedWindowTrialProgram_primitive _ _ _ _ _ _

def reducedRepeatedWindowPrimitives (Q : Point) (hrQ : order • Q=0) : PrimitiveResources :=
  scalePrimitives 26 ((reducedSecpWindowPrimitives Q hrQ).add ⟨0,0,0,0,0,1303⟩)

theorem reducedSecpWindowRepeatedProgram_primitive (Q : Point) (hrQ : order • Q=0) :
    primitiveResources (reducedSecpWindowRepeatedProgram Q hrQ)=reducedRepeatedWindowPrimitives Q hrQ := by
  rw [reducedSecpWindowRepeatedProgram,repeatWindowProgram_primitive,resetReducedWindowTrial,
    primitiveResources_seq,reducedSecpWindowProgram_primitive,reducedResetProgram_primitive]
  rfl
end
end ShorECDLP.Paper2607_13816
