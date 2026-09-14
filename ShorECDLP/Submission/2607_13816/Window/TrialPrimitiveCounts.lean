import ShorECDLP.Submission.«2607_13816».Window.SchedulePrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Window.ExactFourierResources
import ShorECDLP.Submission.«2607_13816».Window.PhysicalRepetition
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
private theorem hadamards_primitive (ws : List Wire) :
    primitiveResources (.unitary (ws.map Gate.H) .done)=⟨0,ws.length,0,0,0,0⟩ := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp [primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
      primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount] at *
    omega

theorem scalarPhasePrepare_primitive :
    primitiveResources (.unitary scalarPhasePrepare .done)=⟨0,514,0,0,0,0⟩ := by
  change primitiveResources (.unitary (scalarPhaseWires.map Gate.H) .done)=_
  rw [hadamards_primitive]
  simp [scalarPhaseWires]

def pointInitializePrimitives (P : ShorECDLP.Secp256k1.Point) : PrimitiveResources :=
  ⟨(constantBits pointLogicalWires.length
    (boolWordToNat (pointCoordinateWord (fig14PointEncoding P)))).count true,0,0,0,0,0⟩
private theorem xor_init (ws : List Wire) (n : Nat) :
    primitiveResources (.unitary (xorConstant ws n) .done)=
      ⟨(constantBits ws.length n).count true,0,0,0,0,0⟩ := by
  rw [primitiveResources_unitary_HPFree _ _ (xorConstant_HPFree _ _),
    xorConstant_xCount,xorConstant_cnotCount,xorConstant_toffoliCount]
  rfl
theorem pointInitialize_primitive (P : ShorECDLP.Secp256k1.Point) :
    primitiveResources (.unitary (pointInitialize P) .done)=pointInitializePrimitives P := by
  exact xor_init _ _

def windowTrialPrimitives (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) : PrimitiveResources :=
  ((⟨0,514,0,0,0,0⟩ : PrimitiveResources).add
    (((⟨1,0,0,0,0,0⟩ : PrimitiveResources).add
      ((pointInitializePrimitives (axisWindowOffset P 17+axisWindowOffset Q 17)).add
        (scalarWindowPrimitives P Q hP hQ hrP hrQ))).add ⟨1,0,0,0,0,0⟩)).add
    ⟨0,0,0,0,65792,514⟩

theorem windowTrialProgram_primitive (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    primitiveResources (windowTrialProgram P Q hP hQ hrP hrQ)=windowTrialPrimitives P Q hP hQ hrP hrQ := by
  have hx : primitiveResources (.unitary [.X 836] .done)=⟨1,0,0,0,0,0⟩ := by
    unfold primitiveResources
    rfl
  rw [windowTrialProgram,primitiveResources_seq,preparedScalarProgram,primitiveResources_seq,
    scalarPhasePrepare_primitive,scalarComputeProgram,primitiveResources_seq,
    primitiveResources_seq,hx,initializedScalarProgram,primitiveResources_seq,
    pointInitialize_primitive,scalarWindowsProgram_primitive,scalarFourierProgram_primitive_exact]
  rfl

private theorem reset_primitive (ws : List Wire) :
    primitiveResources (measureResetWithCorrection ws (fun _ => []))=⟨0,0,0,0,0,ws.length⟩ := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [measureResetWithCorrection,primitiveResources_branch,ih]
    simp [PrimitiveResources.branch,Nat.add_comm]

theorem windowResetProgram_primitive :
    primitiveResources windowResetProgram=⟨0,0,0,0,0,1383⟩ := by
  rw [windowResetProgram,reset_primitive]
  simp [windowResetWires]

def scalePrimitives (n : Nat) (r : PrimitiveResources) : PrimitiveResources :=
  ⟨n*r.x,n*r.h,n*r.cnot,n*r.toffoli,n*r.phase,n*r.measurements⟩
theorem repeatWindowProgram_primitive (a : AdaptiveCircuit) (n : Nat) :
    primitiveResources (repeatWindowProgram a n)=scalePrimitives n (primitiveResources a) := by
  induction n with
  | zero => simp [repeatWindowProgram,scalePrimitives,primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,AdaptiveCircuit.measurementCount]
  | succ n ih =>
    rw [repeatWindowProgram,primitiveResources_seq,ih]
    simp [scalePrimitives,PrimitiveResources.add,Nat.succ_mul,Nat.add_comm]

private theorem generator_nonzero : ShorECDLP.Secp256k1.G≠0 := by
  intro h
  have hg := ShorECDLP.Secp256k1.generator_order
  rw [h,addOrderOf_zero] at hg
  have hp := ShorECDLP.Secp256k1.order_prime.two_le
  omega

noncomputable def secpWindowPrimitives (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) : PrimitiveResources := by
  classical
  exact if hQ : Q=0 then ⟨0,0,0,0,0,0⟩ else
    windowTrialPrimitives ShorECDLP.Secp256k1.G Q generator_nonzero hQ
      ShorECDLP.Secp256k1.generator_nsmul_eq_zero hrQ

theorem secpWindowProgram_primitive (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) :
    primitiveResources (secpWindowProgram Q hrQ)=secpWindowPrimitives Q hrQ := by
  classical
  unfold secpWindowProgram secpWindowPrimitives
  split
  · rfl
  · exact windowTrialProgram_primitive _ _ _ _ _ _

noncomputable def repeatedWindowPrimitives (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) : PrimitiveResources :=
  scalePrimitives 26 ((secpWindowPrimitives Q hrQ).add ⟨0,0,0,0,0,1383⟩)

theorem secpWindowRepeatedProgram_primitive (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) :
    primitiveResources (secpWindowRepeatedProgram Q hrQ)=repeatedWindowPrimitives Q hrQ := by
  rw [secpWindowRepeatedProgram,repeatWindowProgram_primitive,resetWindowTrial,
    primitiveResources_seq,secpWindowProgram_primitive,windowResetProgram_primitive]
  rfl

end
end ShorECDLP.Paper2607_13816
