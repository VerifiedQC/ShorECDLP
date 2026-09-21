import ShorECDLP.Submission.«2607_13816».Window.RawSupport
import ShorECDLP.Submission.«2607_13816».Window.ReducedPrimitives
import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlacePrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] primitiveResources reducedRawFourierProgram reducedRawProgram
  reducedFourierProgram signedRawProgram rawWindowSchedule preparedRawProgram rawTrialResetWires rawTrialReset resetRawTrial preparedRawTrial
/-- Actual five-query core, with raw field operations and no exceptional repair. -/
def signedRawPrimitives (x y : Nat → Nat) : PrimitiveResources :=
  let a := pointLookupPrimitives (fun k => (ShorECDLP.p-x k)%ShorECDLP.p)
  let b := signedPointLookupPrimitives (fun k => (ShorECDLP.p-y k)%ShorECDLP.p)
  let field : PrimitiveResources := ⟨41768209,24259500,67286142,38515101,0,11343835⟩
  ((((((((a.add b).add field).add ⟨1896393,2091012,5630143,2223879,0,522753⟩).add
    (pointLookupPrimitives (fun k => (3*x k)%ShorECDLP.p))).add field).add
    ⟨3068,4088,12983,3062,0,1022⟩).add (pointLookupPrimitives (fun k => x k%ShorECDLP.p))).add b)
theorem signedRawProgram_primitive (x y : Nat → Nat) :
    primitiveResources (signedRawProgram x y)=signedRawPrimitives x y := by
  rw [signedRawProgram,signedRawPrimitives]
  simp only [primitiveResources_seq,fig14LookupX_primitive,signedPointLookupY_primitive,
    secp256k1InPlaceDivision_primitive_exact,secp256k1InPlaceMultiplication_primitive_exact,
    fig14SquareSubtract_primitive_exact,fig14Negate_primitive_exact]

def preparedRawPrimitives (x y : Nat → Nat) : PrimitiveResources :=
  ((⟨0,0,30,0,0,0⟩ : PrimitiveResources).add (signedRawPrimitives x y)).add ⟨0,0,30,0,0,0⟩
theorem preparedRawProgram_primitive (x y : Nat → Nat → Nat) (j : Nat) :
    primitiveResources (preparedRawProgram x y j)=preparedRawPrimitives (x j) (y j) := by
  rw [preparedRawProgram,primitiveResources_seq,primitiveResources_seq,
    windowPrepareCircuit_primitive,parkedRawProgram,primitiveResources_relabel,signedRawProgram_primitive]
  rfl

def rawSchedulePrimitives (x y : Nat → Nat → Nat) : List Nat → PrimitiveResources
  | [] => ⟨0,0,0,0,0,0⟩
  | j::js => (preparedRawPrimitives (x j) (y j)).add (rawSchedulePrimitives x y js)
theorem rawWindowSchedule_primitive (x y : Nat → Nat → Nat) (js : List Nat) :
    primitiveResources (rawWindowSchedule x y js)=rawSchedulePrimitives x y js := by
  induction js with
  | nil => unfold primitiveResources rawWindowSchedule rawSchedulePrimitives; rfl
  | cons j js ih => rw [rawWindowSchedule,primitiveResources_seq,preparedRawProgram_primitive,ih]; rfl

def reducedRawPrimitives (P Q : Point) : PrimitiveResources :=
  (physicalPointLookupPrimitives (firstWindowTable (axisWindowOffset P 16+axisWindowOffset Q 13) P)).add
    (rawSchedulePrimitives (fun j a => (reducedRawX P Q j a).val)
      (fun j a => (reducedRawY P Q j a).val) reducedRawIndices)
theorem reducedRawProgram_primitive (P Q : Point) :
    primitiveResources (reducedRawProgram P Q)=reducedRawPrimitives P Q := by
  rw [reducedRawProgram,initializedRawProgram,primitiveResources_seq,
    physicalPointLookup_primitive,rawWindowSchedule_primitive]
  rfl

def preparedRawTrialPrimitives (Q : Point) : PrimitiveResources :=
  (⟨1,464,0,0,0,0⟩ : PrimitiveResources).add
    ((reducedRawPrimitives G Q).add ⟨0,0,0,0,54168,464⟩)
private theorem unitary_resources (g : Circuit) (a : AdaptiveCircuit) :
    primitiveResources (.unitary g a)=
      (primitiveResources (.unitary g .done)).add (primitiveResources a) :=
  primitiveResources_seq (.unitary g .done) a
private theorem prepare_add (r : PrimitiveResources) :
    (⟨0,464,0,0,0,0⟩ : PrimitiveResources).add
      ((⟨1,0,0,0,0,0⟩ : PrimitiveResources).add (r.add ⟨0,0,0,0,54168,464⟩))=
    (⟨1,464,0,0,0,0⟩ : PrimitiveResources).add (r.add ⟨0,0,0,0,54168,464⟩) := by
  simp only [PrimitiveResources.add,Nat.zero_add,Nat.add_zero]
attribute [local irreducible] reducedRawPrimitives
theorem preparedRawTrial_primitive (Q : Point) :
    primitiveResources (preparedRawTrial Q)=preparedRawTrialPrimitives Q := by
  have hx : primitiveResources (.unitary [.X 836] .done)=⟨1,0,0,0,0,0⟩ := by
    unfold primitiveResources; rfl
  rw [preparedRawTrial,unitary_resources reducedPhasePrepare,
    unitary_resources [.X 836] (reducedRawFourierProgram G Q),reducedPhasePrepare_primitive,hx,
    reducedRawFourierProgram,primitiveResources_seq,reducedRawProgram_primitive,
    reducedFourierProgram_primitive_exact]
  exact prepare_add (reducedRawPrimitives G Q)

def rawRepeatedPrimitives (Q : Point) : PrimitiveResources :=
  scalePrimitives 56 ((preparedRawTrialPrimitives Q).add ⟨0,0,0,0,0,(rawTrialResetWires Q).length⟩)
/-- Exact componentwise worst-branch vector of the same full 56-round program as success. -/
theorem rawRepeatedProgram_primitive (Q : Point) :
    primitiveResources (rawRepeatedProgram Q)=rawRepeatedPrimitives Q := by
  rw [rawRepeatedProgram,repeatWindowProgram_primitive,resetRawTrial,primitiveResources_seq,
    preparedRawTrial_primitive,rawTrialReset,resetRegister_primitiveResources]
  rfl
end
end ShorECDLP.Paper2607_13816
