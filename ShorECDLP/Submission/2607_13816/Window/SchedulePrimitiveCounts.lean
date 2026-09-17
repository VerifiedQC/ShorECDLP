import ShorECDLP.Submission.«2607_13816».Window.PointLookupPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Window.ScalarWindows
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
private theorem xor_primitive (q : Wire) (ws : List Wire) :
    primitiveResources (.unitary (tableXorGates q ws) .done)=⟨0,0,ws.length,0,0,0⟩ := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp [tableXorGates,primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
      primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount] at *
    omega
attribute [local irreducible] primitiveResources
private theorem prepare_primitive (j : Nat) :
    primitiveResources (.unitary (windowPrepareCircuit j) .done)=⟨0,0,30,0,0,0⟩ := by
  rw [windowPrepareCircuit,signedAddressCircuit,primitiveResources_unitary_append,xor_primitive,xor_primitive]
  simp only [windowAddressBits,List.length_range',PrimitiveResources.add]

def preparedCallPrimitives (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) : PrimitiveResources :=
  ((⟨0,0,30,0,0,0⟩ : PrimitiveResources).add (signedPointPrimitives x y hc)).add ⟨0,0,30,0,0,0⟩

theorem preparedWindowCall_primitive (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (j : Nat) :
    primitiveResources (preparedWindowCall x y hc j)=preparedCallPrimitives (x j) (y j) (hc j) := by
  rw [preparedWindowCall,primitiveResources_seq,primitiveResources_seq,prepare_primitive,
    windowCall,parkedWindowProgram,primitiveResources_relabel,signedLookupPointProgram_primitive]
  rfl

def preparedSchedulePrimitives (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) : Nat → Nat → PrimitiveResources
  | 0, _ => ⟨0,0,0,0,0,0⟩
  | n+1, j => (preparedCallPrimitives (x j) (y j) (hc j)).add (preparedSchedulePrimitives x y hc n (j+1))

theorem preparedWindowSchedule_primitive (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    primitiveResources (preparedWindowSchedule x y hc n j)=preparedSchedulePrimitives x y hc n j := by
  induction n generalizing j with
  | zero => unfold preparedWindowSchedule preparedSchedulePrimitives primitiveResources; rfl
  | succ n ih =>
    rw [preparedWindowSchedule,primitiveResources_seq,preparedWindowCall_primitive,ih]
    rfl

def scalarWindowPrimitives (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) : PrimitiveResources :=
  (preparedSchedulePrimitives (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
    (fun k => oddWindowTable_valid P hP hrP (k-0)) 17 0).add
  (preparedSchedulePrimitives (fun k => oddWindowX Q (k-17)) (fun k => oddWindowY Q (k-17))
    (fun k => oddWindowTable_valid Q hQ hrQ (k-17)) 17 17)

theorem scalarWindowsProgram_primitive (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    primitiveResources (scalarWindowsProgram P Q hP hQ hrP hrQ)=scalarWindowPrimitives P Q hP hQ hrP hrQ := by
  rw [scalarWindowsProgram,primitiveResources_seq]
  simp only [axisWindowProgram,preparedWindowSchedule_primitive]
  rfl

end
end ShorECDLP.Paper2607_13816
