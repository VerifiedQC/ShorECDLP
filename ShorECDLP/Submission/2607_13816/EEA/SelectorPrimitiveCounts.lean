import ShorECDLP.Submission.«2607_13816».EEA.DecoderPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem ccx_primitive (a b c : Wire) (next : AdaptiveCircuit) :
    primitiveResources (.unitary [.CCX a b c] next)=
      (⟨0,0,0,1,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]

private theorem mcxTail_primitive (controls : List Wire) (acc target : Wire) (scratch : List Wire)
    (hne : controls≠[]) (hs : controls.length-1≤scratch.length) :
    primitiveResources (mcxVChainTailAdaptive acc controls target scratch)=
      (⟨0,2*(controls.length-1),controls.length-1,controls.length,0,controls.length-1⟩ : PrimitiveResources) := by
  induction controls generalizing acc scratch with
  | nil => exact (hne rfl).elim
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      cases scratch with
      | nil => simp at hs
      | cons w ws =>
        have ht : (b::rest).length-1≤ws.length := by simp only [List.length_cons] at hs ⊢; omega
        rw [mcxVChainTailAdaptive,ccx_primitive,primitiveResources_seq,ih w ws (by simp) ht,measuredAndErase_primitive]
        simp only [PrimitiveResources.add,List.length_cons]
        congr 1 <;> omega

/-- Exact primitive vector of the emitted measurement-uncomputed v-chain. -/
theorem mcxVChainAdaptive_primitive (controls : List Wire) (target : Wire) (scratch : List Wire)
    (hs : controls.length-2≤scratch.length) :
    primitiveResources (mcxVChainAdaptive controls target scratch)=
      (⟨if controls.length=0 then 1 else 0,2*(controls.length-2),
        (if controls.length=1 then 1 else 0)+(controls.length-2),
        controls.length-1,0,controls.length-2⟩ : PrimitiveResources) := by
  cases controls with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      rw [mcxVChainAdaptive,mcxTail_primitive _ _ _ _ (by simp) (by simp only [List.length_cons] at hs ⊢; omega)]
      have h0 : ¬rest.length+1+1=0 := by omega
      have h1 : ¬rest.length+1+1=1 := by omega
      simp only [List.length_cons,if_neg h0,if_neg h1]
      congr 1
      omega

/-- Number of zero bits in the selected low-width constant slice. -/
def zeroBitCount (value first : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (if value.testBit first then 0 else 1)+zeroBitCount value (first+1) n
private theorem unitary_append_primitive (g h : Circuit) (next : AdaptiveCircuit) :
    primitiveResources (.unitary (g++h) next)=primitiveResources (.unitary g (.unitary h next)) := by
  simp [primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
    AdaptiveCircuit.measurementCount,List.map_append,List.sum_append,Nat.add_assoc]
private theorem unitary_nil_primitive (next : AdaptiveCircuit) :
    primitiveResources (.unitary [] next)=primitiveResources next := by
  simp [primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,AdaptiveCircuit.measurementCount]
private theorem unitary_x_primitive (w : Wire) (next : AdaptiveCircuit) :
    primitiveResources (.unitary [.X w] next)=
      (⟨1,0,0,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  simp [primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
    AdaptiveCircuit.measurementCount,PrimitiveResources.add,primitiveXCost,primitiveHCost,primitivePhaseCost]
private theorem zeroMaskFrom_primitive (register : List Wire) (value first : Nat) (next : AdaptiveCircuit) :
    primitiveResources (.unitary (zeroMaskFrom register value first) next)=
      (⟨zeroBitCount value first register.length,0,0,0,0,0⟩ : PrimitiveResources).add
        (primitiveResources next) := by
  induction register generalizing first with
  | nil => simp [zeroMaskFrom,unitary_nil_primitive,zeroBitCount,PrimitiveResources.add]
  | cons w ws ih =>
    rw [zeroMaskFrom,unitary_append_primitive]
    split <;> simp only [unitary_nil_primitive,unitary_x_primitive,ih,List.length_cons,zeroBitCount]
    all_goals simp_all [PrimitiveResources.add,Nat.add_assoc]

/-- Exact equality-compute vector, with the actual constant's two X-mask passes. -/
theorem computeEqConstAdaptive_primitive (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) (hs : register.length-2≤scratch.length) :
    primitiveResources (computeEqConstAdaptive register value flag scratch)=
      (⟨2*zeroBitCount value 0 register.length+(if register.length=0 then 1 else 0),
        2*(register.length-2),(if register.length=1 then 1 else 0)+(register.length-2),
        register.length-1,0,register.length-2⟩ : PrimitiveResources) := by
  have hdone : primitiveResources .done=(⟨0,0,0,0,0,0⟩ : PrimitiveResources) := rfl
  rw [computeEqConstAdaptive,zeroMask,zeroMaskFrom_primitive,primitiveResources_seq,
    mcxVChainAdaptive_primitive _ _ _ hs,zeroMaskFrom_primitive,hdone]
  simp only [PrimitiveResources.add]
  congr 1 <;> omega

/-- The controlled equality selector counts both measured equality computations. -/
theorem toggleEqConstUnderControlAdaptive_primitive (q : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) (hs : register.length-2≤scratch.length) :
    primitiveResources (toggleEqConstUnderControlAdaptive q register value acc flag scratch)=
      (⟨2*(2*zeroBitCount value 0 register.length+(if register.length=0 then 1 else 0)),
        4*(register.length-2),2*((if register.length=1 then 1 else 0)+(register.length-2)),
        2*(register.length-1)+1,0,2*(register.length-2)⟩ : PrimitiveResources) := by
  rw [toggleEqConstUnderControlAdaptive,primitiveResources_seq,ccx_primitive,
    computeEqConstAdaptive_primitive _ _ _ _ hs]
  simp only [PrimitiveResources.add]
  congr 1 <;> omega
end ShorECDLP.Paper2607_13816
