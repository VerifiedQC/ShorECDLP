import ShorECDLP.Submission.«2607_13816».Window.SignedCoordinate
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.DecoderPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Primitive counts for the measured decoder with ordinary reversible leaves. -/
theorem unaryAction_primitive (order : UnaryOrder) (leaf : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (q : Wire) (path : List Wire) (hl : tree.Layout q path) :
    primitiveResources (unaryAction order leaf tree q path)=
      ⟨tree.leafCostSum (fun l w => (primitiveResources (.unitary (leaf l w) .done)).x) q path+4*tree.internalNodes,
       tree.leafCostSum (fun l w => (primitiveResources (.unitary (leaf l w) .done)).h) q path+2*tree.internalNodes,
       tree.leafCostSum (fun l w => (primitiveResources (.unitary (leaf l w) .done)).cnot) q path+3*tree.internalNodes,
       tree.leafCostSum (fun l w => (primitiveResources (.unitary (leaf l w) .done)).toffoli) q path+tree.internalNodes,
       tree.leafCostSum (fun l w => (primitiveResources (.unitary (leaf l w) .done)).phase) q path,
       tree.leafCostSum (fun l w => (primitiveResources (.unitary (leaf l w) .done)).measurements) q path+tree.internalNodes⟩ := by
  simpa using unaryAdaptiveAction_primitive order (fun l w => .unitary (leaf l w) .done) tree q path hl
private theorem xor_primitive (q : Wire) (ws : List Wire) :
    primitiveResources (.unitary (tableXorGates q ws) .done)=⟨0,0,ws.length,0,0,0⟩ := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp [tableXorGates,primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
      primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount] at *
    omega
/-- Decoder overhead plus the exact number of selected table-word bits. -/
theorem tableLookup_primitive (mask : Nat → List Wire) (tree : UnaryActionTree)
    (q : Wire) (path : List Wire) (hl : tree.Layout q path) :
    primitiveResources (tableLookup mask tree q path)=
      ⟨4*tree.internalNodes,2*tree.internalNodes,
       tree.leafCostSum (fun a _ => (mask a).length) q path+3*tree.internalNodes,
       tree.internalNodes,0,tree.internalNodes⟩ := by
  have h := unaryAction_primitive .inc (fun a w => tableXorGates w (mask a)) tree q path hl
  simp only [xor_primitive] at h
  have hz := unaryActionTree_leafCostSum_const tree q path 0 hl
  simp only [hz,Nat.zero_mul,Nat.zero_add] at h
  exact h

/-- A complete w-bit QROM traversal: exact decoder overhead and table-dependent CX payload. -/
theorem tableLookupProgram_primitive (mask : Nat → List Wire) (bits paths : List Wire)
    (q : Wire) (hl : bits.length≤paths.length) (hn : (q::bits++paths).Nodup) :
    primitiveResources (tableLookupProgram mask bits q paths)=
      ⟨4*(2^bits.length-1),2*(2^bits.length-1),
       (tableAddressTree bits 0 1).leafCostSum (fun a _ => (mask a).length) q paths+3*(2^bits.length-1),
       2^bits.length-1,0,2^bits.length-1⟩ := by
  have h := tableLookup_primitive mask (tableAddressTree bits 0 1) q paths
    (tableAddressTree_layout bits paths q 0 1 hl hn)
  have he : (tableAddressTree bits 0 1).internalNodes=2^bits.length-1 := by
    have hh := tableAddressTree_nodes bits 0 1
    omega
  rw [he] at h
  exact h

/-- Exact QROM vector, including every table-dependent data CX. -/
def lookupWordPrimitives (table : Nat → Nat) (bits paths targets : List Wire) (q : Wire) : PrimitiveResources :=
  ⟨4*(2^bits.length-1),2*(2^bits.length-1),
    (tableAddressTree bits 0 1).leafCostSum (fun a _ => (tableWordMask targets (table a)).length) q paths+
      3*(2^bits.length-1),2^bits.length-1,0,2^bits.length-1⟩
/-- Load/add/clear has two exact QROM vectors around one explicit 256-bit adder vector. -/
theorem lookupModularAdd256_primitive (table : Nat → Nat) (bits paths input acc : List Wire)
    (correction : List Bool) (p : Nat) (q c r t f : Wire)
    (hl : bits.length≤paths.length) (hn : (q::bits++paths).Nodup)
    (hi : input.length=256) (ha : acc.length=256) (hk : correction.length=256) :
    primitiveResources (lookupModularAddProgram table bits paths input acc correction p q c r t f)=
      ((lookupWordPrimitives table bits paths input q).add
        ((⟨516,0,2048,1282,0,0⟩ : PrimitiveResources).add
          ((constantGE256Primitives false p).add (constantAdder256Primitives true correction)))).add
        (lookupWordPrimitives table bits paths input q) := by
  rw [lookupModularAddProgram,primitiveResources_seq,primitiveResources_seq,
    controlledModularAdd256_primitive_exact _ _ _ _ _ _ _ _ _ hi ha hk,
    tableLookupProgram_primitive _ _ _ _ hl hn]
  rfl

noncomputable section
attribute [local irreducible] primitiveResources
/-- Same 256-bit modular-adder vector for either physical coordinate bank. -/
def pointLookupAdderPrimitives : PrimitiveResources :=
  (⟨516,0,2048,1282,0,0⟩ : PrimitiveResources).add
    ((constantGE256Primitives false ShorECDLP.p).add
      (constantAdder256Primitives true secp256k1ReductionConstantBits))
def pointLookupPrimitives (table : Nat → Nat) : PrimitiveResources :=
  let load := lookupWordPrimitives table pointLookupAddress pointLookupPath (List.range' 7 256) 836
  (load.add pointLookupAdderPrimitives).add load

theorem fig14LookupX_primitive (table : Nat → Nat) :
    primitiveResources (fig14LookupX table)=pointLookupPrimitives table := by
  exact lookupModularAdd256_primitive table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 263 256) secp256k1ReductionConstantBits ShorECDLP.p
    836 559 560 561 558 (by decide +kernel) (by decide +kernel) (by simp) (by simp) (by simp [secp256k1ReductionConstantBits])
theorem fig14LookupY_primitive (table : Nat → Nat) :
    primitiveResources (fig14LookupY table)=pointLookupPrimitives table := by
  exact lookupModularAdd256_primitive table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p
    836 559 560 561 558 (by decide +kernel) (by decide +kernel) (by simp) (by simp) (by simp [secp256k1ReductionConstantBits])
private theorem negative_point_primitive :
    primitiveResources (negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558)=⟨3070,4088,12983,3062,0,1022⟩ := by
  have h := controlledModularNegate256_primitive_exact (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558 (by simp) (by simp) (by simp)
  have he : primitiveResources (controlledModularNegate (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558)=⟨3068,4088,12983,3062,0,1022⟩ := by
    rw [h]
    decide +kernel
  have hx : primitiveResources (.unitary [Gate.X 854] .done)=(⟨1,0,0,0,0,0⟩ : PrimitiveResources) := by
    unfold primitiveResources
    rfl
  rw [negativeControlledModularNegate,primitiveResources_seq,primitiveResources_seq,he,hx]
  rfl

def signedPointLookupPrimitives (table : Nat → Nat) : PrimitiveResources :=
  let neg : PrimitiveResources := ⟨3070,4088,12983,3062,0,1022⟩
  (neg.add (pointLookupPrimitives table)).add neg

theorem signedPointLookupY_primitive (table : Nat → Nat) :
    primitiveResources (signedPointLookupY table)=signedPointLookupPrimitives table := by
  rw [signedPointLookupY,signedLookupModularAddProgram]
  simp only [List.length_range',primitiveResources_seq,negative_point_primitive]
  change ((⟨3070,4088,12983,3062,0,1022⟩ : PrimitiveResources).add
    (primitiveResources (fig14LookupY table))).add ⟨3070,4088,12983,3062,0,1022⟩=_
  rw [fig14LookupY_primitive]
  rfl


/-- Exact nine-stage signed coordinate vector, including all five load/clear pairs. -/
def signedCoordinatePrimitives (x y : Nat → Nat) : PrimitiveResources :=
  let a := pointLookupPrimitives (fun k => (ShorECDLP.p-x k)%ShorECDLP.p)
  let b := signedPointLookupPrimitives (fun k => (ShorECDLP.p-y k)%ShorECDLP.p)
  let field : PrimitiveResources := ⟨41769233,30986444,70649616,35152647,0,14707307⟩
  ((((((((a.add b).add field).add ⟨1896393,2091012,5630143,2223879,0,522753⟩).add
    (pointLookupPrimitives (fun k => (3*x k)%ShorECDLP.p))).add field).add
    ⟨3068,4088,12983,3062,0,1022⟩).add (pointLookupPrimitives (fun k => x k%ShorECDLP.p))).add b)

theorem signedLookupCoordinateProgram_primitive (x y : Nat → Nat) :
    primitiveResources (signedLookupCoordinateProgram x y)=signedCoordinatePrimitives x y := by
  rw [signedLookupCoordinateProgram,signedCoordinatePrimitives]
  simp only [primitiveResources_seq,fig14LookupX_primitive,signedPointLookupY_primitive,
    secp256k1ZeroAllowedDivision_primitive_exact,secp256k1ZeroAllowedMultiplication_primitive_exact,
    fig14SquareSubtract_primitive_exact,fig14Negate_primitive_exact]
end
end ShorECDLP.Paper2607_13816
