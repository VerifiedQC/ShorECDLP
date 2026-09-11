import ShorECDLP.Submission.«2607_13816».Arithmetic.PrimitiveResources
import ShorECDLP.Submission.«2607_13816».EEA.DualUnaryAction
namespace ShorECDLP.Paper2607_13816
open Quantum

/-- One measured path-AND erasure: the nontrivial branch applies H-CNOT-H. -/
theorem measuredAndErase_primitive (a b c : Wire) :
    primitiveResources (measuredAndErase a b c)=(⟨0,2,1,0,0,1⟩ : PrimitiveResources) := by
  rfl

theorem eraseZeroAnd_primitive (a b c : Wire) :
    primitiveResources (eraseZeroAnd a b c)=(⟨2,2,1,0,0,1⟩ : PrimitiveResources) := by
  rfl

private theorem compute_primitive (a b c : Wire) (next : AdaptiveCircuit) :
    primitiveResources (.unitary (computeZeroAnd a b c) next)=
      (⟨2,0,0,1,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  simp [computeZeroAnd,primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]
private theorem cx_primitive (a b : Wire) (next : AdaptiveCircuit) :
    primitiveResources (.unitary [.CX a b] next)=
      (⟨0,0,1,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]

/-- Exact six-component decoder overhead, separate from actual adaptive leaf costs. -/
theorem unaryAdaptiveAction_primitive (order : UnaryOrder) (leaf : Nat → Wire → AdaptiveCircuit)
    (tree : UnaryActionTree) (q : Wire) (path : List Wire) (hl : tree.Layout q path) :
    primitiveResources (unaryAdaptiveAction order leaf tree q path)=
      ⟨tree.leafCostSum (fun l w => (primitiveResources (leaf l w)).x) q path + 4*tree.internalNodes,
       tree.leafCostSum (fun l w => (primitiveResources (leaf l w)).h) q path + 2*tree.internalNodes,
       tree.leafCostSum (fun l w => (primitiveResources (leaf l w)).cnot) q path + 3*tree.internalNodes,
       tree.leafCostSum (fun l w => (primitiveResources (leaf l w)).toffoli) q path + tree.internalNodes,
       tree.leafCostSum (fun l w => (primitiveResources (leaf l w)).phase) q path,
       tree.leafCostSum (fun l w => (primitiveResources (leaf l w)).measurements) q path + tree.internalNodes⟩ := by
  induction hl with
  | leaf label control ancillas hlocal => simp [unaryAdaptiveAction,UnaryActionTree.leafCostSum,UnaryActionTree.internalNodes]
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
    cases order <;>
      simp only [unaryAdaptiveAction,compute_primitive,cx_primitive,primitiveResources_seq,
        eraseZeroAnd_primitive,ihZero,ihOne,UnaryActionTree.leafCostSum,UnaryActionTree.internalNodes,
        PrimitiveResources.add]
    all_goals congr 1 <;> omega

private theorem two_cx_primitive (a b c d : Wire) (next : AdaptiveCircuit) :
    primitiveResources (.unitary [.CX a b,.CX c d] next)=
      (⟨0,0,2,0,0,0⟩ : PrimitiveResources).add (primitiveResources next) := by
  simp [primitiveResources,PrimitiveResources.add,gidneyGateCount,gidneyCnotCount,
    gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,AdaptiveCircuit.measurementCount]

/-- Paired decoder cleanup is two independent path erasures. -/
theorem eraseDualZeroAnd_primitive (a b c d e f : Wire) :
    primitiveResources (eraseDualZeroAnd a b c d e f)=(⟨4,4,2,0,0,2⟩ : PrimitiveResources) := by
  rw [eraseDualZeroAnd,primitiveResources_seq,eraseZeroAnd_primitive,eraseZeroAnd_primitive]
  rfl

/-- Exact overhead for the paired decoder, leaving actual leaf programs explicit. -/
theorem dualUnaryAdaptiveAction_primitive (order : UnaryOrder) (leaf : Nat → Wire → Wire → AdaptiveCircuit)
    (tree : DualUnaryActionTree) (a b : Wire) (pa pb : List Wire) (hl : tree.Layout a b pa pb) :
    primitiveResources (dualUnaryAdaptiveAction order leaf tree a b pa pb)=
      ⟨tree.leafCostSum (fun l x y => (primitiveResources (leaf l x y)).x) a b pa pb + 8*tree.internalNodes,
       tree.leafCostSum (fun l x y => (primitiveResources (leaf l x y)).h) a b pa pb + 4*tree.internalNodes,
       tree.leafCostSum (fun l x y => (primitiveResources (leaf l x y)).cnot) a b pa pb + 6*tree.internalNodes,
       tree.leafCostSum (fun l x y => (primitiveResources (leaf l x y)).toffoli) a b pa pb + 2*tree.internalNodes,
       tree.leafCostSum (fun l x y => (primitiveResources (leaf l x y)).phase) a b pa pb,
       tree.leafCostSum (fun l x y => (primitiveResources (leaf l x y)).measurements) a b pa pb + 2*tree.internalNodes⟩ := by
  induction hl with
  | leaf => simp [dualUnaryAdaptiveAction,DualUnaryActionTree.leafCostSum,DualUnaryActionTree.internalNodes]
  | node ia ib ca cb pathA pathB zero one restA restB hlocal hzero hone ihZero ihOne =>
    cases order <;>
      simp only [dualUnaryAdaptiveAction,compute_primitive,two_cx_primitive,primitiveResources_seq,
        eraseDualZeroAnd_primitive,ihZero,ihOne,DualUnaryActionTree.leafCostSum,DualUnaryActionTree.internalNodes,
        PrimitiveResources.add]
    all_goals congr 1 <;> omega

end ShorECDLP.Paper2607_13816
