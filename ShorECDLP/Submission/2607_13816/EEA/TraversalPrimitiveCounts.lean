import ShorECDLP.Submission.«2607_13816».EEA.RipplePrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- When leaf cost is independent of its temporary controls, the layout exposes a sum over labels. -/
theorem DualUnaryActionTree.leafCostSum_labels (tree : DualUnaryActionTree)
    (a b : Wire) (pa pb : List Wire) (hl : tree.Layout a b pa pb)
    (cost : Nat → Nat) :
    tree.leafCostSum (fun l _ _ => cost l) a b pa pb = (tree.labels.map cost).sum := by
  induction hl with
  | leaf => simp [leafCostSum,labels]
  | node ia ib ca cb pathA pathB zero one restA restB hlocal hzero hone ihZero ihOne =>
    simp [leafCostSum,labels,ihZero,ihOne]

/-- Exact first-pass primitive costs, expressed only in mode, labels and tree size. -/
theorem intervalFirstTraversalAdaptive_primitive (mode : RippleMode) (special : Bool)
    (rt lt acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (a b : Wire) (pa pb : List Wire)
    (hl : tree.Layout a b pa pb) :
    primitiveResources (intervalFirstTraversalAdaptive mode special rt lt acc carry scratch
      targetAt addendAt tree a b pa pb) =
      ⟨(tree.labels.map (fun l => if maskedZeroLeaf special l then 4 else 0)).sum + 8*tree.internalNodes,
       (tree.labels.map (fun _ => 2)).sum + 4*tree.internalNodes,
       (tree.labels.map (fun l => if maskedZeroLeaf special l then 3 else 5)).sum + 6*tree.internalNodes,
       (tree.labels.map (fun l => rippleFirstCellToffoliCost mode-1+
         (if maskedZeroLeaf special l then 2 else 0))).sum + 2*tree.internalNodes,
       0,(tree.labels.map (fun _ => 1)).sum + 2*tree.internalNodes⟩ := by
  rw [intervalFirstTraversalAdaptive,dualUnaryAdaptiveAction_primitive _ _ _ _ _ _ _ hl]
  simp only [intervalFirstLeafAdaptive_primitive,
    DualUnaryActionTree.leafCostSum_labels tree a b pa pb hl]
  simp

/-- Exact reverse-pass primitive costs for the actual adaptive ripple cells. -/
theorem intervalSecondTraversalAdaptive_primitive (mode : RippleMode) (special : Bool)
    (rt lt acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (a b : Wire) (pa pb : List Wire)
    (hl : tree.Layout a b pa pb) :
    primitiveResources (intervalSecondTraversalAdaptive mode special rt lt acc carry scratch
      targetAt addendAt tree a b pa pb) =
      ⟨(tree.labels.map (fun l => if maskedZeroLeaf special l then 4 else 0)).sum + 8*tree.internalNodes,
       (tree.labels.map (fun _ => 2)).sum + 4*tree.internalNodes,
       (tree.labels.map (fun l => if maskedZeroLeaf special l then 3 else 5)).sum + 6*tree.internalNodes,
       (tree.labels.map (fun l => rippleSecondCellToffoliCost mode-1+
         (if maskedZeroLeaf special l then 2 else 0))).sum + 2*tree.internalNodes,
       0,(tree.labels.map (fun _ => 1)).sum + 2*tree.internalNodes⟩ := by
  rw [intervalSecondTraversalAdaptive,dualUnaryAdaptiveAction_primitive _ _ _ _ _ _ _ hl]
  simp only [intervalSecondLeafAdaptive_primitive,
    DualUnaryActionTree.leafCostSum_labels tree a b pa pb hl]
  simp
end ShorECDLP.Paper2607_13816
