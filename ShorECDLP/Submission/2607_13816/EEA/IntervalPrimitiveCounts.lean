import ShorECDLP.Submission.«2607_13816».EEA.TraversalPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.EndpointPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.Interval
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Scalar primitive vector for a single paired interval traversal. -/
def intervalTraversalPrimitiveFormula (cell : Nat) (special : Bool)
    (labels : List Nat) (nodes : Nat) : PrimitiveResources :=
  ⟨(labels.map (fun l => if maskedZeroLeaf special l then 4 else 0)).sum+8*nodes,
   2*labels.length+4*nodes,
   (labels.map (fun l => if maskedZeroLeaf special l then 3 else 5)).sum+6*nodes,
   (labels.map (fun l => cell+(if maskedZeroLeaf special l then 2 else 0))).sum+2*nodes,
   0,labels.length+2*nodes⟩
/-- Exact endpoint/decoder/ripple sum; no circuit enumeration occurs in this formula. -/
def intervalPrimitiveFormula9 (r : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) : PrimitiveResources :=
  let endpoint : PrimitiveResources :=
    ⟨10+2*(constantBits 9 4).count true+2*(constantBits 9 (n+2)).count true+
      4*(constantBits 9 k).count true,0,190,104,0,0⟩
  let top := fun cell => if intervalHasTopSpecial k K then
    (⟨8*zeroBitCount (intervalTopRelative k K) 0 9,58,31,34+cell,0,29⟩ : PrimitiveResources)
    else ⟨0,0,0,0,0,0⟩
  endpoint.add ((top (rippleFirstCellToffoliCost mode-1)).add
    ((intervalTraversalPrimitiveFormula (rippleFirstCellToffoliCost mode-1)
      (intervalHasTopSpecial k K) (intervalTree r k K).labels (intervalTree r k K).internalNodes).add
    ((⟨0,0,if signUpdate then 1 else 0,0,0,0⟩ : PrimitiveResources).add
    ((intervalTraversalPrimitiveFormula (rippleSecondCellToffoliCost mode-1)
      (intervalHasTopSpecial k K) (intervalTree r k K).labels (intervalTree r k K).internalNodes).add
    ((top (rippleSecondCellToffoliCost mode-1)).add endpoint)))))

/-- Full six-component count for the actual 9-bit interval schedule. -/
theorem intervalAddSub9_primitive (registers : IntervalRegisters) (n k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    (ht : registers.lengthT.length=9) (hq : registers.lengthQ.length=9)
    (hs : registers.lengthS.length=9)
    (he : 9≤registers.endpointScratch.length)
    (heq : 7≤(registers.equalityScratch k K).length) :
    primitiveResources (intervalAddSub registers n k K mode signUpdate target)=
      intervalPrimitiveFormula9 registers n k K mode signUpdate := by
  change primitiveResources ((Quantum.AdaptiveCircuit.unitary
      (prepareIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
        registers.endpointScratch (registers.carry k K) n k) .done).seq
    (((if intervalHasTopSpecial k K then
    topSpecialFirstLeafAdaptive mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  else .unitary [] .done)).seq
      ((intervalFirstTraversalAdaptive mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.carry k K)
          (registers.cellScratch k K) (registers.targetAt target)
          (registers.addendAt target) (intervalTree registers k K)
          registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K)).seq
        ((Quantum.AdaptiveCircuit.unitary
            (intervalSignUpdate registers k K signUpdate) .done).seq
          ((intervalSecondTraversalAdaptive mode (intervalHasTopSpecial k K)
              (registers.rightTop k K) (registers.leftTop k K)
              (registers.accumulator k K) (registers.carry k K)
              (registers.cellScratch k K) (registers.targetAt target)
              (registers.addendAt target) (intervalTree registers k K)
              registers.control registers.control (registers.rightPaths k K)
              (registers.leftPaths k K)).seq
            (((if intervalHasTopSpecial k K then
    topSpecialSecondLeafAdaptive mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  else .unitary [] .done)).seq
              (Quantum.AdaptiveCircuit.unitary
                (restoreIntervalEndpoints registers.lengthT registers.lengthQ
                  registers.lengthS registers.endpointScratch
                  (registers.carry k K) n k) .done))))))) = _
  simp only [primitiveResources_seq]
  rw [prepareIntervalEndpoints9_primitive _ _ _ _ _ _ _ ht hq hs he,
    restoreIntervalEndpoints9_primitive _ _ _ _ _ _ _ ht hq hs he,
    intervalFirstTraversalAdaptive_primitive _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlayout.traversal.1,
    intervalSecondTraversalAdaptive_primitive _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlayout.traversal.1]
  cases hspecial : intervalHasTopSpecial k K <;> cases signUpdate <;>
    simp only [Bool.false_eq_true,if_false,if_true,
      topSpecialFirstLeafAdaptive9_primitive _ _ _ _ _ _ _ _ _ _ _ _ _ hs hq heq,
      topSpecialSecondLeafAdaptive9_primitive _ _ _ _ _ _ _ _ _ _ _ _ _ hs hq heq]
  all_goals simp [intervalPrimitiveFormula9,intervalTraversalPrimitiveFormula,hspecial,
    intervalSignUpdate,primitiveResources,PrimitiveResources.add,gidneyGateCount,
    gidneyCnotCount,gidneyToffoliCount,primitiveXCost,primitiveHCost,primitivePhaseCost,
    AdaptiveCircuit.measurementCount,Nat.mul_comm]
private theorem primitive_middle_reverse (a b c d e f : PrimitiveResources) :
    a.add (b.add (c.add (d.add (e.add (f.add a))))) =
      a.add (f.add (e.add (d.add (c.add (b.add a))))) := by
  cases a; cases b; cases c; cases d; cases e; cases f
  simp only [PrimitiveResources.add]
  congr 1 <;> omega

/-- Swapping the two ripple passes preserves every aggregate primitive count. -/
theorem intervalPrimitiveFormula9_inverse (r : IntervalRegisters) (n k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) :
    intervalPrimitiveFormula9 r n k K mode.inverse signUpdate =
      intervalPrimitiveFormula9 r n k K mode signUpdate := by
  unfold intervalPrimitiveFormula9
  cases mode <;> exact primitive_middle_reverse _ _ _ _ _ _
/-- The fresh adaptive inverse has the same complete primitive vector. -/
theorem intervalAddSubInverse9_primitive (registers : IntervalRegisters) (n k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target)
    (ht : registers.lengthT.length=9) (hq : registers.lengthQ.length=9)
    (hs : registers.lengthS.length=9)
    (he : 9≤registers.endpointScratch.length)
    (heq : 7≤(registers.equalityScratch k K).length) :
    primitiveResources (intervalAddSubInverse registers n k K mode signUpdate target)=
      intervalPrimitiveFormula9 registers n k K mode signUpdate := by
  rw [intervalAddSubInverse,intervalAddSub9_primitive _ _ _ _ _ _ _ hlayout ht hq hs he heq,
    intervalPrimitiveFormula9_inverse]
end ShorECDLP.Paper2607_13816
