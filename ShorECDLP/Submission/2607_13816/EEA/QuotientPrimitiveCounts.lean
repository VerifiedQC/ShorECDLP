import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.QuotientSwap
import ShorECDLP.Submission.«2607_13816».EEA.EndIteration
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Coherent decoder X overhead is the two complete negative-control masks per node. -/
theorem unaryActionUnitary_xCount (order : UnaryOrder) (leaf : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (q : Wire) (path : List Wire) (hl : tree.Layout q path) :
    eeaXCount (unaryActionUnitary order leaf tree q path)=
      tree.leafCostSum (fun l w => eeaXCount (leaf l w)) q path+4*tree.internalNodes := by
  induction hl with
  | leaf label control ancillas hlocal => simp [unaryActionUnitary,UnaryActionTree.leafCostSum,UnaryActionTree.internalNodes]
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
    have hx : eeaXCount (computeZeroAnd control indexBit path)=2 := rfl
    have hc : eeaXCount [.CX control path]=0 := rfl
    cases order <;>
      simp only [unaryActionUnitary,eeaXCount_append,ihZero,ihOne,hx,hc,
        UnaryActionTree.leafCostSum,UnaryActionTree.internalNodes]
    all_goals omega

/-- Exact primitive vector of the coherent quotient/sign selection block. -/
theorem quotientSwapUnitary9_primitive (r : QuotientSwapRegisters) {k K : Nat}
    (hl : QuotientSwapLayout r k K) (hn : r.lengthT.length=9) :
    primitiveResources (.unitary (quotientSwapUnitary r k K) .done)=
      (⟨8+4*(quotientSwapTree r k K).internalNodes,0,
        144+2*(quotientSwapTree r k K).leaves+2*(quotientSwapTree r k K).internalNodes,
        72+(quotientSwapTree r k K).leaves+2*(quotientSwapTree r k K).internalNodes,0,0⟩ : PrimitiveResources) := by
  have hc := quotientSwap_constantScratch_length r hl
  have hq : r.lengthQ.length=9 := hl.lengthT_eq_lengthQ.symm.trans hn
  have hleaf : (quotientSwapTree r k K).leafCostSum
      (fun l w => eeaXCount (quotientSwapLeaf r k l w)) r.control (r.path k K)=0 := by
    simpa [quotientSwapLeaf,controlledSwap_xCount] using
      unaryActionTree_leafCostSum_const (quotientSwapTree r k K) r.control (r.path k K) 0 hl.tree
  have hx : eeaXCount (quotientSwapUnitary r k K)=8+4*(quotientSwapTree r k K).internalNodes := by
    simp only [quotientSwapUnitary,eeaXCount_append,endIteration_cuccaroAdd_xCount,
      endIteration_cuccaroSub_xCount,endIteration_addConstant_xCount,endIteration_subConstant_xCount]
    rw [unaryActionUnitary_xCount _ _ _ _ _ hl.tree,hleaf,hc,hq]
    have hb : (constantBits 9 3).count true=2 := by decide
    rw [hb]
    omega
  rw [primitiveResources_unitary_HPFree _ _ (quotientSwapUnitary_HPFree r k K),hx,
    quotientSwapUnitary_cnotCount r hl,quotientSwapUnitary_toffoliCount r hl,hn]
  rfl
end ShorECDLP.Paper2607_13816
