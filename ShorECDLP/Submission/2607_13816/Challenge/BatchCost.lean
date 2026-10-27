import ShorECDLP.Submission.«2607_13816».Challenge.BatchExecution
import ShorECDLP.Submission.«2607_13816».Challenge.BatchPlacement
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

theorem xorWordCircuit_tCount (cells : List (Wire × Wire)) : ShorECDLP.tCount (xorWordCircuit cells) = 0 := by
  induction cells with
  | nil => rfl
  | cons p ps ih => simpa [xorWordCircuit,tCount,tCost] using ih

theorem registerEqualCircuit_tCount (cells : List (Wire × Wire)) (flag : Wire) (scratch : List Wire)
    (h : cells.length-2 ≤ scratch.length) :
    ShorECDLP.tCount (registerEqualCircuit cells flag scratch) = 7*mcxVChainToffoliCost cells.length := by
  simp only [registerEqualCircuit,tCount_append,xorWordCircuit_tCount,zero_add,add_zero]
  rw [computeEqConst_tCount _ _ _ _ (by simpa using h)]
  simp

theorem batchOpCircuit_tCount (base : Wire) (source : Fin 4) (target : Fin 6) :
    ShorECDLP.tCount (batchOpCircuit base source target) = 35826 := by
  have he (a t : Fin 513 → Wire) :
      ShorECDLP.tCount (registerEqualCircuit (equalityCells a t) (batchFlag base) (batchScratch base)) =
        7 * mcxVChainToffoliCost 513 := by
    have h := registerEqualCircuit_tCount (equalityCells a t) (batchFlag base) (batchScratch base)
      (by simp only [equalityCells,batchScratch,List.length_ofFn]; decide)
    simpa only [equalityCells,List.length_ofFn] using h
  unfold batchOpCircuit endpointTranspositionCircuit endpointTests
  simp only [tCount_append,he,endpointWordCircuit_tCount,endpointUpdateCells,List.length_ofFn]
  rfl

theorem batchQuery_tCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (selection : List (Fin 8 × Fin 5))
    (hl : tree.Layout control paths) :
    (unaryAction .inc (fun l q => batchLeafCircuit read (rows l) base q selection)
      tree control paths).tCount = 7 * tree.internalNodes := by
  rw [unaryAction_tCount _ _ _ _ _ hl]
  have hz (t : UnaryActionTree) (q : Wire) (ws : List Wire) :
      t.leafCostSum (fun l wire => ShorECDLP.tCount (batchLeafCircuit read (rows l) base wire selection)) q ws = 0 := by
    induction t generalizing q ws with
    | leaf l => simp [UnaryActionTree.leafCostSum,batchLeafCircuit,tCount_append]
    | node bit zero one ihz iho =>
      cases ws <;> simp only [UnaryActionTree.leafCostSum,ihz,iho,zero_add]
  rw [hz,zero_add]

def batchCost (nodes : Nat) : List BatchOp → Nat
  | [] => 0
  | .query _ _ :: ops => 7*nodes + batchCost nodes ops
  | .swap _ _ :: ops => 35826 + batchCost nodes ops

private theorem batch_tCount_seq (a b : AdaptiveCircuit) :
    (a.seq b).tCount = a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b

theorem batchSource_tCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths) (ops : List BatchOp) :
    (batchSource read rows base tree control paths ops).tCount = batchCost tree.internalNodes ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | query sources target =>
      simp only [batchSource,batch_tCount_seq,batchQuery_tCount _ _ _ _ _ _ _ hl,ih,batchCost]
    | swap source target =>
      simp only [batchSource,AdaptiveCircuit.tCount,batchOpCircuit_tCount,ih,batchCost]

theorem batchSchedule_cost (nodes : Nat) : batchCost nodes batchSchedule = 98*nodes+573216 := by
  simp only [batchSchedule,batchCost]
  omega

theorem placedBatchSource_tCount (Q : Point) (w : OddWindow) :
    (placedBatchSource Q w).tCount = 3784382 := by
  rw [placedBatchSource,AdaptiveCircuit.relabel_tCount,
    batchSource_tCount _ _ _ _ _ _ batchWindowTree_layout,batchSchedule_cost]
  have h := tableAddressTree_nodes pointLookupAddress 0 1
  change batchWindowTree.internalNodes + 1 = 32768 at h
  omega
end ShorECDLP.Paper2607_13816.ChallengeMigration
