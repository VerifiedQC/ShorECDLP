import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedPrimitiveCounts
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Every fixed gate slot counts, including disabled constant/record controls. -/
def lookupSlots {n : Nat} : List (LookupOp n) → Nat
  | [] => 0
  | .gates gs :: ops => gs.length + lookupSlots ops
  | .erase _ _ _ :: ops => 3 + lookupSlots ops

theorem recordGates_slots {n s e : Nat} (i : Fin s) (gs : Circuit) (next : Straight n s e) :
    (recordGates i gs next).gateSlots = gs.length + next.gateSlots := by
  induction gs <;> simp_all [recordGates,Straight.gateSlots,Nat.add_assoc,Nat.add_left_comm]

theorem lookupProgram_slots (n : Nat) (ops : List (LookupOp n)) (start : Nat) :
    (lookupProgram n ops start).gateSlots = lookupSlots ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp only [lookupProgram,Straight.gateSlots_append,gateProgram_slots,ih,lookupSlots]
    | erase a b t =>
      simp only [lookupProgram,castFinish_gateSlots,Straight.gateSlots_append,andEraseProgram,
        Straight.gateSlots,recordGates_slots,controlledZ,List.length_cons,List.length_nil,ih,lookupSlots]

theorem lookupSlots_append {n : Nat} (xs ys : List (LookupOp n)) :
    lookupSlots (xs++ys) = lookupSlots xs + lookupSlots ys := by
  induction xs with
  | nil => simp [lookupSlots]
  | cons x xs ih => cases x <;> simp_all [lookupSlots,Nat.add_assoc]

theorem unaryLookupOps_slots_le {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (bound : Nat) (hleaf : ∀ l q, (leaf l q).length ≤ bound)
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) :
    lookupSlots (unaryLookupOps leaf tree q anc) ≤
      bound * (tree.internalNodes+1) + 10*tree.internalNodes := by
  induction tree generalizing q anc with
  | leaf l => simpa [unaryLookupOps,lookupSlots,UnaryActionTree.internalNodes] using hleaf l q
  | node bit zero one ihz iho =>
    cases anc with
    | nil => simp [unaryLookupOps,lookupSlots]
    | cons path rest =>
      have hz := ihz path rest
      have ho := iho path rest
      simp only [unaryLookupOps,lookupSlots_append,lookupSlots,ordinaryOp,List.length_map,
        computeZeroAnd,List.length_cons,List.length_nil,UnaryActionTree.internalNodes,
        Nat.mul_add,Nat.mul_one] at *
      omega

theorem pointLeaf_slots {n : Nat} (row : Fin n) (q : Wire) : (pointLeaf row q).length ≤ 513 := by
  simp only [pointLeaf,lookupLeafGates,List.length_map,List.length_zip]
  apply Nat.min_le_left _ _ |>.trans
  simp only [pointRefs,List.length_append,List.length_ofFn,List.length_cons,List.length_nil]
  decide

theorem actualFirstWindow_slots (start : Nat) :
    (actualFirstWindow.program start).gateSlots ≤ 34275318 := by
  have h := unaryLookupOps_slots_le
    (fun l q => pointLeaf ⟨l % 65536,Nat.mod_lt _ (by decide)⟩ q)
    513 (fun _ q => pointLeaf_slots _ q)
    (tableAddressTree (List.range' 855 16) 0 1) 836 (List.range' 519 16)
  have hn := tableAddressTree_nodes (List.range' 855 16) 0 1
  change (tableAddressTree (List.range' 855 16) 0 1).internalNodes+1 = 65536 at hn
  simpa only [actualFirstWindow,reindexStraight_gateSlots,firstLookupProgram,
    castFinish_gateSlots,lookupProgram_slots,firstLookupOps] using
    (show lookupSlots (unaryLookupOps (fun l q => pointLeaf ⟨l % 65536,Nat.mod_lt _ (by decide)⟩ q)
      (tableAddressTree (List.range' 855 16) 0 1) 836 (List.range' 519 16)) ≤ 34275318 by omega)

/-- For a unitary list the five primitive counters partition its actual gates. -/
theorem circuit_length_primitive (gs : Circuit) :
    gs.length = (primitiveResources (.unitary gs .done)).x +
      (primitiveResources (.unitary gs .done)).h +
      (primitiveResources (.unitary gs .done)).cnot +
      (primitiveResources (.unitary gs .done)).toffoli +
      (primitiveResources (.unitary gs .done)).phase := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
      primitiveXCost,primitiveHCost,primitivePhaseCost] <;> omega

theorem zeroBitCount_bound (value bit width : Nat) : zeroBitCount value bit width ≤ width := by
  induction width generalizing bit with
  | zero => rfl
  | succ width ih =>
    simp only [zeroBitCount]
    have h := ih (bit+1)
    split <;> omega

theorem registerEqualCircuit_length_le (cells : List (Wire × Wire)) (flag : Wire) (scratch : List Wire)
    (hl : cells.length = 513) (hs : 511 ≤ scratch.length) :
    (registerEqualCircuit cells flag scratch).length ≤ 3075 := by
  have hx : (xorWordCircuit cells).length = cells.length := by
    simp only [xorWordCircuit,List.length_map]
  have hc := computeEqConst_primitive (cells.map Prod.snd) 0 flag scratch
    (by simpa only [List.length_map,hl] using hs)
  have hlen := circuit_length_primitive (computeEqConst (cells.map Prod.snd) 0 flag scratch)
  rw [hc] at hlen
  simp only [List.length_map,hl] at hlen
  have hz := zeroBitCount_bound 0 0 513
  simp only [registerEqualCircuit,List.length_append,hx,hl]
  norm_num only [mcxVChainCnotCost,mcxVChainToffoliCost] at hlen
  simp only [ite_false] at hlen
  omega

theorem batchOpCircuit_length_le (base : Wire) (source : Fin 4) (target : Fin 6) :
    (batchOpCircuit base source target).length ≤ 13326 := by
  have he (a t : Fin 513 → Wire) :
      (registerEqualCircuit (equalityCells a t) (batchFlag base) (batchScratch base)).length ≤ 3075 :=
    registerEqualCircuit_length_le _ _ _ (by simp only [equalityCells,List.length_ofFn]) (by simp only [batchScratch,List.length_ofFn]; decide)
  unfold batchOpCircuit endpointTranspositionCircuit endpointTests
  simp only [List.length_append,endpointWordCircuit_length,endpointUpdateCells,List.length_ofFn]
  have ha := he (batchWord base ⟨source.val,by omega⟩) (batchWord base target)
  have hb := he (batchWord base 4) (batchWord base target)
  omega

theorem endpointSelectGates_length_le {n : Nat} (q : Wire) (ports : List (Wire × EndpointBit n)) :
    (endpointSelectGates q ports).length ≤ ports.length := by
  induction ports with
  | nil => rfl
  | cons port ports ih =>
    rcases port with ⟨w,tag⟩
    cases tag with
    | inl b =>
      cases b
      · simp_all [endpointSelectGates,endpointSelectGate]; omega
      · simp_all [endpointSelectGates,endpointSelectGate]
    | inr r => simp_all [endpointSelectGates,endpointSelectGate]

theorem batchLeaf_length_le {n : Nat} (row : Fin n) (base q : Wire) (selection : List (Fin 8 × Fin 5)) :
    (batchLeaf row base q selection).length ≤ 514 * selection.length := by
  have hp : (batchPorts row base selection).length = 513 * selection.length := by
    induction selection with
    | nil => simp only [batchPorts,List.flatMap_nil,List.length_nil,Nat.mul_zero]
    | cons x xs ih =>
      simp only [batchPorts,List.flatMap_cons,List.length_append,List.length_ofFn] at ih ⊢
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
  have he := endpointSelectGates_length_le q (batchPorts row base selection)
  have ht : (batchTags base selection).length ≤ selection.length := by
    simpa only [batchTags,List.length_map] using List.length_filter_le (fun p => endpointTagMask p.1 512) selection
  simp only [batchLeaf,List.length_append,List.length_map]
  omega

def batchSlotBound (nodes : Nat) : List BatchOp → Nat
  | [] => 0
  | .query _ _ :: ops => 2570*(nodes+1)+10*nodes+batchSlotBound nodes ops
  | .swap _ _ :: ops => 13326+batchSlotBound nodes ops

theorem batchOps_slots_le {n : Nat} (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (q : Wire) (paths : List Wire) (ops : List BatchOp) :
    lookupSlots (batchOps rows base tree q paths ops) ≤ batchSlotBound tree.internalNodes ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | query sources target =>
      have hl (l : Nat) (control : Wire) :
          (batchLeaf (rows l) base control (batchSelection sources target)).length ≤ 2570 := by
        have h := batchLeaf_length_le (rows l) base control (batchSelection sources target)
        have hs : (batchSelection sources target).length ≤ 5 := by
          cases sources <;> simp only [batchSelection,Bool.false_eq_true,ite_false,ite_true,
            List.length_append,List.length_cons,List.length_nil] <;> decide
        omega
      have h := unaryLookupOps_slots_le _ 2570 hl tree q paths
      simp only [batchOps,lookupSlots_append,batchSlotBound]
      omega
    | swap source target =>
      have h := batchOpCircuit_length_le base source target
      simp only [batchOps,lookupSlots,ordinaryOp,List.length_map,batchSlotBound]
      omega

theorem relabelStraight_slots {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t) :
    (relabelStraight e p).gateSlots = p.gateSlots := by
  induction p <;> simp_all only [relabelStraight,Straight.gateSlots]

theorem batchSlotBound_schedule (nodes : Nat) :
    batchSlotBound nodes batchSchedule = 14*(2570*(nodes+1)+10*nodes)+16*13326 := by
  simp only [batchSchedule,batchSlotBound]
  omega

theorem placedBatchProgram_slots (w : OddWindow) (start : Nat) :
    (placedBatchProgram w start).2.gateSlots ≤ 1183793236 := by
  simp only [placedBatchProgram,relabelCompiled,relabelStraight_slots,batchedEndpointProgram,
    lookupProgram_slots]
  have h := batchOps_slots_le (batchWindowRows w) 1024 batchWindowTree 836 pointLookupPath batchSchedule
  rw [batchSlotBound_schedule] at h
  have hn := tableAddressTree_nodes pointLookupAddress 0 1
  change batchWindowTree.internalNodes + 1 = 32768 at hn
  omega

end ShorECDLP.Paper2607_13816.ChallengeMigration
