import ShorECDLP.Submission.«2607_13816».Challenge.MeasurementBridge
import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Window.LookupPrimitiveCounts
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] sharedCoordinateProgram yNegateProgram placedBatchProgram
  batchedWindowCore batchedWindowPrepared signedLookupCoordinateProgram primitiveResources
  sharedYNegateProgram actualBatchedWindow actualLeftWindows actualRightWindows
  placedBatchSource windowYNegate sequenceCircuit batchedWindowSources

private theorem adder_counts : pointLookupAdderPrimitives.toffoli=2813 ∧
    pointLookupAdderPrimitives.phase=0 ∧ pointLookupAdderPrimitives.measurements=511 := by
  decide +kernel
private theorem lookup_counts (table : Nat → Nat) :
    (pointLookupPrimitives table).toffoli=68347 ∧
    (pointLookupPrimitives table).phase=0 ∧ (pointLookupPrimitives table).measurements=66045 := by
  simp only [pointLookupPrimitives,lookupWordPrimitives,pointLookupAddress,List.length_range',
    PrimitiveResources.add,adder_counts.1,adder_counts.2.1,adder_counts.2.2]
  decide

/-- Source coordinate arithmetic includes both zero-allowed field operations. -/
theorem coordinate_numeric_counts (x y : Nat → Nat) :
    (signedLookupCoordinateProgram x y).tCount = 510203526 ∧
    (signedLookupCoordinateProgram x y).measurementCount = 30272702 := by
  have h : (primitiveResources (signedLookupCoordinateProgram x y)).toffoli = 72886218 ∧
      (primitiveResources (signedLookupCoordinateProgram x y)).phase = 0 ∧
      (primitiveResources (signedLookupCoordinateProgram x y)).measurements = 30272702 := by
    rw [signedLookupCoordinateProgram_primitive]
    simp only [signedCoordinatePrimitives,signedPointLookupPrimitives,PrimitiveResources.add,
      (lookup_counts _).1,(lookup_counts _).2.1,(lookup_counts _).2.2]
    decide
  have ht := primitiveResources_T_of_no_phase _ h.2.1
  rw [h.1] at ht
  exact ⟨ht,by simpa only [primitiveResources] using h.2.2⟩

/-- One actual sign-negation segment, including its two X wrappers. -/
theorem windowYNegate_numeric_counts :
    windowYNegate.tCount = 21434 ∧ windowYNegate.measurementCount = 1022 := by
  have h := controlledModularNegate256_primitive_exact (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558 (by simp) (by simp) (by simp)
  have he : primitiveResources (controlledModularNegate (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558)=⟨3068,4088,12983,3062,0,1022⟩ := by
    rw [h]
    decide +kernel
  have ht := primitiveResources_T_of_no_phase _ (congrArg PrimitiveResources.phase he)
  rw [he] at ht
  have hm := congrArg PrimitiveResources.measurements he
  have hn := negativeControlledModularNegate_resources (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558
  unfold windowYNegate
  rw [hn.1,hn.2]
  constructor
  · exact ht
  · simpa only [primitiveResources] using hm

theorem sharedCoordinateProgram_count (w : OddWindow) (start : Nat) :
    (sharedCoordinateProgram w start).1 = 30272702 := by
  have h := compiled_count_of_run (sharedCoordinateProgram w start)
    (readConstant coefficientAt (0 : Point)) (fun _ => false) _
    (sharedCoordinateProgram_run w start 0 (by simp) (fun _ => false))
  exact h.trans (coordinate_numeric_counts _ _).2

theorem sharedYNegateProgram_count (w : OddWindow) (start : Nat) :
    (sharedYNegateProgram w start).1 = 1022 := by
  exact (compiled_count_of_run _ (fun _ => false) (fun _ => false) _
    (sharedYNegateProgram_run w start (fun _ => false) (fun _ => false))).trans
    windowYNegate_numeric_counts.2

theorem placedBatchProgram_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (placedBatchProgram w start) (readConstant coefficientAt Q) history =
      (placedBatchSource Q w).tCount := by
  simp only [placedBatchProgram,relabelCompiled,compiledTCount,relabelStraight_instantiate,
    AdaptiveCircuit.relabel_tCount,batchedEndpointProgram,lookupProgram_tCount,batchOps_source,
    placedBatchSource]

theorem sharedYNegateProgram_tCount (w : OddWindow) (start : Nat)
    (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    compiledTCount (sharedYNegateProgram w start) read history = windowYNegate.tCount := by
  simp only [sharedYNegateProgram,reindexCompiled,compiledTCount,reindexStraight_instantiate]
  unfold windowYNegate
  exact yNegateProgram_tCount start _ history

theorem batchedWindowCore_tCount (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledTCount (batchedWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (batchedWindowSources Q w)).tCount := by
  unfold batchedWindowCore
  apply sequenceProgram_tCount
  unfold batchedWindowSegments batchedWindowSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact sharedCoordinateProgram_tCount w cursor Q hQ h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h
  · intro cursor h; exact placedBatchProgram_tCount w cursor Q h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h

theorem sequenceCircuit_four_tCount (a b c d : AdaptiveCircuit) :
    (sequenceCircuit [a,b,c,d]).tCount = a.tCount+b.tCount+c.tCount+d.tCount := by
  simp only [sequenceCircuit,adaptive_tCount_seq,AdaptiveCircuit.tCount]
  omega

theorem batchedWindowSources_tCount (Q : Point) (w : OddWindow) :
    (sequenceCircuit (batchedWindowSources Q w)).tCount = 514030776 := by
  unfold batchedWindowSources
  rw [sequenceCircuit_four_tCount,(coordinate_numeric_counts _ _).1,
    windowYNegate_numeric_counts.1,placedBatchSource_tCount]

theorem actualFirstWindow_tCount (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    ((actualFirstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 458745 := by
  simp only [actualFirstWindow,reindexStraight_instantiate,
    readConstant_reindex firstIndex _ _ Q coefficientAt_first]
  exact firstLookupProgram_tCount start Q hQ history

theorem actualBatchedWindow_tCount (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    (((actualBatchedWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount =
      514030776 := by
  have h := surroundCompiled_tCount (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (batchedWindowCore w 0)
    (sequenceCircuit (batchedWindowSources Q w)) (readConstant coefficientAt Q) Fin.elim0
    (batchedWindowCore_tCount w 0 Q hQ Fin.elim0)
  simp only [AdaptiveCircuit.tCount,adaptive_tCount_seq,signedAddressCircuit_tCount,
    Nat.zero_add,Nat.add_zero,batchedWindowSources_tCount] at h
  simp only [actualBatchedWindow,closedWindow_run,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount]
  change compiledTCount (batchedWindowPrepared w 0) (readConstant coefficientAt Q) Fin.elim0 = _
  unfold batchedWindowPrepared
  exact h

theorem batchedWindowCore_count (w : OddWindow) (start : Nat) :
    (batchedWindowCore w start).1 = 30733484 := by
  simp only [batchedWindowCore,batchedWindowSegments,sequenceProgram,appendCompiled,
    sharedCoordinateProgram_count,sharedYNegateProgram_count,placedBatchProgram_count]

theorem surroundCompiled_count {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (surroundCompiled before after p).1 = p.1 := by
  simp only [surroundCompiled,prependCompiled,appendCompiled,Nat.add_zero]

theorem actualBatchedWindow_count (w : OddWindow) :
    (actualBatchedWindow w).count = 30733484 := by
  unfold actualBatchedWindow closedWindow
  change 0 + (batchedWindowPrepared w 0).1 = 30733484
  rw [Nat.zero_add]
  have hp : (batchedWindowPrepared w 0).1 = (batchedWindowCore w 0).1 := by
    unfold batchedWindowPrepared
    exact surroundCompiled_count _ _ _
  rw [hp,batchedWindowCore_count]

theorem actualFirstWindow_count : actualFirstWindow.count = 65535 := rfl

theorem axisCount_constant {n : Nat} (ws : List (OuterWindow n)) (m : Nat)
    (hm : ∀ w ∈ ws, w.count = m) : axisCount ws = ws.length * (m+16) := by
  induction ws with
  | nil => simp [axisCount]
  | cons w ws ih =>
    rw [axisCount,hm w (by simp),ih (by intro v hv; exact hm v (by simp [hv]))]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem actualLeftWindows_count : axisCount actualLeftWindows = 461068051 := by
  unfold actualLeftWindows
  rw [axisCount,actualFirstWindow_count]
  rw [axisCount_constant _ 30733484]
  · simp
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact actualBatchedWindow_count _

theorem actualRightWindows_count : axisCount actualRightWindows = 399535500 := by
  unfold actualRightWindows
  rw [axisCount_constant _ 30733484]
  · simp
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact actualBatchedWindow_count _

theorem standardOuterPlan_lists_stride {n : Nat} (left right : List (OuterWindow n))
    (hl : left.length = 16) (hr : right.length = 13) (reset : List Wire) :
    (standardOuterPlan ⟨left.toArray,by simpa using hl⟩
      ⟨right.toArray,by simpa using hr⟩ reset).stride =
      axisCount left + axisCount right + reset.length := by
  simp only [OuterPlan.stride,standardOuterPlan,Vector.toList,List.toList_toArray]

theorem batchedOuterPlan_stride : batchedOuterPlan.stride = 860607482 := by
  have h := standardOuterPlan_lists_stride actualLeftWindows actualRightWindows
    actualLeftWindows_length actualRightWindows_length batchedResetWires
  apply h.trans
  rw [actualLeftWindows_count,actualRightWindows_count,batchedResetWires_length]

/-- Exact final record count includes the first lookup, all 28 addition windows,
all Fourier measurements, and the full 3931-wire reset in each of 56 rounds. -/
theorem batchedOuterPlan_finalCursor : 56 * batchedOuterPlan.stride = 48194018992 := by
  rw [batchedOuterPlan_stride]

end ShorECDLP.Paper2607_13816.ChallengeMigration
