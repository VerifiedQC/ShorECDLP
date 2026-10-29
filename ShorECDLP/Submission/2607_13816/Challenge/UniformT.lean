import ShorECDLP.Submission.«2607_13816».Challenge.WindowBudget
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
private theorem leaf_t_zero {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire))
    (read : ConstantBit n → Bool) :
    ShorECDLP.tCount ((lookupLeafGates q ports).flatMap (TemplateGate.instantiate read)) = 0 := by
  rw [lookupLeafGates_instantiate]
  induction ports.filter (fun p => read p.1) with
  | nil => rfl
  | cons p ps ih => simpa [ShorECDLP.tCount, tCost] using ih
private theorem unary_t_congr (tree : UnaryActionTree) (f g : Nat → Wire → Circuit)
    (h : ∀ l w, ShorECDLP.tCount (f l w) = ShorECDLP.tCount (g l w))
    (q : Wire) (anc : List Wire) :
    (unaryAction .inc f tree q anc).tCount = (unaryAction .inc g tree q anc).tCount := by
  induction tree generalizing q anc with
  | leaf l => simp [unaryAction,AdaptiveCircuit.tCount,h]
  | node b z o ihz iho => cases anc <;>
      simp only [unaryAction,AdaptiveCircuit.tCount,adaptive_tCount_seq,ihz,iho]
private theorem field_load_uniform (field : PointField) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((fieldLoadProgram field start).instantiate read history).tCount = 229369 := by
  have he : ((fieldLoadProgram field start).instantiate read history).tCount =
      ((fieldLoadProgram field start).instantiate (readConstant (oddWindowCoefficients (.left 0)) 0) history).tCount := by
    simp only [fieldLoadProgram,castFinish_instantiate,lookupProgram_tCount,fieldLoadOps,unaryLookupOps_circuit]
    apply unary_t_congr
    intro l w
    simp only [fieldLeaf,leaf_t_zero]
  exact he.trans (fieldLoadProgram_tCount (.left 0) field start 0 (by simp) history)
private theorem first_load_uniform (start : Nat)
    (read : ConstantBit 65536 → Bool) (history : Fin start → Bool) :
    ((firstLookupProgram start).instantiate read history).tCount = 458745 := by
  have he : ((firstLookupProgram start).instantiate read history).tCount =
      ((firstLookupProgram start).instantiate (readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) 0) history).tCount := by
    simp only [firstLookupProgram,castFinish_instantiate,lookupProgram_tCount,firstLookupOps,unaryLookupOps_circuit]
    apply unary_t_congr
    intro l w
    simp only [pointLeaf,leaf_t_zero]
  exact he.trans (firstLookupProgram_tCount start 0 (by simp) history)
attribute [local irreducible] fieldLoadProgram modularAddProgram
private theorem field_add_uniform (field : PointField) (acc : List Wire)
    (start : Nat) (read : ConstantBit 32768 → Bool) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) read history =
      229369 + (controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount + 229369 := by
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  let target := controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558
  have addT : ∀ h, (add.2.instantiate read h).tCount = target.tCount := by
    intro h
    exact modularAddProgram_tCount 32768 _ _ acc _ _ _ _ _ _ _
      (by simp [hl]) (by simp [secp256k1ReductionConstantBits, hl]) (by omega) read h
  have suffixT : ∀ h, compiledTCount
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩) read h =
      target.tCount + 229369 := by
    intro h
    rw [appendCompiled_tCount add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩ read h 229369
      (fun h => field_load_uniform field _ read h), addT h]
  change compiledTCount
    (appendCompiled ⟨32767, fieldLoadProgram field start⟩
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩)) read history = _
  rw [appendCompiled_tCount _ _ _ _ (target.tCount+229369) suffixT,
    field_load_uniform field start read history]
  exact (Nat.add_assoc _ _ _).symm

private theorem field_add_source (field : PointField) (acc : List Wire)
    (start : Nat) (read : ConstantBit 32768 → Bool) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) read history =
      (lookupModularAddProgram (fun l => fieldValue (windowPoint 0 (.left 0) l) field)
        pointLookupAddress pointLookupPath (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount := by
  rw [field_add_uniform field acc start read hl history]
  simp only [lookupModularAddProgram, adaptive_tCount_seq]
  rw [tableLookupProgram_tCount _ _ _ _ (by decide) (by decide)]
  rfl

private theorem signed_field_uniform (field : PointField) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    compiledTCount (signedFieldProgram field start) read history =
      (signedPointLookupY (fun l => fieldValue (windowPoint 0 (.left 0) l) field)).tCount := by
  unfold signedFieldProgram
  dsimp only
  unfold signedPointLookupY signedLookupModularAddProgram
  simp only [List.length_range']
  rw [adaptive_seq_assoc]
  apply appendCompiled_tCount_eq
  · exact yNegateProgram_tCount start _ history
  · intro h
    apply appendCompiled_tCount_eq
    · exact field_add_source field _ _ read (by simp) h
    · intro h
      exact yNegateProgram_tCount _ _ h

theorem coordinateProgram_tCount_uniform (start : Nat) (read : ConstantBit 32768 → Bool)
    (history : Fin start → Bool) :
    compiledTCount (coordinateProgram start) read history =
      (signedLookupCoordinateProgram (fun l => fieldValue (windowPoint 0 (.left 0) l) .x)
        (fun l => fieldValue (windowPoint 0 (.left 0) l) .y)).tCount := by
  unfold coordinateProgram
  rw [← coordinateSources_eq]
  apply sequenceProgram_tCount
  unfold coordinateSegments coordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact field_add_source .negX _ cursor read (by simp) h
  · intro cursor h
    exact signed_field_uniform .negY cursor read h
  · intro cursor h
    exact zeroDivisionProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact field_add_source .tripleX _ cursor read (by simp) h
  · intro cursor h
    exact zeroMultiplicationProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact field_add_source .x _ cursor read (by simp) h
  · intro cursor h
    exact signed_field_uniform .negY cursor read h

attribute [local irreducible] sharedCoordinateProgram yNegateProgram placedBatchProgram
  batchedWindowCore batchedWindowPrepared signedLookupCoordinateProgram
  sharedYNegateProgram actualBatchedWindow actualLeftWindows actualRightWindows
  placedBatchSource windowYNegate sequenceCircuit batchedWindowSources

theorem sharedCoordinateProgram_tCount_uniform (w : OddWindow) (start : Nat)
    (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    compiledTCount (sharedCoordinateProgram w start) read history = 510203526 := by
  simp only [sharedCoordinateProgram,reindexCompiled,compiledTCount,reindexStraight_instantiate]
  exact (coordinateProgram_tCount_uniform start _ history).trans (coordinate_numeric_counts _ _).1

theorem batchedWindowCore_tCount_uniform (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (batchedWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (batchedWindowSources Q w)).tCount := by
  unfold batchedWindowCore
  apply sequenceProgram_tCount
  unfold batchedWindowSegments batchedWindowSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact (sharedCoordinateProgram_tCount_uniform w cursor _ h).trans (coordinate_numeric_counts _ _).1.symm
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h
  · intro cursor h; exact placedBatchProgram_tCount w cursor Q h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h


theorem actualFirstWindow_tCount_uniform (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((actualFirstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 458745 := by
  simp only [actualFirstWindow,reindexStraight_instantiate]
  exact first_load_uniform start _ history
theorem actualBatchedWindow_tCount_uniform (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    (((actualBatchedWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount =
      514030776 := by
  have h := surroundCompiled_tCount (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (batchedWindowCore w 0)
    (sequenceCircuit (batchedWindowSources Q w)) (readConstant coefficientAt Q) Fin.elim0
    (batchedWindowCore_tCount_uniform w 0 Q Fin.elim0)
  simp only [AdaptiveCircuit.tCount,adaptive_tCount_seq,signedAddressCircuit_tCount,
    Nat.zero_add,Nat.add_zero,batchedWindowSources_tCount] at h
  simp only [actualBatchedWindow,closedWindow_run,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount]
  change compiledTCount (batchedWindowPrepared w 0) (readConstant coefficientAt Q) Fin.elim0 = _
  unfold batchedWindowPrepared
  exact h

theorem actualWindowTCost_bound_uniform (Q : Point) :
    ∀ w ∈ actualLeftWindows ++ actualRightWindows, ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).tCount ≤ actualWindowTCost w := by
  intro w hw start history
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨i,rfl⟩) | ⟨i,rfl⟩
  · rw [actualFirstWindow_tCount_uniform start Q history,actualWindowTCost_first]
  · rw [actualBatchedWindow_tCount_uniform _ start Q history,actualWindowTCost_batched]
  · rw [actualBatchedWindow_tCount_uniform _ start Q history,actualWindowTCost_batched]

attribute [local irreducible] batchedOuterPlan
theorem batchedOuterPlan_round_t_uniform (Q : Point)
    (start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      14393374641 := by
  have h := batchedOuterPlan.round_weighted_t_le actualWindowTCost (readConstant coefficientAt Q)
    (by rw [batchedOuterPlan_left,batchedOuterPlan_right]; exact actualWindowTCost_bound_uniform Q) start history
  rw [batchedOuterPlan_left,batchedOuterPlan_right,actualWindowTCost_total] at h
  exact h

theorem batchedOuterPlan_total_t_uniform (Q : Point) :
    ((batchedOuterPlan.repeat 56 0).instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      806028979896 := by
  exact batchedOuterPlan.repeat_t_le_of_round 14393374641 (readConstant coefficientAt Q)
    (batchedOuterPlan_round_t_uniform Q) 56 0 Fin.elim0

end ShorECDLP.Paper2607_13816.ChallengeMigration
