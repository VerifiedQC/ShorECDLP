import ShorECDLP.Submission.«2607_13816».Challenge.WindowCounts
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Challenge.Official
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] actualFirstWindow actualBatchedWindow actualLeftWindows actualRightWindows
  batchedOuterPlan

/-- Weighted window costs retain the much smaller first lookup. -/
theorem outerAxis_weighted_t_le {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n))
    (cost : OuterWindow n → Nat) (read : ConstantBit n → Bool)
    (hw : ∀ w ∈ ws, ∀ s h, ((w.program s).instantiate read h).tCount ≤ cost w)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((outerAxis wires ws start prior).instantiate read history).tCount ≤
      (ws.map cost).sum + axisFeedback ws.length prior.length := by
  induction ws generalizing start with
  | nil => simp [outerAxis,axisFeedback,Straight.instantiate,AdaptiveCircuit.tCount]
  | cons w ws ih =>
    simp only [outerAxis,castFinish_instantiate]
    apply (outer_append_t_le _ _ read history
      (fourierSlots 16 prior.length + ((ws.map cost).sum+axisFeedback ws.length (prior.length+16))) ?_).trans
    · simp only [prepareOuterBank_t,List.length_cons,List.map_cons,List.sum_cons,axisFeedback]
      have h := hw w (by simp) start history
      omega
    · intro h
      apply (outer_append_t_le _ _ read h
        ((ws.map cost).sum+axisFeedback ws.length (prior.length+16)) ?_).trans
      · have hf := fourierProgram_t_le n .inverse wires.toList (start+w.count) (bankPrior w.count prior) read h
        simp only [Vector.length_toList,bankPrior_length] at hf
        simp only [castFinish_instantiate]
        omega
      · intro h₂
        simpa only [nextBankPrior_length] using
          ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _ (nextBankPrior w.count prior) h₂

theorem OuterPlan.round_weighted_t_le {n : Nat} (p : OuterPlan n)
    (cost : OuterWindow n → Nat) (read : ConstantBit n → Bool)
    (hw : ∀ w ∈ p.left.toList ++ p.right.toList, ∀ s h,
      ((w.program s).instantiate read h).tCount ≤ cost w)
    (start : Nat) (history : Fin start → Bool) :
    ((p.round start).instantiate read history).tCount ≤
      (p.left.toList.map cost).sum + (p.right.toList.map cost).sum + 54168 := by
  have hl := outerAxis_weighted_t_le p.wires p.left.toList cost read
    (fun w h => hw w (List.mem_append_left _ h)) start List.nil history
  have hr (h) := outerAxis_weighted_t_le p.wires p.right.toList cost read
    (fun w h => hw w (List.mem_append_right _ h)) (start+axisCount p.left.toList) List.nil h
  simp only [Vector.length_toList,List.length_nil] at hl hr
  simp only [OuterPlan.round,castFinish_instantiate,Straight.instantiate,TemplateGate.instantiate,
    AdaptiveCircuit.tCount,ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    tCost,Nat.zero_add]
  apply (outer_append_t_le _ _ read history ((p.right.toList.map cost).sum+axisFeedback 13 0) ?_).trans
  · have h := outer_feedback_overhead; omega
  · intro h
    apply (outer_append_t_le _ _ read h 0 ?_).trans
    · have ht := hr h; omega
    · intro h₂
      simp [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
        ShorECDLP.tCount,tCost,resetProgram_t]

def actualWindowTCost (w : OuterWindow 983040) : Nat :=
  if w.count = 65535 then 458745 else 514030776

theorem actualWindowTCost_first : actualWindowTCost actualFirstWindow = 458745 := by
  simp only [actualWindowTCost,actualFirstWindow_count,ite_true]
theorem actualWindowTCost_batched (w : OddWindow) :
    actualWindowTCost (actualBatchedWindow w) = 514030776 := by
  simp only [actualWindowTCost,actualBatchedWindow_count]
  decide

theorem actualWindowTCost_bound (Q : Point) (hQ : order • Q = 0) :
    ∀ w ∈ actualLeftWindows ++ actualRightWindows, ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).tCount ≤ actualWindowTCost w := by
  intro w hw start history
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨i,rfl⟩) | ⟨i,rfl⟩
  · rw [actualFirstWindow_tCount start Q hQ history,actualWindowTCost_first]
  · rw [actualBatchedWindow_tCount _ start Q hQ history,actualWindowTCost_batched]
  · rw [actualBatchedWindow_tCount _ start Q hQ history,actualWindowTCost_batched]

theorem actualWindowTCost_total :
    (actualLeftWindows.map actualWindowTCost).sum +
      (actualRightWindows.map actualWindowTCost).sum = 14393320473 := by
  simp only [actualLeftWindows,actualRightWindows,List.map_cons,List.sum_cons,List.map_ofFn,
    Function.comp_def,actualWindowTCost_first,actualWindowTCost_batched]
  simp

theorem batchedOuterPlan_left : batchedOuterPlan.left.toList = actualLeftWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]
theorem batchedOuterPlan_right : batchedOuterPlan.right.toList = actualRightWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]

theorem batchedOuterPlan_round_t_le (Q : Point) (hQ : order • Q = 0)
    (start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      14393374641 := by
  have h := batchedOuterPlan.round_weighted_t_le actualWindowTCost (readConstant coefficientAt Q)
    (by rw [batchedOuterPlan_left,batchedOuterPlan_right]; exact actualWindowTCost_bound Q hQ) start history
  rw [batchedOuterPlan_left,batchedOuterPlan_right,actualWindowTCost_total] at h
  exact h

theorem OuterPlan.repeat_t_le_of_round {n : Nat} (p : OuterPlan n) (cost : Nat)
    (read : ConstantBit n → Bool)
    (hcost : ∀ start history, ((p.round start).instantiate read history).tCount ≤ cost)
    (trials start : Nat) (history : Fin start → Bool) :
    ((p.repeat trials start).instantiate read history).tCount ≤ trials * cost := by
  induction trials generalizing start with
  | zero => simp [OuterPlan.repeat,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.tCount]
  | succ trials ih =>
    simp only [OuterPlan.repeat,castFinish_instantiate]
    have ha := outer_append_t_le (p.round start) (p.repeat trials (start+p.stride)) read history
      (trials*cost) (fun h => ih _ h)
    have hb := hcost start history
    rw [Nat.succ_mul]
    omega

/-- T upper bound of the actual 56-round five-word program; includes Fourier feedback. -/
theorem batchedOuterPlan_total_t_le (Q : Point) (hQ : order • Q = 0) :
    ((batchedOuterPlan.repeat 56 0).instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      806028979896 := by
  exact batchedOuterPlan.repeat_t_le_of_round 14393374641 (readConstant coefficientAt Q)
    (batchedOuterPlan_round_t_le Q hQ) 56 0 Fin.elim0

/-- The earlier provisional limit omitted the five-word correction overhead. -/
theorem batchedOuterPlan_exceeds_old_measurement_limit :
    47471340504 < 56 * batchedOuterPlan.stride := by
  rw [batchedOuterPlan_finalCursor]
  decide
/-- The revised provisional cap includes the actual five-word correction program. -/
theorem batchedOuterPlan_measurements_fit :
    56 * batchedOuterPlan.stride ≤ officialLimits.measurements := by
  rw [batchedOuterPlan_finalCursor]
  decide
end ShorECDLP.Paper2607_13816.ChallengeMigration
