import ShorECDLP.Submission.«2607_13816».Challenge.DecoderBridge
import ShorECDLP.Submission.«2607_13816».Challenge.RoundReset
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] batchedOuterPlan actualRoundSource

theorem readWord_append_shift (before history : List Bool) (positions : List Nat) :
    readWord (before ++ history) (positions.map (before.length + ·)) = readWord history positions := by
  induction positions with
  | nil => rfl
  | cons i ps ih =>
    simp only [List.map_cons,readWord,List.getElem?_append_right (show before.length ≤ before.length+i by omega),Nat.add_sub_cancel_left,ih]

theorem readWord_suffix (history suffix : List Bool) (positions : List Nat)
    (h : ∀ i ∈ positions, i < history.length) :
    readWord (history ++ suffix) positions = readWord history positions := by
  induction positions with
  | nil => rfl
  | cons i ps ih =>
    simp only [readWord,List.getElem?_append_left (h i (by simp)),ih (fun j hj => h j (by simp [hj]))]

theorem axisPositions_shift {n : Nat} (ws : List (OuterWindow n)) (start offset : Nat) :
    axisPositions ws (offset+start) = (axisPositions ws start).map (offset+·) := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [axisPositions,List.map_append,Nat.add_assoc,ih]
    congr 1


def planRoundAccept {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (start : Nat) (history : List Bool) : Bool :=
  fixedPairAccept (axisPositions p.left.toList start)
    (axisPositions p.right.toList (start+axisCount p.left.toList)) accept history

theorem planRoundAccept_shift {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (start : Nat) (before history : List Bool) :
    planRoundAccept p accept (before.length+start) (before++history) =
      planRoundAccept p accept start history := by
  simp only [planRoundAccept,fixedPairAccept,Nat.add_assoc,
    axisPositions_shift,readWord_append_shift]

theorem planRoundAccept_suffix {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (history suffix : List Bool) (h : history.length = p.stride) :
    planRoundAccept p accept 0 (history++suffix) = planRoundAccept p accept 0 history := by
  have hl : ∀ i ∈ axisPositions p.left.toList 0, i < history.length := by
    intro i hi
    have := (axisPositions_bounds _ _ _ hi).2
    rw [h]; simp only [OuterPlan.stride]; omega
  have hr : ∀ i ∈ axisPositions p.right.toList (0+axisCount p.left.toList), i < history.length := by
    intro i hi
    have := (axisPositions_bounds _ _ _ hi).2
    rw [h]; simp only [OuterPlan.stride]; omega
  simp only [planRoundAccept,fixedPairAccept,readWord_suffix history suffix _ hl,
    readWord_suffix history suffix _ hr]

def planRepeatAccept {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (count : Nat) (history : List Bool) : Bool :=
  (List.range count).any (fun r => planRoundAccept p accept (r*p.stride) history)

theorem planRepeatAccept_cons {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (count : Nat) (before history : List Bool) (h : before.length=p.stride) :
    planRepeatAccept p accept (count+1) (before++history) =
      (planRoundAccept p accept 0 before || planRepeatAccept p accept count history) := by
  simp only [planRepeatAccept,List.range_succ_eq_map,List.any_cons,List.any_map,
    Nat.zero_mul,planRoundAccept_suffix p accept before history h]
  congr 1
  apply congrArg (List.any (List.range count))
  funext r
  dsimp only [Function.comp_def]
  rw [Nat.succ_mul,← h,Nat.add_comm,planRoundAccept_shift]

private theorem round_records_length {n : Nat} (p : OuterPlan n)
    (read : ConstantBit n → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.round 0).instantiate read Fin.elim0).run) :
    b.history.length = p.stride := by
  have h := straight_history_length _ read Fin.elim0 b hb
  simpa only [Nat.zero_add,Nat.sub_zero] using h

theorem actualRoundSource_records (Q : Point) (hQ : order • Q=0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    b.history.length = batchedOuterPlan.stride := by
  rw [← batchedOuterPlan_round_run Q hQ 0 Fin.elim0] at hb
  exact round_records_length _ _ b hb

theorem planRepeatAccept_retry (Q : Point) (hQ : order • Q=0)
    (accept : Nat → Nat → Bool) (count : Nat) (b : InstrumentBranch)
    (hb : b ∈ (repeatWindowProgram (actualRoundSource Q) count).run) :
    planRepeatAccept batchedOuterPlan accept count b.history =
      !repeatWindowFailed (actualRoundSource Q) (planRoundAccept batchedOuterPlan accept 0) count b.history := by
  induction count generalizing b with
  | zero => rfl
  | succ count ih =>
    rw [repeatWindowProgram,AdaptiveCircuit.run_seq] at hb
    obtain ⟨a,ha,hc⟩ := List.mem_flatMap.mp hb
    obtain ⟨c,hcRun,rfl⟩ := List.mem_map.mp hc
    rw [show (a.seq c).history = a.history++c.history from rfl,
      planRepeatAccept_cons _ _ count _ _ (actualRoundSource_records Q hQ a ha),ih c hcRun]
    simp only [repeatWindowFailed,consumeAdaptiveHistory_run _ a ha,
      List.length_append,Nat.add_sub_cancel_right,List.take_left,Bool.not_and,Bool.not_not]

private theorem find_isSome_any {α : Type} (p : α → Bool) (xs : List α) :
    (xs.find? p).isSome = xs.any p := by
  apply Bool.eq_iff_iff.mpr
  exact List.find?_isSome.trans List.any_eq_true.symm

theorem wrappedLayout_verified_any (params : DecoderParams) (Q : Point)
    (positions : List (TrialPositions params)) (h : positions.length ≤ 56) (history : List Bool) :
    (verifiedCandidate ⟨.wrappedShift,params,positions,h⟩ Q history).isSome =
      positions.any (fun pos => fixedPairAccept pos.left.toList pos.right.toList
        (wrappedPairAccept params Q) history) := by
  classical
  simp only [verifiedCandidate,candidates,find_isSome_any,List.any_flatMap]
  apply List.any_congr rfl
  intro pos
  have hh := wrappedTrial_verified_isSome params Q pos history
  simpa only [verifiedCandidate,candidates,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,find_isSome_any] using hh

theorem OuterPlan.verified_repeat_event {n : Nat} (p : OuterPlan n) (Q : Point) (history : List Bool) :
    (verifiedCandidate p.layout Q history).isSome =
      planRepeatAccept p (wrappedPairAccept legacyDecoderParams Q) 56 history := by
  rw [OuterPlan.layout,wrappedLayout_verified_any]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_ofFn,planRepeatAccept,List.mem_range]
  constructor
  · rintro ⟨pos,⟨r,rfl⟩,hr⟩
    exact ⟨r.val,r.isLt,by simpa only [OuterPlan.positions,Vector.toList,List.toList_toArray,planRoundAccept] using hr⟩
  · rintro ⟨r,hr,haccept⟩
    exact ⟨p.positions ⟨r,hr⟩,⟨⟨r,hr⟩,rfl⟩,by
      simpa only [OuterPlan.positions,Vector.toList,List.toList_toArray,planRoundAccept] using haccept⟩

private theorem roundAccept_zero {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (history : List Bool) :
    fixedPairAccept (p.positions ⟨0,by decide⟩).left.toList
      (p.positions ⟨0,by decide⟩).right.toList accept history = planRoundAccept p accept 0 history := by
  simp only [OuterPlan.positions,Vector.toList,List.toList_toArray,Nat.zero_mul,planRoundAccept]

theorem actualRoundFixedAccept_eq (accept : Nat → Nat → Bool) (history : List Bool) :
    actualRoundFixedAccept accept history = planRoundAccept batchedOuterPlan accept 0 history :=
  roundAccept_zero _ accept history

theorem actualCompiledRepeat_verified_event (Q : Point) (hQ : order • Q=0)
    (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.repeat 56 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run) :
    (verifiedCandidate batchedOuterPlan.layout Q b.history).isSome =
      !repeatWindowFailed (actualRoundSource Q)
        (actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q)) 56 b.history := by
  rw [OuterPlan.verified_repeat_event]
  have hh := planRepeatAccept_retry Q hQ (wrappedPairAccept legacyDecoderParams Q) 56 b
    (by rwa [batchedOuterPlan_repeat_run Q hQ] at hb)
  have he : actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) =
      planRoundAccept batchedOuterPlan (wrappedPairAccept legacyDecoderParams Q) 0 :=
    funext (actualRoundFixedAccept_eq _)
  rw [he]
  exact hh


/-- The protected final decoder tests exactly the independent retry event of the actual 56 rounds. -/
theorem actualCompiledRepeat_verified_mass (Q : Point) (hQ : order • Q=0) (hn : Q≠0) :
    Instrument.bornMass
      ((((batchedOuterPlan.repeat 56 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => (verifiedCandidate batchedOuterPlan.layout Q b.history).isSome)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (Instrument.bornMass ((actualRoundSource Q).run.filter
          (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history)) (ket zeroBasisState)) 56 := by
  have he := List.filter_congr (actualCompiledRepeat_verified_event Q hQ)
  rw [he]
  exact actualCompiledRepeat_retry_mass Q hQ hn 56 0 Fin.elim0 _
end ShorECDLP.Paper2607_13816.ChallengeMigration
