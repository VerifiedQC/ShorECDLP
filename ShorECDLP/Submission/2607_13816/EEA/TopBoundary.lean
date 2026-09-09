import ShorECDLP.Submission.«2607_13816».EEA.EndpointPulses
import ShorECDLP.Submission.«2607_13816».EEA.LengthInitialize

/-! # Numeric equality and the interval top-lane accumulator boundary -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

/-- A bounded constant matches exactly the numeric value of the endpoint register. -/
theorem registerMatches_eq_numeric (register : List Wire) (value : Nat) (state : BasisState)
    (hvalue : value < 2^register.length) :
    registerMatches register value state = decide (boolWordToNat (wireValues register state) = value) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change registerMatchesFrom register value 0 state = true ↔ _
  rw [registerMatchesFrom_iff]
  simp only [Nat.zero_add]
  have hword := boolWordToNat_lt_pow_two (wireValues register state)
  rw [show (wireValues register state).length = register.length by simp [wireValues]] at hword
  have hb (i : Nat) (hi : i < register.length) :
      (boolWordToNat (wireValues register state)).testBit i = state register[i] := by
    have hv : i < (wireValues register state).length := by simpa [wireValues] using hi
    rw [← getD_false_eq_testBit_boolWordToNat _ hv, List.getD_eq_getElem _ _ hv]
    simp [wireValues]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < register.length
    · rw [hb i hi, h i hi]
    · have hp : 2^register.length ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (hword.trans_le hp), Nat.testBit_lt_two_pow (hvalue.trans_le hp)]
  · intro h i hi
    rw [← hb i hi, h]

theorem intervalInputs_disjoint_workScratch (r : IntervalRegisters) (h : r.allWires.Nodup) :
    List.Disjoint (r.control :: (r.lengthQ ++ r.lengthS)) (r.work1 ++ r.work2 ++ r.scratch) := by
  obtain ⟨_, ht, hc⟩ := List.nodup_append.mp h
  obtain ⟨_, ht, hw1⟩ := List.nodup_append.mp ht
  obtain ⟨_, ht, hw2⟩ := List.nodup_append.mp ht
  obtain ⟨_, ht, _⟩ := List.nodup_append.mp ht
  obtain ⟨_, ht, hq⟩ := List.nodup_append.mp ht
  obtain ⟨_, _, hs⟩ := List.nodup_append.mp ht
  apply List.disjoint_left.mpr
  intro w hp hw
  simp only [List.mem_cons, List.mem_append] at hp hw
  rcases hp with he | hq' | hs'
  · subst w
    apply hc r.control (by simp) r.control _ rfl
    rcases hw with (h | h) | h <;> simp [h]
  · rcases hw with (h | h) | h
    · exact hw1 w h w (by simp [hq']) rfl
    · exact hw2 w h w (by simp [hq']) rfl
    · exact hq w hq' w (by simp [h]) rfl
  · rcases hw with (h | h) | h
    · exact hw1 w h w (by simp [hs']) rfl
    · exact hw2 w h w (by simp [hs']) rfl
    · exact hs w hs' w h rfl

private theorem getD_mem (xs : List Wire) (i : Nat) (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem intervalWrittenRoles_mem_workScratch (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) (j : Nat) (hj : j < intervalLaneCount k K) :
    ∀ w ∈ [r.accumulator k K, r.targetAt target j, r.addendAt target j, r.carry k K],
      w ∈ r.work1 ++ r.work2 ++ r.scratch := by
  have ha : r.accumulator k K ∈ r.scratch :=
    getD_mem r.scratch _ (by rw [h.scratch_length]; omega)
  have hc : r.carry k K ∈ r.scratch :=
    getD_mem r.scratch _ (by rw [h.scratch_length]; omega)
  have ht : r.targetAt target j ∈ r.work1 ++ r.work2 := by
    cases target
    · exact List.mem_append_left _ (getD_mem r.work1 j (by rw [h.work1_length]; exact hj))
    · exact List.mem_append_right _ (getD_mem r.work2 j (by rw [h.work2_length]; exact hj))
  have hb : r.addendAt target j ∈ r.work1 ++ r.work2 := by
    cases target
    · exact List.mem_append_right _ (getD_mem r.work2 j (by rw [h.work2_length]; exact hj))
    · exact List.mem_append_left _ (getD_mem r.work1 j (by rw [h.work1_length]; exact hj))
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact List.mem_append_right _ ha
  · exact List.mem_append_left _ ht
  · exact List.mem_append_left _ hb
  · exact List.mem_append_right _ hc

private theorem first_accumulator (mode : RippleMode) (value : Nat)
    (rs ls : List Wire) (acc t a c rc lc : Wire) (state : BasisState)
    (hcell : acc ≠ t ∧ acc ≠ a ∧ acc ≠ c)
    (hroot : lc ≠ acc ∧ lc ≠ t ∧ lc ≠ a ∧ lc ≠ c)
    (hreg : ∀ w ∈ [acc,t,a,c], w ∉ ls) :
    topSpecialFirstLeafState mode value rs ls acc t a c rc lc state acc =
      (state acc ^^ (state rc && registerMatches rs value state) ^^
        (state lc && registerMatches ls value state)) := by
  simp only [topSpecialFirstLeafState, writeRippleCell, registerMatches]
  rw [registerMatchesFrom_upd_not_mem _ _ _ _ c _ (hreg c (by simp)),
    registerMatchesFrom_upd_not_mem _ _ _ _ a _ (hreg a (by simp)),
    registerMatchesFrom_upd_not_mem _ _ _ _ t _ (hreg t (by simp)),
    registerMatchesFrom_upd_not_mem _ _ _ _ acc _ (hreg acc (by simp))]
  simp [upd, hcell.1, hcell.2.1, hcell.2.2, hroot.1, hroot.2.1, hroot.2.2.1, hroot.2.2.2]

private theorem second_accumulator (mode : RippleMode) (value : Nat)
    (rs ls : List Wire) (acc t a c rc lc : Wire) (state : BasisState)
    (hcell : acc ≠ t ∧ acc ≠ a ∧ acc ≠ c)
    (hroot : rc ≠ acc ∧ rc ≠ t ∧ rc ≠ a ∧ rc ≠ c)
    (hreg : ∀ w ∈ [acc,t,a,c], w ∉ rs) :
    topSpecialSecondLeafState mode value rs ls acc t a c rc lc state acc =
      (state acc ^^ (state lc && registerMatches ls value state) ^^
        (state rc && registerMatches rs value state)) := by
  simp only [topSpecialSecondLeafState, writeRippleCell, registerMatches]
  rw [registerMatchesFrom_upd_not_mem _ _ _ _ c _ (hreg c (by simp)),
    registerMatchesFrom_upd_not_mem _ _ _ _ a _ (hreg a (by simp)),
    registerMatchesFrom_upd_not_mem _ _ _ _ t _ (hreg t (by simp)),
    registerMatchesFrom_upd_not_mem _ _ _ _ acc _ (hreg acc (by simp))]
  simp [upd, hcell.1, hcell.2.1, hcell.2.2, hroot.1, hroot.2.1, hroot.2.2.1, hroot.2.2.2]

theorem intervalTopInputs_disjoint_roles (r : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (h : IntervalLayout r k K target) :
    ∀ w ∈ [r.accumulator k K, r.targetAt target (intervalTopRelative k K),
      r.addendAt target (intervalTopRelative k K), r.carry k K],
      w ∉ r.control :: (r.lengthQ ++ r.lengthS) := by
  intro w hw hi
  have hj : intervalTopRelative k K < intervalLaneCount k K := by
    simp [intervalTopRelative, intervalLaneCount]
  exact List.disjoint_left.mp (intervalInputs_disjoint_workScratch r h.physical) hi
    (intervalWrittenRoles_mem_workScratch r k K target h _ hj w hw)

private theorem top_first_numeric (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) (h : IntervalLayout r k K target)
    (hspecial : intervalHasTopSpecial k K = true)
    (hclean : Clean (r.cellScratch k K :: r.equalityScratch k K) state) :
    run (intervalTopFirst r k K mode target) state (r.accumulator k K) =
      (state (r.accumulator k K) ^^
        (state r.control && decide (boolWordToNat (wireValues r.lengthS state) = intervalTopRelative k K)) ^^
        (state r.control && decide (boolWordToNat (wireValues r.lengthQ state) = intervalTopRelative k K))) := by
  have hi := intervalTopInputs_disjoint_roles r k K target h
  have hroot : r.control ≠ r.accumulator k K ∧
      r.control ≠ r.targetAt target (intervalTopRelative k K) ∧
      r.control ≠ r.addendAt target (intervalTopRelative k K) ∧ r.control ≠ r.carry k K := by
    have hr (w : Wire) (hw : w ∈ [r.accumulator k K, r.targetAt target (intervalTopRelative k K),
        r.addendAt target (intervalTopRelative k K), r.carry k K]) : r.control ≠ w :=
      fun he => hi w hw (by simp [← he])
    exact ⟨hr _ (by simp), hr _ (by simp), hr _ (by simp), hr _ (by simp)⟩
  have hn := (h.topSpecial hspecial).2.2.1
  have hc := (List.nodup_cons.mp hn).1
  have hcell : r.accumulator k K ≠ r.targetAt target (intervalTopRelative k K) ∧
      r.accumulator k K ≠ r.addendAt target (intervalTopRelative k K) ∧
      r.accumulator k K ≠ r.carry k K := by
    refine ⟨?_,?_,?_⟩ <;> intro he <;> apply hc <;> simp [he]
  rw [run_intervalTopFirst_state r k K mode target state h hclean,
    intervalTopFirstState, if_pos hspecial]
  rw [first_accumulator _ _ _ _ _ _ _ _ _ _ _ hcell hroot]
  · have hp := intervalTopRelative_eq_pow_topBit k K hspecial
    rw [registerMatches_eq_numeric r.lengthS _ state (by rw [hp]; exact Nat.pow_lt_pow_right (by decide) (h.right_top_capacity hspecial)),
      registerMatches_eq_numeric r.lengthQ _ state (by rw [hp]; exact Nat.pow_lt_pow_right (by decide) (h.left_top_capacity hspecial))]
  · intro w hw hm
    exact hi w hw (by simp [hm])

private theorem top_second_numeric (r : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) (state : BasisState) (h : IntervalLayout r k K target)
    (hspecial : intervalHasTopSpecial k K = true)
    (hclean : Clean (r.cellScratch k K :: r.equalityScratch k K) state) :
    run (intervalTopSecond r k K mode target) state (r.accumulator k K) =
      (state (r.accumulator k K) ^^
        (state r.control && decide (boolWordToNat (wireValues r.lengthQ state) = intervalTopRelative k K)) ^^
        (state r.control && decide (boolWordToNat (wireValues r.lengthS state) = intervalTopRelative k K))) := by
  have hi := intervalTopInputs_disjoint_roles r k K target h
  have hroot : r.control ≠ r.accumulator k K ∧
      r.control ≠ r.targetAt target (intervalTopRelative k K) ∧
      r.control ≠ r.addendAt target (intervalTopRelative k K) ∧ r.control ≠ r.carry k K := by
    have hr (w : Wire) (hw : w ∈ [r.accumulator k K, r.targetAt target (intervalTopRelative k K),
        r.addendAt target (intervalTopRelative k K), r.carry k K]) : r.control ≠ w :=
      fun he => hi w hw (by simp [← he])
    exact ⟨hr _ (by simp), hr _ (by simp), hr _ (by simp), hr _ (by simp)⟩
  have hn := (h.topSpecial hspecial).2.2.1
  have hc := (List.nodup_cons.mp hn).1
  have hcell : r.accumulator k K ≠ r.targetAt target (intervalTopRelative k K) ∧
      r.accumulator k K ≠ r.addendAt target (intervalTopRelative k K) ∧
      r.accumulator k K ≠ r.carry k K := by
    refine ⟨?_,?_,?_⟩ <;> intro he <;> apply hc <;> simp [he]
  rw [run_intervalTopSecond_state r k K mode target state h (fun _ => hclean),
    intervalTopSecondState, if_pos hspecial]
  rw [second_accumulator _ _ _ _ _ _ _ _ _ _ _ hcell hroot]
  · have hp := intervalTopRelative_eq_pow_topBit k K hspecial
    rw [registerMatches_eq_numeric r.lengthS _ state (by rw [hp]; exact Nat.pow_lt_pow_right (by decide) (h.right_top_capacity hspecial)),
      registerMatches_eq_numeric r.lengthQ _ state (by rw [hp]; exact Nat.pow_lt_pow_right (by decide) (h.left_top_capacity hspecial))]
  · intro w hw hm
    exact hi w hw (by simp [hm])

private theorem top_switches (enabled : Bool) (L R top : Nat) (horder : L ≤ R) (hbound : R ≤ top) :
    ((enabled && decide (R=top)) ^^ (enabled && decide (L=top))) = intervalAccumulatorBoundary enabled L R top := by
  cases enabled <;> by_cases hl : L=top <;> by_cases hr : R=top <;>
    simp_all [intervalAccumulatorBoundary] <;> omega

/-- Starting with a clean accumulator, the actual first top-lane operation produces
exactly the incoming boundary required by the decreasing main scan. -/
theorem intervalTopFirst_accumulatorBoundary
    (r : IntervalRegisters) (k K : Nat) (mode : RippleMode) (target : IntervalTarget)
    (state : BasisState) (h : IntervalLayout r k K target)
    (hclean : Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (hacc : state (r.accumulator k K) = false)
    (horder : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state))
    (hbound : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K) :
    run (intervalTopFirst r k K mode target) state (r.accumulator k K) =
      intervalAccumulatorBoundary (state r.control) (boolWordToNat (wireValues r.lengthQ state))
        (boolWordToNat (wireValues r.lengthS state)) (intervalMainLabels k K).length := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [top_first_numeric r k K mode target state h hspecial hclean, hacc]
    simp only [Bool.false_xor]
    have hn : (intervalMainLabels k K).length = intervalTopRelative k K := by
      simp [intervalMainLabels, hspecial, intervalTopRelative]
    rw [hn]
    exact top_switches _ _ _ _ horder hbound
  · have hr : boolWordToNat (wireValues r.lengthS state) < (intervalMainLabels k K).length := by
      simp [intervalMainLabels, hspecial]
      unfold intervalTopRelative at hbound
      have hpos : 0 < intervalLaneCount k K := by simp [intervalLaneCount]
      omega
    simp [intervalTopFirst, hspecial, hacc, intervalAccumulatorBoundary, Nat.not_le_of_lt hr]

/-- The actual second top-lane operation consumes the increasing main scan's
outgoing boundary and restores the accumulator to zero. -/
theorem intervalTopSecond_accumulatorClean
    (r : IntervalRegisters) (k K : Nat) (mode : RippleMode) (target : IntervalTarget)
    (state : BasisState) (h : IntervalLayout r k K target)
    (hclean : Clean (r.cellScratch k K :: r.equalityScratch k K) state)
    (hacc : state (r.accumulator k K) = intervalAccumulatorBoundary (state r.control)
      (boolWordToNat (wireValues r.lengthQ state)) (boolWordToNat (wireValues r.lengthS state))
      (intervalMainLabels k K).length)
    (horder : boolWordToNat (wireValues r.lengthQ state) ≤ boolWordToNat (wireValues r.lengthS state))
    (hbound : boolWordToNat (wireValues r.lengthS state) ≤ intervalTopRelative k K) :
    run (intervalTopSecond r k K mode target) state (r.accumulator k K) = false := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · rw [top_second_numeric r k K mode target state h hspecial hclean, hacc]
    have hn : (intervalMainLabels k K).length = intervalTopRelative k K := by
      simp [intervalMainLabels, hspecial, intervalTopRelative]
    rw [hn, ← top_switches _ _ _ _ horder hbound]
    simp
  · have hr : boolWordToNat (wireValues r.lengthS state) < (intervalMainLabels k K).length := by
      simp [intervalMainLabels, hspecial]
      unfold intervalTopRelative at hbound
      have hpos : 0 < intervalLaneCount k K := by simp [intervalLaneCount]
      omega
    simp [intervalTopSecond, hspecial, hacc, intervalAccumulatorBoundary, Nat.not_le_of_lt hr]

end ShorECDLP.Paper2607_13816
