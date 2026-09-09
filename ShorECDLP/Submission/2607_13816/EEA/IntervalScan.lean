import ShorECDLP.Submission.«2607_13816».EEA.IntervalLogical

/-! # Inclusive interval scan and accumulator induction -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
/-- Accumulator value at a cut between adjacent interval labels. -/
def intervalAccumulatorBoundary (enabled : Bool) (L R k : Nat) : Bool := enabled && decide (L < k ∧ k ≤ R)
private theorem first_phase (enabled : Bool) (L R j : Nat) (h : L ≤ R) :
    (intervalAccumulatorBoundary enabled L R (j+1) ^^ (enabled && decide (j=R))) =
      (enabled && decide (L ≤ j ∧ j ≤ R)) := by
  cases enabled <;> by_cases hl : L ≤ j <;> by_cases hr : j < R <;> by_cases he : j=R <;>
    simp_all [intervalAccumulatorBoundary] <;> omega
private theorem second_phase (enabled : Bool) (L R j : Nat) (h : L ≤ R) :
    (intervalAccumulatorBoundary enabled L R j ^^ (enabled && decide (j=L))) =
      (enabled && decide (L ≤ j ∧ j ≤ R)) := by
  cases enabled <;> by_cases hl : L < j <;> by_cases hr : j ≤ R <;> by_cases he : j=L <;>
    simp_all [intervalAccumulatorBoundary] <;> omega
private theorem first_exit (enabled : Bool) (L R j : Nat) (h : L ≤ R) :
    ((enabled && decide (L ≤ j ∧ j ≤ R)) ^^ (enabled && decide (j=L))) =
      intervalAccumulatorBoundary enabled L R j := by
  have hh := congrArg (fun b => b ^^ (enabled && decide (j=L))) (second_phase enabled L R j h)
  simpa using hh.symm
private theorem second_exit (enabled : Bool) (L R j : Nat) (h : L ≤ R) :
    ((enabled && decide (L ≤ j ∧ j ≤ R)) ^^ (enabled && decide (j=R))) =
      intervalAccumulatorBoundary enabled L R (j+1) := by
  have hh := congrArg (fun b => b ^^ (enabled && decide (j=R))) (first_phase enabled L R j h)
  simpa using hh.symm

private theorem first_cell
    (mode : RippleMode) (topSpecial enabled r l : Bool) (rt lt acc t a c L R j : Nat)
    (state : BasisState) (horder : L ≤ R)
    (hacc : state acc = intervalAccumulatorBoundary enabled L R (j+1))
    (hr : (r && if maskedZeroLeaf topSpecial j then !state rt else true) = (enabled && decide (j=R)))
    (hl : (l && if maskedZeroLeaf topSpecial j then !state lt else true) = (enabled && decide (j=L))) :
    intervalFirstLogicalLeaf mode topSpecial rt lt acc t a c j r l state =
      (writeRippleCell t a c (rippleFirstBits mode (enabled && decide (L ≤ j ∧ j ≤ R))
        (readRippleCell t a c state)) state)[acc ↦ intervalAccumulatorBoundary enabled L R j] := by
  unfold intervalFirstLogicalLeaf
  dsimp only
  rw [hr, hl, hacc, first_phase enabled L R j horder, first_exit enabled L R j horder]

private theorem second_cell
    (mode : RippleMode) (topSpecial enabled r l : Bool) (rt lt acc t a c L R j : Nat)
    (state : BasisState) (horder : L ≤ R)
    (hacc : state acc = intervalAccumulatorBoundary enabled L R j)
    (hr : (r && if maskedZeroLeaf topSpecial j then !state rt else true) = (enabled && decide (j=R)))
    (hl : (l && if maskedZeroLeaf topSpecial j then !state lt else true) = (enabled && decide (j=L))) :
    intervalSecondLogicalLeaf mode topSpecial rt lt acc t a c j r l state =
      (writeRippleCell t a c (rippleSecondBits mode (enabled && decide (L ≤ j ∧ j ≤ R))
        (readRippleCell t a c state)) state)[acc ↦ intervalAccumulatorBoundary enabled L R (j+1)] := by
  unfold intervalSecondLogicalLeaf
  dsimp only
  rw [hr, hl, hacc, second_phase enabled L R j horder, second_exit enabled L R j horder]
/-- A first-pass ripple cell with the inclusive control and its outgoing accumulator. -/
def intervalFirstInclusiveCell (mode : RippleMode) (enabled : Bool)
    (acc t a c L R j : Nat) (state : BasisState) : BasisState :=
  (writeRippleCell t a c (rippleFirstBits mode (enabled && decide (L ≤ j ∧ j ≤ R))
    (readRippleCell t a c state)) state)[acc ↦ intervalAccumulatorBoundary enabled L R j]

private theorem first_frame (mode : RippleMode) (enabled : Bool)
    (rt lt acc t a c L R j : Nat) (state : BasisState)
    (h : [rt,lt,acc,t,a,c].Nodup) :
    intervalFirstInclusiveCell mode enabled acc t a c L R j state acc =
        intervalAccumulatorBoundary enabled L R j ∧
      intervalFirstInclusiveCell mode enabled acc t a c L R j state rt = state rt ∧
      intervalFirstInclusiveCell mode enabled acc t a c L R j state lt = state lt := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  rcases h with ⟨⟨_,hra,hrt,hra',hrc⟩,⟨⟨hla,hlt,hla',hlc⟩,_⟩⟩
  simp [intervalFirstInclusiveCell, writeRippleCell, upd, hra, hrt, hra', hrc, hla, hlt, hla', hlc]

/-- A second-pass ripple cell with the inclusive control and its outgoing accumulator. -/
def intervalSecondInclusiveCell (mode : RippleMode) (enabled : Bool)
    (acc t a c L R j : Nat) (state : BasisState) : BasisState :=
  (writeRippleCell t a c (rippleSecondBits mode (enabled && decide (L ≤ j ∧ j ≤ R))
    (readRippleCell t a c state)) state)[acc ↦ intervalAccumulatorBoundary enabled L R (j+1)]

private theorem second_frame (mode : RippleMode) (enabled : Bool)
    (rt lt acc t a c L R j : Nat) (state : BasisState)
    (h : [rt,lt,acc,t,a,c].Nodup) :
    intervalSecondInclusiveCell mode enabled acc t a c L R j state acc =
        intervalAccumulatorBoundary enabled L R (j+1) ∧
      intervalSecondInclusiveCell mode enabled acc t a c L R j state rt = state rt ∧
      intervalSecondInclusiveCell mode enabled acc t a c L R j state lt = state lt := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  rcases h with ⟨⟨_,hra,hrt,hra',hrc⟩,⟨⟨hla,hlt,hla',hlc⟩,_⟩⟩
  simp [intervalSecondInclusiveCell, writeRippleCell, upd, hra, hrt, hra', hrc, hla, hlt, hla', hlc]

/-- The decreasing logical scan uses the inclusive control at every cell and ends
at the lower accumulator boundary. Endpoint pulses include the source zero-leaf mask. -/
theorem intervalFirstLogical_scan
    (mode : RippleMode) (topSpecial enabled rtValue ltValue : Bool)
    (rt lt acc carry L R lo n : Nat) (targetAt addendAt : Nat → Wire)
    (rightPulse leftPulse : Nat → Bool) (state : BasisState)
    (horder : L ≤ R)
    (hlayout : ∀ j, lo ≤ j → j < lo+n → [rt,lt,acc,targetAt j,addendAt j,carry].Nodup)
    (hright : ∀ j, lo ≤ j → j < lo+n →
      (rightPulse j && if maskedZeroLeaf topSpecial j then !rtValue else true) = (enabled && decide (j=R)))
    (hleft : ∀ j, lo ≤ j → j < lo+n →
      (leftPulse j && if maskedZeroLeaf topSpecial j then !ltValue else true) = (enabled && decide (j=L)))
    (hacc : state acc = intervalAccumulatorBoundary enabled L R (lo+n))
    (hrt : state rt = rtValue) (hlt : state lt = ltValue) :
    let result := (List.range' lo n).reverse.foldl (fun s j =>
      intervalFirstLogicalLeaf mode topSpecial rt lt acc (targetAt j) (addendAt j) carry j
        (rightPulse j) (leftPulse j) s) state
    result = (List.range' lo n).reverse.foldl (fun s j =>
        intervalFirstInclusiveCell mode enabled acc (targetAt j) (addendAt j) carry L R j s) state ∧
      result acc = intervalAccumulatorBoundary enabled L R lo ∧ result rt = rtValue ∧ result lt = ltValue := by
  induction n generalizing state with
  | zero => simpa using (show state = state ∧ state acc = intervalAccumulatorBoundary enabled L R lo ∧
        state rt = rtValue ∧ state lt = ltValue from ⟨rfl, by simpa using hacc, hrt, hlt⟩)
  | succ n ih =>
    have hj : lo+n < lo+(n+1) := by omega
    have hlow : lo ≤ lo+n := by omega
    have hc := first_cell mode topSpecial enabled (rightPulse (lo+n)) (leftPulse (lo+n))
      rt lt acc (targetAt (lo+n)) (addendAt (lo+n)) carry L R (lo+n) state horder
      (by simpa [Nat.add_assoc] using hacc)
      (by simpa [hrt] using hright (lo+n) hlow hj)
      (by simpa [hlt] using hleft (lo+n) hlow hj)
    change intervalFirstLogicalLeaf _ _ _ _ _ _ _ _ _ _ _ _ =
      intervalFirstInclusiveCell mode enabled acc (targetAt (lo+n)) (addendAt (lo+n)) carry L R (lo+n) state at hc
    let next := intervalFirstInclusiveCell mode enabled acc (targetAt (lo+n)) (addendAt (lo+n)) carry L R (lo+n) state
    have hf := first_frame mode enabled rt lt acc (targetAt (lo+n)) (addendAt (lo+n)) carry L R (lo+n) state
      (hlayout (lo+n) hlow hj)
    have hi := ih next
      (fun j h1 h2 => hlayout j h1 (by omega))
      (fun j h1 h2 => hright j h1 (by omega))
      (fun j h1 h2 => hleft j h1 (by omega))
      hf.1 (hf.2.1.trans hrt) (hf.2.2.trans hlt)
    simpa only [List.range'_concat, Nat.one_mul, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.cons_append, List.nil_append, List.foldl_cons, hc, next] using hi

/-- The increasing logical scan uses the inclusive control at every cell and ends
at the upper accumulator boundary. Endpoint pulses include the source zero-leaf mask. -/
theorem intervalSecondLogical_scan
    (mode : RippleMode) (topSpecial enabled rtValue ltValue : Bool)
    (rt lt acc carry L R lo n : Nat) (targetAt addendAt : Nat → Wire)
    (rightPulse leftPulse : Nat → Bool) (state : BasisState)
    (horder : L ≤ R)
    (hlayout : ∀ j, lo ≤ j → j < lo+n → [rt,lt,acc,targetAt j,addendAt j,carry].Nodup)
    (hright : ∀ j, lo ≤ j → j < lo+n →
      (rightPulse j && if maskedZeroLeaf topSpecial j then !rtValue else true) = (enabled && decide (j=R)))
    (hleft : ∀ j, lo ≤ j → j < lo+n →
      (leftPulse j && if maskedZeroLeaf topSpecial j then !ltValue else true) = (enabled && decide (j=L)))
    (hacc : state acc = intervalAccumulatorBoundary enabled L R lo)
    (hrt : state rt = rtValue) (hlt : state lt = ltValue) :
    let result := (List.range' lo n).foldl (fun s j =>
      intervalSecondLogicalLeaf mode topSpecial rt lt acc (targetAt j) (addendAt j) carry j
        (rightPulse j) (leftPulse j) s) state
    result = (List.range' lo n).foldl (fun s j =>
        intervalSecondInclusiveCell mode enabled acc (targetAt j) (addendAt j) carry L R j s) state ∧
      result acc = intervalAccumulatorBoundary enabled L R (lo+n) ∧ result rt = rtValue ∧ result lt = ltValue := by
  induction n generalizing lo state with
  | zero => simpa using (show state = state ∧ state acc = intervalAccumulatorBoundary enabled L R lo ∧
        state rt = rtValue ∧ state lt = ltValue from ⟨rfl, hacc, hrt, hlt⟩)
  | succ n ih =>
    have hj : lo < lo+(n+1) := by omega
    have hc := second_cell mode topSpecial enabled (rightPulse lo) (leftPulse lo)
      rt lt acc (targetAt lo) (addendAt lo) carry L R lo state horder hacc
      (by simpa [hrt] using hright lo (by omega) hj)
      (by simpa [hlt] using hleft lo (by omega) hj)
    change intervalSecondLogicalLeaf _ _ _ _ _ _ _ _ _ _ _ _ =
      intervalSecondInclusiveCell mode enabled acc (targetAt lo) (addendAt lo) carry L R lo state at hc
    let next := intervalSecondInclusiveCell mode enabled acc (targetAt lo) (addendAt lo) carry L R lo state
    have hf := second_frame mode enabled rt lt acc (targetAt lo) (addendAt lo) carry L R lo state
      (hlayout lo (by omega) hj)
    have hi := ih (lo+1) next
      (fun j h1 h2 => hlayout j (by omega) (by omega))
      (fun j h1 h2 => hright j (by omega) (by omega))
      (fun j h1 h2 => hleft j (by omega) (by omega))
      hf.1 (hf.2.1.trans hrt) (hf.2.2.trans hlt)
    simpa only [List.range'_succ, List.foldl_cons, hc, next, Nat.add_assoc,
      Nat.add_comm 1 n] using hi

/-- The same physical first traversal enables exactly the inclusive interval.
The endpoint-pulse interpretation and incoming accumulator boundary are explicit. -/
theorem run_intervalFirstTraversal_inclusiveScan
    (mode : RippleMode) (topSpecial enabled : Bool)
    (rt lt acc carry scratch L R lo n : Nat) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rc lc : Wire) (rp lp : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rc lc rp lp rt lt acc carry scratch targetAt addendAt)
    (hlabels : tree.labels = List.range' lo n) (horder : L ≤ R)
    (hcleanR : Clean rp state) (hcleanL : Clean lp state) (hcleanScratch : Clean [scratch] state)
    (hacc : state acc = intervalAccumulatorBoundary enabled L R (lo+n))
    (hright : ∀ j, lo ≤ j → j < lo+n →
      ((state rc && decide (j = (tree.project false).routeLabel state)) &&
        if maskedZeroLeaf topSpecial j then !state rt else true) = (enabled && decide (j=R)))
    (hleft : ∀ j, lo ≤ j → j < lo+n →
      ((state lc && decide (j = (tree.project true).routeLabel state)) &&
        if maskedZeroLeaf topSpecial j then !state lt else true) = (enabled && decide (j=L))) :
    let result := run (intervalFirstTraversal mode topSpecial rt lt acc carry scratch
      targetAt addendAt tree rc lc rp lp) state
    result = (List.range' lo n).reverse.foldl (fun s j =>
        intervalFirstInclusiveCell mode enabled acc (targetAt j) (addendAt j) carry L R j s) state ∧
      result acc = intervalAccumulatorBoundary enabled L R lo := by
  have hnd : tree.labels.Nodup := by rw [hlabels]; exact List.nodup_range'
  have hr := run_intervalFirstTraversal_as_routedFold mode topSpecial rt lt acc carry scratch
    targetAt addendAt tree rc lc rp lp state hlayout hnd hcleanR hcleanL hcleanScratch
  rw [DualUnaryActionTree.visitLabels_dec, hlabels] at hr
  have hs := intervalFirstLogical_scan mode topSpecial enabled (state rt) (state lt)
    rt lt acc carry L R lo n targetAt addendAt
    (fun j => state rc && decide (j = (tree.project false).routeLabel state))
    (fun j => state lc && decide (j = (tree.project true).routeLabel state)) state horder
    (fun j h1 h2 => ?_) hright hleft hacc rfl rfl
  · dsimp only
    rw [hr]
    exact ⟨hs.1, hs.2.1⟩
  · have hj : j ∈ tree.labels := by
      rw [hlabels, List.mem_range']
      exact ⟨j-lo, by omega, by omega⟩
    exact (List.nodup_append.mp (show ([rt,lt,acc,targetAt j,addendAt j,carry] ++ [scratch]).Nodup
      from (hlayout.2 j hj).1)).1

/-- The same physical second traversal enables exactly the inclusive interval.
The endpoint-pulse interpretation and incoming accumulator boundary are explicit. -/
theorem run_intervalSecondTraversal_inclusiveScan
    (mode : RippleMode) (topSpecial enabled : Bool)
    (rt lt acc carry scratch L R lo n : Nat) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rc lc : Wire) (rp lp : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rc lc rp lp rt lt acc carry scratch targetAt addendAt)
    (hlabels : tree.labels = List.range' lo n) (horder : L ≤ R)
    (hcleanR : Clean rp state) (hcleanL : Clean lp state) (hcleanScratch : Clean [scratch] state)
    (hacc : state acc = intervalAccumulatorBoundary enabled L R lo)
    (hright : ∀ j, lo ≤ j → j < lo+n →
      ((state rc && decide (j = (tree.project false).routeLabel state)) &&
        if maskedZeroLeaf topSpecial j then !state rt else true) = (enabled && decide (j=R)))
    (hleft : ∀ j, lo ≤ j → j < lo+n →
      ((state lc && decide (j = (tree.project true).routeLabel state)) &&
        if maskedZeroLeaf topSpecial j then !state lt else true) = (enabled && decide (j=L))) :
    let result := run (intervalSecondTraversal mode topSpecial rt lt acc carry scratch
      targetAt addendAt tree rc lc rp lp) state
    result = (List.range' lo n).foldl (fun s j =>
        intervalSecondInclusiveCell mode enabled acc (targetAt j) (addendAt j) carry L R j s) state ∧
      result acc = intervalAccumulatorBoundary enabled L R (lo+n) := by
  have hnd : tree.labels.Nodup := by rw [hlabels]; exact List.nodup_range'
  have hr := run_intervalSecondTraversal_as_routedFold mode topSpecial rt lt acc carry scratch
    targetAt addendAt tree rc lc rp lp state hlayout hnd hcleanR hcleanL hcleanScratch
  rw [DualUnaryActionTree.visitLabels_inc, hlabels] at hr
  have hs := intervalSecondLogical_scan mode topSpecial enabled (state rt) (state lt)
    rt lt acc carry L R lo n targetAt addendAt
    (fun j => state rc && decide (j = (tree.project false).routeLabel state))
    (fun j => state lc && decide (j = (tree.project true).routeLabel state)) state horder
    (fun j h1 h2 => ?_) hright hleft hacc rfl rfl
  · dsimp only
    rw [hr]
    exact ⟨hs.1, hs.2.1⟩
  · have hj : j ∈ tree.labels := by
      rw [hlabels, List.mem_range']
      exact ⟨j-lo, by omega, by omega⟩
    exact (List.nodup_append.mp (show ([rt,lt,acc,targetAt j,addendAt j,carry] ++ [scratch]).Nodup
      from (hlayout.2 j hj).1)).1

end ShorECDLP.Paper2607_13816
