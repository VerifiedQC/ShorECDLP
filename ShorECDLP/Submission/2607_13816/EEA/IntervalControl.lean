import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf

/-! # Inclusive interval control at the two source leaf passes -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem first_phase (enabled : Bool) (L R j : Nat) (h : L ≤ R) :
    ((enabled && decide (L ≤ j ∧ j < R)) ^^ (enabled && decide (j=R))) =
      (enabled && decide (L ≤ j ∧ j ≤ R)) := by
  cases enabled <;> by_cases hlj : L ≤ j <;> by_cases hjr : j < R <;>
    by_cases he : j=R <;> simp_all <;> omega
private theorem second_phase (enabled : Bool) (L R j : Nat) (h : L ≤ R) :
    ((enabled && decide (L < j ∧ j ≤ R)) ^^ (enabled && decide (j=L))) =
      (enabled && decide (L ≤ j ∧ j ≤ R)) := by
  cases enabled <;> by_cases hlj : L < j <;> by_cases hjr : j ≤ R <;>
    by_cases he : j=L <;> simp_all <;> omega

theorem intervalFirstLeafState_normalize
    (mode : RippleMode) (topSpecial : Bool)
    (rt lt acc t a c scratch label rc lc : Nat) (state : BasisState)
    (hlayout : IntervalLeafLayout rc lc rt lt acc t a c scratch) :
    intervalFirstLeafState mode topSpecial rt lt acc t a c label rc lc state =
      let r := state rc && if maskedZeroLeaf topSpecial label then !state rt else true
      let l := state lc && if maskedZeroLeaf topSpecial label then !state lt else true
      (writeRippleCell t a c (rippleFirstBits mode (state acc ^^ r)
        (readRippleCell t a c state)) state)[acc ↦ state acc ^^ r ^^ l] := by
  have hp := List.nodup_append.mp hlayout
  have hr := hp.2.1
  have hlc : lc ∈ [rc,lc].dedup := by simp
  have hc1 : lc ≠ acc := hp.2.2 lc hlc acc (by simp)
  have hc2 : lc ≠ t := hp.2.2 lc hlc t (by simp)
  have hc3 : lc ≠ a := hp.2.2 lc hlc a (by simp)
  have hc4 : lc ≠ c := hp.2.2 lc hlc c (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rcases hr with ⟨⟨_,_,_,_,_,_⟩,⟨⟨hla,hlt,hla',hlc',_⟩,⟨⟨hat,haa,hac,_⟩,_⟩⟩⟩
  funext w
  simp only [intervalFirstLeafState, endpointLeafToggleState, readRippleCell,
    writeRippleCell, upd]
  simp only [hc1,hc2,hc3,hc4,hlt,hla',hlc',
    hat,haa,hac,Ne.symm hat,Ne.symm haa,Ne.symm hac, ite_false, ite_true]
  by_cases hw : w=acc <;> by_cases hwt : w=t <;> by_cases hwa : w=a <;>
    by_cases hwc : w=c <;> simp_all
theorem intervalSecondLeafState_normalize
    (mode : RippleMode) (topSpecial : Bool)
    (rt lt acc t a c scratch label rc lc : Nat) (state : BasisState)
    (hlayout : IntervalLeafLayout rc lc rt lt acc t a c scratch) :
    intervalSecondLeafState mode topSpecial rt lt acc t a c label rc lc state =
      let r := state rc && if maskedZeroLeaf topSpecial label then !state rt else true
      let l := state lc && if maskedZeroLeaf topSpecial label then !state lt else true
      (writeRippleCell t a c (rippleSecondBits mode (state acc ^^ l)
        (readRippleCell t a c state)) state)[acc ↦ state acc ^^ l ^^ r] := by
  have hp := List.nodup_append.mp hlayout
  have hr := hp.2.1
  have hlc : rc ∈ [rc,lc].dedup := by simp
  have hc1 : rc ≠ acc := hp.2.2 rc hlc acc (by simp)
  have hc2 : rc ≠ t := hp.2.2 rc hlc t (by simp)
  have hc3 : rc ≠ a := hp.2.2 rc hlc a (by simp)
  have hc4 : rc ≠ c := hp.2.2 rc hlc c (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rcases hr with ⟨⟨_,hla,hlt,hla',hlc',_⟩,⟨_,⟨⟨hat,haa,hac,_⟩,_⟩⟩⟩
  funext w
  simp only [intervalSecondLeafState, endpointLeafToggleState, readRippleCell,
    writeRippleCell, upd]
  simp only [hc1,hc2,hc3,hc4,hlt,hla',hlc',
    hat,haa,hac,Ne.symm hat,Ne.symm haa,Ne.symm hac, ite_false, ite_true]
  by_cases hw : w=acc <;> by_cases hwt : w=t <;> by_cases hwa : w=a <;>
    by_cases hwc : w=c <;> simp_all

/-- A decreasing-pass source leaf enables its ripple cell exactly on the inclusive
interval and advances the accumulator to the predicate needed by the next lower label.
The effective endpoint switches include the source's special zero-leaf mask. -/
theorem intervalFirstLeaf_inclusive
    (mode : RippleMode) (topSpecial enabled : Bool)
    (rt lt acc t a c scratch label rc lc L R : Nat) (state : BasisState)
    (hlayout : IntervalLeafLayout rc lc rt lt acc t a c scratch)
    (hclean : state scratch = false) (horder : L ≤ R)
    (hacc : state acc = (enabled && decide (L ≤ label ∧ label < R)))
    (hright : (state rc && if maskedZeroLeaf topSpecial label then !state rt else true) =
      (enabled && decide (label=R)))
    (hleft : (state lc && if maskedZeroLeaf topSpecial label then !state lt else true) =
      (enabled && decide (label=L))) :
    run (intervalFirstLeaf mode topSpecial rt lt acc t a c scratch label rc lc) state =
      (writeRippleCell t a c
        (rippleFirstBits mode (enabled && decide (L ≤ label ∧ label ≤ R))
          (readRippleCell t a c state)) state)
        [acc ↦ enabled && decide (L < label ∧ label ≤ R)] := by
  rw [run_intervalFirstLeaf _ _ _ _ _ _ _ _ _ _ _ _ _ hlayout hclean,
    intervalFirstLeafState_normalize _ _ _ _ _ _ _ _ _ _ _ _ _ hlayout]
  dsimp only
  rw [hright, hleft, hacc, first_phase enabled L R label horder]
  have hh := congrArg (fun b => b ^^ (enabled && decide (label=L)))
    (second_phase enabled L R label horder)
  have hexit : ((enabled && decide (L ≤ label ∧ label ≤ R)) ^^
      (enabled && decide (label=L))) = (enabled && decide (L < label ∧ label ≤ R)) := by
    simpa using hh.symm
  rw [hexit]

/-- The increasing-pass source leaf uses the same inclusive interval and restores the
opposite accumulator phase, ready for the next higher label. -/
theorem intervalSecondLeaf_inclusive
    (mode : RippleMode) (topSpecial enabled : Bool)
    (rt lt acc t a c scratch label rc lc L R : Nat) (state : BasisState)
    (hlayout : IntervalLeafLayout rc lc rt lt acc t a c scratch)
    (hclean : state scratch = false) (horder : L ≤ R)
    (hacc : state acc = (enabled && decide (L < label ∧ label ≤ R)))
    (hright : (state rc && if maskedZeroLeaf topSpecial label then !state rt else true) =
      (enabled && decide (label=R)))
    (hleft : (state lc && if maskedZeroLeaf topSpecial label then !state lt else true) =
      (enabled && decide (label=L))) :
    run (intervalSecondLeaf mode topSpecial rt lt acc t a c scratch label rc lc) state =
      (writeRippleCell t a c
        (rippleSecondBits mode (enabled && decide (L ≤ label ∧ label ≤ R))
          (readRippleCell t a c state)) state)
        [acc ↦ enabled && decide (L ≤ label ∧ label < R)] := by
  rw [run_intervalSecondLeaf _ _ _ _ _ _ _ _ _ _ _ _ _ hlayout hclean,
    intervalSecondLeafState_normalize _ _ _ _ _ _ _ _ _ _ _ _ _ hlayout]
  dsimp only
  rw [hright, hleft, hacc, second_phase enabled L R label horder]
  have hh := congrArg (fun b => b ^^ (enabled && decide (label=R)))
    (first_phase enabled L R label horder)
  have hexit : ((enabled && decide (L ≤ label ∧ label ≤ R)) ^^
      (enabled && decide (label=R))) = (enabled && decide (L ≤ label ∧ label < R)) := by
    simpa using hh.symm
  rw [hexit]

end ShorECDLP.Paper2607_13816
