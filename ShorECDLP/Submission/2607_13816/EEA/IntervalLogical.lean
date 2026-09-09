import ShorECDLP.Submission.«2607_13816».EEA.IntervalControl
import ShorECDLP.Submission.«2607_13816».EEA.DualPulses

/-! # Physical interval traversals as routed ripple scans -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

/-- One source first-pass cell, with Boolean endpoint pulses instead of decoder wires. -/
def intervalFirstLogicalLeaf
    (mode : RippleMode) (topSpecial : Bool) (rt lt acc t a c label : Nat)
    (rightPulse leftPulse : Bool) (state : BasisState) : BasisState :=
  let r := rightPulse && if maskedZeroLeaf topSpecial label then !state rt else true
  let l := leftPulse && if maskedZeroLeaf topSpecial label then !state lt else true
  (writeRippleCell t a c (rippleFirstBits mode (state acc ^^ r)
    (readRippleCell t a c state)) state)[acc ↦ state acc ^^ r ^^ l]

/-- One source second-pass cell, with Boolean endpoint pulses instead of decoder wires. -/
def intervalSecondLogicalLeaf
    (mode : RippleMode) (topSpecial : Bool) (rt lt acc t a c label : Nat)
    (rightPulse leftPulse : Bool) (state : BasisState) : BasisState :=
  let r := rightPulse && if maskedZeroLeaf topSpecial label then !state rt else true
  let l := leftPulse && if maskedZeroLeaf topSpecial label then !state lt else true
  (writeRippleCell t a c (rippleSecondBits mode (state acc ^^ l)
    (readRippleCell t a c state)) state)[acc ↦ state acc ^^ l ^^ r]

private theorem roles_outside
    (D : List Wire) (rt lt acc t a c scratch : Nat)
    (hroles : [rt,lt,acc,t,a,c,scratch].Nodup)
    (houtside : DecoderOutsideIntervalRoles D rt lt acc t a c scratch) :
    ∀ w ∈ [rt,lt,acc,t,a,c], w ∉ D ++ [scratch] := by
  have hs := List.nodup_append.mp (show ([rt,lt,acc,t,a,c] ++ [scratch]).Nodup from hroles)
  intro w hw hmem
  rcases List.mem_append.mp hmem with hd | hd
  · exact List.disjoint_left.mp houtside hd (List.mem_append_left [scratch] hw)
  · have he : w = scratch := by simpa using hd
    exact hs.2.2 w hw scratch (by simp) he

private theorem first_simulation
    (mode : RippleMode) (topSpecial : Bool) (D : List Wire)
    (rt lt acc t a c scratch label rc lc : Nat) (s v : BasisState)
    (hroles : [rt,lt,acc,t,a,c,scratch].Nodup)
    (houtside : DecoderOutsideIntervalRoles D rt lt acc t a c scratch)
    (hrc : rc ∈ D) (hlc : lc ∈ D)
    (hclean : Clean [scratch] s) (hag : AgreesOutside (D ++ [scratch]) s v) :
    AgreesOutside (D ++ [scratch])
      (run (intervalFirstLeaf mode topSpecial rt lt acc t a c scratch label rc lc) s)
      (intervalFirstLogicalLeaf mode topSpecial rt lt acc t a c label (s rc) (s lc) v) := by
  have hlay := intervalLeafLayout_of_decoderRoles D rc lc rt lt acc t a c scratch
    hroles houtside hrc hlc
  rw [run_intervalFirstLeaf _ _ _ _ _ _ _ _ _ _ _ _ _ hlay (hclean scratch (by simp)),
    intervalFirstLeafState_normalize _ _ _ _ _ _ _ _ _ _ _ _ _ hlay]
  have ho := roles_outside D rt lt acc t a c scratch hroles houtside
  have hrt := hag rt (ho rt (by simp))
  have hlt := hag lt (ho lt (by simp))
  have hac := hag acc (ho acc (by simp))
  have ht := hag t (ho t (by simp))
  have ha := hag a (ho a (by simp))
  have hc := hag c (ho c (by simp))
  intro w hw
  have hh := hag w hw
  simp only [intervalFirstLogicalLeaf, readRippleCell, writeRippleCell, upd]
  simp only [hrt,hlt,hac,ht,ha,hc,hh]

private theorem first_preserves
    (mode : RippleMode) (topSpecial : Bool) (D : List Wire)
    (rt lt acc t a c scratch label : Nat) (r l : Bool) (s : BasisState)
    (hroles : [rt,lt,acc,t,a,c,scratch].Nodup)
    (houtside : DecoderOutsideIntervalRoles D rt lt acc t a c scratch) :
    ∀ w ∈ D ++ [scratch], intervalFirstLogicalLeaf mode topSpecial rt lt acc t a c label r l s w = s w := by
  intro w hw
  have ho := roles_outside D rt lt acc t a c scratch hroles houtside
  have hacc : w ≠ acc := fun h => ho acc (by simp) (h ▸ hw)
  have ht : w ≠ t := fun h => ho t (by simp) (h ▸ hw)
  have ha : w ≠ a := fun h => ho a (by simp) (h ▸ hw)
  have hc : w ≠ c := fun h => ho c (by simp) (h ▸ hw)
  simp [intervalFirstLogicalLeaf, writeRippleCell, upd, hacc, ht, ha, hc]

private theorem second_simulation
    (mode : RippleMode) (topSpecial : Bool) (D : List Wire)
    (rt lt acc t a c scratch label rc lc : Nat) (s v : BasisState)
    (hroles : [rt,lt,acc,t,a,c,scratch].Nodup)
    (houtside : DecoderOutsideIntervalRoles D rt lt acc t a c scratch)
    (hrc : rc ∈ D) (hlc : lc ∈ D)
    (hclean : Clean [scratch] s) (hag : AgreesOutside (D ++ [scratch]) s v) :
    AgreesOutside (D ++ [scratch])
      (run (intervalSecondLeaf mode topSpecial rt lt acc t a c scratch label rc lc) s)
      (intervalSecondLogicalLeaf mode topSpecial rt lt acc t a c label (s rc) (s lc) v) := by
  have hlay := intervalLeafLayout_of_decoderRoles D rc lc rt lt acc t a c scratch
    hroles houtside hrc hlc
  rw [run_intervalSecondLeaf _ _ _ _ _ _ _ _ _ _ _ _ _ hlay (hclean scratch (by simp)),
    intervalSecondLeafState_normalize _ _ _ _ _ _ _ _ _ _ _ _ _ hlay]
  have ho := roles_outside D rt lt acc t a c scratch hroles houtside
  have hrt := hag rt (ho rt (by simp))
  have hlt := hag lt (ho lt (by simp))
  have hac := hag acc (ho acc (by simp))
  have ht := hag t (ho t (by simp))
  have ha := hag a (ho a (by simp))
  have hc := hag c (ho c (by simp))
  intro w hw
  have hh := hag w hw
  simp only [intervalSecondLogicalLeaf, readRippleCell, writeRippleCell, upd]
  simp only [hrt,hlt,hac,ht,ha,hc,hh]

private theorem second_preserves
    (mode : RippleMode) (topSpecial : Bool) (D : List Wire)
    (rt lt acc t a c scratch label : Nat) (r l : Bool) (s : BasisState)
    (hroles : [rt,lt,acc,t,a,c,scratch].Nodup)
    (houtside : DecoderOutsideIntervalRoles D rt lt acc t a c scratch) :
    ∀ w ∈ D ++ [scratch], intervalSecondLogicalLeaf mode topSpecial rt lt acc t a c label r l s w = s w := by
  intro w hw
  have ho := roles_outside D rt lt acc t a c scratch hroles houtside
  have hacc : w ≠ acc := fun h => ho acc (by simp) (h ▸ hw)
  have ht : w ≠ t := fun h => ho t (by simp) (h ▸ hw)
  have ha : w ≠ a := fun h => ho a (by simp) (h ▸ hw)
  have hc : w ≠ c := fun h => ho c (by simp) (h ▸ hw)
  simp [intervalSecondLogicalLeaf, writeRippleCell, upd, hacc, ht, ha, hc]

/-- The actual first interval traversal is a routed ripple scan in source visit order.
The decoder, path stacks and cell scratch are restored in this complete-state equality. -/
theorem run_intervalFirstTraversal_as_routedFold
    (mode : RippleMode) (topSpecial : Bool)
    (rt lt acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rc lc : Wire) (rp lp : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rc lc rp lp rt lt acc carry scratch targetAt addendAt)
    (hnodup : tree.labels.Nodup)
    (hcleanR : Clean rp state) (hcleanL : Clean lp state) (hcleanScratch : Clean [scratch] state) :
    run (intervalFirstTraversal mode topSpecial rt lt acc carry scratch targetAt addendAt
      tree rc lc rp lp) state =
      (tree.visitLabels .dec).foldl (fun s label =>
        intervalFirstLogicalLeaf mode topSpecial rt lt acc (targetAt label) (addendAt label) carry label
          (state rc && decide (label = (tree.project false).routeLabel state))
          (state lc && decide (label = (tree.project true).routeLabel state)) s) state := by
  let D := tree.decoderWires rc lc rp lp
  have hscratch : scratch ∉ rp ++ lp := by
    have hn := List.nodup_append.mp (intervalTraversalLayout_decoderScratch tree rc lc rp lp
      rt lt acc carry scratch targetAt addendAt hlayout)
    intro hm
    have hd : scratch ∈ D := by
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hm))
    exact hn.2.2 scratch hd scratch (by simp) rfl
  apply run_dualUnaryActionUnitary_as_routedFold .dec _ _ tree rc lc rp lp
    D (D ++ [scratch]) ([scratch] : List Wire) state hnodup hlayout.1
  · exact intervalFirstLeafFamily_dualPreservesWithScratch mode topSpecial rt lt acc carry scratch
      targetAt addendAt tree.labels D hlayout.2
  · intro label hl a b ha hb s t hc hag
    exact first_simulation mode topSpecial D rt lt acc (targetAt label) (addendAt label)
      carry scratch label a b s t (hlayout.2 label hl).1 (hlayout.2 label hl).2 ha hb hc hag
  · intro label hl a b s w hw
    exact first_preserves mode topSpecial D rt lt acc (targetAt label) (addendAt label)
      carry scratch label a b s (hlayout.2 label hl).1 (hlayout.2 label hl).2 w hw
  · exact fun _ hw => List.mem_append_left _ hw
  · exact fun _ hw => hw
  · exact fun _ hw => List.mem_append_left _ hw
  · exact hcleanR
  · exact hcleanL
  · exact fun _ hw => List.mem_append_right _ hw
  · intro w hw
    have he : w = scratch := by simpa using hw
    simpa [he] using hscratch
  · exact hcleanScratch

/-- The actual second interval traversal is a routed ripple scan in source visit order.
The decoder, path stacks and cell scratch are restored in this complete-state equality. -/
theorem run_intervalSecondTraversal_as_routedFold
    (mode : RippleMode) (topSpecial : Bool)
    (rt lt acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rc lc : Wire) (rp lp : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rc lc rp lp rt lt acc carry scratch targetAt addendAt)
    (hnodup : tree.labels.Nodup)
    (hcleanR : Clean rp state) (hcleanL : Clean lp state) (hcleanScratch : Clean [scratch] state) :
    run (intervalSecondTraversal mode topSpecial rt lt acc carry scratch targetAt addendAt
      tree rc lc rp lp) state =
      (tree.visitLabels .inc).foldl (fun s label =>
        intervalSecondLogicalLeaf mode topSpecial rt lt acc (targetAt label) (addendAt label) carry label
          (state rc && decide (label = (tree.project false).routeLabel state))
          (state lc && decide (label = (tree.project true).routeLabel state)) s) state := by
  let D := tree.decoderWires rc lc rp lp
  have hscratch : scratch ∉ rp ++ lp := by
    have hn := List.nodup_append.mp (intervalTraversalLayout_decoderScratch tree rc lc rp lp
      rt lt acc carry scratch targetAt addendAt hlayout)
    intro hm
    have hd : scratch ∈ D := by
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hm))
    exact hn.2.2 scratch hd scratch (by simp) rfl
  apply run_dualUnaryActionUnitary_as_routedFold .inc _ _ tree rc lc rp lp
    D (D ++ [scratch]) ([scratch] : List Wire) state hnodup hlayout.1
  · exact intervalSecondLeafFamily_dualPreservesWithScratch mode topSpecial rt lt acc carry scratch
      targetAt addendAt tree.labels D hlayout.2
  · intro label hl a b ha hb s t hc hag
    exact second_simulation mode topSpecial D rt lt acc (targetAt label) (addendAt label)
      carry scratch label a b s t (hlayout.2 label hl).1 (hlayout.2 label hl).2 ha hb hc hag
  · intro label hl a b s w hw
    exact second_preserves mode topSpecial D rt lt acc (targetAt label) (addendAt label)
      carry scratch label a b s (hlayout.2 label hl).1 (hlayout.2 label hl).2 w hw
  · exact fun _ hw => List.mem_append_left _ hw
  · exact fun _ hw => hw
  · exact fun _ hw => List.mem_append_left _ hw
  · exact hcleanR
  · exact hcleanL
  · exact fun _ hw => List.mem_append_right _ hw
  · intro w hw
    have he : w = scratch := by simpa using hw
    simpa [he] using hscratch
  · exact hcleanScratch

end ShorECDLP.Paper2607_13816
