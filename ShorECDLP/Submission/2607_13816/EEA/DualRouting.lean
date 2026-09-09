import ShorECDLP.Submission.«2607_13816».EEA.Interval
import ShorECDLP.Submission.«2607_13816».EEA.QuotientSwap

/-! # Numeric routing of both interval endpoint banks -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

theorem sourceTree_routeResidue
    (indexA indexB : Nat → Wire) (tree : DualUnaryActionTree) (labels : Finset Nat)
    (register : List Wire) (second : Bool) (width : Nat) (state : BasisState)
    (hbuild : DualUnaryActionTree.buildSource indexA indexB labels = some tree)
    (hindex : ∀ bit, (if second then indexB bit else indexA bit) = register.getD bit 0)
    (hsource : DualUnaryActionTree.sourceWidth labels ≤ width)
    (hwidth : width ≤ register.length)
    (hvalue : boolWordToNat (wireValues register state) % 2^width ∈ labels) :
    (tree.project second).routeLabel state =
      boolWordToNat (wireValues register state) % 2^width := by
  have hb := DualUnaryActionTree.build_sourceBuilt indexA indexB
    (DualUnaryActionTree.sourceWidth labels) labels tree hbuild
  apply DualUnaryActionTree.project_routeLabel_of_sourceBuilt second hb (by simp) state
  · rw [DualUnaryActionTree.buildSource_labels_eq_sort indexA indexB labels tree hbuild]
    simpa using hvalue
  · intro bit hbit
    have hr : bit < register.length := lt_of_lt_of_le hbit (hsource.trans hwidth)
    have hv : bit < (wireValues register state).length := by simpa [wireValues] using hr
    have hbitWidth : bit < width := lt_of_lt_of_le hbit hsource
    rw [hindex, Nat.testBit_mod_two_pow]
    simp only [hbitWidth, decide_true, Bool.true_and]
    calc
      state (register.getD bit 0) = (wireValues register state).getD bit false := by
        rw [List.getD_eq_getElem _ _ hr, List.getD_eq_getElem _ _ hv]
        simp only [wireValues, List.getElem_map]
      _ = (boolWordToNat (wireValues register state)).testBit bit :=
        getD_false_eq_testBit_boolWordToNat _ hv

/-- The main decoder reads only its source width of each endpoint bank. Its projected
routes are the corresponding residues when those residues belong to the main label set.
The source leaf mask separately distinguishes a top endpoint from an ordinary zero endpoint. -/
theorem intervalTree_routeResidues (registers : IntervalRegisters) (k K : Nat) (state : BasisState)
    (hrWidth : DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤
      registers.lengthS.length)
    (hlWidth : DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤
      registers.lengthQ.length)
    (hrValue : boolWordToNat (wireValues registers.lengthS state) %
      2^DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ∈ intervalMainLabels k K)
    (hlValue : boolWordToNat (wireValues registers.lengthQ state) %
      2^DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ∈ intervalMainLabels k K) :
    ((intervalTree registers k K).project false).routeLabel state =
        boolWordToNat (wireValues registers.lengthS state) %
          2^DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ∧
      ((intervalTree registers k K).project true).routeLabel state =
        boolWordToNat (wireValues registers.lengthQ state) %
          2^DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset := by
  have hb := intervalTree_built registers k K
  constructor
  · exact sourceTree_routeResidue registers.rightIndex registers.leftIndex _ _
      registers.lengthS false (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      state hb (by intro bit; rfl) (by rfl) hrWidth (by simpa using hrValue)
  · exact sourceTree_routeResidue registers.rightIndex registers.leftIndex _ _
      registers.lengthQ true (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      state hb (by intro bit; rfl) (by rfl) hlWidth (by simpa using hlValue)

/-- For endpoints in the main label set, both projected routes equal the full numeric words. -/
theorem intervalTree_routeLabels (registers : IntervalRegisters) (k K : Nat) (state : BasisState)
    (hrWidth : DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤
      registers.lengthS.length)
    (hlWidth : DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤
      registers.lengthQ.length)
    (hrValue : boolWordToNat (wireValues registers.lengthS state) ∈ intervalMainLabels k K)
    (hlValue : boolWordToNat (wireValues registers.lengthQ state) ∈ intervalMainLabels k K) :
    ((intervalTree registers k K).project false).routeLabel state =
        boolWordToNat (wireValues registers.lengthS state) ∧
      ((intervalTree registers k K).project true).routeLabel state =
        boolWordToNat (wireValues registers.lengthQ state) := by
  have hrBound := DualUnaryActionTree.label_lt_two_pow_sourceWidth
    (intervalMainLabels k K).toFinset _ (by simpa using hrValue)
  have hlBound := DualUnaryActionTree.label_lt_two_pow_sourceWidth
    (intervalMainLabels k K).toFinset _ (by simpa using hlValue)
  have hrMod := Nat.mod_eq_of_lt hrBound
  have hlMod := Nat.mod_eq_of_lt hlBound
  have hh := intervalTree_routeResidues registers k K state hrWidth hlWidth
    (by simpa only [hrMod] using hrValue) (by simpa only [hlMod] using hlValue)
  simpa only [hrMod, hlMod] using hh

private theorem project_labels (tree : DualUnaryActionTree) (second : Bool) :
    (tree.project second).labels = tree.labels := by
  induction tree with
  | leaf => rfl
  | node a b zero one ihz iho =>
    simp [DualUnaryActionTree.project, UnaryActionTree.labels,
      DualUnaryActionTree.labels, ihz, iho]

/-- A singleton main tree always routes to zero, independently of either endpoint word.
This also covers the source's one-lane main tree beneath a special top lane. -/
theorem intervalTree_singleton_route (registers : IntervalRegisters) (k K : Nat)
    (state : BasisState) (second : Bool) (hmain : intervalMainLabels k K = [0]) :
    ((intervalTree registers k K).project second).routeLabel state = 0 := by
  have hm := UnaryActionTree.routeLabel_mem_labels
    ((intervalTree registers k K).project second) state
  rw [project_labels] at hm
  have hb := DualUnaryActionTree.buildSource_labels_eq_sort registers.rightIndex registers.leftIndex
    (intervalMainLabels k K).toFinset (intervalTree registers k K) (intervalTree_built registers k K)
  rw [hb] at hm
  simpa [hmain] using hm

end
end ShorECDLP.Paper2607_13816
