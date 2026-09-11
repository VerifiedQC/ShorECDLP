import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceTransforms
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledAdd
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledLT
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantCompare
namespace ShorECDLP.Paper2607_13816
def controlledGidneyCompareLTSource (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) : CorrectionProgram :=
  if threshold=0 then .done
  else if 2^input.length≤threshold then .unitary [.ordinary [.CX q f]] .done
  else .unitary [.ordinary [.CX q f]] (controlledGidneyCompareGESource input dirty threshold q c r t f)
theorem controlledGidneyCompareLTSource_erase (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) :
    (controlledGidneyCompareLTSource input dirty threshold q c r t f).erase=
      controlledGidneyCompareLT input dirty threshold q c r t f := by
  unfold controlledGidneyCompareLTSource controlledGidneyCompareLT
  split
  · rfl
  · split
    · rfl
    · simp [CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,controlledGidneyCompareGESource_erase]
theorem controlledGidneyCompareLTSource_events (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) (hd : dirty.length=input.length) :
    (controlledGidneyCompareLTSource input dirty threshold q c r t f).events=
      if threshold=0 ∨ 2^input.length≤threshold then 0 else 2*input.length := by
  unfold controlledGidneyCompareLTSource
  split
  · rename_i h
    simp [h,CorrectionProgram.events]
  · rename_i h
    split
    · rename_i h'
      simp [h',CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
    · rename_i h'
      simp [h,h',CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,
        controlledGidneyCompareGESource_events _ _ _ _ _ _ _ _ hd]
def gidneyCompareGESource (input dirty : List Wire) (threshold : Nat) (c r t f : Wire) : CorrectionProgram :=
  let q := ([c,r,t,f]++input++dirty).sum+1
  (controlledGidneyCompareGESource input dirty threshold q c r t f).constantControl q
theorem gidneyCompareGESource_erase (input dirty : List Wire) (threshold : Nat) (c r t f : Wire) :
    (gidneyCompareGESource input dirty threshold c r t f).erase=gidneyCompareGE input dirty threshold c r t f := by
  rw [gidneyCompareGESource,CorrectionProgram.erase_constantControl,controlledGidneyCompareGESource_erase]
  rfl
theorem gidneyCompareGESource_events (input dirty : List Wire) (threshold : Nat) (c r t f : Wire)
    (hd : dirty.length=input.length) :
    (gidneyCompareGESource input dirty threshold c r t f).events=
      if threshold=0 ∨ 2^input.length≤threshold then 0 else 2*input.length := by
  rw [gidneyCompareGESource,CorrectionProgram.events_constantControl]
  exact controlledGidneyCompareGESource_events _ _ _ _ _ _ _ _ hd
def gidneyCompareLTSource (input dirty : List Wire) (threshold : Nat) (c r t f : Wire) : CorrectionProgram :=
  if threshold=0 then .done
  else if 2^input.length≤threshold then .unitary [.ordinary [.X f]] .done
  else .unitary [.ordinary [.X f]] (gidneyCompareGESource input dirty threshold c r t f)
theorem gidneyCompareLTSource_erase (input dirty : List Wire) (threshold : Nat) (c r t f : Wire) :
    (gidneyCompareLTSource input dirty threshold c r t f).erase=gidneyCompareLT input dirty threshold c r t f := by
  unfold gidneyCompareLTSource gidneyCompareLT
  split
  · rfl
  · split
    · rfl
    · simp [CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,gidneyCompareGESource_erase]
theorem gidneyCompareLTSource_events (input dirty : List Wire) (threshold : Nat) (c r t f : Wire)
    (hd : dirty.length=input.length) :
    (gidneyCompareLTSource input dirty threshold c r t f).events=
      if threshold=0 ∨ 2^input.length≤threshold then 0 else 2*input.length := by
  unfold gidneyCompareLTSource
  split
  · rename_i h
    simp [h,CorrectionProgram.events]
  · rename_i h
    split
    · rename_i h'
      simp [h',CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
    · rename_i h'
      simp [h,h',CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,
        gidneyCompareGESource_events _ _ _ _ _ _ _ hd]
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
/-- Compile away the virtual quantum control while retaining correction-event provenance. -/
def gidneyAddConstSource (input dirty : List Wire) (constant : List Bool) (c r t : Wire) : CorrectionProgram :=
  let q := ([c,r,t]++input++dirty).sum+1
  (controlledGidneyAddConstSource input dirty constant q c r t).constantControl q
theorem gidneyAddConstSource_erase (input dirty : List Wire) (constant : List Bool) (c r t : Wire) :
    (gidneyAddConstSource input dirty constant c r t).erase=gidneyAddConst input dirty constant c r t := by
  rw [gidneyAddConstSource,CorrectionProgram.erase_constantControl,controlledGidneyAddConstSource_erase]
  rfl
theorem gidneyAddConstSource_events (input dirty : List Wire) (constant : List Bool) (c r t : Wire)
    (hi : 0 < input.length) (hd : dirty.length=input.length-1) (hk : constant.length=input.length) :
    (gidneyAddConstSource input dirty constant c r t).events=
      if constant.all (fun k => !k) then 0 else 2*(input.length-1) := by
  rw [gidneyAddConstSource,CorrectionProgram.events_constantControl]
  exact controlledGidneyAddConstSource_events _ _ _ _ _ _ _ hi hd hk
end ShorECDLP.Paper2607_13816
