import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceCorrections
import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf

namespace ShorECDLP.Paper2607_13816
open Quantum
def measuredAndEraseSource (first second target : Wire) : CorrectionProgram :=
  .reset target (.unitary [] .done) (.unitary [.selected (controlledZ first second)] .done)
theorem measuredAndEraseSource_erase (first second target : Wire) :
    (measuredAndEraseSource first second target).erase=measuredAndErase first second target := by
  rfl
theorem measuredAndEraseSource_events (first second target : Wire) :
    (measuredAndEraseSource first second target).events=1 := by rfl
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
def mcxVChainTailSource (accumulator : Wire) : List Wire → Wire → List Wire → CorrectionProgram
  | [], _, _ => .done
  | [control], target, _ => .unitary [.ordinary [.CCX control accumulator target]] .done
  | control :: nextControl :: controls, target, scratch :: scratches =>
      .unitary [.ordinary [.CCX control accumulator scratch]]
        ((mcxVChainTailSource scratch (nextControl :: controls) target scratches).seq
          (measuredAndEraseSource control accumulator scratch))
  | _ :: _ :: _, _, [] => .done
private theorem mcxVChainTailSource_erase (controls : List Wire) (acc target : Wire) (scratch : List Wire) :
    (mcxVChainTailSource acc controls target scratch).erase=mcxVChainTailAdaptive acc controls target scratch := by
  induction controls generalizing acc scratch with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      cases scratch with
      | nil => rfl
      | cons w ws =>
        simp only [mcxVChainTailSource,mcxVChainTailAdaptive,CorrectionProgram.erase_seq,
          CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,
          List.flatMap_nil,List.append_nil,ih,measuredAndEraseSource_erase]
private theorem mcxVChainTailSource_events (controls : List Wire) (acc target : Wire) (scratch : List Wire)
    (hs : controls.length-1≤scratch.length) :
    (mcxVChainTailSource acc controls target scratch).events=controls.length-1 := by
  induction controls generalizing acc scratch with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      cases scratch with
      | nil => simp at hs
      | cons w ws =>
        have ht : (b::rest).length-1≤ws.length := by simp only [List.length_cons] at hs ⊢; omega
        simp only [mcxVChainTailSource,CorrectionProgram.events_seq,CorrectionProgram.events,
          correctionBlockEvents,CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,
          List.sum_nil,Nat.zero_add,ih w ws ht,measuredAndEraseSource_events,List.length_cons]
        omega
def mcxVChainSource : List Wire → Wire → List Wire → CorrectionProgram
  | [], target, _ => .unitary [.ordinary [.X target]] .done
  | [control], target, _ => .unitary [.ordinary [.CX control target]] .done
  | first :: second :: controls, target, scratches =>
      mcxVChainTailSource second (first :: controls) target scratches
theorem mcxVChainSource_erase (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (mcxVChainSource controls target scratch).erase=mcxVChainAdaptive controls target scratch := by
  cases controls with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest => exact mcxVChainTailSource_erase _ _ _ _
theorem mcxVChainSource_events (controls : List Wire) (target : Wire) (scratch : List Wire)
    (hs : controls.length-2≤scratch.length) :
    (mcxVChainSource controls target scratch).events=controls.length-2 := by
  cases controls with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      rw [mcxVChainSource,mcxVChainTailSource_events _ _ _ _ (by simp only [List.length_cons] at hs ⊢; omega)]
      simp
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
def computeEqConstSource (register : List Wire) (value : Nat)
    (flag : Wire) (scratches : List Wire) : CorrectionProgram :=
  .unitary [.ordinary (zeroMask register value)]
    ((mcxVChainSource register flag scratches).seq
      (.unitary [.ordinary (zeroMask register value)] .done))
theorem computeEqConstSource_erase (register : List Wire) (value : Nat)
    (flag : Wire) (scratches : List Wire) :
    (computeEqConstSource register value flag scratches).erase=computeEqConstAdaptive register value flag scratches := by
  simp [computeEqConstSource,computeEqConstAdaptive,mcxVChainSource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
theorem computeEqConstSource_events (register : List Wire) (value : Nat)
    (flag : Wire) (scratches : List Wire) (hs : register.length-2≤scratches.length) :
    (computeEqConstSource register value flag scratches).events=register.length-2 := by
  simp [computeEqConstSource,mcxVChainSource_events register flag scratches hs,CorrectionProgram.events_seq,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
def toggleEqConstUnderControlSource
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire) : CorrectionProgram :=
  let compute := computeEqConstSource register value flag scratches
  compute.seq (.unitary [.ordinary [.CCX root flag accumulator]] compute)
theorem toggleEqConstUnderControlSource_erase (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire) :
    (toggleEqConstUnderControlSource root register value accumulator flag scratches).erase=toggleEqConstUnderControlAdaptive root register value accumulator flag scratches := by
  simp [toggleEqConstUnderControlSource,toggleEqConstUnderControlAdaptive,computeEqConstSource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
theorem toggleEqConstUnderControlSource_events (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire) (hs : register.length-2≤scratches.length) :
    (toggleEqConstUnderControlSource root register value accumulator flag scratches).events=2*(register.length-2) := by
  simp [toggleEqConstUnderControlSource,computeEqConstSource_events register value flag scratches hs,CorrectionProgram.events_seq,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,Nat.two_mul]
def cleanC3XSource
    (first second third target scratch : Wire) : CorrectionProgram :=
  mcxVChainSource ([first, second, third] : List Wire) target
    ([scratch] : List Wire)
theorem cleanC3XSource_erase (first second third target scratch : Wire) :
    (cleanC3XSource first second third target scratch).erase=cleanC3XAdaptive first second third target scratch := by
  simp [cleanC3XSource,cleanC3XAdaptive,mcxVChainSource_erase]
theorem cleanC3XSource_events (first second third target scratch : Wire) :
    (cleanC3XSource first second third target scratch).events=1 := by
  simp [cleanC3XSource,mcxVChainSource_events ([first,second,third] : List Wire) target ([scratch] : List Wire) (by simp)]
def controlledMajSource
    (control target addend carry scratch : Wire) : CorrectionProgram :=
  .unitary [.ordinary [.CX carry target, .CX carry addend]]
    (cleanC3XSource control target addend carry scratch)
theorem controlledMajSource_erase (control target addend carry scratch : Wire) :
    (controlledMajSource control target addend carry scratch).erase=controlledMajAdaptive control target addend carry scratch := by
  simp [controlledMajSource,controlledMajAdaptive,cleanC3XSource_erase,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
theorem controlledMajSource_events (control target addend carry scratch : Wire) :
    (controlledMajSource control target addend carry scratch).events=1 := by
  simp [controlledMajSource,cleanC3XSource_events,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
def controlledUmaSource
    (control target addend carry scratch : Wire) : CorrectionProgram :=
  (cleanC3XSource control target addend carry scratch).seq
    (.unitary [.ordinary [.CCX control addend target, .CX carry addend, .CX carry target]] .done)
theorem controlledUmaSource_erase (control target addend carry scratch : Wire) :
    (controlledUmaSource control target addend carry scratch).erase=controlledUmaAdaptive control target addend carry scratch := by
  simp [controlledUmaSource,controlledUmaAdaptive,cleanC3XSource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
theorem controlledUmaSource_events (control target addend carry scratch : Wire) :
    (controlledUmaSource control target addend carry scratch).events=1 := by
  simp [controlledUmaSource,cleanC3XSource_events,CorrectionProgram.events_seq,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
def controlledMajInvSource
    (control target addend carry scratch : Wire) : CorrectionProgram :=
  (cleanC3XSource control target addend carry scratch).seq
    (.unitary [.ordinary [.CX carry addend, .CX carry target]] .done)
theorem controlledMajInvSource_erase (control target addend carry scratch : Wire) :
    (controlledMajInvSource control target addend carry scratch).erase=controlledMajInvAdaptive control target addend carry scratch := by
  simp [controlledMajInvSource,controlledMajInvAdaptive,cleanC3XSource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
theorem controlledMajInvSource_events (control target addend carry scratch : Wire) :
    (controlledMajInvSource control target addend carry scratch).events=1 := by
  simp [controlledMajInvSource,cleanC3XSource_events,CorrectionProgram.events_seq,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
def controlledUmaInvSource
    (control target addend carry scratch : Wire) : CorrectionProgram :=
  .unitary [.ordinary [.CX carry target, .CX carry addend, .CCX control addend target]]
    (cleanC3XSource control target addend carry scratch)
theorem controlledUmaInvSource_erase (control target addend carry scratch : Wire) :
    (controlledUmaInvSource control target addend carry scratch).erase=controlledUmaInvAdaptive control target addend carry scratch := by
  simp [controlledUmaInvSource,controlledUmaInvAdaptive,cleanC3XSource_erase,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
theorem controlledUmaInvSource_events (control target addend carry scratch : Wire) :
    (controlledUmaInvSource control target addend carry scratch).events=1 := by
  simp [controlledUmaInvSource,cleanC3XSource_events,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
def rippleFirstCellSource (mode : RippleMode)
    (control target addend carry scratch : Wire) : CorrectionProgram :=
  match mode with
  | .add => controlledMajSource control target addend carry scratch
  | .sub => controlledUmaInvSource control target addend carry scratch
theorem rippleFirstCellSource_erase (mode : RippleMode)
    (control target addend carry scratch : Wire) :
    (rippleFirstCellSource mode control target addend carry scratch).erase=rippleFirstCellAdaptive mode control target addend carry scratch := by
  cases mode <;> simp [rippleFirstCellSource,rippleFirstCellAdaptive,controlledMajSource_erase,controlledUmaInvSource_erase]
theorem rippleFirstCellSource_events (mode : RippleMode)
    (control target addend carry scratch : Wire) :
    (rippleFirstCellSource mode control target addend carry scratch).events=1 := by
  cases mode <;> simp [rippleFirstCellSource,controlledMajSource_events,controlledUmaInvSource_events]
def rippleSecondCellSource (mode : RippleMode)
    (control target addend carry scratch : Wire) : CorrectionProgram :=
  match mode with
  | .add => controlledUmaSource control target addend carry scratch
  | .sub => controlledMajInvSource control target addend carry scratch
theorem rippleSecondCellSource_erase (mode : RippleMode)
    (control target addend carry scratch : Wire) :
    (rippleSecondCellSource mode control target addend carry scratch).erase=rippleSecondCellAdaptive mode control target addend carry scratch := by
  cases mode <;> simp [rippleSecondCellSource,rippleSecondCellAdaptive,controlledUmaSource_erase,controlledMajInvSource_erase]
theorem rippleSecondCellSource_events (mode : RippleMode)
    (control target addend carry scratch : Wire) :
    (rippleSecondCellSource mode control target addend carry scratch).events=1 := by
  cases mode <;> simp [rippleSecondCellSource,controlledUmaSource_events,controlledMajInvSource_events]
end ShorECDLP.Paper2607_13816
