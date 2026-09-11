import ShorECDLP.Submission.«2607_13816».EEA.SourceDecoders
import ShorECDLP.Submission.«2607_13816».EEA.Interval

namespace ShorECDLP.Paper2607_13816
open Quantum
def intervalFirstLeafSource
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) : CorrectionProgram :=
  .unitary [.ordinary (endpointLeafToggle topSpecial label rightTop rightControl accumulator)]
    ((rippleFirstCellSource mode accumulator target addend carry scratch).seq
      (.unitary [.ordinary (endpointLeafToggle topSpecial label leftTop leftControl accumulator)] .done))
theorem intervalFirstLeafSource_erase (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    (intervalFirstLeafSource mode topSpecial rightTop leftTop accumulator target addend carry scratch label rightControl leftControl).erase=intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator target addend carry scratch label rightControl leftControl := by
  simp [intervalFirstLeafSource,intervalFirstLeafAdaptive,rippleFirstCellSource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
theorem intervalFirstLeafSource_events (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    (intervalFirstLeafSource mode topSpecial rightTop leftTop accumulator target addend carry scratch label rightControl leftControl).events=1 := by
  simp [intervalFirstLeafSource,CorrectionProgram.events_seq,CorrectionProgram.events,
    correctionBlockEvents,CorrectionFragment.events,rippleFirstCellSource_events]
def intervalSecondLeafSource
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) : CorrectionProgram :=
  .unitary [.ordinary (endpointLeafToggle topSpecial label leftTop leftControl accumulator)]
    ((rippleSecondCellSource mode accumulator target addend carry scratch).seq
      (.unitary [.ordinary (endpointLeafToggle topSpecial label rightTop rightControl accumulator)] .done))
theorem intervalSecondLeafSource_erase (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    (intervalSecondLeafSource mode topSpecial rightTop leftTop accumulator target addend carry scratch label rightControl leftControl).erase=intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator target addend carry scratch label rightControl leftControl := by
  simp [intervalSecondLeafSource,intervalSecondLeafAdaptive,rippleSecondCellSource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
theorem intervalSecondLeafSource_events (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    (intervalSecondLeafSource mode topSpecial rightTop leftTop accumulator target addend carry scratch label rightControl leftControl).events=1 := by
  simp [intervalSecondLeafSource,CorrectionProgram.events_seq,CorrectionProgram.events,
    correctionBlockEvents,CorrectionFragment.events,rippleSecondCellSource_events]
def topSpecialFirstLeafSource
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) : CorrectionProgram :=
  (toggleEqConstUnderControlSource rightRoot rightRegister topValue accumulator
      eqFlag eqScratches).seq
    ((rippleFirstCellSource mode accumulator target addend carry rippleScratch).seq
      (toggleEqConstUnderControlSource leftRoot leftRegister topValue accumulator
        eqFlag eqScratches))
theorem topSpecialFirstLeafSource_erase (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) :
    (topSpecialFirstLeafSource mode topValue rightRegister leftRegister accumulator target addend carry rippleScratch eqFlag eqScratches rightRoot leftRoot).erase=topSpecialFirstLeafAdaptive mode topValue rightRegister leftRegister accumulator target addend carry rippleScratch eqFlag eqScratches rightRoot leftRoot := by
  simp [topSpecialFirstLeafSource,topSpecialFirstLeafAdaptive,rippleFirstCellSource_erase,toggleEqConstUnderControlSource_erase,CorrectionProgram.erase_seq]
theorem topSpecialFirstLeafSource_events (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hr : rightRegister.length-2≤eqScratches.length) (hl : leftRegister.length-2≤eqScratches.length) :
    (topSpecialFirstLeafSource mode topValue rightRegister leftRegister accumulator target addend carry rippleScratch eqFlag eqScratches rightRoot leftRoot).events=2*(rightRegister.length-2)+2*(leftRegister.length-2)+1 := by
  simp only [topSpecialFirstLeafSource,CorrectionProgram.events_seq,
    toggleEqConstUnderControlSource_events rightRoot rightRegister topValue accumulator eqFlag eqScratches hr,
    toggleEqConstUnderControlSource_events leftRoot leftRegister topValue accumulator eqFlag eqScratches hl,
    rippleFirstCellSource_events]
  omega
def topSpecialSecondLeafSource
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) : CorrectionProgram :=
  (toggleEqConstUnderControlSource leftRoot leftRegister topValue accumulator
      eqFlag eqScratches).seq
    ((rippleSecondCellSource mode accumulator target addend carry rippleScratch).seq
      (toggleEqConstUnderControlSource rightRoot rightRegister topValue accumulator
        eqFlag eqScratches))
theorem topSpecialSecondLeafSource_erase (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) :
    (topSpecialSecondLeafSource mode topValue rightRegister leftRegister accumulator target addend carry rippleScratch eqFlag eqScratches rightRoot leftRoot).erase=topSpecialSecondLeafAdaptive mode topValue rightRegister leftRegister accumulator target addend carry rippleScratch eqFlag eqScratches rightRoot leftRoot := by
  simp [topSpecialSecondLeafSource,topSpecialSecondLeafAdaptive,rippleSecondCellSource_erase,toggleEqConstUnderControlSource_erase,CorrectionProgram.erase_seq]
theorem topSpecialSecondLeafSource_events (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hr : rightRegister.length-2≤eqScratches.length) (hl : leftRegister.length-2≤eqScratches.length) :
    (topSpecialSecondLeafSource mode topValue rightRegister leftRegister accumulator target addend carry rippleScratch eqFlag eqScratches rightRoot leftRoot).events=2*(rightRegister.length-2)+2*(leftRegister.length-2)+1 := by
  simp only [topSpecialSecondLeafSource,CorrectionProgram.events_seq,
    toggleEqConstUnderControlSource_events rightRoot rightRegister topValue accumulator eqFlag eqScratches hr,
    toggleEqConstUnderControlSource_events leftRoot leftRegister topValue accumulator eqFlag eqScratches hl,
    rippleSecondCellSource_events]
  omega
def intervalFirstTraversalSource
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) : CorrectionProgram :=
  dualUnaryAdaptiveActionSource .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeafSource mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths
theorem intervalFirstTraversalSource_erase (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) :
    (intervalFirstTraversalSource mode topSpecial rightTop leftTop accumulator carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).erase=intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop accumulator carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths := by
  simp [intervalFirstTraversalSource,intervalFirstTraversalAdaptive,intervalFirstLeafSource_erase,dualUnaryAdaptiveActionSource_erase]
theorem intervalFirstTraversalSource_events (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hl : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    (intervalFirstTraversalSource mode topSpecial rightTop leftTop accumulator carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).events=tree.leaves+2*tree.internalNodes := by
  rw [intervalFirstTraversalSource,dualUnaryAdaptiveActionSource_events _ _ _ _ _ _ _ hl]
  simp only [intervalFirstLeafSource_events]
  have h : tree.leafCostSum (fun _ _ _ => 1) rightRoot leftRoot rightPaths leftPaths=tree.leaves := by
    induction hl with
    | leaf => rfl
    | node ia ib ca cb pa pb zero one ra rb hlocal hzero hone ihZero ihOne =>
      simp [DualUnaryActionTree.leafCostSum,DualUnaryActionTree.leaves,ihZero,ihOne]
  rw [h]
def intervalSecondTraversalSource
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) : CorrectionProgram :=
  dualUnaryAdaptiveActionSource .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeafSource mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths
theorem intervalSecondTraversalSource_erase (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) :
    (intervalSecondTraversalSource mode topSpecial rightTop leftTop accumulator carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).erase=intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop accumulator carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths := by
  simp [intervalSecondTraversalSource,intervalSecondTraversalAdaptive,intervalSecondLeafSource_erase,dualUnaryAdaptiveActionSource_erase]
theorem intervalSecondTraversalSource_events (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hl : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    (intervalSecondTraversalSource mode topSpecial rightTop leftTop accumulator carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).events=tree.leaves+2*tree.internalNodes := by
  rw [intervalSecondTraversalSource,dualUnaryAdaptiveActionSource_events _ _ _ _ _ _ _ hl]
  simp only [intervalSecondLeafSource_events]
  have h : tree.leafCostSum (fun _ _ _ => 1) rightRoot leftRoot rightPaths leftPaths=tree.leaves := by
    induction hl with
    | leaf => rfl
    | node ia ib ca cb pa pb zero one ra rb hlocal hzero hone ihZero ihOne =>
      simp [DualUnaryActionTree.leafCostSum,DualUnaryActionTree.leaves,ihZero,ihOne]
  rw [h]
private def intervalTopFirstSource
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) : CorrectionProgram :=
  if intervalHasTopSpecial k K then
    topSpecialFirstLeafSource mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  else .unitary [] .done
private theorem intervalTopFirstSource_erase (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) :
    (intervalTopFirstSource registers k K mode target).erase=
      if intervalHasTopSpecial k K then
        topSpecialFirstLeafAdaptive mode (intervalTopRelative k K)
          registers.lengthS registers.lengthQ (registers.accumulator k K)
          (registers.targetAt target (intervalTopRelative k K))
          (registers.addendAt target (intervalTopRelative k K))
          (registers.carry k K) (registers.cellScratch k K)
          (registers.cellScratch k K) (registers.equalityScratch k K)
          registers.control registers.control else .unitary [] .done := by
  unfold intervalTopFirstSource
  split <;> simp [topSpecialFirstLeafSource_erase,CorrectionProgram.erase,correctionBlockErase]
private theorem intervalTopFirstSource_events (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget)
    (hs : registers.lengthS.length-2≤(registers.equalityScratch k K).length)
    (hq : registers.lengthQ.length-2≤(registers.equalityScratch k K).length) :
    (intervalTopFirstSource registers k K mode target).events=
      if intervalHasTopSpecial k K then
        2*(registers.lengthS.length-2)+2*(registers.lengthQ.length-2)+1 else 0 := by
  unfold intervalTopFirstSource
  split <;> simp [topSpecialFirstLeafSource_events _ _ _ _ _ _ _ _ _ _ _ _ _ hs hq,
    CorrectionProgram.events,correctionBlockEvents]
private def intervalTopSecondSource
    (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) : CorrectionProgram :=
  if intervalHasTopSpecial k K then
    topSpecialSecondLeafSource mode (intervalTopRelative k K)
      registers.lengthS registers.lengthQ (registers.accumulator k K)
      (registers.targetAt target (intervalTopRelative k K))
      (registers.addendAt target (intervalTopRelative k K))
      (registers.carry k K) (registers.cellScratch k K)
      (registers.cellScratch k K) (registers.equalityScratch k K)
      registers.control registers.control
  else .unitary [] .done
private theorem intervalTopSecondSource_erase (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget) :
    (intervalTopSecondSource registers k K mode target).erase=
      if intervalHasTopSpecial k K then
        topSpecialSecondLeafAdaptive mode (intervalTopRelative k K)
          registers.lengthS registers.lengthQ (registers.accumulator k K)
          (registers.targetAt target (intervalTopRelative k K))
          (registers.addendAt target (intervalTopRelative k K))
          (registers.carry k K) (registers.cellScratch k K)
          (registers.cellScratch k K) (registers.equalityScratch k K)
          registers.control registers.control else .unitary [] .done := by
  unfold intervalTopSecondSource
  split <;> simp [topSpecialSecondLeafSource_erase,CorrectionProgram.erase,correctionBlockErase]
private theorem intervalTopSecondSource_events (registers : IntervalRegisters) (k K : Nat) (mode : RippleMode)
    (target : IntervalTarget)
    (hs : registers.lengthS.length-2≤(registers.equalityScratch k K).length)
    (hq : registers.lengthQ.length-2≤(registers.equalityScratch k K).length) :
    (intervalTopSecondSource registers k K mode target).events=
      if intervalHasTopSpecial k K then
        2*(registers.lengthS.length-2)+2*(registers.lengthQ.length-2)+1 else 0 := by
  unfold intervalTopSecondSource
  split <;> simp [topSpecialSecondLeafSource_events _ _ _ _ _ _ _ _ _ _ _ _ _ hs hq,
    CorrectionProgram.events,correctionBlockEvents]
def intervalAddSubSource
    (registers : IntervalRegisters) (n k K : Nat) (mode : RippleMode)
    (signUpdate : Bool) (target : IntervalTarget) : CorrectionProgram :=
  (CorrectionProgram.unitary [.ordinary
      (prepareIntervalEndpoints registers.lengthT registers.lengthQ registers.lengthS
        registers.endpointScratch (registers.carry k K) n k)] .done).seq
    ((intervalTopFirstSource registers k K mode target).seq
      ((intervalFirstTraversalSource mode (intervalHasTopSpecial k K)
          (registers.rightTop k K) (registers.leftTop k K)
          (registers.accumulator k K) (registers.carry k K)
          (registers.cellScratch k K) (registers.targetAt target)
          (registers.addendAt target) (intervalTree registers k K)
          registers.control registers.control (registers.rightPaths k K)
          (registers.leftPaths k K)).seq
        ((CorrectionProgram.unitary [.ordinary
            (intervalSignUpdate registers k K signUpdate)] .done).seq
          ((intervalSecondTraversalSource mode (intervalHasTopSpecial k K)
              (registers.rightTop k K) (registers.leftTop k K)
              (registers.accumulator k K) (registers.carry k K)
              (registers.cellScratch k K) (registers.targetAt target)
              (registers.addendAt target) (intervalTree registers k K)
              registers.control registers.control (registers.rightPaths k K)
              (registers.leftPaths k K)).seq
            ((intervalTopSecondSource registers k K mode target).seq
              (CorrectionProgram.unitary [.ordinary
                (restoreIntervalEndpoints registers.lengthT registers.lengthQ
                  registers.lengthS registers.endpointScratch
                  (registers.carry k K) n k)] .done))))))
theorem intervalAddSubSource_erase (registers : IntervalRegisters) (n k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    (intervalAddSubSource registers n k K mode signUpdate target).erase=
      intervalAddSub registers n k K mode signUpdate target := by
  simp only [intervalAddSubSource,CorrectionProgram.erase_seq,intervalTopFirstSource_erase,
    intervalTopSecondSource_erase,intervalFirstTraversalSource_erase,intervalSecondTraversalSource_erase,
    CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]
  rfl
theorem intervalAddSubSource_events (registers : IntervalRegisters) (n k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hl : (intervalTree registers k K).Layout registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K))
    (hs : registers.lengthS.length-2≤(registers.equalityScratch k K).length)
    (hq : registers.lengthQ.length-2≤(registers.equalityScratch k K).length) :
    (intervalAddSubSource registers n k K mode signUpdate target).events=
      2*((intervalTree registers k K).leaves+2*(intervalTree registers k K).internalNodes)+
        2*(if intervalHasTopSpecial k K then
          2*(registers.lengthS.length-2)+2*(registers.lengthQ.length-2)+1 else 0) := by
  simp only [intervalAddSubSource,CorrectionProgram.events_seq,
    intervalFirstTraversalSource_events _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl,
    intervalSecondTraversalSource_events _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl,
    intervalTopFirstSource_events _ _ _ _ _ hs hq,intervalTopSecondSource_events _ _ _ _ _ hs hq,
    CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero]
  omega
def intervalAddSubInverseSource (registers : IntervalRegisters) (n k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) : CorrectionProgram :=
  intervalAddSubSource registers n k K mode.inverse signUpdate target
theorem intervalAddSubInverseSource_erase (registers : IntervalRegisters) (n k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    (intervalAddSubInverseSource registers n k K mode signUpdate target).erase=intervalAddSubInverse registers n k K mode signUpdate target := by
  exact intervalAddSubSource_erase registers n k K mode.inverse signUpdate target
theorem intervalAddSubInverseSource_events (registers : IntervalRegisters) (n k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hl : (intervalTree registers k K).Layout registers.control registers.control
      (registers.rightPaths k K) (registers.leftPaths k K))
    (hs : registers.lengthS.length-2≤(registers.equalityScratch k K).length)
    (hq : registers.lengthQ.length-2≤(registers.equalityScratch k K).length) :
    (intervalAddSubInverseSource registers n k K mode signUpdate target).events=
      2*((intervalTree registers k K).leaves+2*(intervalTree registers k K).internalNodes)+
        2*(if intervalHasTopSpecial k K then
          2*(registers.lengthS.length-2)+2*(registers.lengthQ.length-2)+1 else 0) := by
  exact intervalAddSubSource_events registers n k K mode.inverse signUpdate target hl hs hq
end ShorECDLP.Paper2607_13816
