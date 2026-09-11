import ShorECDLP.Submission.«2607_13816».EEA.SourcePrimitives
import ShorECDLP.Submission.«2607_13816».EEA.DualUnaryAction

namespace ShorECDLP.Paper2607_13816
open Quantum
def eraseZeroAndSource (control indexBit target : Wire) : CorrectionProgram :=
  (CorrectionProgram.unitary [.ordinary [.X indexBit]]
    (measuredAndEraseSource control indexBit target)).seq
    (.unitary [.ordinary [.X indexBit]] .done)
theorem eraseZeroAndSource_erase (control indexBit target : Wire) :
    (eraseZeroAndSource control indexBit target).erase=eraseZeroAnd control indexBit target := by
  simp [eraseZeroAndSource,eraseZeroAnd,CorrectionProgram.erase_seq,CorrectionProgram.erase,
    correctionBlockErase,CorrectionFragment.erase,measuredAndEraseSource_erase]
theorem eraseZeroAndSource_events (control indexBit target : Wire) :
    (eraseZeroAndSource control indexBit target).events=1 := by
  simp [eraseZeroAndSource,CorrectionProgram.events_seq,CorrectionProgram.events,
    correctionBlockEvents,CorrectionFragment.events,measuredAndEraseSource_events]
def eraseDualZeroAndSource (a b c d e f : Wire) : CorrectionProgram :=
  (eraseZeroAndSource d e f).seq (eraseZeroAndSource a b c)
theorem eraseDualZeroAndSource_erase (a b c d e f : Wire) :
    (eraseDualZeroAndSource a b c d e f).erase=eraseDualZeroAnd a b c d e f := by
  simp [eraseDualZeroAndSource,eraseDualZeroAnd,CorrectionProgram.erase_seq,eraseZeroAndSource_erase]
theorem eraseDualZeroAndSource_events (a b c d e f : Wire) :
    (eraseDualZeroAndSource a b c d e f).events=2 := by
  simp [eraseDualZeroAndSource,CorrectionProgram.events_seq,eraseZeroAndSource_events]
def unaryAdaptiveActionSource
    (order : UnaryOrder)
    (leafAction : Nat → Wire → CorrectionProgram) :
    UnaryActionTree → Wire → List Wire → CorrectionProgram
  | .leaf label, control, _ => leafAction label control
  | .node indexBit zero one, control, path :: rest =>
      match order with
      | .inc =>
          .unitary [.ordinary (computeZeroAnd control indexBit path)]
            ((unaryAdaptiveActionSource order leafAction zero path rest).seq
              (.unitary [.ordinary [.CX control path]]
                ((unaryAdaptiveActionSource order leafAction one path rest).seq
                  (.unitary [.ordinary [.CX control path]]
                    (eraseZeroAndSource control indexBit path)))))
      | .dec =>
          .unitary [.ordinary (computeZeroAnd control indexBit path)]
            (.unitary [.ordinary [.CX control path]]
              ((unaryAdaptiveActionSource order leafAction one path rest).seq
                (.unitary [.ordinary [.CX control path]]
                  ((unaryAdaptiveActionSource order leafAction zero path rest).seq
                    (eraseZeroAndSource control indexBit path)))))
  | .node _ _ _, _, [] => .done
def dualUnaryAdaptiveActionSource
    (order : UnaryOrder)
    (leafAction : Nat → Wire → Wire → CorrectionProgram) :
    DualUnaryActionTree → Wire → Wire →
      List Wire → List Wire → CorrectionProgram
  | .leaf label, controlA, controlB, _, _ =>
      leafAction label controlA controlB
  | .node indexBitA indexBitB zero one,
      controlA, controlB, pathA :: restA, pathB :: restB =>
      match order with
      | .inc =>
          .unitary [.ordinary (computeZeroAnd controlA indexBitA pathA)]
            (.unitary [.ordinary (computeZeroAnd controlB indexBitB pathB)]
              ((dualUnaryAdaptiveActionSource order leafAction zero
                  pathA pathB restA restB).seq
                (.unitary [.ordinary [.CX controlA pathA, .CX controlB pathB]]
                  ((dualUnaryAdaptiveActionSource order leafAction one
                      pathA pathB restA restB).seq
                    (.unitary [.ordinary [.CX controlB pathB, .CX controlA pathA]]
                      (eraseDualZeroAndSource controlA indexBitA pathA
                        controlB indexBitB pathB))))))
      | .dec =>
          .unitary [.ordinary (computeZeroAnd controlA indexBitA pathA)]
            (.unitary [.ordinary (computeZeroAnd controlB indexBitB pathB)]
              (.unitary [.ordinary [.CX controlA pathA, .CX controlB pathB]]
                ((dualUnaryAdaptiveActionSource order leafAction one
                    pathA pathB restA restB).seq
                  (.unitary [.ordinary [.CX controlB pathB, .CX controlA pathA]]
                    ((dualUnaryAdaptiveActionSource order leafAction zero
                        pathA pathB restA restB).seq
                      (eraseDualZeroAndSource controlA indexBitA pathA
                        controlB indexBitB pathB))))))
  | .node _ _ _ _, _, _, _, _ => .done
theorem unaryAdaptiveActionSource_erase (order : UnaryOrder) (leaf : Nat → Wire → CorrectionProgram)
    (tree : UnaryActionTree) (q : Wire) (path : List Wire) :
    (unaryAdaptiveActionSource order leaf tree q path).erase=
      unaryAdaptiveAction order (fun l w => (leaf l w).erase) tree q path := by
  induction tree generalizing q path with
  | leaf label => rfl
  | node index zero one ihZero ihOne =>
    cases path with
    | nil => rfl
    | cons w ws =>
      cases order <;> simp [unaryAdaptiveActionSource,unaryAdaptiveAction,CorrectionProgram.erase,
        correctionBlockErase,CorrectionFragment.erase,CorrectionProgram.erase_seq,ihZero,ihOne,eraseZeroAndSource_erase]
theorem unaryAdaptiveActionSource_events (order : UnaryOrder) (leaf : Nat → Wire → CorrectionProgram)
    (tree : UnaryActionTree) (q : Wire) (path : List Wire) (hl : tree.Layout q path) :
    (unaryAdaptiveActionSource order leaf tree q path).events=
      tree.leafCostSum (fun l w => (leaf l w).events) q path+tree.internalNodes := by
  induction hl with
  | leaf => simp [unaryAdaptiveActionSource,UnaryActionTree.leafCostSum,UnaryActionTree.internalNodes]
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
    cases order <;>
      simp only [unaryAdaptiveActionSource,CorrectionProgram.events,correctionBlockEvents,
        CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Nat.zero_add,CorrectionProgram.events_seq,eraseZeroAndSource_events,ihZero,ihOne,
        UnaryActionTree.leafCostSum,UnaryActionTree.internalNodes]
    all_goals omega

theorem dualUnaryAdaptiveActionSource_erase (order : UnaryOrder)
    (leaf : Nat → Wire → Wire → CorrectionProgram) (tree : DualUnaryActionTree)
    (a b : Wire) (pa pb : List Wire) :
    (dualUnaryAdaptiveActionSource order leaf tree a b pa pb).erase=
      dualUnaryAdaptiveAction order (fun l x y => (leaf l x y).erase) tree a b pa pb := by
  induction tree generalizing a b pa pb with
  | leaf label => rfl
  | node ia ib zero one ihZero ihOne =>
    cases pa with
    | nil => rfl
    | cons wa ws =>
      cases pb with
      | nil => rfl
      | cons wb vs =>
        cases order <;> simp [dualUnaryAdaptiveActionSource,dualUnaryAdaptiveAction,CorrectionProgram.erase,
          correctionBlockErase,CorrectionFragment.erase,CorrectionProgram.erase_seq,ihZero,ihOne,eraseDualZeroAndSource_erase]
theorem dualUnaryAdaptiveActionSource_events (order : UnaryOrder)
    (leaf : Nat → Wire → Wire → CorrectionProgram) (tree : DualUnaryActionTree)
    (a b : Wire) (pa pb : List Wire) (hl : tree.Layout a b pa pb) :
    (dualUnaryAdaptiveActionSource order leaf tree a b pa pb).events=
      tree.leafCostSum (fun l x y => (leaf l x y).events) a b pa pb+2*tree.internalNodes := by
  induction hl with
  | leaf => simp [dualUnaryAdaptiveActionSource,DualUnaryActionTree.leafCostSum,DualUnaryActionTree.internalNodes]
  | node ia ib ca cb pathA pathB zero one restA restB hlocal hzero hone ihZero ihOne =>
    cases order <;>
      simp only [dualUnaryAdaptiveActionSource,CorrectionProgram.events,correctionBlockEvents,
        CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Nat.zero_add,CorrectionProgram.events_seq,eraseDualZeroAndSource_events,ihZero,ihOne,
        DualUnaryActionTree.leafCostSum,DualUnaryActionTree.internalNodes]
    all_goals omega
end ShorECDLP.Paper2607_13816
