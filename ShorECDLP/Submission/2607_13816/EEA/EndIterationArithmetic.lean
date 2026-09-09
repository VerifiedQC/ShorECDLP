import ShorECDLP.Submission.«2607_13816».EEA.EndIteration
import ShorECDLP.Submission.«2607_13816».EEA.LengthArithmetic

/-! # Arithmetic length replacement at an enabled EEA iteration boundary -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

/-- Truth-minus-one highest label, or the all-ones sentinel for an all-zero range. -/
def upperLengthOfBits (width K : Nat) (bits : List Bool) : Nat :=
  if bits.reverse.findIdx id < bits.length then
    truthMinusOneValue width (K - bits.reverse.findIdx id) else 2^width - 1

/-- Encoded right length of the first set label, or the all-ones sentinel. -/
def lowerLengthOfBits (n width k : Nat) (bits : List Bool) : Nat :=
  if bits.findIdx id < bits.length then
    rightLengthValue n width (k + bits.findIdx id) else 2^width - 1

private theorem upper_replace (width k K : Nat) (hkK : k ≤ K)
    (old new target : List Bool)
    (hold : old.length = K - k + 1) (hnew : new.length = K - k + 1)
    (htarget : target = constantBits width (upperLengthOfBits width K old)) :
    highestPositionWordAction width k K true new
      (highestPositionWordAction width k K true old target) =
      constantBits width (upperLengthOfBits width K new) := by
  rw [highestPositionWordAction_lastSet width k K hkK new _ hnew,
    highestPositionWordAction_lastSet width k K hkK old target hold, htarget]
  change xorConstantBits
    (xorConstantBits (xorConstantBits (List.replicate width false) _) _) _ = _
  dsimp only [upperLengthOfBits]
  rw [xorConstantBits_involutive]
  rfl

private theorem lower_replace (n width k K : Nat) (hkK : k ≤ K)
    (old new target : List Bool)
    (hold : old.length = K - k + 1) (hnew : new.length = K - k + 1)
    (htarget : target = constantBits width (lowerLengthOfBits n width k old)) :
    rightLengthWordAction n width k K true new
      (rightLengthWordAction n width k K true old target) =
      constantBits width (lowerLengthOfBits n width k new) := by
  rw [rightLengthWordAction_firstSet n width k K hkK new _ hnew,
    rightLengthWordAction_firstSet n width k K hkK old target hold, htarget]
  change xorConstantBits
    (xorConstantBits (xorConstantBits (List.replicate width false) _) _) _ = _
  dsimp only [lowerLengthOfBits]
  rw [xorConstantBits_involutive]
  rfl

/-- Consistent old length words are replaced by the decoded lengths of the swapped
work banks. This is a local arithmetic consistency premise, not a reachability claim. -/
theorem endIterationLengthWords_replace
    (r : EndIterationRegisters) (n : Nat) (windows : EndIterationWindows)
    (boundary4 boundary5 : Nat) (state : BasisState)
    (hupper : windows.k4 ≤ windows.K4)
    (hlower : windows.k5 ≤ windows.K5Decode n) (henabled : state r.control = true)
    (hT : wireValues r.lengthT state = constantBits r.lengthT.length
      (upperLengthOfBits r.lengthT.length windows.K4
        (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
          (wireValues r.work1 state))))
    (hRP : wireValues r.lengthRP state = constantBits r.lengthRP.length
      (lowerLengthOfBits n r.lengthRP.length windows.k5
        (endIterationLowerRangeBits true boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues r.work2 state)))) :
    endIterationLengthWords r n windows boundary4 boundary5 state =
      (constantBits r.lengthT.length (upperLengthOfBits r.lengthT.length windows.K4
        (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
          (wireValues r.work2 state))),
       constantBits r.lengthRP.length (lowerLengthOfBits n r.lengthRP.length windows.k5
        (endIterationLowerRangeBits true boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues r.work1 state)))) := by
  have hu (work : List Bool) :
      (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4) work).length =
        windows.K4 - windows.k4 + 1 := by
    simp only [endIterationUpperRangeBits, List.length_map, zeroMapLabels_eq_range', List.length_range']
    omega
  have hd (work : List Bool) :
      (endIterationLowerRangeBits true boundary5
        (zeroMapLabels windows.k5 (windows.K5Decode n)) work).length =
        windows.K5Decode n - windows.k5 + 1 := by
    simp only [endIterationLowerRangeBits, List.length_map, zeroMapLabels_eq_range', List.length_range']
    omega
  simp only [endIterationLengthWords, endIterationSwappedWorkWords, henabled, ↓reduceIte]
  rw [upper_replace _ _ _ hupper _ _ _ (hu _) (hu _) hT,
    lower_replace _ _ _ _ hlower _ _ _ (hd _) (hd _) hRP]

/-- The actual enabled iteration-end circuit replaces consistent old metadata by
the decoded lengths of the swapped work banks. Existing route and readiness
premises are unchanged. -/
theorem swapWorkAndLengthUnaryShared_lengths
    (r : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (boundary4 boundary5 : Nat)
    (hboundary4 : windows.k4 ≤ boundary4 ∧ boundary4 ≤ windows.K4)
    (hboundary5 : windows.k5 ≤ boundary5 ∧
      boundary5 ≤ windows.K5Decode n)
    (state : BasisState)
    (hlayout : EndIterationLayout r n windows)
    (hroute4 : (r.upperTree windows).routeLabel
      (run (constMinus r.lengthRP r.constants r.carry (n + 2))
        (run (controlledWorkSwap r.control r.work1 r.work2)
          state)) = boundary4)
    (hroute5 : (r.lowerTree n windows).routeLabel
      (run (addConstant r.lengthT r.constants r.carry 3)
        (run
          (lenUpdateLtUnary n windows.k4 windows.K4 (r.upperTree windows) r.control
            (r.rangeAccumulator windows.k4 windows.K4)
            (r.temporary windows.k4 windows.K4) r.carry
            (r.path windows.k4 windows.K4)
            r.work1At r.work2At
            r.lengthT r.lengthRP r.constants)
          (run (controlledWorkSwap r.control r.work1 r.work2)
            state))) = boundary5)
    (hready : EndIterationReady r state)
    (henabled : state r.control = true)
    (hT : wireValues r.lengthT state = constantBits r.lengthT.length
      (upperLengthOfBits r.lengthT.length windows.K4
        (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
          (wireValues r.work1 state))))
    (hRP : wireValues r.lengthRP state = constantBits r.lengthRP.length
      (lowerLengthOfBits n r.lengthRP.length windows.k5
        (endIterationLowerRangeBits true boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues r.work2 state)))) :
    (wireValues r.lengthT (run (swapWorkAndLengthUnaryShared r n windows) state),
      wireValues r.lengthRP (run (swapWorkAndLengthUnaryShared r n windows) state)) =
      (constantBits r.lengthT.length (upperLengthOfBits r.lengthT.length windows.K4
        (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
          (wireValues r.work2 state))),
       constantBits r.lengthRP.length (lowerLengthOfBits n r.lengthRP.length windows.k5
        (endIterationLowerRangeBits true boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues r.work1 state)))) := by
  have h := swapWorkAndLengthUnaryShared_correct r n windows boundary4 boundary5
    hboundary4 hboundary5 state hlayout hroute4 hroute5 hready
  dsimp only at h
  rw [h.2.2.1]
  exact endIterationLengthWords_replace r n windows boundary4 boundary5 state
    (hboundary4.1.trans hboundary4.2) (hboundary5.1.trans hboundary5.2) henabled hT hRP

end ShorECDLP.Paper2607_13816
