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

private theorem endpoint_word_append (a b : List Bool) :
    boolWordToNat (a ++ b) = boolWordToNat a + 2^a.length * boolWordToNat b := by
  induction a with
  | nil => simp
  | cons bit bits ih =>
    simp only [List.cons_append, boolWordToNat_cons, ih, List.length_cons, pow_succ]
    ring

private theorem boolWordToNat_size_from_highest (bits : List Bool) :
    (boolWordToNat bits).size = bits.length - bits.reverse.findIdx id := by
  suffices h : ∀ bs : List Bool, (boolWordToNat bs.reverse).size = bs.length - bs.findIdx id by
    simpa using h bits.reverse
  intro bs
  induction bs with
  | nil => simp [boolWordToNat_nil]
  | cons bit bs ih =>
    rw [List.reverse_cons, endpoint_word_append]
    cases bit with
    | false => simpa [List.findIdx_cons, boolWordToNat_cons, boolWordToNat_nil] using ih
    | true =>
      have hb : boolWordToNat bs.reverse < 2^bs.length := by simpa only [List.length_reverse] using boolWordToNat_lt_pow_two bs.reverse
      have hlo : bs.length < (boolWordToNat bs.reverse + 2^bs.length).size :=
        Nat.lt_size.mpr (by omega)
      have hhi : (boolWordToNat bs.reverse + 2^bs.length).size ≤ bs.length+1 :=
        Nat.size_le.mpr (by simp only [pow_succ]; simpa using (by omega : boolWordToNat bs.reverse + 2^bs.length < 2^bs.length*2))
      simp only [boolWordToNat_cons, Bool.toNat_true, boolWordToNat_nil,
        mul_zero, add_zero, mul_one, List.length_reverse, List.findIdx_cons,
        id_eq, Bool.cond_true, List.length_cons, Nat.sub_zero]
      omega

/-- A nonzero upper scan reports the bit length of its numeric word, shifted by
its first one-based label. -/
private theorem upperLengthOfBits_bitLength (width k K : Nat) (bits : List Bool)
    (hk : 0 < k) (hkK : k ≤ K) (hlen : bits.length = K-k+1)
    (hpos : 0 < boolWordToNat bits) :
    upperLengthOfBits width K bits =
      truthMinusOneValue width (k-1+(boolWordToNat bits).size) := by
  have hs := boolWordToNat_size_from_highest bits
  have hp : 0 < (boolWordToNat bits).size := Nat.size_pos.mpr (by omega)
  have hf : bits.reverse.findIdx id < bits.length := by omega
  unfold upperLengthOfBits
  rw [if_pos hf]
  congr 1
  omega

/-- A nonzero lower scan reports the position determined by the reversed word's
bit length. -/
private theorem lowerLengthOfBits_bitLength (n width k : Nat) (bits : List Bool)
    (hpos : 0 < boolWordToNat bits.reverse) :
    lowerLengthOfBits n width k bits =
      rightLengthValue n width (k+bits.length-(boolWordToNat bits.reverse).size) := by
  have hs := boolWordToNat_size_from_highest bits.reverse
  simp only [List.length_reverse, List.reverse_reverse] at hs
  have hp : 0 < (boolWordToNat bits.reverse).size := Nat.size_pos.mpr (by omega)
  have hf : bits.findIdx id < bits.length := by omega
  unfold lowerLengthOfBits
  rw [if_pos hf]
  congr 1
  omega

/-- An all-zero numeric scan produces the source all-ones sentinel. -/
private theorem lengthOfBits_zero (n width k K : Nat) (bits : List Bool)
    (hzero : boolWordToNat bits = 0) :
    upperLengthOfBits width K bits = 2^width-1 ∧
      lowerLengthOfBits n width k bits.reverse = 2^width-1 := by
  have hs := boolWordToNat_size_from_highest bits
  rw [hzero, Nat.size_zero] at hs
  have hf : ¬bits.reverse.findIdx id < bits.length := by omega
  simp only [upperLengthOfBits, lowerLengthOfBits, List.length_reverse, if_neg hf, and_self]

theorem upperLengthOfBits_numeric (width k K : Nat) (bits : List Bool)
    (hk : 0 < k) (hkK : k ≤ K) (hlen : bits.length = K-k+1) :
    upperLengthOfBits width K bits = if boolWordToNat bits = 0 then 2^width-1
      else truthMinusOneValue width (k-1+(boolWordToNat bits).size) := by
  by_cases hz : boolWordToNat bits = 0
  · rw [if_pos hz]; exact (lengthOfBits_zero 0 width k K bits hz).1
  · rw [if_neg hz]
    exact upperLengthOfBits_bitLength width k K bits hk hkK hlen (by omega)

theorem lowerLengthOfBits_numeric (n width k : Nat) (bits : List Bool) :
    lowerLengthOfBits n width k bits = if boolWordToNat bits.reverse = 0 then 2^width-1
      else rightLengthValue n width (k+bits.length-(boolWordToNat bits.reverse).size) := by
  by_cases hz : boolWordToNat bits.reverse = 0
  · rw [if_pos hz]
    simpa only [List.reverse_reverse] using (lengthOfBits_zero n width k 0 bits.reverse hz).2
  · rw [if_neg hz]; exact lowerLengthOfBits_bitLength n width k bits (by omega)

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

/-- Consistent old length words are replaced by the numerical bit lengths of
both swapped scan words, with the all-ones sentinel for a zero word. -/
private theorem endIterationLengthWords_numeric
    (r : EndIterationRegisters) (n : Nat) (windows : EndIterationWindows)
    (boundary4 boundary5 : Nat) (state : BasisState)
    (hk4 : 0 < windows.k4) (hupper : windows.k4 ≤ windows.K4)
    (hlower : windows.k5 ≤ windows.K5Decode n) (henabled : state r.control = true)
    (hT : wireValues r.lengthT state = constantBits r.lengthT.length
      (upperLengthOfBits r.lengthT.length windows.K4
        (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
          (wireValues r.work1 state))))
    (hRP : wireValues r.lengthRP state = constantBits r.lengthRP.length
      (lowerLengthOfBits n r.lengthRP.length windows.k5
        (endIterationLowerRangeBits true boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues r.work2 state)))) :
    let upper := endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
      (wireValues r.work2 state)
    let lower := endIterationLowerRangeBits true boundary5
      (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues r.work1 state)
    endIterationLengthWords r n windows boundary4 boundary5 state =
      (constantBits r.lengthT.length (if boolWordToNat upper = 0 then 2^r.lengthT.length-1
        else truthMinusOneValue r.lengthT.length (windows.k4-1+(boolWordToNat upper).size)),
       constantBits r.lengthRP.length (if boolWordToNat lower.reverse = 0 then 2^r.lengthRP.length-1
        else rightLengthValue n r.lengthRP.length
          (windows.k5+lower.length-(boolWordToNat lower.reverse).size))) := by
  dsimp only
  rw [endIterationLengthWords_replace r n windows boundary4 boundary5 state hupper hlower henabled hT hRP]
  rw [upperLengthOfBits_numeric r.lengthT.length windows.k4 windows.K4 _ hk4 hupper,
    lowerLengthOfBits_numeric]
  simp only [endIterationUpperRangeBits, List.length_map, zeroMapLabels_eq_range', List.length_range']
  omega

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

/-- The same actual enabled bank-and-length circuit produces metadata determined
by the numerical bit lengths of its swapped scan words. Old metadata consistency
and routing remain explicit; this is not a whole-loop reachability theorem. -/
theorem swapWorkAndLengthUnaryShared_numeric_lengths
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
    let upper := endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
      (wireValues r.work2 state)
    let lower := endIterationLowerRangeBits true boundary5
      (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues r.work1 state)
    (wireValues r.lengthT (run (swapWorkAndLengthUnaryShared r n windows) state),
      wireValues r.lengthRP (run (swapWorkAndLengthUnaryShared r n windows) state)) =
      (constantBits r.lengthT.length (if boolWordToNat upper = 0 then 2^r.lengthT.length-1
        else truthMinusOneValue r.lengthT.length (windows.k4-1+(boolWordToNat upper).size)),
       constantBits r.lengthRP.length (if boolWordToNat lower.reverse = 0 then 2^r.lengthRP.length-1
        else rightLengthValue n r.lengthRP.length
          (windows.k5+lower.length-(boolWordToNat lower.reverse).size))) := by
  have h := swapWorkAndLengthUnaryShared_correct r n windows boundary4 boundary5
    hboundary4 hboundary5 state hlayout hroute4 hroute5 hready
  dsimp only at h ⊢
  rw [h.2.2.1]
  exact endIterationLengthWords_numeric r n windows boundary4 boundary5 state
    hlayout.k4_positive hlayout.k4_le_K4 hlayout.k5_le_decode henabled hT hRP

end ShorECDLP.Paper2607_13816
