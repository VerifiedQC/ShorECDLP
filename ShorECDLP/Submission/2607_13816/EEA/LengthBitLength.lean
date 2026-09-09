import ShorECDLP.Submission.«2607_13816».EEA.EndIterationArithmetic
import ShorECDLP.Submission.«2607_13816».EEA.InitialEncoding

/-! # Decoded length values as ordinary binary lengths -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem length_subtract_of_le (width value sub : Nat) (hle : sub ≤ value) :
    (value + 2^width - sub % 2^width) % 2^width = (value - sub) % 2^width := by
  have hm : 0 < 2^width := Nat.pow_pos (by decide)
  have hleft : sub % 2^width ≤ value + 2^width := by
    have h := Nat.mod_lt sub hm
    omega
  apply Nat.ModEq.sub hleft hle
  · show (value + 2^width) % 2^width = value % 2^width
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  · exact Nat.mod_mod sub (2^width)

private theorem length_zero_sentinel (width : Nat) :
    truthMinusOneValue width 0 = 2^width - 1 := by
  change (0 + 2^width - 1 % 2^width) % 2^width = 2^width - 1
  cases width with
  | zero => norm_num
  | succ width =>
    have hp : 0 < 2^width := Nat.pow_pos (by decide)
    have hm : 1 < 2^(width+1) := by rw [Nat.pow_succ]; omega
    rw [Nat.mod_eq_of_lt hm, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]

/-- The upper writer encodes the ordinary little-endian word's binary length,
with the source-window offset. Zero remains the truth-minus-one sentinel. -/
theorem upperLengthOfBits_size (width k K : Nat) (hkK : k ≤ K)
    (bits : List Bool) (hlen : bits.length = K - k + 1) :
    upperLengthOfBits width K bits = truthMinusOneValue width
      (if boolWordToNat bits = 0 then 0 else k + (boolWordToNat bits).size - 1) := by
  have hs := bigEndianWord_size bits.reverse
  simp only [List.reverse_reverse, List.length_reverse] at hs
  have hi : bits.reverse.findIdx id ≤ bits.length := by
    simpa using (List.findIdx_le_length (xs := bits.reverse) (p := id))
  by_cases hz : boolWordToNat bits = 0
  · have hiEq : bits.reverse.findIdx id = bits.length := by
      rw [hz] at hs
      simp only [Nat.size_zero] at hs
      omega
    simp [upperLengthOfBits, hz, hiEq, length_zero_sentinel]
  · have hp : 0 < (boolWordToNat bits).size := Nat.size_pos.mpr (by omega)
    have hfind : bits.reverse.findIdx id < bits.length := by omega
    have he : K - bits.reverse.findIdx id = k + (boolWordToNat bits).size - 1 := by omega
    simp [upperLengthOfBits, hz, hfind, he]

/-- The lower writer encodes the ordinary big-endian word's binary length plus
the omitted trailing positions. An all-zero word still encodes zero length. -/
theorem lowerLengthOfBits_size (n width k K : Nat) (hkK : k ≤ K) (hK : K ≤ n + 3)
    (bits : List Bool) (hlen : bits.length = K - k + 1) :
    lowerLengthOfBits n width k bits = truthMinusOneValue width
      (if boolWordToNat bits.reverse = 0 then 0
       else n + 3 - K + (boolWordToNat bits.reverse).size) := by
  have hs := bigEndianWord_size bits
  have hi : bits.findIdx id ≤ bits.length := List.findIdx_le_length
  by_cases hz : boolWordToNat bits.reverse = 0
  · have hiEq : bits.findIdx id = bits.length := by
      rw [hz] at hs
      simp only [Nat.size_zero] at hs
      omega
    simp [lowerLengthOfBits, hz, hiEq, length_zero_sentinel]
  · have hp : 0 < (boolWordToNat bits.reverse).size := Nat.size_pos.mpr (by omega)
    have hfind : bits.findIdx id < bits.length := by omega
    have hpos : k + bits.findIdx id ≤ n + 3 := by omega
    have hlenpos : 1 ≤ n + 3 - K + (boolWordToNat bits.reverse).size := by omega
    simp only [lowerLengthOfBits, hfind, hz, ↓reduceIte]
    change (n + 3 + 2^width - (k + bits.findIdx id) % 2^width) % 2^width =
      (n + 3 - K + (boolWordToNat bits.reverse).size + 2^width - 1 % 2^width) % 2^width
    rw [length_subtract_of_le width (n+3) _ hpos,
      length_subtract_of_le width _ 1 hlenpos]
    congr 1
    omega


/-- The actual enabled iteration-end circuit writes ordinary binary lengths of
its swapped, decoded work ranges. The old lengths are assumed arithmetically
consistent; no intermediate list-index encoding premise is required. -/
theorem swapWorkAndLengthUnaryShared_bitLengths
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
    (hT : wireValues r.lengthT state = constantBits r.lengthT.length (truthMinusOneValue r.lengthT.length (if
        boolWordToNat (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
        (wireValues r.work1 state)) = 0 then 0 else windows.k4 + (boolWordToNat (endIterationUpperRangeBits true
        boundary4 (zeroMapLabels windows.k4 windows.K4) (wireValues r.work1 state))).size - 1)))
    (hRP : wireValues r.lengthRP state = constantBits r.lengthRP.length (truthMinusOneValue r.lengthRP.length
        (if boolWordToNat (endIterationLowerRangeBits true boundary5 (zeroMapLabels windows.k5 (windows.K5Decode
        n)) (wireValues r.work2 state)).reverse = 0 then 0 else n + 3 - windows.K5Decode n + (boolWordToNat
        (endIterationLowerRangeBits true boundary5 (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues
        r.work2 state)).reverse).size))) :
    (wireValues r.lengthT (run (swapWorkAndLengthUnaryShared r n windows) state),
      wireValues r.lengthRP (run (swapWorkAndLengthUnaryShared r n windows) state)) =
      (constantBits r.lengthT.length (truthMinusOneValue r.lengthT.length (if boolWordToNat
        (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4) (wireValues r.work2
        state)) = 0 then 0 else windows.k4 + (boolWordToNat (endIterationUpperRangeBits true boundary4
        (zeroMapLabels windows.k4 windows.K4) (wireValues r.work2 state))).size - 1)),
       constantBits r.lengthRP.length (truthMinusOneValue r.lengthRP.length (if boolWordToNat
        (endIterationLowerRangeBits true boundary5 (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues
        r.work1 state)).reverse = 0 then 0 else n + 3 - windows.K5Decode n + (boolWordToNat
        (endIterationLowerRangeBits true boundary5 (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues
        r.work1 state)).reverse).size))) := by
  have hu (work : List Wire) :
      upperLengthOfBits r.lengthT.length windows.K4 (endIterationUpperRangeBits true boundary4 (zeroMapLabels
        windows.k4 windows.K4) (wireValues work state)) = (truthMinusOneValue r.lengthT.length (if boolWordToNat
        (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4) (wireValues work
        state)) = 0 then 0 else windows.k4 + (boolWordToNat (endIterationUpperRangeBits true boundary4
        (zeroMapLabels windows.k4 windows.K4) (wireValues work state))).size - 1)) := by
    apply upperLengthOfBits_size _ _ _ (hboundary4.1.trans hboundary4.2)
    rw [endIterationUpperRangeBits, List.length_map, zeroMapLabels_eq_range', List.length_range']
    omega
  have hd (work : List Wire) :
      lowerLengthOfBits n r.lengthRP.length windows.k5 (endIterationLowerRangeBits true boundary5 (zeroMapLabels
        windows.k5 (windows.K5Decode n)) (wireValues work state)) = (truthMinusOneValue r.lengthRP.length (if
        boolWordToNat (endIterationLowerRangeBits true boundary5 (zeroMapLabels windows.k5 (windows.K5Decode n))
        (wireValues work state)).reverse = 0 then 0 else n + 3 - windows.K5Decode n + (boolWordToNat
        (endIterationLowerRangeBits true boundary5 (zeroMapLabels windows.k5 (windows.K5Decode n)) (wireValues
        work state)).reverse).size)) := by
    apply lowerLengthOfBits_size _ _ _ _ (hboundary5.1.trans hboundary5.2)
      (Nat.min_le_right _ _)
    rw [endIterationLowerRangeBits, List.length_map, zeroMapLabels_eq_range', List.length_range']
    omega
  have h := swapWorkAndLengthUnaryShared_lengths r n windows boundary4 boundary5
    hboundary4 hboundary5 state hlayout hroute4 hroute5 hready henabled
    (by rw [hu]; exact hT) (by rw [hd]; exact hRP)
  simpa only [hu, hd] using h

end ShorECDLP.Paper2607_13816
