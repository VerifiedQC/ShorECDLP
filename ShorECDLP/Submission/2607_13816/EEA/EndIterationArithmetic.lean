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

private theorem length_constant_succ (width value : Nat) :
    constantBits (width+1) value = value.testBit 0 :: constantBits width (value/2) := by
  unfold constantBits
  simp only [List.replicate_succ, xorConstantBits]
  cases hbit : value.testBit 0 <;> simp
private theorem length_constant_getD (width value i : Nat) (hi : i < width) :
    (constantBits width value).getD i false = value.testBit i := by
  induction width generalizing value i with
  | zero => omega
  | succ width ih =>
    rw [length_constant_succ]
    cases i with
    | zero => rfl
    | succ i =>
      change (constantBits width (value/2)).getD i false = value.testBit (i+1)
      rw [ih _ _ (by omega), Nat.testBit_div_two]

private theorem length_size_div_pow_two (value offset : Nat) :
    (value / 2^offset).size = value.size-offset := by
  by_cases ho : value.size ≤ offset
  · rw [Nat.div_eq_of_lt (Nat.size_le.mp ho), Nat.size_zero, Nat.sub_eq_zero_of_le ho]
  · have ho : offset < value.size := by omega
    have hp : 0 < 2^offset := Nat.two_pow_pos _
    have hu : (value/2^offset).size ≤ value.size-offset := by
      apply Nat.size_le.mpr
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      rw [← pow_add, Nat.sub_add_cancel (by omega : offset ≤ value.size)]
      exact Nat.lt_size_self _
    have hl : value.size-offset-1 < (value/2^offset).size := by
      apply Nat.lt_size.mpr
      apply (Nat.le_div_iff_mul_le hp).mpr
      rw [← pow_add]
      apply Nat.lt_size.mp
      omega
    omega

private theorem upper_range_packed (k K B value : Nat) (tail : List Bool)
    (hk : 0 < k) (hkK : k ≤ K) (hfit : value < 2^B) :
    endIterationUpperRangeBits true B (zeroMapLabels k K) (constantBits B value ++ tail) =
      constantBits (K-k+1) (value / 2^(k-1)) := by
  simp only [endIterationUpperRangeBits, zeroMapLabels_eq_range']
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range', constantBits_length]; omega
  · intro i hi hj
    have hib : i < K-k+1 := by simpa only [constantBits_length] using hj
    rw [← List.getD_eq_getElem _ false hj, length_constant_getD _ _ _ hib]
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
    rw [Nat.testBit_div_two_pow]
    have he : i+(k-1) = k+i-1 := by omega
    rw [he]
    by_cases hb : k+i ≤ B
    · simp only [decide_eq_true hb, Bool.true_and]
      rw [List.getD_append _ _ _ _ (by simp only [constantBits_length]; omega),
        length_constant_getD _ _ _ (by omega)]
    · have hpow : 2^B ≤ 2^(k+i-1) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (hfit.trans_le hpow)]
      simp only [decide_eq_false hb, Bool.true_and, Bool.false_and]

/-- A canonical low coefficient field is recovered by an upper scan whose
window starts no later than its highest bit. The masked tail is arbitrary. -/
theorem upperLengthOfBits_packed_coefficient (width k K B value : Nat) (tail : List Bool)
    (hk : 0 < k) (hstart : k ≤ value.size) (hstop : value.size ≤ K)
    (hfit : value < 2^B) :
    upperLengthOfBits width K
      (endIterationUpperRangeBits true B (zeroMapLabels k K) (constantBits B value ++ tail)) =
      truthMinusOneValue width value.size := by
  have hkK := hstart.trans hstop
  rw [upper_range_packed k K B value tail hk hkK hfit,
    upperLengthOfBits_numeric width k K _ hk hkK (constantBits_length _ _),
    boolWordToNat_constantBits]
  have hsize := length_size_div_pow_two value (k-1)
  have hcap : value / 2^(k-1) < 2^(K-k+1) := by
    apply Nat.size_le.mp
    omega
  rw [Nat.mod_eq_of_lt hcap]
  have hn : value / 2^(k-1) ≠ 0 := by
    intro hz; rw [hz, Nat.size_zero] at hsize; omega
  rw [if_neg hn, hsize]
  congr 1
  omega

private theorem length_high_bit (value : Nat) (hpos : 0 < value) :
    value.testBit (value.size-1) = true := by
  have hs : 0 < value.size := Nat.size_pos.mpr hpos
  have hp : 0 < 2^(value.size-1) := Nat.two_pow_pos _
  have hlo : 1 ≤ value/2^(value.size-1) := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    simp only [one_mul]
    exact Nat.lt_size.mp (by omega)
  have hhi : value/2^(value.size-1) < 2 := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hs]
    exact Nat.lt_size_self _
  have hdiv : value/2^(value.size-1) = 1 := by omega
  rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
  decide

private theorem lower_range_packed_bit (k K B R value i : Nat) (pre : List Bool)
    (hk : 0 < k) (hK : K ≤ pre.length+R) (hB : pre.length < B)
    (hi : i < K-k+1) (hkK : k ≤ K) :
    (endIterationLowerRangeBits true B (zeroMapLabels k K)
      (pre ++ (constantBits R value).reverse)).getD i false =
        (decide (B ≤ k+i) && value.testBit (pre.length+R-(k+i))) := by
  have hlen : (endIterationLowerRangeBits true B (zeroMapLabels k K)
      (pre ++ (constantBits R value).reverse)).length = K-k+1 := by
    simp only [endIterationLowerRangeBits, List.length_map, zeroMapLabels_eq_range', List.length_range']
    omega
  rw [List.getD_eq_getElem _ false (by omega : i < (endIterationLowerRangeBits true B (zeroMapLabels k K) (pre ++ (constantBits R value).reverse)).length)]
  simp only [endIterationLowerRangeBits, zeroMapLabels_eq_range', List.getElem_map,
    List.getElem_range', Nat.one_mul, Bool.true_and]
  by_cases hb : B ≤ k+i
  · simp only [decide_eq_true hb, Bool.true_and]
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_reverse _ (by simp only [constantBits_length]; omega)]
    simp only [constantBits_length]
    rw [length_constant_getD _ _ _ (by omega)]
    congr 1
    omega
  · simp only [decide_eq_false hb, Bool.false_and]

/-- A lower scan of a packed big-endian remainder recovers its highest set
position, even when the arbitrary prefix extends below the masked boundary. -/
theorem lowerLengthOfBits_packed_remainder (n width k K B R value : Nat) (pre : List Bool)
    (hk : 0 < k) (hbank : pre.length+R = n+3) (hK : K ≤ n+3)
    (hB : pre.length < B) (hfit : value < 2^R) (hpos : 0 < value)
    (hstart : k ≤ n+4-value.size) (hstop : n+4-value.size ≤ K)
    (hmask : B ≤ n+4-value.size) :
    lowerLengthOfBits n width k
      (endIterationLowerRangeBits true B (zeroMapLabels k K)
        (pre ++ (constantBits R value).reverse)) =
      rightLengthValue n width (n+4-value.size) := by
  let bits := endIterationLowerRangeBits true B (zeroMapLabels k K)
    (pre ++ (constantBits R value).reverse)
  have hkK := hstart.trans hstop
  have hsize : value.size ≤ R := Nat.size_le.mpr hfit
  have hpositive : 0 < value.size := Nat.size_pos.mpr hpos
  have hlen : bits.length = K-k+1 := by
    simp only [bits, endIterationLowerRangeBits, List.length_map, zeroMapLabels_eq_range', List.length_range']
    omega
  have hidx : n+4-value.size-k < bits.length := by omega
  have hfind : bits.findIdx id = n+4-value.size-k := by
    apply (List.findIdx_eq hidx).mpr
    constructor
    · change bits[n+4-value.size-k] = true
      rw [← List.getD_eq_getElem bits false hidx,
        lower_range_packed_bit k K B R value _ pre hk (by omega) hB (by omega) hkK]
      have he : k+(n+4-value.size-k) = n+4-value.size := by omega
      rw [he, decide_eq_true hmask, Bool.true_and]
      have hp : pre.length+R-(n+4-value.size) = value.size-1 := by omega
      rw [hp]; exact length_high_bit value hpos
    · intro j hj
      change bits[j] = false
      rw [← List.getD_eq_getElem bits false (by omega),
        lower_range_packed_bit k K B R value j pre hk (by omega) hB (by omega) hkK]
      have hp : value.size ≤ pre.length+R-(k+j) := by omega
      have hv : value < 2^(pre.length+R-(k+j)) := Nat.size_le.mp hp
      rw [Nat.testBit_lt_two_pow hv, Bool.and_false]
  change lowerLengthOfBits n width k bits = _
  unfold lowerLengthOfBits
  rw [hfind, if_pos hidx]
  congr 1
  omega

/-- A zero packed remainder yields the all-ones sentinel, independent of the
masked prefix and without a highest-bit window premise. -/
theorem lowerLengthOfBits_packed_zero (n width k K B R : Nat) (pre : List Bool)
    (hk : 0 < k) (hkK : k ≤ K) (hK : K ≤ pre.length+R) (hB : pre.length < B) :
    lowerLengthOfBits n width k
      (endIterationLowerRangeBits true B (zeroMapLabels k K)
        (pre ++ (constantBits R 0).reverse)) = 2^width-1 := by
  let bits := endIterationLowerRangeBits true B (zeroMapLabels k K)
    (pre ++ (constantBits R 0).reverse)
  have hlen : bits.length = K-k+1 := by
    simp only [bits, endIterationLowerRangeBits, List.length_map, zeroMapLabels_eq_range', List.length_range']
    omega
  have hf : bits.findIdx id = bits.length := by
    apply List.findIdx_eq_length_of_false
    intro bit hbit
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hbit
    rw [← he]
    change bits[i] = false
    rw [← List.getD_eq_getElem bits false hi,
      lower_range_packed_bit k K B R 0 i pre hk hK hB (by omega) hkK]
    simp only [Nat.zero_testBit, Bool.and_false]
  change lowerLengthOfBits n width k bits = _
  simp only [lowerLengthOfBits, hf, Nat.lt_irrefl, if_false]

private theorem endpoint_mod_sub (width a b : Nat) (hb : b ≤ a) :
    (a+2^width-b%2^width)%2^width = (a-b)%2^width := by
  have hp : 0 < 2^width := Nat.two_pow_pos _
  have ha : Nat.ModEq (2^width) (a+2^width) a := by simp [Nat.ModEq]
  have hm : Nat.ModEq (2^width) (b%2^width) b := by simp [Nat.ModEq]
  exact Nat.ModEq.sub (by have := Nat.mod_lt b hp; omega) hb ha hm

private theorem rightLengthValue_bitLength (n width size : Nat) (hs : 0 < size) (hb : size ≤ n+3) :
    rightLengthValue n width (n+4-size) = truthMinusOneValue width size := by
  change (n+3+2^width-(n+4-size)%2^width)%2^width = (size+2^width-1%2^width)%2^width
  rw [endpoint_mod_sub _ _ _ (by omega), endpoint_mod_sub _ _ _ (by omega)]
  congr 1
  omega

private theorem endpoint_truth_zero (width : Nat) : truthMinusOneValue width 0 = 2^width-1 := by
  change (0+2^width-1%2^width)%2^width = 2^width-1
  have hp : 0 < 2^width := Nat.two_pow_pos _
  by_cases h : 2^width = 1
  · simp [h]
  · have hh : 1 < 2^width := by omega
    rw [Nat.mod_eq_of_lt hh]
    simp only [zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]

private theorem endpoint_packed_lower_length (n width k K B R value : Nat) (pre : List Bool)
    (hk : 0 < k) (hkK : k ≤ K) (hbank : pre.length+R = n+3) (hK : K ≤ n+3)
    (hB : pre.length < B) (hfit : value < 2^R)
    (hcover : value ≠ 0 → k ≤ n+4-value.size ∧ n+4-value.size ≤ K ∧ B ≤ n+4-value.size) :
    lowerLengthOfBits n width k (endIterationLowerRangeBits true B (zeroMapLabels k K)
      (pre ++ (constantBits R value).reverse)) = truthMinusOneValue width value.size := by
  by_cases hz : value = 0
  · subst value
    rw [lowerLengthOfBits_packed_zero n width k K B R pre hk hkK (by omega) hB,
      Nat.size_zero, endpoint_truth_zero]
  · obtain ⟨hstart,hstop,hmask⟩ := hcover hz
    rw [lowerLengthOfBits_packed_remainder n width k K B R value pre hk hbank hK hB hfit
      (by omega) hstart hstop hmask]
    exact rightLengthValue_bitLength n width value.size (Nat.size_pos.mpr (by omega))
      (by have hs := Nat.size_le.mpr hfit; omega)

/-- The actual enabled endpoint circuit replaces canonical old coefficient and
remainder lengths by the lengths of the exchanged fields. Scan consistency is
derived from packed bank views; field capacity, geometry and routing stay explicit. -/
theorem swapWorkAndLengthUnaryShared_canonical_lengths
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
    (t tPrime remainder rPrime R RPrime : Nat) (tail1 tail2 pre1 pre2 : List Bool)
    (hw1u : wireValues r.work1 state = constantBits boundary4 t ++ tail1)
    (hw2u : wireValues r.work2 state = constantBits boundary4 tPrime ++ tail2)
    (hw1l : wireValues r.work1 state = pre1 ++ (constantBits R remainder).reverse)
    (hw2l : wireValues r.work2 state = pre2 ++ (constantBits RPrime rPrime).reverse)
    (ht : t < 2^boundary4) (htp : tPrime < 2^boundary4)
    (hr : remainder < 2^R) (hrp : rPrime < 2^RPrime)
    (htWindow : windows.k4 ≤ t.size ∧ t.size ≤ windows.K4)
    (htpWindow : windows.k4 ≤ tPrime.size ∧ tPrime.size ≤ windows.K4)
    (hp1 : pre1.length < boundary5) (hp2 : pre2.length < boundary5)
    (hrWindow : remainder ≠ 0 → windows.k5 ≤ n+4-remainder.size ∧
      n+4-remainder.size ≤ windows.K5Decode n ∧ boundary5 ≤ n+4-remainder.size)
    (hrpWindow : rPrime ≠ 0 → windows.k5 ≤ n+4-rPrime.size ∧
      n+4-rPrime.size ≤ windows.K5Decode n ∧ boundary5 ≤ n+4-rPrime.size)
    (hT : wireValues r.lengthT state = constantBits r.lengthT.length
      (truthMinusOneValue r.lengthT.length t.size))
    (hRP : wireValues r.lengthRP state = constantBits r.lengthRP.length
      (truthMinusOneValue r.lengthRP.length rPrime.size)) :
    (wireValues r.lengthT (run (swapWorkAndLengthUnaryShared r n windows) state),
      wireValues r.lengthRP (run (swapWorkAndLengthUnaryShared r n windows) state)) =
      (constantBits r.lengthT.length (truthMinusOneValue r.lengthT.length tPrime.size),
       constantBits r.lengthRP.length (truthMinusOneValue r.lengthRP.length remainder.size)) := by
  have hb1 : pre1.length+R = n+3 := by
    have hh := congrArg List.length hw1l
    simpa only [wireValues, List.length_map, hlayout.work1_length,
      List.length_append, List.length_reverse, constantBits_length] using hh.symm
  have hb2 : pre2.length+RPrime = n+3 := by
    have hh := congrArg List.length hw2l
    simpa only [wireValues, List.length_map, hlayout.work2_length,
      List.length_append, List.length_reverse, constantBits_length] using hh.symm
  have hK : windows.K5Decode n ≤ n+3 := Nat.min_le_right _ _
  have hu1 : upperLengthOfBits r.lengthT.length windows.K4
      (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
        (wireValues r.work1 state)) = truthMinusOneValue r.lengthT.length t.size := by
    rw [hw1u]
    exact upperLengthOfBits_packed_coefficient _ _ _ _ _ _ hlayout.k4_positive
      htWindow.1 htWindow.2 ht
  have hu2 : upperLengthOfBits r.lengthT.length windows.K4
      (endIterationUpperRangeBits true boundary4 (zeroMapLabels windows.k4 windows.K4)
        (wireValues r.work2 state)) = truthMinusOneValue r.lengthT.length tPrime.size := by
    rw [hw2u]
    exact upperLengthOfBits_packed_coefficient _ _ _ _ _ _ hlayout.k4_positive
      htpWindow.1 htpWindow.2 htp
  have hl1 : lowerLengthOfBits n r.lengthRP.length windows.k5
      (endIterationLowerRangeBits true boundary5 (zeroMapLabels windows.k5 (windows.K5Decode n))
        (wireValues r.work1 state)) = truthMinusOneValue r.lengthRP.length remainder.size := by
    rw [hw1l]
    exact endpoint_packed_lower_length _ _ _ _ _ _ _ _ hlayout.k5_positive
      hlayout.k5_le_decode hb1 hK hp1 hr hrWindow
  have hl2 : lowerLengthOfBits n r.lengthRP.length windows.k5
      (endIterationLowerRangeBits true boundary5 (zeroMapLabels windows.k5 (windows.K5Decode n))
        (wireValues r.work2 state)) = truthMinusOneValue r.lengthRP.length rPrime.size := by
    rw [hw2l]
    exact endpoint_packed_lower_length _ _ _ _ _ _ _ _ hlayout.k5_positive
      hlayout.k5_le_decode hb2 hK hp2 hrp hrpWindow
  have result := swapWorkAndLengthUnaryShared_lengths r n windows boundary4 boundary5
    hboundary4 hboundary5 state hlayout hroute4 hroute5 hready henabled
    (by rw [hu1]; exact hT) (by rw [hl2]; exact hRP)
  rw [hu2, hl1] at result
  exact result

end ShorECDLP.Paper2607_13816
