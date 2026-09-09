import ShorECDLP.Submission.«2607_13816».EEA.PackedRotation
import ShorECDLP.Submission.«2607_13816».EEA.BlockBRemainder

/-! # Recovering the aligned divisor from canonical rotated packing -/
namespace ShorECDLP.Paper2607_13816
open Classical

private theorem zero_word (n : Nat) : boolWordToNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

private theorem coefficient_tail_zero (width value start : Nat) (hs : start ≤ width)
    (hv : value < 2^start) :
    (constantBits width value).drop start = List.replicate (width-start) false := by
  apply boolWordToNat_injective_of_length
  · simp only [List.length_drop,constantBits_length,List.length_replicate]
  · have hh := boolWordToNat_slice (constantBits width value) start (width-start) (by simp; omega)
    have ht : ((constantBits width value).drop start).take (width-start) = (constantBits width value).drop start := by
      apply (List.take_eq_self_iff _).mpr
      simp
    rw [ht,boolWordToNat_constantBits] at hh
    have hw : value < 2^width := hv.trans_le (Nat.pow_le_pow_right (by decide) hs)
    rw [Nat.mod_eq_of_lt hw,Nat.div_eq_of_lt hv,Nat.zero_mod] at hh
    rw [hh,zero_word]

private theorem rotated_tail_slice (bits : List Bool) (shift start : Nat)
    (hs : shift+start ≤ bits.length) :
    ((bits.rotate shift).drop start).take (bits.length-shift-start) = bits.drop (shift+start) := by
  rw [List.rotate_eq_drop_append_take (by omega),List.drop_append,List.length_drop,
    Nat.sub_eq_zero_of_le (by omega : start ≤ bits.length-shift),List.drop_zero,List.drop_drop]
  have he : (bits.drop (shift+start)).length = bits.length-shift-start := by simp only [List.length_drop]; omega
  rw [← he,List.take_left]

/-- The selected field of the rotated canonical second bank is the logical
divisor when the coefficient fits strictly below its lower boundary. -/
theorem packedRotatedDivisor_value (coefficientWidth divisorWidth coefficient divisor shift start : Nat)
    (hstart : start+shift ≤ coefficientWidth)
    (hc : coefficient < 2^(start+shift)) (hd : divisor < 2^divisorWidth) :
    let bank := (constantBits coefficientWidth coefficient ++ (constantBits divisorWidth divisor).reverse).rotate shift
    boolWordToNat ((bank.drop start).take (coefficientWidth+divisorWidth-shift-start)).reverse = divisor := by
  let bits := constantBits coefficientWidth coefficient ++ (constantBits divisorWidth divisor).reverse
  have hl : bits.length = coefficientWidth+divisorWidth := by simp only [bits,List.length_append,List.length_reverse,constantBits_length]
  have hr := rotated_tail_slice bits shift start (by rw [hl]; omega)
  dsimp only
  rw [← hl,hr]
  change boolWordToNat ((constantBits coefficientWidth coefficient ++ (constantBits divisorWidth divisor).reverse).drop (shift+start)).reverse = divisor
  rw [List.drop_append,constantBits_length,Nat.sub_eq_zero_of_le (by omega : shift+start ≤ coefficientWidth),List.drop_zero,
    coefficient_tail_zero coefficientWidth coefficient (shift+start) (by omega) (by simpa [Nat.add_comm] using hc),
    List.reverse_append,List.reverse_reverse,List.reverse_replicate]
  have append_zero (bs : List Bool) (n : Nat) : boolWordToNat (bs ++ List.replicate n false) = boolWordToNat bs := by
    induction bs with
    | nil => simp [zero_word]
    | cons b bs ih => simp [ih]
  rw [append_zero,boolWordToNat_constantBits,Nat.mod_eq_of_lt hd]

/-- With canonical packed input banks, actual Block B compares or subtracts
the logical divisor shifted by the stored amount. Packing and fit obligations
remain explicit; this is not a reachable-state invariant. -/
theorem blockBForward_packedRemainder (r : IndexedStepRegisters) (n index : Nat)
    (logical : EEAState) (state : BasisState) (h : IndexedStepLayout r n index)
    (hc : Clean r.aux state) (hphase : state r.phase1 = false) (hsign0 : state r.sign = false)
    (hrp : wireAnd r.lengthRPrime state = false)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length logical.lT)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length logical.lQ)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length logical.shift)
    (hleftLow : (certifiedActiveWindows n index).remainder.start ≤ logical.lT+logical.lQ+2)
    (hleftHigh : logical.lT+logical.lQ+2-(certifiedActiveWindows n index).remainder.start < 2^r.lengthQ.length)
    (hrightLow : logical.shift+(certifiedActiveWindows n index).remainder.start ≤ n+3)
    (hrightHigh : n+3-logical.shift-(certifiedActiveWindows n index).remainder.start < 2^r.lengthS.length)
    (horder : logical.lT+logical.lQ+2-(certifiedActiveWindows n index).remainder.start ≤
      n+3-logical.shift-(certifiedActiveWindows n index).remainder.start)
    (hdivWidth : logical.lRPrime ≤ n+3)
    (hspan : logical.lT+logical.lQ+1+logical.shift ≤ n+3-logical.lRPrime)
    (hcoeff : logical.tPrime < 2^(logical.lT+logical.lQ+1+logical.shift))
    (hdiv : logical.rPrime < 2^logical.lRPrime)
    (hrem : logical.r < 2^(n+3-(logical.lT+logical.lQ+1)))
    (hwork1 : wireValues r.work1 state =
      constantBits logical.lT logical.t ++ [false] ++ (constantBits logical.lQ logical.q).reverse ++
        (constantBits (n+3-(logical.lT+logical.lQ+1)) logical.r).reverse)
    (hwork2 : wireValues r.work2 state =
      (constantBits (n+3-logical.lRPrime) logical.tPrime ++
        (constantBits logical.lRPrime logical.rPrime).reverse).rotate logical.shift) :
    boolWordToNat ((wireValues r.work1
      (run (blockBForward r n (certifiedActiveWindows n index).remainder) state)).drop
        (logical.lT+logical.lQ+1)).reverse =
      if state r.phase2 && decide (logical.rPrime*2^logical.shift ≤ logical.r) then
        logical.r-logical.rPrime*2^logical.shift else logical.r := by
  have hb := blockBForward_remainderValue r n index logical.lT logical.lQ logical.shift state h hc hphase hsign0 hrp
    ht hq hs hleftLow hleftHigh hrightLow hrightHigh horder
  let pre := constantBits logical.lT logical.t ++ [false] ++ (constantBits logical.lQ logical.q).reverse
  have hpre : pre.length = logical.lT+logical.lQ+1 := by simp only [pre,List.length_append,List.length_reverse,constantBits_length,List.length_singleton]; omega
  have hdecode : boolWordToNat ((wireValues r.work1 state).drop (logical.lT+logical.lQ+1)).reverse = logical.r := by
    rw [hwork1]
    change boolWordToNat ((pre ++ (constantBits (n+3-(logical.lT+logical.lQ+1)) logical.r).reverse).drop (logical.lT+logical.lQ+1)).reverse = _
    rw [List.drop_left' hpre,List.reverse_reverse,boolWordToNat_constantBits,Nat.mod_eq_of_lt hrem]
  have hd := packedRotatedDivisor_value (n+3-logical.lRPrime) logical.lRPrime logical.tPrime logical.rPrime
    logical.shift (logical.lT+logical.lQ+1) hspan hcoeff hdiv
  have hwidth : n+3-logical.shift-(logical.lT+logical.lQ+2)+1 =
      n+3-logical.lRPrime+logical.lRPrime-logical.shift-(logical.lT+logical.lQ+1) := by
    let w := (certifiedActiveWindows n index).remainder
    change w.start ≤ logical.lT+logical.lQ+2 at hleftLow
    change logical.shift+w.start ≤ n+3 at hrightLow
    change logical.lT+logical.lQ+2-w.start ≤ n+3-logical.shift-w.start at horder
    have hw : 1 ≤ w.start := by simp only [w,certifiedActiveWindows,certifiedRemainderWindow]; omega
    omega
  dsimp only at hb hd
  rw [hdecode,hwidth,hwork2,hd] at hb
  exact hb

end ShorECDLP.Paper2607_13816
