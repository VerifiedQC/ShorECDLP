import ShorECDLP.Submission.«2607_13816».EEA.PackedDivisor

/-! # Complete canonical Block B output and comparison sign -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem high_compare (bits : List Bool) (count y : Nat) :
    boolWordToNat (bits.take count).reverse < y ↔
      boolWordToNat bits.reverse < y*2^(bits.length-count) := by
  have append_value (a b : List Bool) : boolWordToNat (a++b) = boolWordToNat a+2^a.length*boolWordToNat b := by
    induction a with
    | nil => simp
    | cons c a ih => simp only [List.cons_append,boolWordToNat_cons,List.length_cons,ih,Nat.pow_succ]; ring
  have he := append_value (bits.drop count).reverse (bits.take count).reverse
  rw [← List.reverse_append,List.take_append_drop,List.length_reverse,List.length_drop] at he
  have hlo := boolWordToNat_lt_pow_two (bits.drop count).reverse
  simp only [List.length_reverse,List.length_drop] at hlo
  rw [he]
  constructor
  · intro h; have hh : boolWordToNat (bits.take count).reverse+1≤y := by omega
    nlinarith
  · intro h; by_contra hn
    have hh : y≤boolWordToNat (bits.take count).reverse := by omega
    nlinarith
/-- Actual Block B records the logical shifted-divisor comparison in its sign. -/
theorem blockBForward_packedSign (r : IndexedStepRegisters) (n index : Nat)
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
    run (blockBForward r n (certifiedActiveWindows n index).remainder) state r.sign =
      (decide (logical.r < logical.rPrime*2^logical.shift) ^^ state r.phase2) := by
  have hb := blockBForward_activeArithmetic r n index logical.lT logical.lQ logical.shift state h hc hphase hsign0 hrp
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
  let width := n+3-logical.shift-(logical.lT+logical.lQ+2)+1
  let bits := (wireValues r.work1 state).drop (logical.lT+logical.lQ+1)
  have hsuffix : bits.length-width = logical.shift := by
    simp only [bits,wireValues,List.length_drop,List.length_map,h.work1_length,width]
    rw [hwidth]
    omega
  have hcompare := high_compare bits width logical.rPrime
  rw [hsuffix] at hcompare
  have hbits : boolWordToNat bits.reverse = logical.r := hdecode
  rw [hbits] at hcompare
  dsimp only at hb hd
  have hsign := hb.2.1
  rw [hwidth,hwork2,hd] at hsign
  have he : decide (boolWordToNat (bits.take width).reverse < logical.rPrime) =
      decide (logical.r < logical.rPrime*2^logical.shift) := by simp only [hcompare]
  rw [← hwidth] at hsign
  rw [he] at hsign
  exact hsign

/-- Canonical output bank, logical comparison sign, complete external frame,
and clean auxiliary bank for the actual remainder block. -/
theorem blockBForward_packedContract (r : IndexedStepRegisters) (n index : Nat)
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
    let final := run (blockBForward r n (certifiedActiveWindows n index).remainder) state
    let result := if state r.phase2 && decide (logical.rPrime*2^logical.shift ≤ logical.r) then
      logical.r-logical.rPrime*2^logical.shift else logical.r
    wireValues r.work1 final =
      constantBits logical.lT logical.t ++ [false] ++ (constantBits logical.lQ logical.q).reverse ++
        (constantBits (n+3-(logical.lT+logical.lQ+1)) result).reverse ∧
    final r.sign = (decide (logical.r < logical.rPrime*2^logical.shift) ^^ state r.phase2) ∧
    AgreesOutside (r.sign :: r.work1) final state ∧ Clean r.aux final := by
  refine ⟨?_,?_,blockBForward_frame r n index state h hc,?_⟩
  · exact blockBForward_packedWork1 r n index logical state h hc hphase hsign0 hrp
      ht hq hs hleftLow hleftHigh hrightLow hrightHigh horder hdivWidth hspan hcoeff hdiv hrem hwork1 hwork2
  · exact blockBForward_packedSign r n index logical state h hc hphase hsign0 hrp
      ht hq hs hleftLow hleftHigh hrightLow hrightHigh horder hdivWidth hspan hcoeff hdiv hrem hwork1 hwork2
  · exact (blockBForward_activeArithmetic r n index logical.lT logical.lQ logical.shift state h hc hphase hsign0 hrp
      ht hq hs hleftLow hleftHigh hrightLow hrightHigh horder).2.2

end ShorECDLP.Paper2607_13816
