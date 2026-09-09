import ShorECDLP.Submission.«2607_13816».EEA.BlockBReduction

/-! # Numeric remainder effect of the complete source Block B -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem be_append (xs ys : List Bool) :
    boolWordToNat (xs++ys).reverse = boolWordToNat ys.reverse + 2^ys.length*boolWordToNat xs.reverse := by
  have le_append (a b : List Bool) : boolWordToNat (a++b) = boolWordToNat a+2^a.length*boolWordToNat b := by
    induction a with
    | nil => simp
    | cons c a ih => simp only [List.cons_append,boolWordToNat_cons,List.length_cons,ih,Nat.pow_succ]; ring
  rw [List.reverse_append,le_append,List.length_reverse]
private theorem conditional_scaled (x y low scale : Nat) (phase : Bool)
    (hl : low < scale) :
    (if phase && decide (y≤x) then x-y else x)*scale+low =
      if phase && decide (y*scale≤x*scale+low) then x*scale+low-y*scale else x*scale+low := by
  have he : y≤x ↔ y*scale≤x*scale+low := by
    constructor
    · intro hy; nlinarith
    · intro hy
      by_contra hn
      have hh : x+1≤y := by omega
      nlinarith
  simp only [← he]
  split
  · have hh : y≤x := by simp_all
    have hm := Nat.mul_le_mul_right scale hh
    rw [Nat.sub_mul]
    omega
  · rfl
/-- Decoding all remainder bits yields conditional subtraction of the aligned
divisor, including the low shift bits preserved by the actual source circuit. -/
theorem blockBForward_remainderValue (r : IndexedStepRegisters) (n index ellT ellQ shift : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (hphase : state r.phase1 = false) (hsign0 : state r.sign = false)
    (hrp : wireAnd r.lengthRPrime state = false)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length ellT)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length ellQ)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : (certifiedActiveWindows n index).remainder.start ≤ ellT+ellQ+2)
    (hleftHigh : ellT+ellQ+2-(certifiedActiveWindows n index).remainder.start < 2^r.lengthQ.length)
    (hrightLow : shift+(certifiedActiveWindows n index).remainder.start ≤ n+3)
    (hrightHigh : n+3-shift-(certifiedActiveWindows n index).remainder.start < 2^r.lengthS.length)
    (horder : ellT+ellQ+2-(certifiedActiveWindows n index).remainder.start ≤
      n+3-shift-(certifiedActiveWindows n index).remainder.start) :
    let w := (certifiedActiveWindows n index).remainder
    let start := ellT+ellQ+1
    let width := n+3-shift-(ellT+ellQ+2)+1
    let remainder := fun st => boolWordToNat ((wireValues r.work1 st).drop start).reverse
    let divisor := boolWordToNat (((wireValues r.work2 state).drop start).take width).reverse * 2^shift
    remainder (run (blockBForward r n w) state) =
      if state r.phase2 && decide (divisor ≤ remainder state) then remainder state-divisor else remainder state := by
  let w := (certifiedActiveWindows n index).remainder
  let start := ellT+ellQ+1
  let width := n+3-shift-(ellT+ellQ+2)+1
  let before := wireValues r.work1 state
  let x := boolWordToNat ((before.drop start).take width).reverse
  let y := boolWordToNat (((wireValues r.work2 state).drop start).take width).reverse
  let result := if state r.phase2 && decide (y≤x) then x-y else x
  let low := boolWordToNat (before.drop (n+3-shift)).reverse
  have hw : 1 ≤ w.start := by simp only [w,certifiedActiveWindows,certifiedRemainderWindow]; omega
  change w.start ≤ ellT+ellQ+2 at hleftLow
  change shift+w.start ≤ n+3 at hrightLow
  change ellT+ellQ+2-w.start ≤ n+3-shift-w.start at horder
  have hend : start+width = n+3-shift := by dsimp only [start,width]; omega
  have hlen : before.length = n+3 := by simp only [before,wireValues,List.length_map,h.work1_length]
  have hpre : (before.take start).length = start := by rw [List.length_take,hlen]; omega
  have hlowlen : (before.drop (n+3-shift)).length = shift := by rw [List.length_drop,hlen]; omega
  have hlow : low < 2^shift := by
    have hh := boolWordToNat_lt_pow_two (before.drop (n+3-shift)).reverse
    simpa only [List.length_reverse,hlowlen] using hh
  have hsplit : boolWordToNat (before.drop start).reverse = x*2^shift+low := by
    have he := be_append ((before.drop start).take width) ((before.drop start).drop width)
    rw [List.take_append_drop,List.drop_drop,hend,hlowlen] at he
    simpa only [x,low,Nat.mul_comm,Nat.add_comm] using he
  have hresult : result < 2^width := by
    have hh := boolWordToNat_lt_pow_two ((before.drop start).take width).reverse
    have hl : ((before.drop start).take width).reverse.length ≤ width := by simp
    have hx : x < 2^width := hh.trans_le (Nat.pow_le_pow_right (by decide) hl)
    dsimp only [result]
    split <;> omega
  have hword := blockBForward_activeWord r n index ellT ellQ shift state h hc hphase hsign0 hrp ht hq hs
    hleftLow hleftHigh hrightLow hrightHigh horder
  change boolWordToNat ((wireValues r.work1 (run (blockBForward r n w) state)).drop start).reverse =
    if state r.phase2 && decide (y*2^shift ≤ boolWordToNat (before.drop start).reverse) then
      boolWordToNat (before.drop start).reverse-y*2^shift else boolWordToNat (before.drop start).reverse
  rw [hword]
  change boolWordToNat ((before.take start ++ (constantBits width result).reverse ++ before.drop (n+3-shift)).drop start).reverse = _
  have hd := List.drop_left' (l₂ := (constantBits width result).reverse ++ before.drop (n+3-shift)) hpre
  rw [List.append_assoc,hd,be_append,hlowlen,List.reverse_reverse,
    boolWordToNat_constantBits,Nat.mod_eq_of_lt hresult,hsplit]
  rw [Nat.mul_comm,Nat.add_comm]
  exact conditional_scaled x y low (2^shift) (state r.phase2) hlow

end ShorECDLP.Paper2607_13816
