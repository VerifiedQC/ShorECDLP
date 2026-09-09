import ShorECDLP.Submission.«2607_13816».EEA.BlockECoefficient
import ShorECDLP.Submission.«2607_13816».EEA.PackedRotation

/-! # Logical coefficients inside the physical Block E windows -/
namespace ShorECDLP.Paper2607_13816
open Classical

private theorem rotated_prefix_slice (pre suffix : List Bool) (shift start width : Nat)
    (hspan : shift+start+width ≤ pre.length) :
    (((pre++suffix).rotate shift).drop start).take width =
      (pre.drop (shift+start)).take width := by
  rw [List.rotate_eq_drop_append_take (by simp only [List.length_append]; omega),
    List.drop_append,List.length_drop,List.length_append,
    Nat.sub_eq_zero_of_le (by omega : start ≤ pre.length+suffix.length-shift),List.drop_zero,List.drop_drop]
  rw [List.take_append_of_le_length (by simp only [List.length_drop,List.length_append]; omega)]
  rw [List.drop_append,Nat.sub_eq_zero_of_le (by omega : shift+start ≤ pre.length),List.drop_zero]
  rw [List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

private theorem rotated_prefix_value (pre suffix : List Bool) (shift start width : Nat)
    (hspan : shift+start+width ≤ pre.length) :
    boolWordToNat ((((pre++suffix).rotate shift).drop start).take width) =
      (boolWordToNat pre / 2^(shift+start))%2^width := by
  rw [rotated_prefix_slice pre suffix shift start width hspan]
  exact boolWordToNat_slice pre (shift+start) width hspan

private theorem append_false_value (bits : List Bool) :
    boolWordToNat (bits++[false]) = boolWordToNat bits := by
  induction bits with
  | nil => simp
  | cons b bits ih => simp [ih]

private theorem coefficient_window_value (work : List Wire) (window : ActiveWindow)
    (s : BasisState) (pre suffix : List Bool) (shift width : Nat)
    (hpacked : wireValues work s = (pre++suffix).rotate shift)
    (hwidth : width ≤ window.stop-window.start+1)
    (hspan : shift+(window.start-1)+width ≤ pre.length) :
    boolWordToNat ((wireValues (IndexedStepRegisters.windowSlice work window) s).take width) =
      (boolWordToNat pre/2^(shift+(window.start-1)))%2^width := by
  simp only [IndexedStepRegisters.windowSlice,wireValues,List.map_take,List.map_drop,List.take_take,
    Nat.min_eq_left hwidth]
  change boolWordToNat (((wireValues work s).drop (window.start-1)).take width) = _
  rw [hpacked]
  exact rotated_prefix_value pre suffix shift (window.start-1) width hspan

/-- The actual Block E circuit updates the selected logical coefficient bits and
preserves the complete neighboring packed fields. Bounds state that both selected
windows lie within their respective coefficient fields. -/
theorem blockEForward_packedCoefficients (r : IndexedStepRegisters) (n index B : Nat)
    (window : ActiveWindow) (s : BasisState) (logical : EEAState)
    (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hr : IndexedStepReady r s)
    (hb : boolWordToNat (prepareLatestPaperTBoundaryWords (s r.phase2)
      (wireValues r.lengthT s) (wireValues r.lengthRPrime s)
      (wireValues r.tBoundary.lengthSLow s) n).1 = B)
    (hv : B ∈ quotientSwapLabels window.start window.stop)
    (ht : logical.t < 2^logical.lT)
    (htp : logical.tPrime < 2^(n+3-logical.lRPrime))
    (hspan1 : window.start-1+(B-window.start+1) ≤ logical.lT+1)
    (hspan2 : logical.shift+(window.start-1)+(B-window.start+1) ≤ n+3-logical.lRPrime)
    (hwork1 : wireValues r.work1 s =
      constantBits logical.lT logical.t ++ [false] ++
        (constantBits logical.lQ logical.q).reverse ++
        (constantBits (n+3-(logical.lT+logical.lQ+1)) logical.r).reverse)
    (hwork2 : wireValues r.work2 s =
      (constantBits (n+3-logical.lRPrime) logical.tPrime ++
        (constantBits logical.lRPrime logical.rPrime).reverse).rotate logical.shift) :
    let offset := window.start-1
    let m := B-window.start+1
    let modulus := 2^m
    let x := (logical.t/2^offset)%modulus
    let y := (logical.tPrime/2^(logical.shift+offset))%modulus
    let subEnable := s r.phase1 && !(!s r.phase2 && s r.sign)
    let middle := if subEnable then (y+modulus-x)%modulus else y
    let packed2 := (constantBits (n+3-logical.lRPrime) logical.tPrime ++
      (constantBits logical.lRPrime logical.rPrime).reverse).rotate logical.shift
    let final := run (blockEForward r n window) s
    wireValues r.work2 final = packed2.take offset ++
      constantBits m (if s r.phase1 then (middle+x)%modulus else middle) ++
        packed2.drop (offset+m) ∧
      wireValues r.work1 final = wireValues r.work1 s ∧
      final r.sign = ((s r.sign ^^ s r.phase1) ^^
        (s r.phase1 && decide (modulus ≤ middle+x))) ∧
      IndexedStepReady r final ∧
      AgreesOutside (r.sign :: (r.coefficient window).work1 ++
        (r.coefficient window).work2) final s := by
  have hm : B-window.start+1 ≤ window.stop-window.start+1 := by
    have hv' := hv
    simp only [quotientSwapLabels,List.mem_range'] at hv'
    omega
  have hx := coefficient_window_value r.work1 window s
    (constantBits logical.lT logical.t ++ [false])
    ((constantBits logical.lQ logical.q).reverse ++
      (constantBits (n+3-(logical.lT+logical.lQ+1)) logical.r).reverse)
    0 (B-window.start+1)
    (by simpa only [List.rotate_zero,List.append_assoc] using hwork1) hm
    (by simpa using hspan1)
  simp only [append_false_value,boolWordToNat_constantBits,Nat.mod_eq_of_lt ht,
    Nat.zero_add] at hx
  have hy := coefficient_window_value r.work2 window s
    (constantBits (n+3-logical.lRPrime) logical.tPrime)
    (constantBits logical.lRPrime logical.rPrime).reverse
    logical.shift (B-window.start+1) hwork2 hm (by simpa using hspan2)
  simp only [boolWordToNat_constantBits,Nat.mod_eq_of_lt htp] at hy
  change boolWordToNat ((wireValues (r.coefficient window).work1 s).take
    (B-window.start+1)) = _ at hx
  change boolWordToNat ((wireValues (r.coefficient window).work2 s).take
    (B-window.start+1)) = _ at hy
  have hf := blockEForward_workBanks r n index window s h hw hr (by rw [hb]; exact hv)
  dsimp only at hf ⊢
  simpa only [hb,hx,hy,hwork2] using hf

end ShorECDLP.Paper2607_13816
