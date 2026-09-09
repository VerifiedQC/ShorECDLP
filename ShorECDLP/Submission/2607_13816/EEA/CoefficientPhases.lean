import ShorECDLP.Submission.«2607_13816».EEA.PackedCoefficient
/-! # Phase-dependent canonical coefficient update -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem coefficient_recompose (value pos width : Nat) :
    value%2^pos + 2^pos*((value/2^pos)%2^width) +
      2^(pos+width)*(value/2^(pos+width)) = value := by
  rw [Nat.pow_add,← Nat.div_div_eq_div_mul]
  calc
    _ = value%2^pos + 2^pos*((value/2^pos)%2^width + 2^width*(value/2^pos/2^width)) := by ring
    _ = value := by rw [Nat.mod_add_div,Nat.mod_add_div]

private theorem coefficient_sub_add (M x y : Nat) (hx : x<M) (hy : y<M) :
    (((y+M-x)%M+x)%M = y) ∧ (M ≤ (y+M-x)%M+x ↔ y<x) := by
  by_cases hxy : x ≤ y
  · have hsplit : y+M-x = (y-x)+M := by omega
    have hd : y-x<M := by omega
    rw [hsplit,Nat.add_mod_right,Nat.mod_eq_of_lt hd]
    have hadd : y-x+x=y := by omega
    rw [hadd,Nat.mod_eq_of_lt hy]
    omega
  · have hl : y+M-x<M := by omega
    rw [Nat.mod_eq_of_lt hl]
    have hadd : y+M-x+x=y+M := by omega
    rw [hadd,Nat.add_mod_right,Nat.mod_eq_of_lt hy]
    omega

private theorem coefficient_pair_cases (M x y : Nat) (p1 p2 sign : Bool)
    (hx : x<M) (hy : y<M) :
    let middle := if p1 && !(!p2 && sign) then (y+M-x)%M else y
    (if p1 then (middle+x)%M else middle) =
      (if p1 && !p2 && sign then (y+x)%M else y) ∧
    ((sign ^^ p1) ^^ (p1 && decide (M ≤ middle+x))) =
      (if p1 then (if !p2 && sign then decide (M ≤ y+x)
        else ((sign ^^ true) ^^ decide (y<x))) else sign) := by
  have hh := coefficient_sub_add M x y hx hy
  cases p1 <;> cases p2 <;> cases sign <;> simp [hh.1,hh.2]

/-- The two actual arithmetic scans reduce to one phase-selected coefficient update. -/
theorem blockEForward_coefficientPhaseCases (r : IndexedStepRegisters) (n index : Nat)
    (window : ActiveWindow) (s : BasisState) (logical : EEAState)
    (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hr : IndexedStepReady r s)
    (htmeta : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthT.length logical.lT)
    (hrmeta : boolWordToNat (wireValues r.lengthRPrime s) = truthMinusOneValue r.lengthT.length logical.lRPrime)
    (hsmeta : boolWordToNat (wireValues r.tBoundary.lengthSLow s) = truthMinusOneValue r.lengthT.length logical.shift)
    (hthi : logical.lT+1 < 2^r.lengthT.length)
    (hlo : logical.lRPrime+logical.shift ≤ n+3)
    (hhi : n+3-logical.lRPrime-logical.shift < 2^r.lengthT.length)
    (hv : (if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1) ∈ quotientSwapLabels window.start window.stop)
    (ht : logical.t < 2^logical.lT)
    (htp : logical.tPrime < 2^(n+3-logical.lRPrime))
    (hspan1 : window.start-1+((if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1)-window.start+1) ≤ logical.lT+1)
    (hspan2 : logical.shift+(window.start-1)+((if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1)-window.start+1) ≤ n+3-logical.lRPrime)
    (hwork1 : wireValues r.work1 s =
      constantBits logical.lT logical.t ++ [false] ++
        (constantBits logical.lQ logical.q).reverse ++
        (constantBits (n+3-(logical.lT+logical.lQ+1)) logical.r).reverse)
    (hwork2 : wireValues r.work2 s =
      (constantBits (n+3-logical.lRPrime) logical.tPrime ++
        (constantBits logical.lRPrime logical.rPrime).reverse).rotate logical.shift) :
    let offset := window.start-1
    let m := (if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1)-window.start+1
    let modulus := 2^m
    let x := (logical.t/2^offset)%modulus
    let y := (logical.tPrime/2^(logical.shift+offset))%modulus
    let pos := logical.shift+offset
    let updated := if s r.phase1 && !s r.phase2 && s r.sign then
      logical.tPrime%2^pos + 2^pos*((y+x)%modulus) +
        2^(pos+m)*(logical.tPrime/2^(pos+m)) else logical.tPrime
    let final := run (blockEForward r n window) s
    wireValues r.work2 final =
      (constantBits (n+3-logical.lRPrime) updated ++
        (constantBits logical.lRPrime logical.rPrime).reverse).rotate logical.shift ∧
      updated < 2^(n+3-logical.lRPrime) ∧
      wireValues r.work1 final = wireValues r.work1 s ∧
      final r.sign = (if s r.phase1 then
        (if !s r.phase2 && s r.sign then decide (modulus ≤ y+x)
          else ((s r.sign ^^ true) ^^ decide (y<x))) else s r.sign) ∧
      IndexedStepReady r final ∧
      AgreesOutside (r.sign :: (r.coefficient window).work1 ++
        (r.coefficient window).work2) final s := by
  let B := if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1
  let m := B-window.start+1
  let pos := logical.shift+(window.start-1)
  let x := (logical.t/2^(window.start-1))%2^m
  let y := (logical.tPrime/2^pos)%2^m
  have hp := coefficient_pair_cases (2^m) x y (s r.phase1) (s r.phase2) (s r.sign)
    (Nat.mod_lt _ (Nat.pow_pos (by decide))) (Nat.mod_lt _ (Nat.pow_pos (by decide)))
  have hu : logical.tPrime%2^pos + 2^pos*(if s r.phase1 && !s r.phase2 && s r.sign then (y+x)%2^m else y) +
      2^(pos+m)*(logical.tPrime/2^(pos+m)) =
      if s r.phase1 && !s r.phase2 && s r.sign then
        logical.tPrime%2^pos + 2^pos*((y+x)%2^m) + 2^(pos+m)*(logical.tPrime/2^(pos+m))
      else logical.tPrime := by
    split
    · rfl
    · exact coefficient_recompose logical.tPrime pos m
  have hf := blockEForward_logicalCoefficient r n index window s logical h hw hr
    htmeta hrmeta hsmeta hthi hlo hhi hv ht htp hspan1 hspan2 hwork1 hwork2
  dsimp only [x,y,pos,m,B] at hp hu
  dsimp only at hf ⊢
  rw [hp.1,hp.2,hu] at hf
  exact hf

private theorem ordinary_coefficient_update (value addend pos width : Nat) (active : Bool)
    (hcarry : active = true → value/2^pos+addend < 2^width) :
    (if active then value%2^pos + 2^pos*(((value/2^pos)%2^width+addend)%2^width) +
      2^(pos+width)*(value/2^(pos+width)) else value) =
      if active then value+2^pos*addend else value := by
  cases ha : active
  · simp
  · have hsum := hcarry ha
    have hy : value/2^pos < 2^width := by omega
    simp only [if_true,Nat.mod_eq_of_lt hy,Nat.mod_eq_of_lt hsum]
    have hr := coefficient_recompose value pos width
    rw [Nat.mod_eq_of_lt hy] at hr
    calc
      _ = (value%2^pos + 2^pos*(value/2^pos) + 2^(pos+width)*(value/2^(pos+width))) + 2^pos*addend := by ring
      _ = _ := by rw [hr]

private theorem ordinary_coefficient_sign (value addend pos width : Nat) (p1 p2 sign : Bool)
    (hfit : value < 2^(pos+width))
    (hcarry : (p1 && !p2 && sign) = true → value/2^pos+addend < 2^width) :
    (if p1 then (if !p2 && sign then decide (2^width ≤ (value/2^pos)%2^width+addend)
      else ((sign ^^ true) ^^ decide ((value/2^pos)%2^width<addend))) else sign) =
    (if p1 then (if !p2 && sign then false
      else ((sign ^^ true) ^^ decide (value<addend*2^pos))) else sign) := by
  have hy : value/2^pos < 2^width := (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).2
    (by simpa only [Nat.pow_add,Nat.mul_comm] using hfit)
  rw [Nat.mod_eq_of_lt hy]
  simp only [Nat.div_lt_iff_lt_mul (show 0 < 2^pos from Nat.pow_pos (by decide))]
  cases p1 <;> cases p2 <;> cases sign <;> simp_all

/-- Under explicit bounds preventing overflow, the actual coefficient stage is ordinary shifted addition and comparison. -/
theorem blockEForward_coefficientOrdinary (r : IndexedStepRegisters) (n index : Nat)
    (window : ActiveWindow) (s : BasisState) (logical : EEAState)
    (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hr : IndexedStepReady r s)
    (htmeta : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthT.length logical.lT)
    (hrmeta : boolWordToNat (wireValues r.lengthRPrime s) = truthMinusOneValue r.lengthT.length logical.lRPrime)
    (hsmeta : boolWordToNat (wireValues r.tBoundary.lengthSLow s) = truthMinusOneValue r.lengthT.length logical.shift)
    (hthi : logical.lT+1 < 2^r.lengthT.length)
    (hlo : logical.lRPrime+logical.shift ≤ n+3)
    (hhi : n+3-logical.lRPrime-logical.shift < 2^r.lengthT.length)
    (hv : (if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1) ∈ quotientSwapLabels window.start window.stop)
    (ht : logical.t < 2^logical.lT)
    (htp : logical.tPrime < 2^(n+3-logical.lRPrime))
    (hspan1 : window.start-1+((if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1)-window.start+1) ≤ logical.lT+1)
    (hspan2 : logical.shift+(window.start-1)+((if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1)-window.start+1) ≤ n+3-logical.lRPrime)
    (haddend : logical.t < 2^(if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1))
    (hcoeff : logical.tPrime < 2^(logical.shift+(if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1)))
    (hcarry : (s r.phase1 && !s r.phase2 && s r.sign) = true →
      logical.tPrime/2^logical.shift+logical.t < 2^(if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1))
    (hwork1 : wireValues r.work1 s =
      constantBits logical.lT logical.t ++ [false] ++
        (constantBits logical.lQ logical.q).reverse ++
        (constantBits (n+3-(logical.lT+logical.lQ+1)) logical.r).reverse)
    (hwork2 : wireValues r.work2 s =
      (constantBits (n+3-logical.lRPrime) logical.tPrime ++
        (constantBits logical.lRPrime logical.rPrime).reverse).rotate logical.shift) :
    let updated := if s r.phase1 && !s r.phase2 && s r.sign then
      logical.tPrime+2^logical.shift*logical.t else logical.tPrime
    let final := run (blockEForward r n window) s
    wireValues r.work2 final =
      (constantBits (n+3-logical.lRPrime) updated ++
        (constantBits logical.lRPrime logical.rPrime).reverse).rotate logical.shift ∧
      updated < 2^(n+3-logical.lRPrime) ∧
      wireValues r.work1 final = wireValues r.work1 s ∧
      final r.sign = (if s r.phase1 then
        (if !s r.phase2 && s r.sign then false
          else ((s r.sign ^^ true) ^^ decide (logical.tPrime<logical.t*2^logical.shift))) else s r.sign) ∧
      IndexedStepReady r final ∧
      AgreesOutside (r.sign :: (r.coefficient window).work1 ++
        (r.coefficient window).work2) final s := by
  let B := if s r.phase2 then n+3-logical.lRPrime-logical.shift else logical.lT+1
  have hstart : window.start = 1 := by rw [hw]; rfl
  have hB : 1 ≤ B := by
    have hh := hv
    simp only [quotientSwapLabels,List.mem_range',hstart] at hh
    omega
  have hf := blockEForward_coefficientPhaseCases r n index window s logical h hw hr
    htmeta hrmeta hsmeta hthi hlo hhi hv ht htp hspan1 hspan2 hwork1 hwork2
  have hu := ordinary_coefficient_update logical.tPrime logical.t logical.shift B
    (s r.phase1 && !s r.phase2 && s r.sign) hcarry
  have hs := ordinary_coefficient_sign logical.tPrime logical.t logical.shift B
    (s r.phase1) (s r.phase2) (s r.sign) hcoeff hcarry
  dsimp only [B] at hB hu hs
  dsimp only at hf ⊢
  simp only [hstart,Nat.sub_self,Nat.add_zero,Nat.pow_zero,Nat.div_one,
    Nat.sub_add_cancel hB,Nat.mod_eq_of_lt haddend] at hf
  rw [hu,hs] at hf
  exact hf

end ShorECDLP.Paper2607_13816
