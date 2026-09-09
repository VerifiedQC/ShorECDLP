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


private theorem coefficient_zero_extend (small big value : Nat) (hle : small ≤ big)
    (hfit : value < 2^small) :
    constantBits big value = constantBits small value ++ List.replicate (big-small) false := by
  have hz (k : Nat) : boolWordToNat (List.replicate k false) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,ih]
  have ha (bits : List Bool) (k : Nat) :
      boolWordToNat (bits ++ List.replicate k false) = boolWordToNat bits := by
    induction bits with
    | nil => simp [hz]
    | cons b bs ih => simp [ih]
  apply boolWordToNat_injective_of_length
  · simp only [constantBits_length,List.length_append,List.length_replicate]; omega
  · rw [ha,boolWordToNat_constantBits,boolWordToNat_constantBits,
      Nat.mod_eq_of_lt hfit,Nat.mod_eq_of_lt (hfit.trans_le (Nat.pow_le_pow_right (by decide) hle))]

private theorem coefficient_widen_packing (bank T R t rem : Nat)
    (hspan : T+1+R ≤ bank) (ht : t < 2^T) (hr : rem < 2^R) :
    constantBits T t ++ [false] ++ (constantBits (bank-(T+1)) rem).reverse =
      constantBits (bank-R-1) t ++ [false] ++ (constantBits R rem).reverse := by
  rw [coefficient_zero_extend R (bank-(T+1)) rem (by omega) hr,
    List.reverse_append,List.reverse_replicate,
    coefficient_zero_extend T (bank-R-1) t (by omega) ht]
  have he : bank-(T+1)-R = bank-R-1-T := by omega
  rw [he]
  simp only [List.append_assoc]
  congr 1
  rw [← List.append_assoc,← List.append_assoc]
  congr 1
  change List.replicate 1 false ++ _ = _ ++ List.replicate 1 false
  rw [← List.replicate_add,← List.replicate_add,Nat.add_comm]

/-- In the swap phase, leading zeros from the bounded remainder extend the
coefficient field. The actual subtract/add pair restores both banks and toggles
only the comparison sign, even when its selected width exceeds the stored T. -/
theorem blockEForward_swapComparison (r : IndexedStepRegisters) (n index : Nat)
    (window : ActiveWindow) (s : BasisState) (v : EEAState)
    (h : IndexedStepLayout r n index)
    (hw : window = (certifiedActiveWindows n index).coefficient)
    (hr : IndexedStepReady r s) (hp1 : s r.phase1 = true) (hp2 : s r.phase2 = true)
    (htmeta : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthT.length v.lT)
    (hrmeta : boolWordToNat (wireValues r.lengthRPrime s) = truthMinusOneValue r.lengthT.length v.lRPrime)
    (hsmeta : boolWordToNat (wireValues r.tBoundary.lengthSLow s) = truthMinusOneValue r.lengthT.length v.shift)
    (hthi : v.lT+1 < 2^r.lengthT.length)
    (hspan : v.lT+1+v.lRPrime ≤ n+3)
    (hshift : 0 < v.shift) (hlo : v.lRPrime+v.shift ≤ n+3)
    (hhi : n+3-v.lRPrime-v.shift < 2^r.lengthT.length)
    (hv : n+3-v.lRPrime-v.shift ∈ quotientSwapLabels window.start window.stop)
    (ht : v.t < 2^v.lT) (htB : v.t < 2^(n+3-v.lRPrime-v.shift))
    (htp : v.tPrime < 2^(n+3-v.lRPrime)) (hrem : v.r < 2^v.lRPrime)
    (hwork1 : wireValues r.work1 s = constantBits v.lT v.t ++ [false] ++
      (constantBits (n+3-(v.lT+1)) v.r).reverse)
    (hwork2 : wireValues r.work2 s =
      (constantBits (n+3-v.lRPrime) v.tPrime ++
        (constantBits v.lRPrime v.rPrime).reverse).rotate v.shift) :
    let final := run (blockEForward r n window) s
    wireValues r.work1 final = wireValues r.work1 s ∧
      wireValues r.work2 final = wireValues r.work2 s ∧
      final r.sign = (s r.sign ^^ decide (v.t*2^v.shift ≤ v.tPrime)) ∧
      IndexedStepReady r final ∧
      AgreesOutside (r.sign :: (r.coefficient window).work1 ++
        (r.coefficient window).work2) final s := by
  let B := n+3-v.lRPrime-v.shift
  let wide := { v with lT := n+3-v.lRPrime-1, lQ := 0 }
  have hstart : window.start = 1 := by rw [hw]; rfl
  have hB : 1 ≤ B := by
    have hh := hv
    simp only [quotientSwapLabels,List.mem_range',hstart] at hh
    dsimp [B]; omega
  have hp := prepareLatestPaperTBoundaryWords_arithmetic (s r.phase2) (wireValues r.lengthT s)
    (wireValues r.lengthRPrime s) (wireValues r.tBoundary.lengthSLow s)
    v.lT v.lRPrime v.shift n
    (by simpa only [wireValues,List.length_map] using h.tBoundary.lengthRP_length.symm)
    (by simp only [wireValues,List.length_map,TBoundaryRegisters.lengthSLow,List.length_take,
        Nat.min_eq_left h.tBoundary.lengthS_capacity]; rfl)
    (by simpa only [wireValues,List.length_map] using h.tBoundary.positive)
    (by simpa only [wireValues,List.length_map] using htmeta)
    (by simpa only [wireValues,List.length_map] using hrmeta)
    (by simpa only [wireValues,List.length_map] using hsmeta)
    (by simpa only [wireValues,List.length_map] using hthi) hlo
    (by simpa only [wireValues,List.length_map] using hhi)
  have hb := congrArg Prod.fst hp
  simp only [hp2,ite_true] at hb
  have hwide : wireValues r.work1 s = constantBits wide.lT wide.t ++ [false] ++
      (constantBits wide.lQ wide.q).reverse ++
      (constantBits (n+3-(wide.lT+wide.lQ+1)) wide.r).reverse := by
    rw [hwork1,coefficient_widen_packing (n+3) v.lT v.lRPrime v.t v.r hspan ht hrem]
    have he : n+3-(n+3-v.lRPrime-1+0+1) = v.lRPrime := by omega
    simp only [wide,he,constantBits,List.replicate_zero,xorConstantBits,List.reverse_nil,List.append_nil]
  have hf := blockEForward_canonicalCoefficient r n index B window s wide h hw hr (by simpa only [hp2,B] using hb) hv
    (ht.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [wide]; omega))) htp
    (by dsimp [wide,B]; rw [hstart]; omega)
    (by dsimp [wide,B]; rw [hstart]; omega) hwide hwork2
  have hy : v.tPrime/2^v.shift < 2^B := (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).2
    (by rw [← Nat.pow_add]; have he : B+v.shift=n+3-v.lRPrime := by dsimp [B]; omega
        rw [he]; exact htp)
  change v.t < 2^B at htB
  have hc := coefficient_sub_add (2^B) v.t (v.tPrime/2^v.shift) htB hy
  dsimp only [wide] at hf
  simp only [hstart,Nat.sub_self,Nat.add_zero,Nat.pow_zero,Nat.div_one,
    Nat.sub_add_cancel hB,Nat.mod_eq_of_lt htB,Nat.mod_eq_of_lt hy,
    hp1,hp2,Bool.not_true,Bool.false_and,Bool.not_false,Bool.and_self,ite_true] at hf
  have hre := coefficient_recompose v.tPrime v.shift B
  rw [Nat.mod_eq_of_lt hy] at hre
  rw [hc.1,hre] at hf
  simp only [hc.2,Bool.true_and] at hf
  have hs : ((s r.sign ^^ true) ^^ decide (v.tPrime/2^v.shift<v.t)) =
      (s r.sign ^^ decide (v.t*2^v.shift ≤ v.tPrime)) := by
    simp only [Nat.div_lt_iff_lt_mul (show 0<2^v.shift from Nat.pow_pos (by decide))]
    by_cases hh : v.tPrime < v.t*2^v.shift <;> cases s r.sign <;> simp_all
  exact ⟨hf.2.2.1,hf.1.trans hwork2.symm,(by simpa only [Bool.true_and] using hf.2.2.2.1.trans hs),hf.2.2.2.2⟩

private theorem endpoint_packed_repartition (bank T R t rem : Nat)
    (hspan : T+1+R ≤ bank) (ht : t < 2^T) (hr : rem < 2^R) :
    constantBits T t ++ [false] ++ (constantBits (bank-(T+1)) rem).reverse =
      constantBits (bank-R) t ++ (constantBits R rem).reverse := by
  rw [coefficient_widen_packing bank T R t rem hspan ht hr]
  have hfit : t < 2^(bank-R-1) :=
    ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [coefficient_zero_extend (bank-R-1) (bank-R) t (by omega) hfit]
  have he : bank-R-(bank-R-1) = 1 := by omega
  rw [he]
  rfl
/-- Zero padding gives the upper and lower endpoint views of the same canonical banks. -/
theorem endpoint_canonical_bank_views (bank oldT newT RP old new rem rp : Nat)
    (hT : oldT ≤ newT) (hspan : newT+1+RP ≤ bank)
    (hold : old < 2^oldT) (hnew : new < 2^newT)
    (hrem : rem < 2^RP) (hrp : rp < 2^RP) :
    let first := constantBits oldT old ++ [false] ++ (constantBits (bank-(oldT+1)) rem).reverse
    let second := constantBits (bank-RP) new ++ (constantBits RP rp).reverse
    first = constantBits (bank-RP) old ++ (constantBits RP rem).reverse ∧
      first = constantBits newT old ++ [false] ++ (constantBits (bank-(newT+1)) rem).reverse ∧
      second = constantBits newT new ++ [false] ++ (constantBits (bank-(newT+1)) rp).reverse := by
  have ho := endpoint_packed_repartition bank oldT RP old rem (by omega) hold hrem
  have hon := hold.trans_le (Nat.pow_le_pow_right (by decide) hT)
  exact ⟨ho, ho.trans (endpoint_packed_repartition bank newT RP old rem hspan hon hrem).symm,
    (endpoint_packed_repartition bank newT RP new rp hspan hnew hrp).symm⟩


end ShorECDLP.Paper2607_13816
