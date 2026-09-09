import ShorECDLP.Submission.«2607_13816».EEA.QuotientStep

/-! # Canonical quotient/remainder repacking -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem constant_succ (width value : Nat) :
    constantBits (width+1) value = value.testBit 0 :: constantBits width (value/2) := by
  unfold constantBits
  simp only [List.replicate_succ,xorConstantBits]
  cases hbit : value.testBit 0 <;> simp
private theorem quotient_append_bit (width value : Nat) (b : Bool) :
    (constantBits (width+1) (Nat.bit b value)).reverse = (constantBits width value).reverse ++ [b] := by
  rw [constant_succ,Nat.testBit_bit_zero,Nat.bit_div_two,List.reverse_cons]
private theorem append_false_value (bits : List Bool) :
    boolWordToNat (bits++[false]) = boolWordToNat bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp only [List.cons_append,boolWordToNat_cons,ih]
private theorem remainder_leading_zero (width value : Nat) (hv : value < 2^width) :
    (constantBits (width+1) value).reverse = false :: (constantBits width value).reverse := by
  have he : constantBits (width+1) value = constantBits width value ++ [false] := by
    apply boolWordToNat_injective_of_length (by simp only [constantBits_length,List.length_append,List.length_singleton])
    rw [append_false_value,boolWordToNat_constantBits,boolWordToNat_constantBits,
      Nat.mod_eq_of_lt hv,Nat.mod_eq_of_lt (hv.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
  rw [he,List.reverse_append]
  rfl
private theorem word_update (ws : List Wire) (i : Nat) (b : Bool) (s : BasisState)
    (hn : ws.Nodup) (hi : i < ws.length) :
    wireValues ws s[ws.getD i 0 ↦ b] = (wireValues ws s).set i b := by
  rw [List.getD_eq_getElem _ _ hi]
  apply List.ext_getElem
  · simp only [wireValues,List.length_map,List.length_set]
  · intro j hj hj'
    have hjw : j < ws.length := by simpa only [wireValues,List.length_map] using hj
    by_cases he : j = i
    · subst j; simp [wireValues,upd]
    · have hw : ws[j] ≠ ws[i] := fun hh => he (hn.getElem_inj_iff.mp hh)
      simp [wireValues,upd,hw,Ne.symm he]
private theorem packed_push (T Q width t q rem : Nat) (b : Bool) (hr : rem < 2^width) :
    (constantBits T t ++ [false] ++ (constantBits Q q).reverse ++
      (constantBits (width+1) rem).reverse).set (T+Q+1) b =
    constantBits T t ++ [false] ++ (constantBits (Q+1) (Nat.bit b q)).reverse ++
      (constantBits width rem).reverse := by
  rw [remainder_leading_zero width rem hr,quotient_append_bit]
  let pre := constantBits T t ++ [false] ++ (constantBits Q q).reverse
  have hp : pre.length = T+Q+1 := by simp only [pre,List.length_append,List.length_reverse,constantBits_length,List.length_singleton]; omega
  change (pre ++ (false :: (constantBits width rem).reverse)).set (T+Q+1) b = _
  rw [List.set_append_right _ _ (by omega : pre.length ≤ T+Q+1)]
  simp only [hp,Nat.sub_self,List.set_cons_zero]
  simp only [pre,List.append_assoc,List.cons_append,List.nil_append]
private theorem packed_push_zero (T Q width t q rem : Nat) (hr : rem < 2^width) :
    (constantBits T t ++ [false] ++ (constantBits Q q).reverse ++
      (constantBits (width+1) rem).reverse).getD (T+Q+1) false = false := by
  rw [remainder_leading_zero width rem hr]
  let pre := constantBits T t ++ [false] ++ (constantBits Q q).reverse
  have hp : pre.length = T+Q+1 := by simp only [pre,List.length_append,List.length_reverse,constantBits_length,List.length_singleton]; omega
  change (pre ++ (false :: (constantBits width rem).reverse)).getD (T+Q+1) false = _
  rw [List.getD_append_right _ _ _ _ (by omega : pre.length ≤ T+Q+1),hp,Nat.sub_self]
  rfl

private theorem packed_pop (T Q width t q rem : Nat) (hQ : 0 < Q) (hr : rem < 2^width) :
    (constantBits T t ++ [false] ++ (constantBits Q q).reverse ++
      (constantBits width rem).reverse).set (T+Q) false =
    constantBits T t ++ [false] ++ (constantBits (Q-1) (q/2)).reverse ++
      (constantBits (width+1) rem).reverse := by
  have he : Q = (Q-1)+1 := by omega
  rw [show constantBits Q q = q.testBit 0 :: constantBits (Q-1) (q/2) by
    conv_lhs => rw [he]
    exact constant_succ _ _,List.reverse_cons,remainder_leading_zero width rem hr]
  let pre := constantBits T t ++ [false] ++ (constantBits (Q-1) (q/2)).reverse
  have hp : pre.length = T+Q := by
    simp only [pre,List.length_append,List.length_reverse,constantBits_length,List.length_singleton]
    omega
  have ha : constantBits T t ++ [false] ++ ((constantBits (Q-1) (q/2)).reverse ++ [q.testBit 0]) ++
      (constantBits width rem).reverse = pre ++ (q.testBit 0 :: (constantBits width rem).reverse) := by
    simp only [pre,List.append_assoc,List.cons_append,List.nil_append]
  rw [ha,List.set_append_right _ _ (by omega : pre.length ≤ T+Q),hp,Nat.sub_self,List.set_cons_zero]
private theorem packed_pop_bit (T Q width t q rem : Nat) (hQ : 0 < Q) :
    (constantBits T t ++ [false] ++ (constantBits Q q).reverse ++
      (constantBits width rem).reverse).getD (T+Q) false = q.testBit 0 := by
  have he : Q = (Q-1)+1 := by omega
  rw [show constantBits Q q = q.testBit 0 :: constantBits (Q-1) (q/2) by
    conv_lhs => rw [he]
    exact constant_succ _ _,List.reverse_cons]
  let pre := constantBits T t ++ [false] ++ (constantBits (Q-1) (q/2)).reverse
  have hp : pre.length = T+Q := by
    simp only [pre,List.length_append,List.length_reverse,constantBits_length,List.length_singleton]
    omega
  have ha : constantBits T t ++ [false] ++ ((constantBits (Q-1) (q/2)).reverse ++ [q.testBit 0]) ++
      (constantBits width rem).reverse = pre ++ (q.testBit 0 :: (constantBits width rem).reverse) := by
    simp only [pre,List.append_assoc,List.cons_append,List.nil_append]
  rw [ha,List.getD_append_right _ _ _ _ (by omega : pre.length ≤ T+Q),hp,Nat.sub_self]
  rfl

private theorem bank_geometry (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) : r.work1.Nodup ∧ r.sign ∉ r.lengthQ ∧
      (∀ wire ∈ r.work1, wire ≠ r.sign ∧ wire ∉ r.lengthQ) := by
  let before := [r.phase1,r.phase2,r.iter,r.sign]
  let rest := r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux
  have hp : (before ++ (r.work1 ++ rest)).Nodup := by
    simpa only [before,rest,IndexedStepRegisters.allWires,List.append_assoc] using h.physical
  have hf := (List.nodup_append.mp hp).2.2
  have hb := List.nodup_append.mp (List.nodup_append.mp hp).2.1
  refine ⟨hb.1,?_,?_⟩
  · intro hm
    exact hf r.sign (by simp [before]) r.sign (List.mem_append_right _ (by simp [rest,hm])) rfl
  · intro wire hw
    refine ⟨Ne.symm (hf r.sign (by simp [before]) wire (List.mem_append_left _ hw)),?_⟩
    intro hq
    exact hb.2.2 wire hw wire (by simp [rest,hq]) rfl

/-- In phase 2, a zero high remainder bit becomes the appended quotient bit,
and the sign is cleared by the actual complete quotient block. -/
theorem blockDForward_pushPacking (r : IndexedStepRegisters) (n index T Q width t q rem : Nat)
    (w : ActiveWindow) (s : BasisState) (h : IndexedStepLayout r n index)
    (hql : QuotientSwapLayout (r.quotient w) w.start w.stop) (hc : Clean r.aux s)
    (hw : 1 ≤ w.start) (hp1 : s r.phase1 = false) (hp2 : s r.phase2 = true)
    (ht : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length Q)
    (hfit : T+Q+2 < 2^r.lengthQ.length) (hlo : w.start ≤ T+Q+2) (hhi : T+Q+2 ≤ w.stop)
    (hquot : q < 2^Q) (hrem : rem < 2^width)
    (hpacked : wireValues r.work1 s = constantBits T t ++ [false] ++
      (constantBits Q q).reverse ++ (constantBits (width+1) rem).reverse) :
    let final := run (blockDForward r w) s
    wireValues r.work1 final = constantBits T t ++ [false] ++
      (constantBits (Q+1) (Nat.bit (s r.sign) q)).reverse ++ (constantBits width rem).reverse ∧
    Nat.bit (s r.sign) q < 2^(Q+1) ∧ final r.sign = false ∧
    wireValues r.lengthQ final = constantBits r.lengthQ.length (truthMinusOneValue r.lengthQ.length (Q+1)) ∧
    AgreesOutside (r.lengthQ ++ (r.sign :: r.work1)) final s ∧ Clean r.aux final := by
  let final := run (blockDForward r w) s
  let target := r.work1.getD (T+Q+1) 0
  have hd := blockDForward_logical r n index T Q w s h hql hc hw ht hq
    (by simpa [hp1,hp2,Nat.add_assoc] using hfit)
    (by simpa [hp1,hp2,Nat.add_assoc] using hlo)
    (by simpa [hp1,hp2,Nat.add_assoc] using hhi) (by simp [hp1])
  have hb : wireValues r.lengthQ final = constantBits r.lengthQ.length (truthMinusOneValue r.lengthQ.length (Q+1)) ∧
      AgreesOutside r.lengthQ final s[r.sign ↦ s target][target ↦ s r.sign] ∧ Clean r.aux final := by
    simpa [final,target,hp1,hp2,Nat.add_assoc] using hd
  have hg := bank_geometry r n index h
  have hi : T+Q+1 < r.work1.length := by
    have he := congrArg List.length hpacked
    simp only [wireValues,List.length_map,List.length_append,List.length_reverse,constantBits_length,List.length_singleton] at he
    omega
  have htMem : target ∈ r.work1 := by
    dsimp only [target]
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  have hts : target ≠ r.sign := (hg.2.2 target htMem).1
  have hz : s target = false := by
    have he := congrArg (fun bits => bits.getD (T+Q+1) false) hpacked
    dsimp only at he
    rw [packed_push_zero T Q width t q rem hrem] at he
    change (r.work1.map s).getD (T+Q+1) false = false at he
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),List.getElem_map] at he
    simpa only [target,List.getD_eq_getElem _ _ hi] using he
  have hword : wireValues r.work1 final = (wireValues r.work1 s).set (T+Q+1) (s r.sign) := by
    have hf : wireValues r.work1 final = wireValues r.work1 s[r.sign ↦ s target][target ↦ s r.sign] := by
      apply List.map_congr_left
      intro wire hm
      exact hb.2.1 wire (hg.2.2 wire hm).2
    rw [hf,word_update r.work1 (T+Q+1) (s r.sign) s[r.sign ↦ s target] hg.1 hi]
    congr 1
    apply List.map_congr_left
    intro wire hm
    simp only [upd,(hg.2.2 wire hm).1,if_false]
  dsimp only
  refine ⟨?_,?_,?_,hb.1,?_,hb.2.2⟩
  · rw [hword,hpacked,packed_push T Q width t q rem (s r.sign) hrem]
  · cases s r.sign <;> simp only [Nat.bit,Bool.cond_false,Bool.cond_true,Nat.pow_succ] <;> omega
  · simpa only [upd,Ne.symm hts,if_false,if_true,hz] using hb.2.1 r.sign hg.2.1
  · intro wire hn
    have hQ : wire ∉ r.lengthQ := fun hh => hn (List.mem_append_left _ hh)
    have hs : wire ≠ r.sign := fun hh => hn (List.mem_append_right _ (List.mem_cons.mpr (Or.inl hh)))
    have ht' : wire ≠ target := by intro hh; subst wire; exact hn (List.mem_append_right _ (List.mem_cons.mpr (Or.inr htMem)))
    simpa only [upd,hs,ht',if_false] using hb.2.1 wire hQ
/-- In phase 3, a clear sign receives the last quotient bit; the remainder gains a zero high bit. -/
theorem blockDForward_popPacking (r : IndexedStepRegisters) (n index T Q width t q rem : Nat)
    (w : ActiveWindow) (s : BasisState) (h : IndexedStepLayout r n index)
    (hql : QuotientSwapLayout (r.quotient w) w.start w.stop) (hc : Clean r.aux s)
    (hw : 1 ≤ w.start) (hp1 : s r.phase1 = true) (hp2 : s r.phase2 = false)
    (hQpos : 0 < Q) (hsign : s r.sign = false)
    (ht : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length Q)
    (hfit : T+Q+1 < 2^r.lengthQ.length) (hlo : w.start ≤ T+Q+1) (hhi : T+Q+1 ≤ w.stop)
    (hquot : q < 2^Q) (hrem : rem < 2^width)
    (hpacked : wireValues r.work1 s = constantBits T t ++ [false] ++
      (constantBits Q q).reverse ++ (constantBits width rem).reverse) :
    let final := run (blockDForward r w) s
    wireValues r.work1 final = constantBits T t ++ [false] ++
      (constantBits (Q-1) (q/2)).reverse ++ (constantBits (width+1) rem).reverse ∧
    q/2 < 2^(Q-1) ∧ final r.sign = q.testBit 0 ∧
    wireValues r.lengthQ final = constantBits r.lengthQ.length (truthMinusOneValue r.lengthQ.length (Q-1)) ∧
    AgreesOutside (r.lengthQ ++ (r.sign :: r.work1)) final s ∧ Clean r.aux final := by
  let final := run (blockDForward r w) s
  let target := r.work1.getD (T+Q) 0
  have hd := blockDForward_logical r n index T Q w s h hql hc hw ht hq
    (by simpa [hp1,hp2,Nat.add_assoc] using hfit)
    (by simpa [hp1,hp2,Nat.add_assoc] using hlo)
    (by simpa [hp1,hp2,Nat.add_assoc] using hhi) (by simpa [hp1,hp2] using hQpos)
  have hb : wireValues r.lengthQ final = constantBits r.lengthQ.length (truthMinusOneValue r.lengthQ.length (Q-1)) ∧
      AgreesOutside r.lengthQ final s[r.sign ↦ s target][target ↦ s r.sign] ∧ Clean r.aux final := by
    simpa [final,target,hp1,hp2,Nat.add_assoc] using hd
  have hg := bank_geometry r n index h
  have hi : T+Q < r.work1.length := by
    have he := congrArg List.length hpacked
    simp only [wireValues,List.length_map,List.length_append,List.length_reverse,constantBits_length,List.length_singleton] at he
    omega
  have htMem : target ∈ r.work1 := by
    dsimp only [target]
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  have hts : target ≠ r.sign := (hg.2.2 target htMem).1
  have hz : s target = q.testBit 0 := by
    have he := congrArg (fun bits => bits.getD (T+Q) false) hpacked
    dsimp only at he
    rw [packed_pop_bit T Q width t q rem hQpos] at he
    change (r.work1.map s).getD (T+Q) false = q.testBit 0 at he
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),List.getElem_map] at he
    simpa only [target,List.getD_eq_getElem _ _ hi] using he
  have hword : wireValues r.work1 final = (wireValues r.work1 s).set (T+Q) (s r.sign) := by
    have hf : wireValues r.work1 final = wireValues r.work1 s[r.sign ↦ s target][target ↦ s r.sign] := by
      apply List.map_congr_left
      intro wire hm
      exact hb.2.1 wire (hg.2.2 wire hm).2
    rw [hf,word_update r.work1 (T+Q) (s r.sign) s[r.sign ↦ s target] hg.1 hi]
    congr 1
    apply List.map_congr_left
    intro wire hm
    simp only [upd,(hg.2.2 wire hm).1,if_false]
  dsimp only
  refine ⟨?_,?_,?_,hb.1,?_,hb.2.2⟩
  · rw [hword,hpacked,hsign,packed_pop T Q width t q rem hQpos hrem]
  · have hp : 2^Q = 2^(Q-1)*2 := by
      conv_lhs => rw [show Q = (Q-1)+1 by omega]
      exact Nat.pow_succ _ _
    omega
  · simpa only [upd,Ne.symm hts,if_false,if_true,hz] using hb.2.1 r.sign hg.2.1
  · intro wire hn
    have hQ : wire ∉ r.lengthQ := fun hh => hn (List.mem_append_left _ hh)
    have hs : wire ≠ r.sign := fun hh => hn (List.mem_append_right _ (List.mem_cons.mpr (Or.inl hh)))
    have ht' : wire ≠ target := by intro hh; subst wire; exact hn (List.mem_append_right _ (List.mem_cons.mpr (Or.inr htMem)))
    simpa only [upd,hs,ht',if_false] using hb.2.1 wire hQ
end ShorECDLP.Paper2607_13816
