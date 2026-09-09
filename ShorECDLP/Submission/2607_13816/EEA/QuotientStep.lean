import ShorECDLP.Submission.«2607_13816».EEA.QuotientCounters
import ShorECDLP.Submission.«2607_13816».EEA.PhaseQuotient

/-! # Complete logical quotient-block composition -/
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Complete Block D updates its length word and swaps the selected quotient bit
with sign in the unequal-phase cases. Every other wire is restored. -/
theorem blockDForward_logical (r : IndexedStepRegisters) (n index T Q : Nat)
    (w : ActiveWindow) (s : BasisState) (h : IndexedStepLayout r n index)
    (hql : QuotientSwapLayout (r.quotient w) w.start w.stop) (hc : Clean r.aux s)
    (hw : 1 ≤ w.start)
    (ht : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length Q)
    (hfit : T+(if !s r.phase1 && s r.phase2 then Q+1 else Q)+1 < 2^r.lengthQ.length)
    (hlo : w.start ≤ T+(if !s r.phase1 && s r.phase2 then Q+1 else Q)+1)
    (hhi : T+(if !s r.phase1 && s r.phase2 then Q+1 else Q)+1 ≤ w.stop)
    (hpositive : (s r.phase1 && !s r.phase2) = true → 0 < Q) :
    let q1 := if !s r.phase1 && s r.phase2 then Q+1 else Q
    let qfinal := if s r.phase1 && !s r.phase2 then q1-1 else q1
    let target := r.work1.getD (T+q1) 0
    let final := run (blockDForward r w) s
    wireValues r.lengthQ final = constantBits r.lengthQ.length (truthMinusOneValue r.lengthQ.length qfinal) ∧
      AgreesOutside r.lengthQ final
        (if s r.phase1 ^^ s r.phase2 then s[r.sign ↦ s target][target ↦ s r.sign] else s) ∧
      Clean r.aux final := by
  let q1 := if !s r.phase1 && s r.phase2 then Q+1 else Q
  let target := r.work1.getD (T+q1) 0
  let first := run (blockD1Forward r) s
  let middle := run (blockD2Forward r w) first
  let final := run (blockD3Forward r) middle
  let before := [r.phase1,r.phase2,r.iter,r.sign] ++ r.work1 ++ r.work2 ++ r.lengthT
  let after := r.lengthS ++ r.lengthRPrime ++ r.aux
  have hp : (before ++ (r.lengthQ ++ after)).Nodup := by
    simpa only [before,after,IndexedStepRegisters.allWires,List.append_assoc] using h.physical
  have hn (wire : Wire) (hm : wire ∈ before ∨ wire ∈ after) : wire ∉ r.lengthQ := by
    intro hq'
    rcases hm with hb | ha
    · exact (List.nodup_append.mp hp).2.2 wire hb wire (List.mem_append_left _ hq') rfl
    · exact (List.nodup_append.mp (List.nodup_append.mp hp).2.1).2.2 wire hq' wire ha rfl
  have hba (a b : Wire) (ha : a ∈ before) (hb : b ∈ after) : a ≠ b :=
    (List.nodup_append.mp hp).2.2 a ha b (List.mem_append_right _ hb)
  have htlen : T+q1 < r.work1.length := by
    have he := hql.work1_length
    change ((r.work1.drop (w.start-1)).take (w.stop-w.start+1)).length = _ at he
    simp only [List.length_take,List.length_drop] at he
    change w.start ≤ T+q1+1 at hlo
    change T+q1+1 ≤ w.stop at hhi
    omega
  have htMem : target ∈ r.work1 := by
    dsimp only [target]
    rw [List.getD_eq_getElem _ _ htlen]
    exact List.getElem_mem _
  have hsBefore : r.sign ∈ before := by simp [before]
  have htBefore : target ∈ before := by simp [before,htMem]
  have hp1Before : r.phase1 ∈ before := by simp [before]
  have hp2Before : r.phase2 ∈ before := by simp [before]
  have hall := h.physical
  simp only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append,List.nodup_cons] at hall
  have hp1s : r.phase1 ≠ r.sign := by intro he; apply hall.1; simp [he]
  have hp2s : r.phase2 ≠ r.sign := by intro he; apply hall.2.1; simp [he]
  have hp1t : r.phase1 ≠ target := by intro he; apply hall.1; simp [he,htMem]
  have hp2t : r.phase2 ≠ target := by intro he; apply hall.2.1; simp [he,htMem]
  have h1 := blockD1Forward_logicalLength r n index Q s h hc hq
  have hfirst (wire : Wire) (hm : wire ∈ before ∨ wire ∈ after) : first wire = s wire :=
    h1.2.1 wire (hn wire hm)
  have hf1 := hfirst r.phase1 (Or.inl hp1Before)
  have hf2 := hfirst r.phase2 (Or.inl hp2Before)
  have hfs := hfirst r.sign (Or.inl hsBefore)
  have hft := hfirst target (Or.inl htBefore)
  have hT : boolWordToNat (wireValues r.lengthT first) = truthMinusOneValue r.lengthQ.length T := by
    have he : wireValues r.lengthT first = wireValues r.lengthT s := by
      apply List.map_congr_left
      intro wire hm
      exact hfirst wire (Or.inl (by simp [before,hm]))
    rw [he]; exact ht
  have hQ : boolWordToNat (wireValues r.lengthQ first) = truthMinusOneValue r.lengthQ.length q1 := h1.1
  have hm : middle = if s r.phase1 ^^ s r.phase2 then
      first[r.sign ↦ s target][target ↦ s r.sign] else first := by
    have he := blockD2Forward_logical r n index T q1 w first h hql h1.2.2 hw hT hQ hfit hlo hhi
    change middle = if first r.phase1 ^^ first r.phase2 then
      first[r.sign ↦ first target][target ↦ first r.sign] else first at he
    simpa only [hf1,hf2,hfs,hft] using he
  have hmid (wire : Wire) (hs : wire ≠ r.sign) (ht' : wire ≠ target) : middle wire = first wire := by
    rw [hm]
    split <;> simp only [upd,hs,ht',if_false]
  have hmid1 : middle r.phase1 = s r.phase1 := (hmid _ hp1s hp1t).trans hf1
  have hmid2 : middle r.phase2 = s r.phase2 := (hmid _ hp2s hp2t).trans hf2
  have hmidQ : wireValues r.lengthQ middle = wireValues r.lengthQ first := by
    apply List.map_congr_left
    intro wire hq'
    apply hmid
    · intro he; subst wire; exact hn r.sign (Or.inl hsBefore) hq'
    · intro he; subst wire; exact hn target (Or.inl htBefore) hq'
  have hmidClean : Clean r.aux middle := by
    intro wire ha
    have ha' : wire ∈ after := by simp [after,ha]
    rw [hmid wire (Ne.symm (hba _ _ hsBefore ha')) (Ne.symm (hba _ _ htBefore ha'))]
    exact h1.2.2 wire ha
  have hpos : (middle r.phase1 && !middle r.phase2) = true → 0 < q1 := by
    rw [hmid1,hmid2]
    intro he
    have hp1 : s r.phase1 = true := by
      cases hh : s r.phase1
      · simp only [hh,Bool.false_and,Bool.false_eq_true] at he
      · rfl
    simpa only [q1,hp1,Bool.not_true,Bool.false_and,Bool.false_eq_true,if_false] using hpositive he
  have h3 := blockD3Forward_logicalLength r n index q1 middle h hmidClean (hmidQ ▸ hQ) hpos
  have hnum : boolWordToNat (wireValues r.lengthQ final) = truthMinusOneValue r.lengthQ.length
      (if s r.phase1 && !s r.phase2 then q1-1 else q1) := by
    simpa only [hmid1,hmid2] using h3.1
  have hword : wireValues r.lengthQ final = constantBits r.lengthQ.length
      (truthMinusOneValue r.lengthQ.length (if s r.phase1 && !s r.phase2 then q1-1 else q1)) := by
    apply boolWordToNat_injective_of_length (by simp only [wireValues,List.length_map,constantBits_length])
    have hb := boolWordToNat_lt_pow_two (wireValues r.lengthQ final)
    simp only [wireValues,List.length_map] at hb
    change boolWordToNat (wireValues r.lengthQ final) < 2^r.lengthQ.length at hb
    rw [hnum] at hb
    rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt hb]
    exact hnum
  have hframe : AgreesOutside r.lengthQ middle
      (if s r.phase1 ^^ s r.phase2 then s[r.sign ↦ s target][target ↦ s r.sign] else s) := by
    intro wire hw'
    have hf := h1.2.1 wire hw'
    change first wire = s wire at hf
    simp only [hm,ite_apply,upd,hf]
  have hfinal : run (blockDForward r w) s = final := by
    simp only [blockDForward,run_append]
    rfl
  dsimp only
  rw [hfinal]
  refine ⟨hword,?_,h3.2.2⟩
  intro wire hw'
  exact (h3.2.1 wire hw').trans (hframe wire hw')
end ShorECDLP.Paper2607_13816
