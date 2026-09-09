import ShorECDLP.Submission.«2607_13816».EEA.CoefficientInvariant
import ShorECDLP.Submission.«2607_13816».EEA.LogicalPhase
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem phase_regroup_disjoint (a b c d e : List Wire)
    (h : (a++(b++(c++(d++e)))).Nodup) :
    List.Disjoint (a++c++e) (d++b) := by
  obtain ⟨_,hrest,ha⟩ := List.nodup_append.mp h
  obtain ⟨_,hrest,hb⟩ := List.nodup_append.mp hrest
  obtain ⟨_,hrest,hc⟩ := List.nodup_append.mp hrest
  obtain ⟨_,_,hd⟩ := List.nodup_append.mp hrest
  apply List.disjoint_left.mpr
  intro w hw hn
  simp only [List.mem_append] at hw hn
  rcases hw with (hw | hw) | hw <;> rcases hn with hn | hn
  · exact ha w hw w (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hn))) rfl
  · exact ha w hw w (List.mem_append_left _ hn) rfl
  · exact hc w hw w (List.mem_append_left _ hn) rfl
  · exact hb w hn w (List.mem_append_left _ hw) rfl
  · exact hd w hn w hw rfl
  · exact hb w hn w (List.mem_append_right _ (List.mem_append_right _ hw)) rfl

/-- The actual D/E/F/G coefficient phase enters its comparison phase exactly
when the last quotient bit is consumed and the divisor length is nonzero.
The complete state equation retains every coefficient-stage data output. -/
theorem blockDEFGForward_coefficientPhase (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hc : Clean r.aux s) (hp1 : s r.phase1 = true) (hp2 : s r.phase2 = false)
    (hsign : s r.sign = false) (hQ : 0 < v.lQ)
    (htmeta : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthT.length v.lT)
    (hqmeta : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length v.lQ)
    (hrmeta : boolWordToNat (wireValues r.lengthRPrime s) = truthMinusOneValue r.lengthT.length v.lRPrime)
    (hsmeta : boolWordToNat (wireValues r.tBoundary.lengthSLow s) = truthMinusOneValue r.lengthT.length v.shift)
    (hqfit : v.lT+v.lQ+1 < 2^r.lengthQ.length)
    (hqlo : (certifiedActiveWindows n index).quotientSwap.start ≤ v.lT+v.lQ+1)
    (hqhi : v.lT+v.lQ+1 ≤ (certifiedActiveWindows n index).quotientSwap.stop)
    (hthi : v.lT+1 < 2^r.lengthT.length)
    (hlo : v.lRPrime+v.shift ≤ n+3)
    (hhi : n+3-v.lRPrime-v.shift < 2^r.lengthT.length)
    (hv : v.lT+1 ∈ quotientSwapLabels 1 (certifiedActiveWindows n index).coefficient.stop)
    (ht : v.t < 2^v.lT) (htp : v.tPrime < 2^(n+3-v.lRPrime))
    (hspan : v.shift+(v.lT+1) ≤ n+3-v.lRPrime)
    (hbound : v.tPrime < 2^v.shift*v.t)
    (hquot : v.q < 2^v.lQ) (hrem : v.r < 2^(n+3-(v.lT+v.lQ+1)))
    (hwork1 : wireValues r.work1 s = constantBits v.lT v.t ++ [false] ++
      (constantBits v.lQ v.q).reverse ++ (constantBits (n+3-(v.lT+v.lQ+1)) v.r).reverse)
    (hwork2 : wireValues r.work2 s = (constantBits (n+3-v.lRPrime) v.tPrime ++
      (constantBits v.lRPrime v.rPrime).reverse).rotate v.shift)
    (hsfull : boolWordToNat (wireValues r.lengthS s) = truthMinusOneValue r.lengthS.length v.shift)
    (hswidth : 0 < r.lengthS.length) (hsinc : v.shift+1 < 2^r.lengthS.length)
    (hrpfit : v.lRPrime < 2^r.lengthRPrime.length) :
    let pre := blockDForward r (certifiedActiveWindows n index).quotientSwap ++
      blockEForward r n (certifiedActiveWindows n index).coefficient ++ blockFForward r
    let mid := run pre s
    let switch := decide (v.lQ=1) && !decide (v.lRPrime=0)
    run (pre ++ blockGForward r) s = mid[r.phase2 ↦ switch][r.sign ↦ switch] ∧
    IndexedStepReady r (run (pre ++ blockGForward r) s) := by
  let pre := blockDForward r (certifiedActiveWindows n index).quotientSwap ++
    blockEForward r n (certifiedActiveWindows n index).coefficient ++ blockFForward r
  let mid := run pre s
  obtain ⟨_,_,hdQ,hdS,hdSign,_,_,hdReady,_,_,hdFrame⟩ :=
    blockDEFForward_completeCoefficient r n index s v h hc hp1 hp2 hsign hQ
      htmeta hqmeta hrmeta hsmeta hqfit hqlo hqhi hthi hlo hhi hv ht htp hspan
      hbound hquot hrem hwork1 hwork2 hsfull hswidth hsinc
  have hsep := phase_regroup_disjoint [r.phase1,r.phase2,r.iter] (r.sign :: r.work1 ++ r.work2)
    r.lengthT (r.lengthQ ++ r.lengthS) (r.lengthRPrime ++ r.aux)
    (by simpa only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append] using h.physical)
  have hpres : ∀ wire ∈ [r.phase1,r.phase2,r.iter] ++ r.lengthT ++ (r.lengthRPrime ++ r.aux),
      mid wire = s wire := by
    intro wire hw
    apply hdFrame wire
    have hn := List.disjoint_left.mp hsep hw
    intro hm
    apply hn
    simp only [List.mem_append] at hm ⊢
    rcases hm with (hm | hm) | hm
    · exact Or.inl (Or.inl hm)
    · exact Or.inr hm
    · exact Or.inl (Or.inr hm)
  have hp1m : mid r.phase1 = true := (hpres _ (by simp)).trans hp1
  have hp2m : mid r.phase2 = false := (hpres _ (by simp)).trans hp2
  have hsgm : mid r.sign = false := hdSign
  have hrword : wireValues r.lengthRPrime mid = wireValues r.lengthRPrime s := by
    apply List.map_congr_left
    intro wire hw
    exact hpres _ (by simp [hw])
  have hepmem : r.shiftEpoch ∈ r.aux := by
    change r.aux.getD 1 0 ∈ r.aux
    rw [List.getD_eq_getElem _ _ (by rw [h.aux_length]; decide)]
    exact List.getElem_mem _
  have hepoch : mid r.shiftEpoch = false := (hpres _ (by simp [hepmem])).trans (hc _ hepmem)
  have hrwidth : r.lengthRPrime.length = r.lengthT.length := h.tBoundary.lengthRP_length
  have hqmeta' : boolWordToNat (wireValues r.lengthQ mid) = truthMinusOneValue r.lengthQ.length (v.lQ-1) := by
    change wireValues r.lengthQ mid = _ at hdQ
    rw [hdQ,boolWordToNat_constantBits]
    exact Nat.mod_mod _ _
  have hqfit' : v.lQ-1 < 2^r.lengthQ.length := by omega
  have hg := blockGForward_logical r n index (v.lQ-1) v.lRPrime (v.shift+1) mid h hdReady hepoch
    hqmeta' (by simpa only [hrword,hrwidth] using hrmeta) hdS hqfit' hrpfit hsinc
  have hQeq : v.lQ-1=0 ↔ v.lQ=1 := by omega
  have hSpos : ¬ v.shift+1=0 := by omega
  have hupdate : mid[r.phase1 ↦ true] = mid := by
    funext wire
    by_cases hw : wire = r.phase1
    · subst wire; simp only [upd_same,hp1m]
    · simp only [upd,hw,ite_false]
  dsimp only at hg ⊢
  simp only [hp1m,hp2m,hsgm,Bool.false_xor,Bool.and_true,Bool.and_self,
    hQeq,decide_eq_false hSpos,Bool.xor_false,hupdate] at hg
  simpa only [pre,mid,Classical.run_append] using hg
end ShorECDLP.Paper2607_13816
