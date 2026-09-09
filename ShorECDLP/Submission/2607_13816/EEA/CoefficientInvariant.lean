import ShorECDLP.Submission.«2607_13816».EEA.QuotientCoefficient
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem coefficient_bound_step (t tp shift T : Nat) (bit : Bool)
    (ht : t < 2^T) (hp : tp < 2^shift*t) :
    tp < 2^(shift+(T+1)) ∧ tp/2^shift+t < 2^(T+1) ∧
    (if bit then tp+2^shift*t else tp) < 2^(shift+1)*t := by
  have hpow : 0 < 2^shift := Nat.pow_pos (by decide)
  have hdiv : tp/2^shift < t := (Nat.div_lt_iff_lt_mul hpow).mpr (by simpa only [Nat.mul_comm] using hp)
  have hscale : 2^shift*t < 2^shift*2^T := Nat.mul_lt_mul_of_pos_left ht hpow
  constructor
  · rw [Nat.pow_add,Nat.pow_succ]
    nlinarith
  constructor
  · rw [Nat.pow_succ]
    omega
  · rw [Nat.pow_succ]
    cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> nlinarith
private theorem coefficient_weighted_step (t tp shift q : Nat) :
    (if q.testBit 0 then tp+2^shift*t else tp) + 2^(shift+1)*t*(q/2) =
      tp+2^shift*t*q := by
  have hq := Nat.bit_testBit_zero_shiftRight_one q
  rw [Nat.shiftRight_eq_div_pow] at hq
  simp only [Nat.pow_one,Nat.bit] at hq
  rw [Nat.pow_succ]
  cases hb : q.testBit 0 <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] at hq ⊢
  all_goals simp only [Bool.cond_false,Bool.cond_true] at hq
  all_goals conv_rhs => rw [← hq]
  all_goals ring
/-- The actual coefficient stage preserves the accumulated product and a strict
coefficient bound, which supplies both the selected fit and no-overflow facts.
The quotient here is the unweighted packed prefix; multiplying it by `2^shift`
recovers its remaining contribution to the source coefficient recurrence. -/
theorem blockDEFForward_coefficientInvariant (r : IndexedStepRegisters) (n index : Nat)
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
    (hswidth : 0 < r.lengthS.length) (hsinc : v.shift+1 < 2^r.lengthS.length) :
    let updated := if v.q.testBit 0 then v.tPrime+2^v.shift*v.t else v.tPrime
    let final := run (blockDForward r (certifiedActiveWindows n index).quotientSwap ++
      blockEForward r n (certifiedActiveWindows n index).coefficient ++ blockFForward r) s
    wireValues r.work2 final = (constantBits (n+3-v.lRPrime) updated ++
      (constantBits v.lRPrime v.rPrime).reverse).rotate (v.shift+1) ∧
    boolWordToNat (wireValues r.lengthS final) = truthMinusOneValue r.lengthS.length (v.shift+1) ∧
    updated < 2^(n+3-v.lRPrime) ∧ IndexedStepReady r final ∧
    updated < 2^(v.shift+1)*v.t ∧
    updated+2^(v.shift+1)*v.t*(v.q/2) = v.tPrime+2^v.shift*v.t*v.q := by
  have hb := coefficient_bound_step v.t v.tPrime v.shift v.lT (v.q.testBit 0) ht hbound
  have hf := blockDEFForward_coefficient r n index s v h hc hp1 hp2 hsign hQ
    htmeta hqmeta hrmeta hsmeta hqfit hqlo hqhi hthi hlo hhi hv ht htp hspan
    hb.1 (fun _ => hb.2.1) hquot hrem hwork1 hwork2 hsfull hswidth hsinc
  exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,hb.2.2,
    coefficient_weighted_step v.t v.tPrime v.shift v.q⟩


private theorem coefficient_post_frame_separation (r : IndexedStepRegisters)
    (h : r.allWires.Nodup) : List.Disjoint (r.sign :: r.work1 ++ r.lengthQ) (r.work2 ++ r.lengthS) := by
  simp only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append] at h
  have h := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp h).2).2).2
  obtain ⟨hsg,h⟩ := List.nodup_cons.mp h
  obtain ⟨_,h,hw1⟩ := List.nodup_append.mp h
  obtain ⟨_,h,hw2⟩ := List.nodup_append.mp h
  obtain ⟨_,h,_⟩ := List.nodup_append.mp h
  obtain ⟨_,_,hq⟩ := List.nodup_append.mp h
  apply List.disjoint_left.mpr
  intro wire ha hb
  simp only [List.mem_append,List.mem_cons] at ha hb
  rcases ha with (ha | ha) | ha <;> rcases hb with hb | hb
  · subst wire; exact hsg (by simp [hb])
  · subst wire; exact hsg (by simp [hb])
  · exact hw1 wire ha wire (by simp [hb]) rfl
  · exact hw1 wire ha wire (by simp [hb]) rfl
  · exact hw2 wire hb wire (by simp [ha]) rfl
  · exact hq wire ha wire (by simp [hb]) rfl

/-- Complete packed coefficient-step outputs and frame for the actual D/E/F
sequence. The remaining quotient and remainder survive post-shift, so the
conserved weighted contribution is attached to the final physical banks. -/
theorem blockDEFForward_completeCoefficient (r : IndexedStepRegisters) (n index : Nat)
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
    (hswidth : 0 < r.lengthS.length) (hsinc : v.shift+1 < 2^r.lengthS.length) :
    let updated := if v.q.testBit 0 then v.tPrime+2^v.shift*v.t else v.tPrime
    let final := run (blockDForward r (certifiedActiveWindows n index).quotientSwap ++
      blockEForward r n (certifiedActiveWindows n index).coefficient ++ blockFForward r) s
    wireValues r.work1 final = constantBits v.lT v.t ++ [false] ++
      (constantBits (v.lQ-1) (v.q/2)).reverse ++
      (constantBits (n+3-(v.lT+(v.lQ-1)+1)) v.r).reverse ∧
    wireValues r.work2 final = (constantBits (n+3-v.lRPrime) updated ++
      (constantBits v.lRPrime v.rPrime).reverse).rotate (v.shift+1) ∧
    wireValues r.lengthQ final = constantBits r.lengthQ.length
      (truthMinusOneValue r.lengthQ.length (v.lQ-1)) ∧
    boolWordToNat (wireValues r.lengthS final) = truthMinusOneValue r.lengthS.length (v.shift+1) ∧
    final r.sign = false ∧ v.q/2 < 2^(v.lQ-1) ∧
    updated < 2^(n+3-v.lRPrime) ∧ IndexedStepReady r final ∧
    updated < 2^(v.shift+1)*v.t ∧
    updated+2^(v.shift+1)*v.t*(v.q/2) = v.tPrime+2^v.shift*v.t*v.q ∧
    AgreesOutside (r.lengthQ ++ (r.sign :: r.work1 ++ r.work2) ++ r.lengthS) final s := by
  let circuit := blockDForward r (certifiedActiveWindows n index).quotientSwap ++
    blockEForward r n (certifiedActiveWindows n index).coefficient
  let mid := run circuit s
  let final := run (circuit ++ blockFForward r) s
  have hb := coefficient_bound_step v.t v.tPrime v.shift v.lT (v.q.testBit 0) ht hbound
  obtain ⟨hd1,hd2,hdFit,hdq,hdSign,hdQ,hdReady,hdFrame⟩ :=
    blockDEForward_coefficient r n index s v h hc hp1 hp2 hsign hQ
      htmeta hqmeta hrmeta hsmeta hqfit hqlo hqhi hthi hlo hhi hv ht htp hspan
      hb.1 (fun _ => hb.2.1) hquot hrem hwork1 hwork2
  obtain ⟨he2,heS,heFit,heReady,heBound,heSum⟩ :=
    blockDEFForward_coefficientInvariant r n index s v h hc hp1 hp2 hsign hQ
      htmeta hqmeta hrmeta hsmeta hqfit hqlo hqhi hthi hlo hhi hv ht htp hspan
      hbound hquot hrem hwork1 hwork2 hsfull hswidth hsinc
  have hfr : AgreesOutside (r.work2 ++ r.lengthS) (run (blockFForward r) mid) mid :=
    postShiftUnitary_frame r.postShift mid h.postShift (blockFForward_readiness r n index mid h hdReady).1
  have hfinal : final = run (blockFForward r) mid := by
    simp only [final,mid,Classical.run_append]
  have hpres : ∀ wire ∈ r.sign :: r.work1 ++ r.lengthQ, final wire = mid wire := by
    intro wire hw
    rw [hfinal]
    exact hfr wire (List.disjoint_left.mp (coefficient_post_frame_separation r h.physical) hw)
  have hword : ∀ wires : List Wire, (∀ wire ∈ wires, wire ∈ r.sign :: r.work1 ++ r.lengthQ) →
      wireValues wires final = wireValues wires mid := by
    intro wires hw
    exact List.map_congr_left (fun wire hm => hpres wire (hw wire hm))
  have h1 := hword r.work1 (by intro wire hw; simp [hw])
  have hq := hword r.lengthQ (by intro wire hw; simp [hw])
  have hzero : mid r.sign = false := by
    change mid r.sign = _ at hdSign
    have hcomp : decide (v.tPrime < v.t*2^v.shift) = true := by
      apply decide_eq_true
      simpa only [Nat.mul_comm] using hbound
    simpa only [hcomp,Bool.xor_self,ite_self] using hdSign
  dsimp only
  change wireValues r.work1 final = _ ∧ _
  refine ⟨h1.trans hd1,he2,hq.trans hdQ,heS,(hpres _ (by simp)).trans hzero,
    hdq,heFit,heReady,heBound,heSum,?_⟩
  intro wire hn
  have hnF : wire ∉ r.work2 ++ r.lengthS := by
    intro hw
    apply hn
    simp only [List.mem_append,List.mem_cons] at hw ⊢
    rcases hw with hw | hw
    · exact Or.inl (Or.inr (Or.inr hw))
    · exact Or.inr hw
  have hnDE : wire ∉ r.lengthQ ++ (r.sign :: r.work1 ++ r.work2) :=
    fun hw => hn (List.mem_append_left _ hw)
  change final wire = s wire
  rw [hfinal]
  exact (hfr wire hnF).trans (hdFrame wire hnDE)

end ShorECDLP.Paper2607_13816
