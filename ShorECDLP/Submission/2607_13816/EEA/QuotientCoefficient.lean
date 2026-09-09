import ShorECDLP.Submission.«2607_13816».EEA.QuotientPacking
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPhases
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem regroup_disjoint (a b c d e : List Wire)
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

private theorem quotient_metadata_separation (r : IndexedStepRegisters)
    (h : r.allWires.Nodup) :
    List.Disjoint ([r.phase1,r.phase2,r.iter] ++ r.work2 ++ r.lengthT ++ r.lengthS ++ r.lengthRPrime ++ r.aux)
      (r.lengthQ ++ (r.sign :: r.work1)) := by
  have hh := regroup_disjoint [r.phase1,r.phase2,r.iter] (r.sign :: r.work1)
    (r.work2 ++ r.lengthT) r.lengthQ (r.lengthS ++ r.lengthRPrime ++ r.aux)
    (by simpa only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append] using h)
  simpa only [List.append_assoc] using hh

private theorem coefficient_metadata_separation (r : IndexedStepRegisters)
    (h : r.allWires.Nodup) :
    List.Disjoint ([r.phase1,r.phase2,r.iter] ++ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux)
      (r.sign :: r.work1 ++ r.work2) := by
  have hh := regroup_disjoint [r.phase1,r.phase2,r.iter] (r.sign :: r.work1 ++ r.work2)
    (r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime) ([] : List Wire) r.aux
    (by simpa only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append] using h)
  simpa only [List.append_assoc,List.nil_append] using hh

private theorem ready_of_aux_clean (r : IndexedStepRegisters) (s : BasisState)
    (hlen : r.aux.length = 22) (hc : Clean r.aux s) : IndexedStepReady r s := by
  intro w hw
  apply hc w
  simp only [IndexedStepRegisters.sharedScratch,List.mem_cons,List.mem_append] at hw
  rcases hw with rfl | hw | hw
  · dsimp only [IndexedStepRegisters.control]
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; decide)]
    exact List.getElem_mem _
  · exact List.mem_of_mem_take (List.mem_of_mem_drop hw)
  · exact List.mem_of_mem_drop hw


/-- In the coefficient phase, the actual quotient and coefficient blocks consume one
quotient bit and conditionally add the shifted coefficient. All bounds are on the
initial logical fields; no intermediate-state readiness premise is assumed. -/
theorem blockDEForward_coefficient (r : IndexedStepRegisters) (n index : Nat)
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
    (hcoeff : v.tPrime < 2^(v.shift+(v.lT+1)))
    (hcarry : v.q.testBit 0 = true → v.tPrime/2^v.shift+v.t < 2^(v.lT+1))
    (hquot : v.q < 2^v.lQ) (hrem : v.r < 2^(n+3-(v.lT+v.lQ+1)))
    (hwork1 : wireValues r.work1 s = constantBits v.lT v.t ++ [false] ++
      (constantBits v.lQ v.q).reverse ++ (constantBits (n+3-(v.lT+v.lQ+1)) v.r).reverse)
    (hwork2 : wireValues r.work2 s = (constantBits (n+3-v.lRPrime) v.tPrime ++
      (constantBits v.lRPrime v.rPrime).reverse).rotate v.shift) :
    let updated := if v.q.testBit 0 then v.tPrime+2^v.shift*v.t else v.tPrime
    let final := run (blockDForward r (certifiedActiveWindows n index).quotientSwap ++
      blockEForward r n (certifiedActiveWindows n index).coefficient) s
    wireValues r.work1 final = constantBits v.lT v.t ++ [false] ++
      (constantBits (v.lQ-1) (v.q/2)).reverse ++
      (constantBits (n+3-(v.lT+(v.lQ-1)+1)) v.r).reverse ∧
    wireValues r.work2 final = (constantBits (n+3-v.lRPrime) updated ++
      (constantBits v.lRPrime v.rPrime).reverse).rotate v.shift ∧
    updated < 2^(n+3-v.lRPrime) ∧ v.q/2 < 2^(v.lQ-1) ∧
    final r.sign = (if v.q.testBit 0 then false else
      (true ^^ decide (v.tPrime < v.t*2^v.shift))) ∧
    wireValues r.lengthQ final = constantBits r.lengthQ.length
      (truthMinusOneValue r.lengthQ.length (v.lQ-1)) ∧
    IndexedStepReady r final := by
  let w := (certifiedActiveWindows n index).quotientSwap
  let cw := (certifiedActiveWindows n index).coefficient
  let mid := run (blockDForward r w) s
  have hwidth : r.lengthT.length = r.lengthQ.length := h.quotient.lengthT_eq_lengthQ
  have hstart : 1 ≤ w.start := by
    dsimp [w,certifiedActiveWindows,quotientSwapWindow]
    omega
  have hd := blockDForward_popPacking r n index v.lT v.lQ
    (n+3-(v.lT+v.lQ+1)) v.t v.q v.r w s h h.quotient hc hstart hp1 hp2 hQ hsign
    (by simpa only [hwidth] using htmeta) hqmeta hqfit hqlo hqhi hquot hrem hwork1
  change wireValues r.work1 mid = _ ∧ _ at hd
  have hsign' : mid r.sign = v.q.testBit 0 := hd.2.2.1
  have hpres : ∀ wire ∈ [r.phase1,r.phase2,r.iter] ++ r.work2 ++ r.lengthT ++
      r.lengthS ++ r.lengthRPrime ++ r.aux, mid wire = s wire := by
    intro wire hm
    exact hd.2.2.2.2.1 wire (List.disjoint_left.mp (quotient_metadata_separation r h.physical) hm)
  have hword : ∀ wires : List Wire, (∀ wire ∈ wires, wire ∈
      [r.phase1,r.phase2,r.iter] ++ r.work2 ++ r.lengthT ++ r.lengthS ++ r.lengthRPrime ++ r.aux) →
      wireValues wires mid = wireValues wires s := by
    intro wires hm
    exact List.map_congr_left (fun wire hw => hpres wire (hm wire hw))
  have hp1' : mid r.phase1 = true := (hpres _ (by simp)).trans hp1
  have hp2' : mid r.phase2 = false := (hpres _ (by simp)).trans hp2
  have htword := hword r.lengthT (by intro wire hw; simp [hw])
  have hrword := hword r.lengthRPrime (by intro wire hw; simp [hw])
  have hsword := hword r.tBoundary.lengthSLow (by
    intro wire hw
    have hm : wire ∈ r.lengthS := List.mem_of_mem_take hw
    simp [hm])
  have hw2 := hword r.work2 (by intro wire hw; simp [hw])
  have hgeom : v.lT+v.lQ+1 ≤ n+3 := by
    have he := congrArg List.length hwork1
    simp only [wireValues,List.length_map,List.length_append,List.length_reverse,
      constantBits_length,List.length_singleton,h.work1_length] at he
    omega
  have hremwidth : n+3-(v.lT+v.lQ+1)+1 = n+3-(v.lT+(v.lQ-1)+1) := by omega
  let next := {v with q := v.q/2, lQ := v.lQ-1}
  have he := blockEForward_coefficientOrdinary r n index cw mid next h rfl
    (ready_of_aux_clean r mid h.aux_length hd.2.2.2.2.2)
    (by simpa only [htword] using htmeta) (by simpa only [hrword] using hrmeta)
    (by simpa only [hsword] using hsmeta) hthi hlo hhi
    (by simpa only [hp2',Bool.false_eq_true,ite_false] using hv)
    ht htp
    (by simp [cw,certifiedActiveWindows,coefficientWindow,next,hp2'])
    (by simpa [cw,certifiedActiveWindows,coefficientWindow,next,hp2',Nat.add_assoc] using hspan)
    (by simpa only [hp2',Bool.false_eq_true,ite_false] using
      (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : v.lT ≤ v.lT+1))))
    (by simpa only [hp2',Bool.false_eq_true,ite_false] using hcoeff)
    (by simpa only [hp1',hp2',hsign',Bool.not_false,Bool.true_and,Bool.false_eq_true,ite_false] using hcarry)
    (by simpa only [next,hremwidth] using hd.1)
    (by simpa only [hw2] using hwork2)
  dsimp only [next] at he
  have heQ : wireValues r.lengthQ (run (blockEForward r n cw) mid) = wireValues r.lengthQ mid := by
    apply List.map_congr_left
    intro wire hm
    apply he.2.2.2.2.2 wire
    have hn := List.disjoint_left.mp (coefficient_metadata_separation r h.physical)
      (show wire ∈ [r.phase1,r.phase2,r.iter] ++ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux by simp [hm])
    intro hw
    apply hn
    simp only [IndexedStepRegisters.coefficient,List.mem_cons,List.mem_append] at hw ⊢
    rcases hw with (hw | hw) | hw
    · exact Or.inl (Or.inl hw)
    · exact Or.inl (Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take hw)))
    · exact Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take hw))
  dsimp only
  simp only [Classical.run_append]
  change wireValues r.work1 (run (blockEForward r n cw) mid) = _ ∧ _
  refine ⟨he.2.2.1.trans (by simpa only [hremwidth] using hd.1), ?_, ?_, hd.2.1, ?_, heQ.trans hd.2.2.2.1, he.2.2.2.2.1⟩
  · simpa only [hp1',hp2',hsign',Bool.not_false,Bool.true_and] using he.1
  · simpa only [hp1',hp2',hsign',Bool.not_false,Bool.true_and] using he.2.1
  · have hs := he.2.2.2.1
    simp only [hp1',hp2',hsign',Bool.not_false,Bool.true_and,ite_true] at hs
    cases hb : v.q.testBit 0 <;> simpa only [hb,Bool.false_eq_true,ite_false,ite_true,Bool.false_xor] using hs

end ShorECDLP.Paper2607_13816
