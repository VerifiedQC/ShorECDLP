import ShorECDLP.Submission.«2607_13816».EEA.QuotientMicrostep
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Comparison selects quotient processing once the divisor exceeds the remainder. -/
def remainderFinishMicrostep (v : EEAState) : EEAState :=
  { v with phase := if v.sign then .quotient else .remainder, sign := false }
theorem blockEFGForward_remainder_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase=.remainder)
    (hQ : v.lQ=0) (hR : 0<v.lRPrime) (hS : 0<v.shift) (hQfit : v.lQ<2^r.lengthQ.length)
    (hRfit : v.lRPrime<2^r.lengthRPrime.length) (hSfit : v.shift<2^r.lengthS.length) :
    IndexedPackedState r n
      (run (blockEForward r n (certifiedActiveWindows n index).coefficient ++
        blockFForward r ++ blockGForward r) s) (remainderFinishMicrostep v) := by
  have hr : IndexedStepReady r s := by
    intro wire hm
    apply hp.clean wire
    simp only [IndexedStepRegisters.sharedScratch,List.mem_cons,List.mem_append] at hm
    rcases hm with he | he | he
    · subst wire
      change r.aux.getD 0 0 ∈ r.aux
      rw [List.getD_eq_getElem _ _ (by rw [h.aux_length]; decide)]
      exact List.getElem_mem _
    · exact List.mem_of_mem_take (List.mem_of_mem_drop he)
    · exact List.mem_of_mem_drop he
  have hp1 : s r.phase1=false := by simpa [hphase,EEAPhase.bits] using hp.phase1
  have hp2 : s r.phase2=false := by simpa [hphase,EEAPhase.bits] using hp.phase2
  have he := blockEForward_inactive r n index _ s h rfl hr hp1
  have hf : run (blockFForward r) s=s := postShiftUnitary_idle r.postShift s h.postShift
    (blockFForward_readiness r n index s h hr).1 hp1
  have hepoch : s r.shiftEpoch=false := hp.clean _ (by
    change r.aux.getD 1 0 ∈ r.aux
    rw [List.getD_eq_getElem _ _ (by rw [h.aux_length]; decide)]
    exact List.getElem_mem _)
  have hg := blockGForward_logical r n index v.lQ v.lRPrime v.shift s h hr hepoch
    hp.lengthQ hp.lengthRP hp.lengthS hQfit hRfit hSfit
  have hrun : run (blockGForward r) s=
      s[r.phase1 ↦ false][r.phase2 ↦ v.sign][r.sign ↦ false] := by
    simpa [hp1,hp2,hp.sign,hQ,show v.lRPrime≠0 by omega,show v.shift≠0 by omega] using hg.1
  rw [Classical.run_append,Classical.run_append,he,hf]
  let out := run (blockGForward r) s
  change out=s[r.phase1 ↦ false][r.phase2 ↦ v.sign][r.sign ↦ false] at hrun
  have hn := h.physical
  simp only [IndexedStepRegisters.allWires,List.cons_append,List.nil_append,List.nodup_cons] at hn
  have hstable (wire : Wire) (hw : wire ∈ r.work1++r.work2++r.lengthT++r.lengthQ++r.lengthS++r.lengthRPrime++r.aux) : out wire=s wire := by
    have h1 : wire≠r.phase1 := by intro he; subst wire; exact hn.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
    have h2 : wire≠r.phase2 := by intro he; subst wire; exact hn.2.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
    have hsg : wire≠r.sign := by intro he; subst wire; exact hn.2.2.2.1 hw
    rw [hrun]
    simp only [upd,h1,h2,hsg,if_false]
  have hword (ws : List Wire) (hw : ∀ wire∈ws, wire ∈ r.work1++r.work2++r.lengthT++r.lengthQ++r.lengthS++r.lengthRPrime++r.aux) : wireValues ws out=wireValues ws s := by
    apply List.map_congr_left
    intro w hm
    exact hstable w (hw w hm)
  constructor
  · change wireValues r.work1 out=_
    rw [hword r.work1 (by intro w hw; simp [hw])]
    exact hp.work1
  · change wireValues r.work2 out=_
    rw [hword r.work2 (by intro w hw; simp [hw])]
    exact hp.work2
  · change boolWordToNat (wireValues r.lengthT out)=_
    rw [hword r.lengthT (by intro w hw; simp [hw])]
    exact hp.lengthT
  · change boolWordToNat (wireValues r.lengthQ out)=_
    rw [hword r.lengthQ (by intro w hw; simp [hw])]
    exact hp.lengthQ
  · change boolWordToNat (wireValues r.lengthRPrime out)=_
    rw [hword r.lengthRPrime (by intro w hw; simp [hw])]
    exact hp.lengthRP
  · change boolWordToNat (wireValues r.lengthS out)=_
    rw [hword r.lengthS (by intro w hw; simp [hw])]
    exact hp.lengthS
  · change out r.phase1=_
    rw [hrun]
    have h12 : r.phase1≠r.phase2 := by intro he; exact hn.1 (by simp [he])
    have h1s : r.phase1≠r.sign := by intro he; exact hn.1 (by simp [he])
    cases hv : v.sign <;> simp [hv,remainderFinishMicrostep,EEAPhase.bits,upd,h12,h1s]
  · change out r.phase2=_
    rw [hrun]
    have h2s : r.phase2≠r.sign := by intro he; exact hn.2.1 (by simp [he])
    cases hv : v.sign <;> simp [hv,remainderFinishMicrostep,EEAPhase.bits,upd,h2s]
  · change out r.sign=false
    rw [hrun]
    simp [upd]
  · change out r.iter=v.iter
    rw [hrun]
    have hi1 : r.iter≠r.phase1 := by intro he; exact hn.1 (by simp [← he])
    have hi2 : r.iter≠r.phase2 := by intro he; exact hn.2.1 (by simp [← he])
    have his : r.iter≠r.sign := by intro he; exact hn.2.2.1 (by simp [he])
    simpa [upd,hi1,hi2,his] using hp.iter
  · intro w hw
    exact (hstable w (by simp [hw])).trans (hp.clean w hw)


/-- One complete remainder-alignment step, including its comparison transition. -/
def remainderAlignmentMicrostep (v : EEAState) : EEAState :=
  remainderFinishMicrostep (remainderMicrostep (preShiftMicrostep v))

/-- All eight actual blocks preserve complete packing while advancing alignment.
The comparison selects quotient entry, and the positive shift disables H. -/
private theorem remainder_prefix_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase=.remainder) (hsign : v.sign=false)
    (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hSfit : v.shift+1<2^r.lengthS.length)
    (hspan : v.lT+v.lQ+1+(v.shift+1)+v.lRPrime≤n+3)
    (htp : v.tPrime<2^(v.lT+v.lQ+1+(v.shift+1)))
    (hrp : v.rPrime<2^v.lRPrime) (hrem : v.r<2^(n+3-(v.lT+v.lQ+1)))
    (hleftLow : (certifiedActiveWindows n index).remainder.start≤v.lT+v.lQ+2)
    (hleftHigh : v.lT+v.lQ+2-(certifiedActiveWindows n index).remainder.start<2^r.lengthQ.length)
    (hrightLow : v.shift+1+(certifiedActiveWindows n index).remainder.start≤n+3)
    (hrightHigh : n+3-(v.shift+1)-(certifiedActiveWindows n index).remainder.start<2^r.lengthS.length) :
    IndexedPackedState r n
      (run (blockAForward r ++ blockBForward r n (certifiedActiveWindows n index).remainder ++
        blockCForward r ++ blockDForward r (certifiedActiveWindows n index).quotientSwap) s)
      (remainderMicrostep (preShiftMicrostep v)) := by
  let a := run (blockAForward r) s
  let u := preShiftMicrostep v
  have hph : v.phase.bits.1=false := by simp [hphase,EEAPhase.bits]
  have ha := blockAForward_packed r n index s v h hp hph hR hRfit hwidth (by omega)
    (by simp [hphase,EEAPhase.bits]) (by intro _; exact hSfit)
  have hu : u.shift=v.shift+1 := by simp [u,preShiftMicrostep,hphase,EEAPhase.bits]
  let b := run (blockBForward r n (certifiedActiveWindows n index).remainder) a
  let mid := remainderMicrostep u
  have hb : IndexedPackedState r n b mid := blockBForward_packed r n index a u h ha.1 hph
    hsign hR hRfit (by change v.lT+v.lQ+1+u.shift+v.lRPrime≤_; rw [hu]; exact hspan)
    (by change v.tPrime<2^(v.lT+v.lQ+1+u.shift); rw [hu]; exact htp) hrp hrem
    hleftLow hleftHigh (by rw [hu]; exact hrightLow) (by rw [hu]; exact hrightHigh)
  have hzR : wireAnd r.lengthRPrime b=false := by
    rw [wireAnd_encoded_zero r.lengthRPrime b mid.lRPrime hb.lengthRP hRfit]
    exact decide_eq_false (by change v.lRPrime≠0; omega)
  have hc := blockCForward_nonterminal r n index b h hb.clean hzR
  have hd := blockDForward_remainder_idle r n index b h hb.clean
    (hb.phase1.trans hph)
    (hb.phase2.trans (by change v.phase.bits.2=false; simp [hphase,EEAPhase.bits]))
  rw [Classical.run_append,Classical.run_append,Classical.run_append]
  change IndexedPackedState r n
    (run (blockDForward r (certifiedActiveWindows n index).quotientSwap) (run (blockCForward r) b)) mid
  rw [hc,hd]
  exact hb

theorem indexedStepUnitary_remainder_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase=.remainder) (hsign : v.sign=false)
    (hQ : v.lQ=0) (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hSfit : v.shift+1<2^r.lengthS.length)
    (hspan : v.lT+v.lQ+1+(v.shift+1)+v.lRPrime≤n+3)
    (htp : v.tPrime<2^(v.lT+v.lQ+1+(v.shift+1)))
    (hrp : v.rPrime<2^v.lRPrime) (hrem : v.r<2^(n+3-(v.lT+v.lQ+1)))
    (hleftLow : (certifiedActiveWindows n index).remainder.start≤v.lT+v.lQ+2)
    (hleftHigh : v.lT+v.lQ+2-(certifiedActiveWindows n index).remainder.start<2^r.lengthQ.length)
    (hrightLow : v.shift+1+(certifiedActiveWindows n index).remainder.start≤n+3)
    (hrightHigh : n+3-(v.shift+1)-(certifiedActiveWindows n index).remainder.start<2^r.lengthS.length) :
    IndexedPackedState r n (run (indexedStepUnitary r n index) s) (remainderAlignmentMicrostep v) := by
  let pre := blockAForward r ++ blockBForward r n (certifiedActiveWindows n index).remainder ++
    blockCForward r ++ blockDForward r (certifiedActiveWindows n index).quotientSwap
  let b := run pre s
  let mid := remainderMicrostep (preShiftMicrostep v)
  have hb : IndexedPackedState r n b mid := remainder_prefix_packed r n index s v h hp hphase
    hsign hR hRfit hwidth hSfit hspan htp hrp hrem hleftLow hleftHigh hrightLow hrightHigh
  have hu : mid.shift=v.shift+1 := by simp [mid,remainderMicrostep,preShiftMicrostep,hphase,EEAPhase.bits]
  let tail := blockEForward r n (certifiedActiveWindows n index).coefficient ++ blockFForward r ++ blockGForward r
  let out := run tail b
  have hqm : mid.lQ=0 := hQ
  have hsm : mid.shift=v.shift+1 := hu
  have hf : IndexedPackedState r n out (remainderFinishMicrostep mid) :=
    blockEFGForward_remainder_packed r n index b mid h hb hphase hqm hR
      (by rw [hsm]; omega) (by rw [hqm]; exact Nat.two_pow_pos _) hRfit
      (by rw [hsm]; exact hSfit)
  have hready : IndexedStepReady r out := by
    intro wire hm
    apply hf.clean wire
    simp only [IndexedStepRegisters.sharedScratch,List.mem_cons,List.mem_append] at hm
    rcases hm with he | he | he
    · subst wire
      change r.aux.getD 0 0 ∈ r.aux
      rw [List.getD_eq_getElem _ _ (by rw [h.aux_length]; decide)]
      exact List.getElem_mem _
    · exact List.mem_of_mem_take (List.mem_of_mem_drop he)
    · exact List.mem_of_mem_drop he
  have hzS : wireAnd r.lengthS out=false := by
    rw [wireAnd_encoded_zero r.lengthS out (remainderFinishMicrostep mid).shift hf.lengthS
      (by change mid.shift<_; rw [hsm]; exact hSfit)]
    exact decide_eq_false (by change mid.shift≠0; rw [hsm]; omega)
  have hH := blockHForward_nonzeroShift r n index out h hready hzS
  have hprogram : indexedStepUnitary r n index=pre++tail++blockHForward r n index := by
    simp only [indexedStepUnitary,pre,tail,List.append_assoc]
  rw [hprogram,Classical.run_append,Classical.run_append]
  change IndexedPackedState r n (run (blockHForward r n index) out) _
  rw [hH]
  exact hf

end ShorECDLP.Paper2607_13816
