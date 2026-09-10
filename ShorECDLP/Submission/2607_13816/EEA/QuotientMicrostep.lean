import ShorECDLP.Submission.«2607_13816».EEA.ShiftState
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Finishing a quotient digit enters coefficient processing when alignment reaches zero. -/
def quotientFinishMicrostep (v : EEAState) : EEAState :=
  { v with phase := if v.shift=0 then .coefficient else .quotient }

/-- E/F are disabled during quotient processing and G changes only the phase bits.
The positive quotient length prevents a comparison-phase transition. -/
theorem blockEFGForward_quotient_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase=.quotient) (hsign : v.sign=false)
    (hQ : 0<v.lQ) (hQfit : v.lQ<2^r.lengthQ.length)
    (hRfit : v.lRPrime<2^r.lengthRPrime.length) (hSfit : v.shift<2^r.lengthS.length) :
    IndexedPackedState r n
      (run (blockEForward r n (certifiedActiveWindows n index).coefficient ++
        blockFForward r ++ blockGForward r) s) (quotientFinishMicrostep v) := by
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
  have hp2 : s r.phase2=true := by simpa [hphase,EEAPhase.bits] using hp.phase2
  have hs : s r.sign=false := hp.sign.trans hsign
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
      s[r.phase1 ↦ decide (v.shift=0)][r.phase2 ↦ !decide (v.shift=0)][r.sign ↦ false] := by
    simpa [hp1,hp2,hs,show v.lQ≠0 by omega] using hg.1
  rw [Classical.run_append,Classical.run_append,he,hf]
  let out := run (blockGForward r) s
  change out=s[r.phase1 ↦ decide (v.shift=0)][r.phase2 ↦ !decide (v.shift=0)][r.sign ↦ false] at hrun
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
    by_cases hz : v.shift=0 <;> simp [quotientFinishMicrostep,EEAPhase.bits,hz,upd,h12,h1s]
  · change out r.phase2=_
    rw [hrun]
    have h2s : r.phase2≠r.sign := by intro he; exact hn.2.1 (by simp [he])
    by_cases hz : v.shift=0 <;> simp [quotientFinishMicrostep,EEAPhase.bits,hz,upd,h2s]
  · change out r.sign=v.sign
    rw [hrun]
    simp [upd,hsign]
  · change out r.iter=v.iter
    rw [hrun]
    have hi1 : r.iter≠r.phase1 := by intro he; exact hn.1 (by simp [← he])
    have hi2 : r.iter≠r.phase2 := by intro he; exact hn.2.1 (by simp [← he])
    have his : r.iter≠r.sign := by intro he; exact hn.2.2.1 (by simp [he])
    simpa [upd,hi1,hi2,his] using hp.iter
  · intro w hw
    exact (hstable w (by simp [hw])).trans (hp.clean w hw)

/-- One complete quotient microstep of the actual eight-block schedule. -/
def quotientMicrostep (v : EEAState) : EEAState :=
  quotientFinishMicrostep (quotientPushMicrostep (remainderMicrostep (preShiftMicrostep v)))

/-- The complete quotient step derives all intermediate packed states and phase
changes. Its positive output quotient disables H, including at zero shift. -/
theorem indexedStepUnitary_quotient_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase=.quotient) (hsign : v.sign=false)
    (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hshift : 0<v.shift) (hsfit : v.shift<2^r.lengthS.length)
    (hspan : v.lT+v.lQ+1+v.shift+v.lRPrime≤n+3)
    (htp : v.tPrime<2^(v.lT+v.lQ+v.shift))
    (hrp : v.rPrime<2^v.lRPrime) (hrem : v.r<v.rPrime*2^v.shift)
    (hleftLow : (certifiedActiveWindows n index).remainder.start≤v.lT+v.lQ+2)
    (hleftHigh : v.lT+v.lQ+2-(certifiedActiveWindows n index).remainder.start<2^r.lengthQ.length)
    (hrightLow : v.shift-1+(certifiedActiveWindows n index).remainder.start≤n+3)
    (hrightHigh : n+3-(v.shift-1)-(certifiedActiveWindows n index).remainder.start<2^r.lengthS.length)
    (hfit : v.lT+v.lQ+2<2^r.lengthQ.length)
    (hlo : (certifiedActiveWindows n index).quotientSwap.start≤v.lT+v.lQ+2)
    (hhi : v.lT+v.lQ+2≤(certifiedActiveWindows n index).quotientSwap.stop)
    (hq : v.q<2^v.lQ) :
    let next := quotientMicrostep v
    IndexedPackedState r n
      (run (indexedStepUnitary r n index) s) next ∧
    next.r<v.rPrime*2^(v.shift-1) ∧ next.q<2^next.lQ ∧
    v.r=(if (remainderMicrostep (preShiftMicrostep v)).sign then v.rPrime*2^(v.shift-1) else 0)+next.r := by
  let pre := blockAForward r ++ blockBForward r n (certifiedActiveWindows n index).remainder ++
    blockCForward r ++ blockDForward r (certifiedActiveWindows n index).quotientSwap
  let tail := blockEForward r n (certifiedActiveWindows n index).coefficient ++ blockFForward r ++ blockGForward r
  let d := run pre s
  let mid := quotientPushMicrostep (remainderMicrostep (preShiftMicrostep v))
  let out := run tail d
  have hd := blockABCDForward_quotient_packed r n index s v h hp hphase hsign hR hRfit
    hwidth hshift hsfit hspan htp hrp hrem hleftLow hleftHigh hrightLow hrightHigh hfit hlo hhi hq
  change IndexedPackedState r n d mid ∧ _ at hd
  have hqm : mid.lQ=v.lQ+1 := rfl
  have hsm : mid.shift=v.shift-1 := by simp [mid,quotientPushMicrostep,remainderMicrostep,preShiftMicrostep,hphase,EEAPhase.bits]
  have hqfit : mid.lQ<2^r.lengthQ.length := by rw [hqm]; omega
  have hqpos : 0<mid.lQ := by rw [hqm]; omega
  have hsfit' : mid.shift<2^r.lengthS.length := by rw [hsm]; omega
  have hf : IndexedPackedState r n out (quotientFinishMicrostep mid) :=
    blockEFGForward_quotient_packed r n index d mid h hd.1 hphase rfl hqpos hqfit hRfit hsfit'
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
  have hzero : wireAnd r.lengthQ out=false := by
    rw [wireAnd_encoded_zero r.lengthQ out (quotientFinishMicrostep mid).lQ hf.lengthQ hqfit]
    exact decide_eq_false (by change mid.lQ≠0; omega)
  have hH := blockHForward_nonzeroQuotient r n index out h hready hzero
  have hprogram : indexedStepUnitary r n index=pre++tail++blockHForward r n index := by
    simp only [indexedStepUnitary,pre,tail,List.append_assoc]
  dsimp only
  rw [hprogram,Classical.run_append,Classical.run_append]
  change IndexedPackedState r n (run (blockHForward r n index) out) (quotientMicrostep v) ∧ _
  rw [hH]
  exact ⟨hf,hd.2⟩

end ShorECDLP.Paper2607_13816
