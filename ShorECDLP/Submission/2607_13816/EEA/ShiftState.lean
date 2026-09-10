import ShorECDLP.Submission.«2607_13816».EEA.QuotientState
namespace ShorECDLP.Paper2607_13816
open Classical

/-- The initial shift advances remainder alignment or backs up one quotient bit. -/
def preShiftMicrostep (v : EEAState) : EEAState :=
  { v with shift := if v.phase.bits.2 then v.shift-1 else v.shift+1 }

private theorem preshift_packed_disjoint (a b c d e : List Wire)
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

/-- Block A preserves complete packing while updating the same logical shift in
both the rotated second bank and encoded counter. -/
theorem blockAForward_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase.bits.1=false)
    (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hshift : v.shift<2^r.lengthS.length)
    (hdec : v.phase.bits.2=true → 0<v.shift)
    (hinc : v.phase.bits.2=false → v.shift+1<2^r.lengthS.length) :
    IndexedPackedState r n (run (blockAForward r) s) (preShiftMicrostep v) ∧
    (preShiftMicrostep v).shift<2^r.lengthS.length := by
  have hrz : wireAnd r.lengthRPrime s=false := by
    rw [wireAnd_encoded_zero r.lengthRPrime s v.lRPrime hp.lengthRP hRfit]
    exact decide_eq_false (by omega)
  rw [blockAForward_nonterminal r n index s h hp.clean hrz]
  let out := run (preShiftUnitary r.preShift) s
  have hr : ShiftReady r.preShift s := by
    have hlen : r.blockScratch.length=17 := by
      simp [IndexedStepRegisters.blockScratch,IndexedStepRegisters.sourceScratch,h.aux_length]
    have hsub (wire : Wire) (hw : wire ∈ r.blockScratch) : wire ∈ r.aux :=
      List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_mem_drop hw))
    have hget (k : Nat) (hk : k<17) : r.blockScratch.getD k 0 ∈ r.blockScratch := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    intro wire hw
    apply hp.clean wire
    apply hsub
    simp only [ShiftRegisters.scratch,IndexedStepRegisters.preShift,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hw
    rcases hw with hw | hw | hw | hw
    · subst wire; exact hget 0 (by decide)
    · subst wire; exact hget 1 (by decide)
    · exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
    · exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have he := preShiftUnitary_shiftEncoding r.preShift s h.preShift hr
    (hp.phase1.trans hphase)
    (constantBits (n+3-v.lRPrime) v.tPrime ++ (constantBits v.lRPrime v.rPrime).reverse)
    v.shift hp.work2 hp.lengthS (by change 0<r.work2.length; rw [h.work2_length]; omega)
    hwidth hshift (by simpa only [IndexedStepRegisters.preShift,hp.phase2] using hdec)
    (by simpa only [IndexedStepRegisters.preShift,hp.phase2] using hinc)
  dsimp only [IndexedStepRegisters.preShift] at he
  rw [hp.phase2] at he
  have hf := preShiftUnitary_frame r.preShift s h.preShift hr
  have hsep := preshift_packed_disjoint ([r.phase1,r.phase2,r.iter,r.sign]++r.work1) r.work2
    (r.lengthT++r.lengthQ) r.lengthS (r.lengthRPrime++r.aux)
    (by simpa only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append] using h.physical)
  have hphysical : List.Disjoint ([r.phase1,r.phase2,r.iter,r.sign] ++ r.work1 ++
      r.lengthT ++ r.lengthQ ++ r.lengthRPrime ++ r.aux) (r.work2++r.lengthS) := by
    apply List.disjoint_left.mpr
    intro wire hw hm
    apply List.disjoint_left.mp hsep (by simpa only [List.mem_append,or_assoc] using hw)
    simpa only [List.mem_append,or_comm] using hm
  have hstable (wire : Wire) (hw : wire ∈ [r.phase1,r.phase2,r.iter,r.sign] ++ r.work1 ++
      r.lengthT ++ r.lengthQ ++ r.lengthRPrime ++ r.aux) : out wire=s wire :=
    hf wire (List.disjoint_left.mp hphysical hw)
  have hword (ws : List Wire) (hw : ∀ wire ∈ ws, wire ∈ [r.phase1,r.phase2,r.iter,r.sign] ++ r.work1 ++
      r.lengthT ++ r.lengthQ ++ r.lengthRPrime ++ r.aux) : wireValues ws out=wireValues ws s := by
    apply List.map_congr_left
    intro wire hm
    exact hstable wire (hw wire hm)
  constructor
  · constructor
    · change wireValues r.work1 out=_
      rw [hword r.work1 (by intro w hw; simp [hw])]
      exact hp.work1
    · exact he.1
    · change boolWordToNat (wireValues r.lengthT out)=_
      rw [hword r.lengthT (by intro w hw; simp [hw])]
      exact hp.lengthT
    · change boolWordToNat (wireValues r.lengthQ out)=_
      rw [hword r.lengthQ (by intro w hw; simp [hw])]
      exact hp.lengthQ
    · change boolWordToNat (wireValues r.lengthRPrime out)=_
      rw [hword r.lengthRPrime (by intro w hw; simp [hw])]
      exact hp.lengthRP
    · exact he.2.1
    · exact (hstable _ (by simp)).trans hp.phase1
    · exact (hstable _ (by simp)).trans hp.phase2
    · exact (hstable _ (by simp)).trans hp.sign
    · exact (hstable _ (by simp)).trans hp.iter
    · intro wire hw
      exact (hstable wire (by simp [hw])).trans (hp.clean wire hw)
  · exact he.2.2
/-- The actual A/B/C/D quotient prefix derives its shifted division bound from
the original remainder bound and decrements alignment before extracting a digit. -/
theorem blockABCDForward_quotient_packed (r : IndexedStepRegisters) (n index : Nat)
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
    let next := quotientPushMicrostep (remainderMicrostep (preShiftMicrostep v))
    IndexedPackedState r n
      (run (blockAForward r ++ blockBForward r n (certifiedActiveWindows n index).remainder ++
        blockCForward r ++ blockDForward r (certifiedActiveWindows n index).quotientSwap) s) next ∧
    next.r<v.rPrime*2^(v.shift-1) ∧ next.q<2^next.lQ ∧
    v.r=(if (remainderMicrostep (preShiftMicrostep v)).sign then v.rPrime*2^(v.shift-1) else 0)+next.r := by
  let shifted := preShiftMicrostep v
  let a := run (blockAForward r) s
  have hs : shifted.shift=v.shift-1 := by simp [shifted,preShiftMicrostep,hphase,EEAPhase.bits]
  have ha : IndexedPackedState r n a shifted := (blockAForward_packed r n index s v h hp
    (by simp [hphase,EEAPhase.bits]) hR hRfit hwidth hsfit (fun _ => hshift)
    (by simp [hphase,EEAPhase.bits])).1
  have he : v.rPrime*2^v.shift=2*(v.rPrime*2^(v.shift-1)) := by
    conv_lhs => rw [show v.shift=v.shift-1+1 by omega]
    rw [Nat.pow_succ]
    ring
  have hd := blockBCDForward_quotient_packed r n index a shifted h ha hphase hsign hR hRfit
    (by change v.lT+v.lQ+2+shifted.shift+v.lRPrime≤n+3; rw [hs]; omega)
    (by change v.tPrime<2^(v.lT+v.lQ+1+shifted.shift); rw [hs,show v.lT+v.lQ+1+(v.shift-1)=v.lT+v.lQ+v.shift by omega]; exact htp)
    hrp (by change v.r<2*(v.rPrime*2^shifted.shift); rw [hs,← he]; exact hrem)
    hleftLow hleftHigh (by simpa only [hs] using hrightLow)
    (by simpa only [hs] using hrightHigh) hfit hlo hhi hq
  dsimp only
  rw [List.append_assoc (blockAForward r),List.append_assoc (blockAForward r),Classical.run_append]
  change IndexedPackedState r n (run (blockBForward r n (certifiedActiveWindows n index).remainder ++
    blockCForward r ++ blockDForward r (certifiedActiveWindows n index).quotientSwap) a) _ ∧ _
  simpa only [List.append_assoc,hs] using hd

end ShorECDLP.Paper2607_13816
