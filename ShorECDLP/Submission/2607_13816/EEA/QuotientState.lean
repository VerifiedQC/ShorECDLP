import ShorECDLP.Submission.«2607_13816».EEA.RemainderState
import ShorECDLP.Submission.«2607_13816».EEA.QuotientPacking
namespace ShorECDLP.Paper2607_13816
open Classical

/-- The quotient block appends the comparison bit and clears the sign. -/
def quotientPushMicrostep (v : EEAState) : EEAState :=
  { v with
    q := Nat.bit v.sign v.q
    lQ := v.lQ+1
    sign := false }

private theorem quotient_packed_disjoint (a b c d e : List Wire)
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

/-- Actual quotient insertion preserves the complete packed state. The required
zero high remainder bit follows from its numeric bound. -/
theorem blockDForward_quotient_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase=.quotient)
    (hspan : v.lT+v.lQ+2≤n+3)
    (hfit : v.lT+v.lQ+2<2^r.lengthQ.length)
    (hlo : (certifiedActiveWindows n index).quotientSwap.start≤v.lT+v.lQ+2)
    (hhi : v.lT+v.lQ+2≤(certifiedActiveWindows n index).quotientSwap.stop)
    (hq : v.q<2^v.lQ) (hrem : v.r<2^(n+3-(v.lT+v.lQ+2))) :
    IndexedPackedState r n (run (blockDForward r (certifiedActiveWindows n index).quotientSwap) s)
      (quotientPushMicrostep v) ∧ (quotientPushMicrostep v).q<2^(quotientPushMicrostep v).lQ := by
  let out := run (blockDForward r (certifiedActiveWindows n index).quotientSwap) s
  have hw : r.lengthT.length=r.lengthQ.length := h.quotient.lengthT_eq_lengthQ
  have ht : boolWordToNat (wireValues r.lengthT s)=truthMinusOneValue r.lengthQ.length v.lT := by
    simpa only [hw] using hp.lengthT
  have hwidth : n+3-(v.lT+v.lQ+2)+1=n+3-(v.lT+v.lQ+1) := by omega
  have hd := blockDForward_pushPacking r n index v.lT v.lQ (n+3-(v.lT+v.lQ+2)) v.t v.q v.r
    (certifiedActiveWindows n index).quotientSwap s h h.quotient hp.clean
    (by simp only [certifiedActiveWindows,quotientSwapWindow]; omega)
    (by simpa [hphase] using hp.phase1) (by simpa [hphase] using hp.phase2)
    ht hp.lengthQ hfit hlo hhi hq hrem (by rw [hwidth]; exact hp.work1)
  dsimp only at hd
  have hsep := quotient_packed_disjoint [r.phase1,r.phase2,r.iter] (r.sign::r.work1)
    (r.work2++r.lengthT) r.lengthQ (r.lengthS++r.lengthRPrime++r.aux)
    (by simpa only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append] using h.physical)
  have hstable (wire : Wire) (hw : wire ∈ [r.phase1,r.phase2,r.iter] ++
      (r.work2++r.lengthT) ++ (r.lengthS++r.lengthRPrime++r.aux)) : out wire=s wire :=
    hd.2.2.2.2.1 wire (List.disjoint_left.mp hsep hw)
  have hword (ws : List Wire) (hw : ∀ wire ∈ ws, wire ∈ [r.phase1,r.phase2,r.iter] ++
      (r.work2++r.lengthT) ++ (r.lengthS++r.lengthRPrime++r.aux)) : wireValues ws out=wireValues ws s := by
    apply List.map_congr_left
    intro wire hm
    exact hstable wire (hw wire hm)
  constructor
  · constructor
    · simpa only [quotientPushMicrostep,hp.sign,Nat.add_assoc] using hd.1
    · change wireValues r.work2 out=_
      rw [hword r.work2 (by intro w hw; simp [hw])]
      exact hp.work2
    · change boolWordToNat (wireValues r.lengthT out)=_
      rw [hword r.lengthT (by intro w hw; simp [hw])]
      exact hp.lengthT
    · change boolWordToNat (wireValues r.lengthQ out)=_
      rw [hd.2.2.2.1,boolWordToNat_constantBits]
      apply Nat.mod_eq_of_lt
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · change boolWordToNat (wireValues r.lengthRPrime out)=_
      rw [hword r.lengthRPrime (by intro w hw; simp [hw])]
      exact hp.lengthRP
    · change boolWordToNat (wireValues r.lengthS out)=_
      rw [hword r.lengthS (by intro w hw; simp [hw])]
      exact hp.lengthS
    · exact (hstable _ (by simp)).trans hp.phase1
    · exact (hstable _ (by simp)).trans hp.phase2
    · exact hd.2.2.1
    · exact (hstable _ (by simp)).trans hp.iter
    · exact hd.2.2.2.2.2
  · simpa only [quotientPushMicrostep,hp.sign] using hd.2.1
/-- One quotient digit reduces the remainder below its aligned divisor. -/
theorem remainderMicrostep_quotient_bound (v : EEAState) (hp : v.phase=.quotient)
    (hb : v.r<2*(v.rPrime*2^v.shift)) :
    (remainderMicrostep v).r<v.rPrime*2^v.shift ∧
    v.r=(if (remainderMicrostep v).sign then v.rPrime*2^v.shift else 0)+(remainderMicrostep v).r := by
  by_cases hle : v.rPrime*2^v.shift≤v.r
  · simp [remainderMicrostep,hp,EEAPhase.bits,hle,Nat.not_lt.mpr hle]
    omega
  · simp [remainderMicrostep,hp,EEAPhase.bits,hle,Nat.lt_of_not_ge hle]

/-- Consecutive actual B/C/D blocks compute one division digit. The input division
bound supplies the zero high remainder bit needed for quotient insertion. -/
theorem blockBCDForward_quotient_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase=.quotient) (hsign : v.sign=false)
    (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hspan : v.lT+v.lQ+2+v.shift+v.lRPrime≤n+3)
    (htp : v.tPrime<2^(v.lT+v.lQ+1+v.shift))
    (hrp : v.rPrime<2^v.lRPrime) (hdouble : v.r<2*(v.rPrime*2^v.shift))
    (hleftLow : (certifiedActiveWindows n index).remainder.start≤v.lT+v.lQ+2)
    (hleftHigh : v.lT+v.lQ+2-(certifiedActiveWindows n index).remainder.start<2^r.lengthQ.length)
    (hrightLow : v.shift+(certifiedActiveWindows n index).remainder.start≤n+3)
    (hrightHigh : n+3-v.shift-(certifiedActiveWindows n index).remainder.start<2^r.lengthS.length)
    (hfit : v.lT+v.lQ+2<2^r.lengthQ.length)
    (hlo : (certifiedActiveWindows n index).quotientSwap.start≤v.lT+v.lQ+2)
    (hhi : v.lT+v.lQ+2≤(certifiedActiveWindows n index).quotientSwap.stop)
    (hq : v.q<2^v.lQ) :
    let next := quotientPushMicrostep (remainderMicrostep v)
    IndexedPackedState r n
      (run (blockBForward r n (certifiedActiveWindows n index).remainder ++ blockCForward r ++
        blockDForward r (certifiedActiveWindows n index).quotientSwap) s) next ∧
    next.r<v.rPrime*2^v.shift ∧ next.q<2^next.lQ ∧
    v.r=(if (remainderMicrostep v).sign then v.rPrime*2^v.shift else 0)+next.r := by
  let w := n+3-(v.lT+v.lQ+2)
  have hdiv : v.rPrime*2^v.shift<2^w := by
    have he := Nat.mul_lt_mul_of_pos_right hrp (Nat.two_pow_pos v.shift)
    rw [← Nat.pow_add] at he
    exact he.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp only [w]; omega))
  have hrem : v.r<2^(n+3-(v.lT+v.lQ+1)) := by
    have he : n+3-(v.lT+v.lQ+1)=w+1 := by dsimp only [w]; omega
    rw [he,Nat.pow_succ]
    omega
  let mid := remainderMicrostep v
  let b := run (blockBForward r n (certifiedActiveWindows n index).remainder) s
  have hb : IndexedPackedState r n b mid := blockBForward_packed r n index s v h hp
    (by simp [hphase,EEAPhase.bits]) hsign hR hRfit (by omega) htp hrp hrem
    hleftLow hleftHigh hrightLow hrightHigh
  have hbound := remainderMicrostep_quotient_bound v hphase hdouble
  have hrz : wireAnd r.lengthRPrime b=false := by
    rw [wireAnd_encoded_zero r.lengthRPrime b mid.lRPrime hb.lengthRP hRfit]
    exact decide_eq_false (by change ¬ v.lRPrime=0; omega)
  have hc := blockCForward_nonterminal r n index b h hb.clean hrz
  have hd := blockDForward_quotient_packed r n index b mid h hb hphase (by dsimp only [mid,remainderMicrostep]; omega)
    hfit hlo hhi hq (hbound.1.trans hdiv)
  dsimp only
  rw [Classical.run_append,Classical.run_append]
  change IndexedPackedState r n (run (blockDForward r (certifiedActiveWindows n index).quotientSwap)
    (run (blockCForward r) b)) _ ∧ _
  rw [hc]
  exact ⟨hd.1,hbound.1,hd.2,hbound.2⟩

end ShorECDLP.Paper2607_13816
