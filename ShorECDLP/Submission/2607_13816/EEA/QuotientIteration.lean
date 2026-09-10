import ShorECDLP.Submission.«2607_13816».EEA.QuotientMicrostep
import ShorECDLP.Submission.«2607_13816».EEA.Schedule
namespace ShorECDLP.Paper2607_13816
open Classical
/-- A quotient digit preserves the accumulated division identity at the new alignment. -/
theorem quotientMicrostep_conservation (v : EEAState) (hp : v.phase=.quotient)
    (hs : 0<v.shift) (hr : v.r<v.rPrime*2^v.shift) :
    v.q*(v.rPrime*2^v.shift)+v.r=
      (quotientMicrostep v).q*(v.rPrime*2^(v.shift-1))+(quotientMicrostep v).r ∧
    (quotientMicrostep v).r<v.rPrime*2^(v.shift-1) := by
  let shifted := preShiftMicrostep v
  have hshift : shifted.shift=v.shift-1 := by simp [shifted,preShiftMicrostep,hp,EEAPhase.bits]
  have he : v.rPrime*2^v.shift=2*(v.rPrime*2^(v.shift-1)) := by
    conv_lhs => rw [show v.shift=v.shift-1+1 by omega]
    rw [Nat.pow_succ]
    ring
  have hb := remainderMicrostep_quotient_bound shifted hp (by
    change v.r<2*(v.rPrime*2^shifted.shift)
    rw [hshift,← he]
    exact hr)
  change (remainderMicrostep shifted).r<v.rPrime*2^shifted.shift ∧
    v.r=(if (remainderMicrostep shifted).sign then v.rPrime*2^shifted.shift else 0)+
      (remainderMicrostep shifted).r at hb
  rw [hshift] at hb
  constructor
  · change v.q*(v.rPrime*2^v.shift)+v.r=
      Nat.bit (remainderMicrostep shifted).sign v.q*(v.rPrime*2^(v.shift-1))+
        (remainderMicrostep shifted).r
    rw [he,hb.2]
    cases (remainderMicrostep shifted).sign <;> simp [Nat.bit]
      <;> ring
  · exact hb.1
private theorem quotient_coordinates (v : EEAState) (count : Nat)
    (hp : v.phase=.quotient) (hs : v.sign=false) (hpos : 0<v.shift) (hc : count≤v.shift) :
    let w := quotientMicrostep^[count] v
    w.t=v.t ∧ w.lT=v.lT ∧ w.tPrime=v.tPrime ∧ w.rPrime=v.rPrime ∧
    w.lRPrime=v.lRPrime ∧ w.iter=v.iter ∧ w.lQ=v.lQ+count ∧ w.shift=v.shift-count ∧
    w.sign=false ∧ w.phase=(if count=v.shift then .coefficient else .quotient) := by
  induction count with
  | zero => simpa [if_neg (by omega : 0≠v.shift)] using And.intro hs hp
  | succ k ih =>
    obtain ⟨ht,hT,htp,hrp,hR,hi,hQ,hS,hsg,hph⟩ := ih (by omega)
    rw [if_neg (by omega : k≠v.shift)] at hph
    have hz : v.shift-k-1=0 ↔ k+1=v.shift := by omega
    simp only [Function.iterate_succ_apply',quotientMicrostep,quotientFinishMicrostep,
      quotientPushMicrostep,remainderMicrostep,preShiftMicrostep,hph,EEAPhase.bits,
      ht,hT,htp,hrp,hR,hi,hQ,hS,↓reduceIte,hz]
    simp only [Nat.sub_sub,Nat.add_assoc,and_self]

private theorem quotient_arithmetic (v : EEAState) (count : Nat)
    (hp : v.phase=.quotient) (hs : v.sign=false) (hpos : 0<v.shift) (hc : count≤v.shift)
    (hr : v.r<v.rPrime*2^v.shift) (hq : v.q<2^v.lQ) :
    let w := quotientMicrostep^[count] v
    w.r<v.rPrime*2^(v.shift-count) ∧ w.q<2^(v.lQ+count) ∧
    v.q*(v.rPrime*2^v.shift)+v.r=w.q*(v.rPrime*2^(v.shift-count))+w.r := by
  induction count with
  | zero => simpa using And.intro hr hq
  | succ k ih =>
    obtain ⟨hrk,hqk,heq⟩ := ih (by omega)
    obtain ⟨_,_,_,hrp,_,_,_,hS,_,hph⟩ := quotient_coordinates v k hp hs hpos (by omega)
    rw [if_neg (by omega : k≠v.shift)] at hph
    have ha := quotientMicrostep_conservation (quotientMicrostep^[k] v) hph
      (by rw [hS]; omega) (by rw [hrp,hS]; exact hrk)
    rw [hrp,hS] at ha
    have hexp : v.shift-k-1=v.shift-(k+1) := by omega
    rw [hexp] at ha
    dsimp only at hrk hqk heq ⊢
    rw [Function.iterate_succ_apply']
    refine ⟨ha.2,?_,heq.trans ha.1⟩
    change Nat.bit (remainderMicrostep (preShiftMicrostep (quotientMicrostep^[k] v))).sign
      (quotientMicrostep^[k] v).q<2^(v.lQ+(k+1))
    rw [show v.lQ+(k+1)=(v.lQ+k)+1 by omega,Nat.pow_succ]
    cases (remainderMicrostep (preShiftMicrostep (quotientMicrostep^[k] v))).sign <;>
      simp only [Nat.bit,Bool.cond_false,Bool.cond_true] <;> omega

/-- An actual quotient schedule preserves packing from original arithmetic bounds.
Every intermediate remainder, quotient capacity and phase is derived by induction. -/
theorem indexedScheduleUnitary_quotient_packed (r : IndexedStepRegisters) (n start count : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (hphase : v.phase=.quotient) (hsign : v.sign=false)
    (hpositive : 0<v.shift) (hcount : count≤v.shift)
    (hlayout : ∀ offset<count, IndexedStepLayout r n (start+offset))
    (hwindows : ∀ offset<count,
      (certifiedActiveWindows n (start+offset)).remainder.start≤v.lT+(v.lQ+offset)+2 ∧
      v.lT+(v.lQ+offset)+2-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthQ.length ∧
      v.shift-offset-1+(certifiedActiveWindows n (start+offset)).remainder.start≤n+3 ∧
      n+3-(v.shift-offset-1)-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthS.length ∧
      (certifiedActiveWindows n (start+offset)).quotientSwap.start≤v.lT+(v.lQ+offset)+2 ∧
      v.lT+(v.lQ+offset)+2≤(certifiedActiveWindows n (start+offset)).quotientSwap.stop)
    (hcapacity : v.lT+v.lQ+v.shift+1<2^r.lengthQ.length)
    (hspan : v.lT+v.lQ+1+v.shift+v.lRPrime≤n+3)
    (htp : v.tPrime<2^(v.lT+v.lQ+v.shift))
    (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hSfit : v.shift<2^r.lengthS.length)
    (hrp : v.rPrime<2^v.lRPrime) (hr : v.r<v.rPrime*2^v.shift) (hq : v.q<2^v.lQ) :
    IndexedPackedState r n (run (indexedScheduleUnitary r n start count) s)
      (quotientMicrostep^[count] v) := by
  suffices hall : ∀ k≤count, IndexedPackedState r n
      (run (indexedScheduleUnitary r n start k) s) (quotientMicrostep^[k] v) by
    exact hall count (by omega)
  intro k
  induction k with
  | zero => intro _; exact hp
  | succ k ih =>
    intro hk
    have hpk := ih (by omega)
    obtain ⟨_,hT,htp',hrp',hR',_,hQ,hS,hsg,hph⟩ :=
      quotient_coordinates v k hphase hsign hpositive (by omega)
    rw [if_neg (by omega : k≠v.shift)] at hph
    have ha := quotient_arithmetic v k hphase hsign hpositive (by omega) hr hq
    dsimp only at ha
    obtain ⟨hll,hlh,hrl,hrh,hql,hqh⟩ := hwindows k (by omega)
    have hstep := indexedStepUnitary_quotient_packed r n (start+k)
      (run (indexedScheduleUnitary r n start k) s) (quotientMicrostep^[k] v)
      (hlayout k (by omega)) hpk hph hsg
      (by simpa only [hR'] using hR) (by simpa only [hR'] using hRfit)
      hwidth (by rw [hS]; omega) (by rw [hS]; omega)
      (by rw [hT,hQ,hS,hR']; omega)
      (by rw [htp',hT,hQ,hS,show v.lT+(v.lQ+k)+(v.shift-k)=v.lT+v.lQ+v.shift by omega]; exact htp)
      (by simpa only [hrp',hR'] using hrp) (by simpa only [hrp',hS] using ha.1)
      (by simpa only [hT,hQ] using hll) (by simpa only [hT,hQ] using hlh)
      (by simpa only [hS] using hrl) (by simpa only [hS] using hrh)
      (by rw [hT,hQ]; omega) (by simpa only [hT,hQ] using hql)
      (by simpa only [hT,hQ] using hqh) (by simpa only [hQ] using ha.2.1)
    rw [indexedScheduleUnitary_snoc,Classical.run_append,Function.iterate_succ_apply']
    exact hstep.1

/-- The complete actual quotient phase computes Euclidean division and enters the
coefficient phase with the true quotient bit length. -/
theorem indexedScheduleUnitary_quotient_complete (r : IndexedStepRegisters) (n start : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (hphase : v.phase=.quotient) (hsign : v.sign=false)
    (hpositive : 0<v.shift)
    (hlayout : ∀ offset<v.shift, IndexedStepLayout r n (start+offset))
    (hwindows : ∀ offset<v.shift,
      (certifiedActiveWindows n (start+offset)).remainder.start≤v.lT+(v.lQ+offset)+2 ∧
      v.lT+(v.lQ+offset)+2-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthQ.length ∧
      v.shift-offset-1+(certifiedActiveWindows n (start+offset)).remainder.start≤n+3 ∧
      n+3-(v.shift-offset-1)-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthS.length ∧
      (certifiedActiveWindows n (start+offset)).quotientSwap.start≤v.lT+(v.lQ+offset)+2 ∧
      v.lT+(v.lQ+offset)+2≤(certifiedActiveWindows n (start+offset)).quotientSwap.stop)
    (hcapacity : v.lT+v.lQ+v.shift+1<2^r.lengthQ.length)
    (hspan : v.lT+v.lQ+1+v.shift+v.lRPrime≤n+3)
    (htp : v.tPrime<2^(v.lT+v.lQ+v.shift))
    (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hSfit : v.shift<2^r.lengthS.length)
    (hrp : v.rPrime<2^v.lRPrime) (hr : v.r<v.rPrime*2^v.shift) (hqzero : v.q=0) (hQzero : v.lQ=0)
    (hlower : v.rPrime*2^(v.shift-1)≤v.r) :
    let w := quotientMicrostep^[v.shift] v
    IndexedPackedState r n (run (indexedScheduleUnitary r n start v.shift) s) w ∧
    w.phase=.coefficient ∧ w.shift=0 ∧ w.lQ=v.shift ∧
    w.q=v.r/v.rPrime ∧ w.r=v.r%v.rPrime ∧ w.q.size=v.shift := by
  have hq : v.q<2^v.lQ := by rw [hqzero]; exact Nat.two_pow_pos _
  have hpacked := indexedScheduleUnitary_quotient_packed r n start v.shift s v hp hphase hsign
    hpositive (by omega) hlayout hwindows hcapacity hspan htp hR hRfit hwidth hSfit hrp hr hq
  obtain ⟨_,_,_,_,_,_,hQ,hS,_,hph⟩ := quotient_coordinates v v.shift hphase hsign hpositive (by omega)
  have ha := quotient_arithmetic v v.shift hphase hsign hpositive (by omega) hr hq
  dsimp only at hpacked hQ hS hph ha ⊢
  simp only [Nat.sub_self,Nat.pow_zero,Nat.mul_one,hqzero,Nat.zero_mul,Nat.zero_add,hQzero,
    if_true] at ha hQ hS hph
  let w := quotientMicrostep^[v.shift] v
  have heq : v.r=w.q*v.rPrime+w.r := ha.2.2
  have hrem : w.r<v.rPrime := ha.1
  have hdiv : v.r/v.rPrime=w.q := Nat.div_eq_of_lt_le (by omega) (by nlinarith [heq])
  have hmod : v.r%v.rPrime=w.r := by
    rw [heq]
    simp [Nat.add_mod,Nat.mod_eq_of_lt hrem]
  have hrpos : 0<v.rPrime := by omega
  have hlo : 2^(v.shift-1)≤w.q := by
    rw [← hdiv,Nat.le_div_iff_mul_le hrpos,Nat.mul_comm]
    exact hlower
  have hsize : w.q.size=v.shift := by
    have hl := Nat.lt_size.mpr hlo
    have hu : w.q.size≤v.shift := Nat.size_le.mpr ha.2.1
    omega
  exact ⟨hpacked,hph,hS,hQ,hdiv.symm,hmod.symm,hsize⟩

end ShorECDLP.Paper2607_13816
