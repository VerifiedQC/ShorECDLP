import ShorECDLP.Submission.«2607_13816».EEA.RemainderMicrostep
import ShorECDLP.Submission.«2607_13816».EEA.Schedule
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem remainder_coordinates (v : EEAState) (steps count : Nat)
    (hp : v.phase=.remainder) (hs : v.sign=false) (hpos : 0<steps) (hc : count≤steps)
    (hlo : v.rPrime*2^(v.shift+steps-1)≤v.r) (hhi : v.r<v.rPrime*2^(v.shift+steps)) :
    let w := remainderAlignmentMicrostep^[count] v
    w.t=v.t ∧ w.lT=v.lT ∧ w.tPrime=v.tPrime ∧ w.rPrime=v.rPrime ∧
    w.lRPrime=v.lRPrime ∧ w.iter=v.iter ∧ w.q=v.q ∧ w.r=v.r ∧ w.lQ=v.lQ ∧
    w.shift=v.shift+count ∧ w.sign=false ∧
    w.phase=(if count=steps then .quotient else .remainder) := by
  induction count with
  | zero => simpa [if_neg (by omega : 0≠steps)] using And.intro hs hp
  | succ k ih =>
    obtain ⟨ht,hT,htp,hrp,hR,hi,hq,hr,hQ,hS,hsg,hph⟩ := ih (by omega)
    rw [if_neg (by omega : k≠steps)] at hph
    have he : (v.r<v.rPrime*2^(v.shift+k+1)) ↔ k+1=steps := by
      constructor
      · intro hh
        by_contra hn
        have hm : v.rPrime*2^(v.shift+k+1)≤v.rPrime*2^(v.shift+steps-1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
        omega
      · intro hh
        simpa only [Nat.add_assoc,hh] using hhi
    simp only [Function.iterate_succ_apply',remainderAlignmentMicrostep,remainderFinishMicrostep,
      remainderMicrostep,preShiftMicrostep,hph,EEAPhase.bits,ht,hT,htp,hrp,hR,hi,hq,hr,hQ,hS,
      Bool.false_and,Bool.xor_false,Bool.false_eq_true,if_false,Nat.add_assoc]
    simp [← Nat.add_assoc,he]
/-- The actual alignment schedule derives every intermediate phase and packed state. -/
theorem indexedScheduleUnitary_remainder_packed (r : IndexedStepRegisters) (n start steps count : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (hphase : v.phase=.remainder) (hsign : v.sign=false) (hpositive : 0<steps) (hcount : count≤steps)
    (hlayout : ∀ offset<count, IndexedStepLayout r n (start+offset))
    (hwindows : ∀ offset<count,
      (certifiedActiveWindows n (start+offset)).remainder.start≤v.lT+v.lQ+2 ∧
      v.lT+v.lQ+2-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthQ.length ∧
      v.shift+offset+1+(certifiedActiveWindows n (start+offset)).remainder.start≤n+3 ∧
      n+3-(v.shift+offset+1)-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthS.length)
    (hQ : v.lQ=0) (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hSfit : v.shift+steps<2^r.lengthS.length)
    (hspan : v.lT+v.lQ+1+(v.shift+steps)+v.lRPrime≤n+3)
    (htp : v.tPrime<2^(v.lT+v.lQ+1+(v.shift+1)))
    (hrp : v.rPrime<2^v.lRPrime) (hrem : v.r<2^(n+3-(v.lT+v.lQ+1)))
    (hlower : v.rPrime*2^(v.shift+steps-1)≤v.r)
    (hupper : v.r<v.rPrime*2^(v.shift+steps)) :
    IndexedPackedState r n (run (indexedScheduleUnitary r n start count) s)
      (remainderAlignmentMicrostep^[count] v) := by
  suffices hall : ∀ k≤count, IndexedPackedState r n
      (run (indexedScheduleUnitary r n start k) s) (remainderAlignmentMicrostep^[k] v) by
    exact hall count (by omega)
  intro k
  induction k with
  | zero => intro _; exact hp
  | succ k ih =>
    intro hk
    have hpk := ih (by omega)
    obtain ⟨_,hT,htp',hrp',hR',_,_,hr',hQ',hS,hsg,hph⟩ :=
      remainder_coordinates v steps k hphase hsign hpositive (by omega) hlower hupper
    rw [if_neg (by omega : k≠steps)] at hph
    obtain ⟨hll,hlh,hrl,hrh⟩ := hwindows k (by omega)
    have hstep := indexedStepUnitary_remainder_packed r n (start+k)
      (run (indexedScheduleUnitary r n start k) s) (remainderAlignmentMicrostep^[k] v)
      (hlayout k (by omega)) hpk hph hsg
      (by simpa only [hQ'] using hQ)
      (by simpa only [hR'] using hR) (by simpa only [hR'] using hRfit)
      hwidth (by rw [hS]; omega)
      (by rw [hT,hQ',hS,hR']; omega)
      (by rw [htp',hT,hQ',hS]; exact htp.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      (by simpa only [hrp',hR'] using hrp) (by simpa only [hr',hT,hQ'] using hrem)
      (by simpa only [hT,hQ'] using hll) (by simpa only [hT,hQ'] using hlh)
      (by simpa only [hS] using hrl) (by simpa only [hS] using hrh)
    rw [indexedScheduleUnitary_snoc,Classical.run_append,Function.iterate_succ_apply']
    exact hstep

/-- The quotient bit length gives the first divisor alignment above the remainder. -/
theorem division_alignment_interval (a b : Nat) (hb : 0<b) (hab : b≤a) :
    0<(a/b).size ∧ b*2^((a/b).size-1)≤a ∧ a<b*2^(a/b).size := by
  have hqpos : 0<a/b := Nat.div_pos hab hb
  have hsize : 0<(a/b).size := Nat.size_pos.mpr hqpos
  have hlo : 2^((a/b).size-1)≤a/b := Nat.lt_size.mp (by omega)
  have hhi : a/b+1≤2^(a/b).size := by have hh := Nat.lt_size_self (a/b); omega
  have hmul : b*(a/b)≤a := by have hh := Nat.div_mul_le_self a b; simpa [Nat.mul_comm] using hh
  have hrem := Nat.mod_lt a hb
  have heq := Nat.mod_add_div a b
  refine ⟨hsize,(Nat.mul_le_mul_left b hlo).trans hmul,?_⟩
  have hm := Nat.mul_le_mul_left b hhi
  nlinarith

theorem indexedScheduleUnitary_remainder_complete (r : IndexedStepRegisters) (n start : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (hphase : v.phase=.remainder) (hsign : v.sign=false) (hzero : v.shift=0)
    (hrpos : 0<v.rPrime) (hrlower : v.rPrime≤v.r)
    (hlayout : ∀ offset<(v.r/v.rPrime).size, IndexedStepLayout r n (start+offset))
    (hwindows : ∀ offset<(v.r/v.rPrime).size,
      (certifiedActiveWindows n (start+offset)).remainder.start≤v.lT+v.lQ+2 ∧
      v.lT+v.lQ+2-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthQ.length ∧
      v.shift+offset+1+(certifiedActiveWindows n (start+offset)).remainder.start≤n+3 ∧
      n+3-(v.shift+offset+1)-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthS.length)
    (hQ : v.lQ=0) (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hSfit : v.shift+(v.r/v.rPrime).size<2^r.lengthS.length)
    (hspan : v.lT+v.lQ+1+(v.shift+(v.r/v.rPrime).size)+v.lRPrime≤n+3)
    (htp : v.tPrime<2^(v.lT+v.lQ+1+(v.shift+1)))
    (hrp : v.rPrime<2^v.lRPrime) (hrem : v.r<2^(n+3-(v.lT+v.lQ+1)))
 :
    let steps := (v.r/v.rPrime).size
    let next := remainderAlignmentMicrostep^[steps] v
    IndexedPackedState r n (run (indexedScheduleUnitary r n start steps) s) next ∧
      next.phase=.quotient ∧ next.sign=false ∧ next.shift=steps ∧ next.r=v.r ∧ next.q=v.q ∧
      v.rPrime*2^(next.shift-1)≤next.r ∧ next.r<v.rPrime*2^next.shift := by
  obtain ⟨hpositive,hlo,hhi⟩ := division_alignment_interval v.r v.rPrime hrpos hrlower
  let steps := (v.r/v.rPrime).size
  have hlower : v.rPrime*2^(v.shift+steps-1)≤v.r := by simpa [hzero,steps] using hlo
  have hupper : v.r<v.rPrime*2^(v.shift+steps) := by simpa [hzero,steps] using hhi
  have hpnext := indexedScheduleUnitary_remainder_packed r n start steps steps s v hp hphase
    hsign hpositive (by omega) hlayout hwindows hQ hR hRfit hwidth hSfit hspan htp hrp hrem hlower hupper
  obtain ⟨_,_,_,_,_,_,hq,hr,_,hS,hsg,hph⟩ :=
    remainder_coordinates v steps steps hphase hsign hpositive (by omega) hlower hupper
  dsimp only at hpnext hq hr hS hsg hph ⊢
  simp only [hzero,Nat.zero_add,if_true] at hS hph
  refine ⟨hpnext,hph,hsg,hS,hr,hq,?_,?_⟩
  · rw [hS,hr]; exact hlo
  · rw [hS,hr]; exact hhi

end ShorECDLP.Paper2607_13816
