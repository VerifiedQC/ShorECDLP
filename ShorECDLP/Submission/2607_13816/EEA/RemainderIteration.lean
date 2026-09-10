import ShorECDLP.Submission.«2607_13816».EEA.RemainderMicrostep
import ShorECDLP.Submission.«2607_13816».EEA.Schedule
import ShorECDLP.Submission.«2607_13816».EEA.QuotientIteration
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

/-- Every proper alignment prefix satisfies the adaptive cleanup preconditions. -/
theorem indexedScheduleAdaptive_remainder_input (r : IndexedStepRegisters) (n start steps count : Nat)
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
    IndexedScheduleAdaptiveInput r n start count s := by
  rw [indexedScheduleAdaptiveInput_iff_prefix]
  intro k hk
  have hpk := indexedScheduleUnitary_remainder_packed r n start steps k s v hp
    hphase hsign hpositive (by omega)
    (fun offset ho => hlayout offset (by omega))
    (fun offset ho => hwindows offset (by omega))
    hQ hR hRfit hwidth hSfit hspan htp hrp hrem hlower hupper
  have hsame : (remainderAlignmentMicrostep^[k] v).lRPrime = v.lRPrime := by
    exact (remainder_coordinates v steps k hphase hsign hpositive (by omega) hlower hupper).2.2.2.2.1
  exact hpk.cleanupInput (hlayout k hk) (by rw [hsame]; exact hR)
    (by rw [hsame]; exact hRfit)

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

/-- All four actual phases reach a canonical state with a smaller second remainder. -/
theorem indexedScheduleUnitary_full_iteration_packed (r : IndexedStepRegisters) (n start steps : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (hphase : v.phase=.remainder) (hsign : v.sign=false)
    (hsteps : steps=(v.r/v.rPrime).size) (hzero : v.shift=0)
    (hrpos : 0<v.rPrime) (hrlower : v.rPrime≤v.r)
    (halignLayout : ∀ offset<steps, IndexedStepLayout r n (start+offset))
    (halignWindows : ∀ offset<steps,
      (certifiedActiveWindows n (start+offset)).remainder.start≤v.lT+v.lQ+2 ∧
      v.lT+v.lQ+2-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthQ.length ∧
      offset+1+(certifiedActiveWindows n (start+offset)).remainder.start≤n+3 ∧
      n+3-(offset+1)-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthS.length)
    (hlayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+offset))
    (hwindows : ∀ offset<steps,
      (certifiedActiveWindows n (start+steps+offset)).remainder.start≤v.lT+(v.lQ+offset)+2 ∧
      v.lT+(v.lQ+offset)+2-(certifiedActiveWindows n (start+steps+offset)).remainder.start<2^r.lengthQ.length ∧
      steps-offset-1+(certifiedActiveWindows n (start+steps+offset)).remainder.start≤n+3 ∧
      n+3-(steps-offset-1)-(certifiedActiveWindows n (start+steps+offset)).remainder.start<2^r.lengthS.length ∧
      (certifiedActiveWindows n (start+steps+offset)).quotientSwap.start≤v.lT+(v.lQ+offset)+2 ∧
      v.lT+(v.lQ+offset)+2≤(certifiedActiveWindows n (start+steps+offset)).quotientSwap.stop)
    (hcapacity : v.lT+v.lQ+steps+1<2^r.lengthQ.length)
    (hspan : v.lT+v.lQ+1+steps+v.lRPrime≤n+3)
    (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hSfit : steps<2^r.lengthS.length)
    (hrp : v.rPrime<2^v.lRPrime) (hqzero : v.q=0) (hQzero : v.lQ=0)
    (hcoeffLayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+steps+offset))
    (hcoeffWindows : ∀ offset<steps,
      (certifiedActiveWindows n (start+steps+steps+offset)).quotientSwap.start ≤ v.lT+(steps-offset)+1 ∧
      v.lT+(steps-offset)+1 ≤ (certifiedActiveWindows n (start+steps+steps+offset)).quotientSwap.stop ∧
      v.lT+1 ∈ quotientSwapLabels 1 (certifiedActiveWindows n (start+steps+steps+offset)).coefficient.stop)
    (htmeta : v.lT+1<2^r.lengthT.length)
    (hupperT : n+3-v.lRPrime<2^r.lengthT.length)
    (ht : v.t<2^v.lT) (htpSmall : v.tPrime<v.t)
    (hcapacityT : n+3<2^r.lengthT.length)
    (hT : v.lT=v.t.size) (hRP : v.lRPrime=v.rPrime.size)
    (hswapLayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+steps+steps+offset))
    (hswapWindows : ∀ offset<steps, n+3-v.lRPrime-(steps-offset) ∈
      quotientSwapLabels 1 (certifiedActiveWindows n (start+steps+steps+steps+offset)).coefficient.stop)
    (hstep : (start+steps+steps+steps+(steps-1))%4=0)
    (hboundary4 : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k4 ≤ n+3-v.lRPrime ∧
      n+3-v.lRPrime ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K4)
    (hboundary5 : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k5 ≤ ((v.tPrime+v.t*(v.r/v.rPrime))).size+2 ∧
      ((v.tPrime+v.t*(v.r/v.rPrime))).size+2 ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K5Decode n)
    (htWindow : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k4 ≤ v.t.size ∧
      v.t.size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K4)
    (htpWindow : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k4 ≤ ((v.tPrime+v.t*(v.r/v.rPrime))).size ∧
      ((v.tPrime+v.t*(v.r/v.rPrime))).size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K4)
    (hrWindow : v.r%v.rPrime ≠ 0 → (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k5 ≤ n+4-(v.r%v.rPrime).size ∧
      n+4-(v.r%v.rPrime).size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K5Decode n)
    (hrpWindow : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k5 ≤ n+4-v.rPrime.size ∧
      n+4-v.rPrime.size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K5Decode n) :
    let aligned := remainderAlignmentMicrostep^[steps] v
    let divided := quotientMicrostep^[steps] aligned
    let accumulated := coefficientMicrostep^[steps] divided
    let next := endpointMicrostep (swapBeforeEndpointMicrostep^[steps] accumulated)
    IndexedPackedState r n (run (indexedScheduleUnitary r n start (steps+(steps+(steps+steps)))) s) next ∧
      next.Canonical ∧ next.rPrime<v.rPrime := by
  obtain ⟨hpositive,hlower,hupper⟩ := division_alignment_interval v.r v.rPrime hrpos hrlower
  rw [← hsteps] at hpositive hlower hupper
  have hrem : v.r<2^(n+3-(v.lT+v.lQ+1)) := by
    have hb : v.rPrime*2^steps≤2^(v.lRPrime+steps) := by
      rw [Nat.pow_add]
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt hrp)
    exact (hupper.trans_le hb).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have htpAlign : v.tPrime<2^(v.lT+v.lQ+1+(v.shift+1)) :=
    htpSmall.trans (ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  have hpacked := indexedScheduleUnitary_remainder_packed r n start steps steps s v hp
    hphase hsign hpositive (by omega) halignLayout
    (by simpa only [hzero,Nat.zero_add] using halignWindows) hQzero hR hRfit hwidth
    (by simpa only [hzero,Nat.zero_add] using hSfit)
    (by simpa only [hzero,Nat.zero_add] using hspan) htpAlign hrp hrem
    (by simpa only [hzero,Nat.zero_add] using hlower)
    (by simpa only [hzero,Nat.zero_add] using hupper)
  obtain ⟨htt,hTT,htpW,hrpW,hRR,hi,hqW,hrW,hQW,hSW,hsgW,hphW⟩ :=
    remainder_coordinates v steps steps hphase hsign hpositive (by omega)
      (by simpa only [hzero,Nat.zero_add] using hlower)
      (by simpa only [hzero,Nat.zero_add] using hupper)
  simp only [hzero,Nat.zero_add,if_true] at hSW hphW
  let aligned := remainderAlignmentMicrostep^[steps] v
  let mid := run (indexedScheduleUnitary r n start steps) s
  have hc := indexedScheduleUnitary_quotient_coefficient_swap_packed r n (start+steps) mid aligned
    hpacked hphW hsgW
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hpositive)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hlayout)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hwindows)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcapacity)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hspan)
    (by change (remainderAlignmentMicrostep^[steps] v).tPrime<_; rw [htpW,hTT,hQW,hSW]
        exact htpSmall.trans (ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega))))
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hR)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hRfit)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hwidth)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hSfit)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hrp)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hupper)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hqzero)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hQzero)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hlower)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcoeffLayout)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcoeffWindows)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htmeta)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hupperT)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using ht)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htpSmall)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcapacityT)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hT)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hRP)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hswapLayout)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hswapWindows)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hstep)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hboundary4)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hboundary5)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htWindow)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htpWindow)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hrWindow)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hrpWindow)
  dsimp only at hc ⊢
  rw [indexedScheduleUnitary_append,Classical.run_append]
  simpa only [aligned,mid,hSW,hrpW] using hc

private theorem quotient_payload (v : EEAState) (count : Nat) :
    let w := quotientMicrostep^[count] v
    w.t=v.t ∧ w.tPrime=v.tPrime ∧ w.rPrime=v.rPrime ∧ w.iter=v.iter := by
  induction count with
  | zero => simp
  | succ k ih =>
    simpa only [Function.iterate_succ_apply',quotientMicrostep,quotientFinishMicrostep,
      quotientPushMicrostep,remainderMicrostep,preShiftMicrostep] using ih
private theorem coefficient_payload (v : EEAState) (count : Nat) :
    let w := coefficientMicrostep^[count] v
    w.t=v.t ∧ w.r=v.r ∧ w.rPrime=v.rPrime ∧ w.iter=v.iter := by
  induction count with
  | zero => simp
  | succ k ih => simpa only [Function.iterate_succ_apply',coefficientMicrostep] using ih
private theorem swap_payload (v : EEAState) (count : Nat) :
    let w := swapBeforeEndpointMicrostep^[count] v
    w.t=v.t ∧ w.tPrime=v.tPrime ∧ w.r=v.r ∧ w.rPrime=v.rPrime ∧ w.iter=v.iter := by
  induction count with
  | zero => simp
  | succ k ih => simpa only [Function.iterate_succ_apply',swapBeforeEndpointMicrostep] using ih

/-- The actual four-phase circuit refines the mathematical Euclidean step. -/
theorem indexedScheduleUnitary_paperStep_packed (r : IndexedStepRegisters) (n start steps : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (hphase : v.phase=.remainder) (hsign : v.sign=false)
    (hsteps : steps=(v.r/v.rPrime).size) (hzero : v.shift=0)
    (hrpos : 0<v.rPrime) (hrlower : v.rPrime≤v.r)
    (halignLayout : ∀ offset<steps, IndexedStepLayout r n (start+offset))
    (halignWindows : ∀ offset<steps,
      (certifiedActiveWindows n (start+offset)).remainder.start≤v.lT+v.lQ+2 ∧
      v.lT+v.lQ+2-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthQ.length ∧
      offset+1+(certifiedActiveWindows n (start+offset)).remainder.start≤n+3 ∧
      n+3-(offset+1)-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthS.length)
    (hlayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+offset))
    (hwindows : ∀ offset<steps,
      (certifiedActiveWindows n (start+steps+offset)).remainder.start≤v.lT+(v.lQ+offset)+2 ∧
      v.lT+(v.lQ+offset)+2-(certifiedActiveWindows n (start+steps+offset)).remainder.start<2^r.lengthQ.length ∧
      steps-offset-1+(certifiedActiveWindows n (start+steps+offset)).remainder.start≤n+3 ∧
      n+3-(steps-offset-1)-(certifiedActiveWindows n (start+steps+offset)).remainder.start<2^r.lengthS.length ∧
      (certifiedActiveWindows n (start+steps+offset)).quotientSwap.start≤v.lT+(v.lQ+offset)+2 ∧
      v.lT+(v.lQ+offset)+2≤(certifiedActiveWindows n (start+steps+offset)).quotientSwap.stop)
    (hcapacity : v.lT+v.lQ+steps+1<2^r.lengthQ.length)
    (hspan : v.lT+v.lQ+1+steps+v.lRPrime≤n+3)
    (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hwidth : 0<r.lengthS.length) (hSfit : steps<2^r.lengthS.length)
    (hrp : v.rPrime<2^v.lRPrime) (hqzero : v.q=0) (hQzero : v.lQ=0)
    (hcoeffLayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+steps+offset))
    (hcoeffWindows : ∀ offset<steps,
      (certifiedActiveWindows n (start+steps+steps+offset)).quotientSwap.start ≤ v.lT+(steps-offset)+1 ∧
      v.lT+(steps-offset)+1 ≤ (certifiedActiveWindows n (start+steps+steps+offset)).quotientSwap.stop ∧
      v.lT+1 ∈ quotientSwapLabels 1 (certifiedActiveWindows n (start+steps+steps+offset)).coefficient.stop)
    (htmeta : v.lT+1<2^r.lengthT.length)
    (hupperT : n+3-v.lRPrime<2^r.lengthT.length)
    (ht : v.t<2^v.lT) (htpSmall : v.tPrime<v.t)
    (hcapacityT : n+3<2^r.lengthT.length)
    (hT : v.lT=v.t.size) (hRP : v.lRPrime=v.rPrime.size)
    (hswapLayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+steps+steps+offset))
    (hswapWindows : ∀ offset<steps, n+3-v.lRPrime-(steps-offset) ∈
      quotientSwapLabels 1 (certifiedActiveWindows n (start+steps+steps+steps+offset)).coefficient.stop)
    (hstep : (start+steps+steps+steps+(steps-1))%4=0)
    (hboundary4 : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k4 ≤ n+3-v.lRPrime ∧
      n+3-v.lRPrime ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K4)
    (hboundary5 : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k5 ≤ ((v.tPrime+v.t*(v.r/v.rPrime))).size+2 ∧
      ((v.tPrime+v.t*(v.r/v.rPrime))).size+2 ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K5Decode n)
    (htWindow : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k4 ≤ v.t.size ∧
      v.t.size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K4)
    (htpWindow : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k4 ≤ ((v.tPrime+v.t*(v.r/v.rPrime))).size ∧
      ((v.tPrime+v.t*(v.r/v.rPrime))).size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K4)
    (hrWindow : v.r%v.rPrime ≠ 0 → (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k5 ≤ n+4-(v.r%v.rPrime).size ∧
      n+4-(v.r%v.rPrime).size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K5Decode n)
    (hrpWindow : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k5 ≤ n+4-v.rPrime.size ∧
      n+4-v.rPrime.size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K5Decode n) :
    IndexedPackedState r n
      (run (indexedScheduleUnitary r n start (steps+(steps+(steps+steps)))) s) (paperStep v) := by
  obtain ⟨hpositive,hlower,hupper⟩ := division_alignment_interval v.r v.rPrime hrpos hrlower
  rw [← hsteps] at hpositive hlower hupper
  have hrem : v.r<2^(n+3-(v.lT+v.lQ+1)) := by
    have hb : v.rPrime*2^steps≤2^(v.lRPrime+steps) := by
      rw [Nat.pow_add]
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt hrp)
    exact (hupper.trans_le hb).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have htpAlign : v.tPrime<2^(v.lT+v.lQ+1+(v.shift+1)) :=
    htpSmall.trans (ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  have hpacked := indexedScheduleUnitary_remainder_packed r n start steps steps s v hp
    hphase hsign hpositive (by omega) halignLayout
    (by simpa only [hzero,Nat.zero_add] using halignWindows) hQzero hR hRfit hwidth
    (by simpa only [hzero,Nat.zero_add] using hSfit)
    (by simpa only [hzero,Nat.zero_add] using hspan) htpAlign hrp hrem
    (by simpa only [hzero,Nat.zero_add] using hlower)
    (by simpa only [hzero,Nat.zero_add] using hupper)
  obtain ⟨htt,hTT,htpW,hrpW,hRR,hi,hqW,hrW,hQW,hSW,hsgW,hphW⟩ :=
    remainder_coordinates v steps steps hphase hsign hpositive (by omega)
      (by simpa only [hzero,Nat.zero_add] using hlower)
      (by simpa only [hzero,Nat.zero_add] using hupper)
  simp only [hzero,Nat.zero_add,if_true] at hSW hphW
  let aligned := remainderAlignmentMicrostep^[steps] v
  let mid := run (indexedScheduleUnitary r n start steps) s
  have hc := indexedScheduleUnitary_quotient_coefficient_swap_packed r n (start+steps) mid aligned
    hpacked hphW hsgW
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hpositive)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hlayout)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hwindows)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcapacity)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hspan)
    (by change (remainderAlignmentMicrostep^[steps] v).tPrime<_; rw [htpW,hTT,hQW,hSW]
        exact htpSmall.trans (ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega))))
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hR)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hRfit)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hwidth)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hSfit)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hrp)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hupper)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hqzero)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hQzero)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hlower)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcoeffLayout)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcoeffWindows)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htmeta)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hupperT)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using ht)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htpSmall)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcapacityT)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hT)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hRP)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hswapLayout)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hswapWindows)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hstep)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hboundary4)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hboundary5)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htWindow)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htpWindow)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hrWindow)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hrpWindow)
  have hd := indexedScheduleUnitary_quotient_complete r n (start+steps) mid aligned
    hpacked hphW hsgW
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hpositive)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hlayout)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hwindows)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcapacity)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hspan)
    (by change (remainderAlignmentMicrostep^[steps] v).tPrime<_; rw [htpW,hTT,hQW,hSW]
        exact htpSmall.trans (ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega))))
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hR)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hRfit)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hwidth)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hSfit)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hrp)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hupper)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hqzero)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hQzero)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hlower)
  have hcoef := indexedScheduleUnitary_quotient_coefficient_packed r n (start+steps) mid aligned
    hpacked hphW hsgW
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hpositive)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hlayout)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hwindows)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcapacity)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hspan)
    (by change (remainderAlignmentMicrostep^[steps] v).tPrime<_; rw [htpW,hTT,hQW,hSW]
        exact htpSmall.trans (ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega))))
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hR)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hRfit)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hwidth)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hSfit)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hrp)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hupper)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hqzero)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hQzero)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hlower)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcoeffLayout)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hcoeffWindows)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htmeta)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using hupperT)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using ht)
    (by simpa only [aligned,htt,hTT,htpW,hrpW,hRR,hqW,hrW,hQW,hSW] using htpSmall)
  let divided := quotientMicrostep^[steps] aligned
  let acc := coefficientMicrostep^[steps] divided
  let swapped := swapBeforeEndpointMicrostep^[steps] acc
  let next := endpointMicrostep swapped
  have hcanon : next.Canonical := by
    simpa only [next,swapped,acc,divided,aligned,hSW] using hc.2.1
  have htpAcc : acc.tPrime=v.tPrime+v.t*(v.r/v.rPrime) := by
    simpa only [acc,divided,aligned,hSW,htt,htpW,hrW,hrpW] using hcoef.2.2.2.2.2.2.1
  have hrDiv : divided.r=v.r%v.rPrime := by
    simpa only [divided,aligned,hSW,hrW,hrpW] using hd.2.2.2.2.2.1
  obtain ⟨hqt,_,hqrp,hqi⟩ := quotient_payload aligned steps
  obtain ⟨hct,hcr,hcrp,hci⟩ := coefficient_payload divided steps
  obtain ⟨hst,hstp,hsr,hsrp,hsi⟩ := swap_payload acc steps
  have htNext : next.t=v.tPrime+v.t*(v.r/v.rPrime) := hstp.trans htpAcc
  have htpNext : next.tPrime=v.t := hst.trans (hct.trans (hqt.trans htt))
  have hrNext : next.r=v.rPrime := hsrp.trans (hcrp.trans (hqrp.trans hrpW))
  have hrpNext : next.rPrime=v.r%v.rPrime := hsr.trans (hcr.trans hrDiv)
  have hiNext : next.iter = !v.iter := by
    change (!(swapBeforeEndpointMicrostep^[steps] acc).iter) = (!v.iter)
    rw [hsi,hci,hqi,hi]
  have heq : next=paperStep v := by
    obtain ⟨hq,hQ,hS,hph,hsg,hT,hR⟩ := hcanon
    rw [paperStep_nonterminal (by omega : v.rPrime≠0)]
    change next = {
      t := v.tPrime+(v.r/v.rPrime)*v.t, q := 0, r := v.rPrime,
      tPrime := v.t, rPrime := v.r%v.rPrime, lT := (v.tPrime+(v.r/v.rPrime)*v.t).size,
      lQ := 0, lRPrime := (v.r%v.rPrime).size, shift := 0, phase := .remainder, sign := false, iter := !v.iter }
    cases hrecord : next
    simp only [EEAState.mk.injEq]
    rw [hrecord] at htNext htpNext hrNext hrpNext hiNext hq hQ hS hph hsg hT hR
    exact ⟨by simpa only [Nat.mul_comm] using htNext,hq,hrNext,htpNext,hrpNext,
      by simpa only [Nat.mul_comm] using hT.trans (congrArg Nat.size htNext),hQ,hR.trans (congrArg Nat.size hrpNext),
      hS,hph,hsg,hiNext⟩
  have hpnext : IndexedPackedState r n
      (run (indexedScheduleUnitary r n start (steps+(steps+(steps+steps)))) s) next := by
    rw [indexedScheduleUnitary_append,Classical.run_append]
    simpa only [next,swapped,acc,divided,aligned,mid,hSW] using hc.1
  rw [heq] at hpnext
  exact hpnext

private def iterationFrame {p x spent : Nat} {v : EEAState}
    (hreach : PaperBoundaryReachable p x spent v) (hactive : v.rPrime≠0)
    (within : Nat) (hpos : 1≤within) (hle : within≤4*(paperQuotient v).size) :
    PaperActiveFrame p x (4*spent+within) where
  spent := spent
  boundary := v
  reachable := hreach
  nonterminal := hactive
  within := within
  within_pos := hpos
  within_le := hle
  time_eq := rfl

private theorem alignment_windows {p x spent n : Nat} {v : EEAState}
    (hreach : PaperBoundaryReachable p x spent v) (hp : p.Prime)
    (hx : 1≤x) (hxp : x<p) (hbits : p<2^n) (hactive : v.rPrime≠0)
    (offset : Nat) (ho : offset<(paperQuotient v).size) :
    (certifiedActiveWindows n (4*spent+1+offset)).remainder.start≤v.lT+v.lQ+2 ∧
    offset+1+(certifiedActiveWindows n (4*spent+1+offset)).remainder.start≤n+3 := by
  let frame := iterationFrame hreach hactive (offset+1) (by omega) (by omega)
  have hw := frame.certifiedRemainderWindow_covers hp hx hxp hbits (by
    change offset+1≤2*(paperQuotient v).size
    omega)
  have hi := hreach.invariant hp hx hxp
  have htime : 4*spent+(offset+1)=4*spent+1+offset := by omega
  simp only [ActiveWindow.Covers, PaperActiveFrame.remainderLeft,
    PaperActiveFrame.remainderRight, frame, iterationFrame,
    remainderQuotientLength, remainderShiftLength, if_pos (by omega : offset+1≤(paperQuotient v).size),
    Nat.add_zero, htime] at hw
  have hspan := hreach.alignment_span hp hx hxp hbits hactive
  obtain ⟨_,hQ,_,_,_,hT,_⟩ := hi.canonical
  simp only [certifiedActiveWindows]
  rw [hQ,hT]
  constructor
  · simpa only [Nat.add_zero] using hw.1
  · omega

private theorem division_windows {p x spent n : Nat} {v : EEAState}
    (hreach : PaperBoundaryReachable p x spent v) (hp : p.Prime)
    (hx : 1≤x) (hxp : x<p) (hbits : p<2^n) (hactive : v.rPrime≠0)
    (offset : Nat) (ho : offset<(paperQuotient v).size) :
    let steps := (paperQuotient v).size
    let w := certifiedActiveWindows n (4*spent+1+steps+offset)
    w.remainder.start≤v.lT+(v.lQ+offset)+2 ∧
    steps-offset-1+w.remainder.start≤n+3 ∧
    w.quotientSwap.start≤v.lT+(v.lQ+offset)+2 ∧
    v.lT+(v.lQ+offset)+2≤w.quotientSwap.stop := by
  let steps := (paperQuotient v).size
  let frame := iterationFrame hreach hactive (steps+offset+1) (by omega) (by dsimp [steps]; omega)
  have hw := frame.certifiedRemainderWindow_covers hp hx hxp hbits (by
    change steps+offset+1≤2*steps
    dsimp [steps]; omega)
  have hswap := frame.quotientSwapWindow_contains hp hx hxp hbits
    (by change steps<steps+offset+1; omega)
    (by change steps+offset+1≤3*steps; dsimp [steps]; omega)
  have hi := hreach.invariant hp hx hxp
  have htime : 4*spent+(steps+offset+1)=4*spent+1+steps+offset := by omega
  have hnot : ¬steps+offset+1≤steps := by omega
  have hle : steps+offset+1≤2*steps := by dsimp [steps]; omega
  dsimp only [steps] at htime hnot hle
  simp only [ActiveWindow.Covers, PaperActiveFrame.remainderLeft,
    PaperActiveFrame.remainderRight, frame, iterationFrame, steps,
    remainderQuotientLength, remainderShiftLength,
    if_neg hnot, htime] at hw
  simp only [ActiveWindow.Contains, PaperActiveFrame.swapLocation, frame, iterationFrame,
    swapQuotientLength, steps,
    if_pos hle, htime] at hswap
  have hspan := hreach.alignment_span hp hx hxp hbits hactive
  obtain ⟨_,hQ,_,_,_,hT,_⟩ := hi.canonical
  dsimp only
  simp only [certifiedActiveWindows,hQ,hT,Nat.zero_add]
  change _ ∧ _ ∧ _ ∧ _
  omega
private theorem coefficient_windows {p x spent n : Nat} {v : EEAState}
    (hreach : PaperBoundaryReachable p x spent v) (hp : p.Prime)
    (hx : 1≤x) (hxp : x<p) (hlower : 2^(n-1)<p) (hbits : p<2^n) (hactive : v.rPrime≠0)
    (offset : Nat) (ho : offset<(paperQuotient v).size) :
    let steps := (paperQuotient v).size
    let w := certifiedActiveWindows n (4*spent+1+steps+steps+offset)
    w.quotientSwap.start≤v.lT+(steps-offset)+1 ∧
    v.lT+(steps-offset)+1≤w.quotientSwap.stop ∧
    v.lT+1 ∈ quotientSwapLabels 1 w.coefficient.stop := by
  let steps := (paperQuotient v).size
  let frame := iterationFrame hreach hactive (2*steps+offset+1) (by omega) (by dsimp [steps]; omega)
  have hc := frame.coefficientWindow_covers hp hx hxp hlower hbits
  have hswap := frame.quotientSwapWindow_contains hp hx hxp hbits
    (by change steps<2*steps+offset+1; omega)
    (by change 2*steps+offset+1≤3*steps; dsimp [steps]; omega)
  have htime : 4*spent+(2*steps+offset+1)=4*spent+1+steps+steps+offset := by omega
  have hnot : ¬2*steps+offset+1≤2*steps := by omega
  have hle : 2*steps+offset+1≤3*steps := by dsimp [steps]; omega
  dsimp only [steps] at htime hnot hle
  simp only [ActiveWindow.Covers,PaperActiveFrame.coefficientRight,frame,iterationFrame,
    steps,if_pos hle,htime] at hc
  simp only [ActiveWindow.Contains,PaperActiveFrame.swapLocation,frame,iterationFrame,
    swapQuotientLength,steps,if_neg hnot,htime] at hswap
  have heq : 3*(paperQuotient v).size-(2*(paperQuotient v).size+offset+1)+1=(paperQuotient v).size-offset := by omega
  rw [heq] at hswap
  have hT := (hreach.invariant hp hx hxp).canonical.2.2.2.2.2.1
  dsimp only
  simp [certifiedActiveWindows,hT,quotientSwapLabels]
  omega

private theorem swap_windows {p x spent n : Nat} {v : EEAState}
    (hreach : PaperBoundaryReachable p x spent v) (hp : p.Prime)
    (hx : 1≤x) (hxp : x<p) (hlower : 2^(n-1)<p) (hbits : p<2^n) (hactive : v.rPrime≠0)
    (offset : Nat) (ho : offset<(paperQuotient v).size) :
    let steps := (paperQuotient v).size
    n+3-v.lRPrime-(steps-offset) ∈ quotientSwapLabels 1
      (certifiedActiveWindows n (4*spent+1+steps+steps+steps+offset)).coefficient.stop := by
  let steps := (paperQuotient v).size
  let frame := iterationFrame hreach hactive (3*steps+offset+1) (by omega) (by dsimp [steps]; omega)
  have hc := frame.coefficientWindow_covers hp hx hxp hlower hbits
  have htime : 4*spent+(3*steps+offset+1)=4*spent+1+steps+steps+steps+offset := by omega
  have hnot : ¬3*steps+offset+1≤3*steps := by omega
  dsimp only [steps] at htime hnot
  simp only [ActiveWindow.Covers,PaperActiveFrame.coefficientRight,frame,iterationFrame,
    steps,if_neg hnot,htime] at hc
  have heq : 4*(paperQuotient v).size-(3*(paperQuotient v).size+offset+1)+1=(paperQuotient v).size-offset := by omega
  rw [heq] at hc
  have hR := (hreach.invariant hp hx hxp).canonical.2.2.2.2.2.2
  dsimp only
  simp [certifiedActiveWindows,hR,quotientSwapLabels]
  omega


/-- Reachability supplies all logical arithmetic and packing-capacity premises of an iteration. -/
theorem indexedScheduleUnitary_reachable_paperStep (r : IndexedStepRegisters) (n start steps : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (p x spent : Nat) (hreach : PaperBoundaryReachable p x spent v)
    (hprime : p.Prime) (hx : 1≤x) (hxp : x<p) (hlower : 2^(n-1)<p) (hbits : p<2^n)
    (hactive : v.rPrime≠0) (hstart : start=4*spent+1)
    (hcapacityQ : n+3<2^r.lengthQ.length)
    (hcapacityS : n+3<2^r.lengthS.length)
    (hcapacityR : n+3<2^r.lengthRPrime.length)
    (hsteps : steps=(v.r/v.rPrime).size)
    (halignLayout : ∀ offset<steps, IndexedStepLayout r n (start+offset))
    (hlayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+offset))
    (hcoeffLayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+steps+offset))
    (hcapacityT : n+3<2^r.lengthT.length)
    (hswapLayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+steps+steps+offset))
    (hboundary4 : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k4 ≤ n+3-v.lRPrime ∧
      n+3-v.lRPrime ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K4)
    (hboundary5 : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k5 ≤ ((v.tPrime+v.t*(v.r/v.rPrime))).size+2 ∧
      ((v.tPrime+v.t*(v.r/v.rPrime))).size+2 ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K5Decode n)
    (htWindow : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k4 ≤ v.t.size ∧
      v.t.size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K4)
    (htpWindow : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k4 ≤ ((v.tPrime+v.t*(v.r/v.rPrime))).size ∧
      ((v.tPrime+v.t*(v.r/v.rPrime))).size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K4)
    (hrWindow : v.r%v.rPrime ≠ 0 → (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k5 ≤ n+4-(v.r%v.rPrime).size ∧
      n+4-(v.r%v.rPrime).size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K5Decode n)
    (hrpWindow : (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).k5 ≤ n+4-v.rPrime.size ∧
      n+4-v.rPrime.size ≤ (endIterationWindowsAt n (start+steps+steps+steps+(steps-1))).K5Decode n) :
    IndexedPackedState r n
      (run (indexedScheduleUnitary r n start (steps+(steps+(steps+steps)))) s) (paperStep v) := by
  have hi := hreach.invariant hprime hx hxp
  obtain ⟨hqzero,hQzero,hzero,hphase,hsign,hT,hRP⟩ := hi.canonical
  have hrpos : 0<v.rPrime := Nat.pos_of_ne_zero hactive
  have hrlower := hi.remainder_decreases.le
  have hspan := hreach.alignment_span hprime hx hxp hbits hactive
  change v.lT+v.lQ+1+(v.r/v.rPrime).size+v.lRPrime≤n+3 at hspan
  rw [← hsteps] at hspan
  have hR : 0<v.lRPrime := by rw [hRP]; exact Nat.size_pos.mpr hrpos
  have hrp : v.rPrime<2^v.lRPrime := by rw [hRP]; exact Nat.lt_size_self _
  have ht : v.t<2^v.lT := by rw [hT]; exact Nat.lt_size_self _
  have hwidth : 0<r.lengthS.length := by
    by_contra hh
    have hz : r.lengthS.length=0 := by omega
    simp only [hz,pow_zero] at hcapacityS
    omega
  have hpositive : 0<steps := by
    rw [hsteps]
    exact Nat.size_pos.mpr (Nat.div_pos hrlower hrpos)
  have hstep : (start+steps+steps+steps+(steps-1))%4=0 := by
    rw [hstart]
    omega
  have hstepsQ : steps=(paperQuotient v).size := hsteps
  have halignWindows := fun offset (ho : offset<steps) => by
    have hw := alignment_windows hreach hprime hx hxp hbits hactive offset (by omega)
    rw [← hstart] at hw
    exact And.intro hw.1 (And.intro
      (show v.lT+v.lQ+2-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthQ.length by omega)
      (And.intro hw.2
      (show n+3-(offset+1)-(certifiedActiveWindows n (start+offset)).remainder.start<2^r.lengthS.length by omega)))
  have hwindows := fun offset (ho : offset<steps) => by
    have hw := division_windows hreach hprime hx hxp hbits hactive offset (by omega)
    dsimp only at hw
    rw [← hstart,← hstepsQ] at hw
    exact And.intro hw.1 (And.intro
      (show v.lT+(v.lQ+offset)+2-(certifiedActiveWindows n (start+steps+offset)).remainder.start<2^r.lengthQ.length by omega)
      (And.intro hw.2.1 (And.intro
      (show n+3-(steps-offset-1)-(certifiedActiveWindows n (start+steps+offset)).remainder.start<2^r.lengthS.length by omega)
      hw.2.2)))
  have hcoeffWindows := fun offset (ho : offset<steps) => by
    have hw := coefficient_windows hreach hprime hx hxp hlower hbits hactive offset (by omega)
    dsimp only at hw
    rw [← hstart,← hstepsQ] at hw
    exact hw
  have hswapWindows := fun offset (ho : offset<steps) => by
    have hw := swap_windows hreach hprime hx hxp hlower hbits hactive offset (by omega)
    dsimp only at hw
    rw [← hstart,← hstepsQ] at hw
    exact hw
  exact indexedScheduleUnitary_paperStep_packed r n start steps s v hp hphase hsign
    hsteps hzero hrpos hrlower halignLayout halignWindows hlayout hwindows
    (by omega) hspan hR (by omega) hwidth (by omega) hrp hqzero hQzero
    hcoeffLayout hcoeffWindows (by omega) (by omega) ht hi.coefficient_increases
    hcapacityT hT hRP hswapLayout hswapWindows hstep hboundary4 hboundary5
    htWindow htpWindow hrWindow hrpWindow

/-- All active iteration arithmetic and scan windows follow from reachability. -/
theorem indexedScheduleUnitary_active_paperStep (r : IndexedStepRegisters) (n start steps : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (p x spent : Nat) (hreach : PaperBoundaryReachable p x spent v)
    (hprime : p.Prime) (hx : 1≤x) (hxp : x<p) (hlower : 2^(n-1)<p) (hbits : p<2^n)
    (hactive : v.rPrime≠0) (hstart : start=4*spent+1)
    (hcapacityQ : n+3<2^r.lengthQ.length)
    (hcapacityS : n+3<2^r.lengthS.length)
    (hcapacityR : n+3<2^r.lengthRPrime.length)
    (hsteps : steps=(v.r/v.rPrime).size)
    (halignLayout : ∀ offset<steps, IndexedStepLayout r n (start+offset))
    (hlayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+offset))
    (hcoeffLayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+steps+offset))
    (hcapacityT : n+3<2^r.lengthT.length)
    (hswapLayout : ∀ offset<steps, IndexedStepLayout r n (start+steps+steps+steps+offset)) :
    IndexedPackedState r n
      (run (indexedScheduleUnitary r n start (steps+(steps+(steps+steps)))) s) (paperStep v) := by
  have hi := hreach.invariant hprime hx hxp
  obtain ⟨_,hQ,_,_,_,hT,hR⟩ := hi.canonical
  have hrpos : 0<v.rPrime := Nat.pos_of_ne_zero hactive
  have hqpos : 0<v.r/v.rPrime := Nat.div_pos hi.remainder_decreases.le hrpos
  have hspos : 0<steps := by rw [hsteps]; exact Nat.size_pos.mpr hqpos
  have hspan := hreach.alignment_span hprime hx hxp hbits hactive
  change v.lT+v.lQ+1+(v.r/v.rPrime).size+v.lRPrime≤n+3 at hspan
  rw [←hsteps] at hspan
  let nextT := v.tPrime+v.t*(v.r/v.rPrime)
  have htBound : nextT<2^(v.lT+steps) := by
    have ht : v.t<2^v.lT := by rw [hT]; exact Nat.lt_size_self _
    have hq : v.r/v.rPrime<2^steps := by rw [hsteps]; exact Nat.lt_size_self _
    calc
      nextT < v.t+v.t*(v.r/v.rPrime) := Nat.add_lt_add_right hi.coefficient_increases _
      _ = v.t*(v.r/v.rPrime+1) := by ring
      _ ≤ v.t*2^steps := Nat.mul_le_mul_left _ (by omega)
      _ < 2^v.lT*2^steps := Nat.mul_lt_mul_of_pos_right ht (by positivity)
      _ = 2^(v.lT+steps) := by rw [Nat.pow_add]
  have htSize : nextT.size≤v.lT+steps := Nat.size_le.mpr htBound
  have htLe : v.t≤nextT := by dsimp [nextT]; nlinarith
  have htSizeLe := Nat.size_le_size htLe
  have hRpos : 0<v.rPrime.size := Nat.size_pos.mpr hrpos
  have hremSize : (v.r%v.rPrime).size≤v.rPrime.size :=
    Nat.size_le_size (Nat.mod_lt _ hrpos).le
  have hclock : start+steps+steps+steps+(steps-1)=4*spent+4*steps := by rw [hstart]; omega
  let frame : PaperActiveFrame p x (4*spent+4*steps) := {
    spent := spent
    boundary := v
    reachable := hreach
    nonterminal := hactive
    within := 4*steps
    within_pos := by omega
    within_le := by change 4*steps≤4*(v.r/v.rPrime).size; omega
    time_eq := rfl }
  have hwT := frame.lengthTWindow_covers hprime hx hxp hlower hbits
    (by change 4*steps=4*(v.r/v.rPrime).size; omega)
  have hwR := frame.lengthRPrimeWindow_covers hprime hx hxp hbits
    (by change 4*steps=4*(v.r/v.rPrime).size; omega)
  have hnext : (paperStep v).t=nextT := by
    rw [(paperStep_coefficients hactive).1]
    dsimp [nextT,paperQuotient]
    ring
  simp only [ActiveWindow.Covers,PaperActiveFrame.lengthTRight,frame] at hwT
  simp only [ActiveWindow.Covers,PaperActiveFrame.lengthRPrimeLeft,frame,hnext] at hwR
  have hdecode : (endIterationWindowsAt n (4*spent+4*steps)).K5Decode n=n+3 := by
    simp only [endIterationWindowsAt,certifiedActiveWindows,EndIterationWindows.K5Decode]
    omega
  apply indexedScheduleUnitary_reachable_paperStep r n start steps s v hp
    p x spent hreach hprime hx hxp hlower hbits hactive hstart hcapacityQ hcapacityS hcapacityR
    hsteps halignLayout hlayout hcoeffLayout hcapacityT hswapLayout
  all_goals rw [hclock]
  · simp only [endIterationWindowsAt,certifiedActiveWindows]
    rw [hR]
    omega
  · rw [hdecode]
    change (lengthRPrimeWindow n (4*spent+4*steps)).start≤nextT.size+2 ∧ nextT.size+2≤n+3
    omega
  · simpa only [endIterationWindowsAt,certifiedActiveWindows] using And.intro hwT.1 (by omega : v.t.size≤(lengthTWindow n (4*spent+4*steps)).stop)
  · change (lengthTWindow n (4*spent+4*steps)).start≤nextT.size ∧ nextT.size≤(lengthTWindow n (4*spent+4*steps)).stop
    omega
  · intro hn
    have hpos : 0<(v.r%v.rPrime).size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [hdecode]
    change (lengthRPrimeWindow n (4*spent+4*steps)).start≤n+4-(v.r%v.rPrime).size ∧ n+4-(v.r%v.rPrime).size≤n+3
    omega
  · rw [hdecode]
    change (lengthRPrimeWindow n (4*spent+4*steps)).start≤n+4-v.rPrime.size ∧ n+4-v.rPrime.size≤n+3
    omega

end ShorECDLP.Paper2607_13816
