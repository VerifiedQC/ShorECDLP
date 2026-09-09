import ShorECDLP.Submission.«2607_13816».EEA.CoefficientState
import ShorECDLP.Submission.«2607_13816».EEA.Schedule
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem coefficient_coordinates (v : EEAState) (count : Nat) :
    let w := coefficientMicrostep^[count] v
    w.t=v.t ∧ w.lT=v.lT ∧ w.r=v.r ∧ w.rPrime=v.rPrime ∧ w.lRPrime=v.lRPrime ∧
    w.iter=v.iter ∧ w.lQ=v.lQ-count ∧ w.shift=v.shift+count ∧ w.q=v.q/2^count := by
  induction count with
  | zero => simp
  | succ k ih =>
    dsimp only at ih ⊢
    obtain ⟨ht,hT,hr,hrp,hR,hi,hQ,hS,hq⟩ := ih
    simp only [Function.iterate_succ_apply',coefficientMicrostep,ht,hT,hr,hrp,hR,hi,hQ,hS,hq]
    simp only [Nat.sub_sub,Nat.add_assoc,Nat.div_div_eq_div_mul,Nat.pow_succ,
      and_self]
private theorem coefficient_still_active (v : EEAState) (count : Nat)
    (hp : v.phase=.coefficient) (hs : v.sign=false) (hc : count<v.lQ) :
    (coefficientMicrostep^[count] v).phase=.coefficient ∧
    (coefficientMicrostep^[count] v).sign=false := by
  cases count with
  | zero => simpa using And.intro hp hs
  | succ k =>
    have hQ := (coefficient_coordinates v k).2.2.2.2.2.2.1
    have hn : (coefficientMicrostep^[k] v).lQ ≠ 1 := by rw [hQ]; omega
    simp [Function.iterate_succ_apply',coefficientMicrostep,hn]
/-- A sequence of actual coefficient microsteps preserves the packed interpretation.
Only the initial arithmetic bounds and the chosen schedule's physical/window bounds
are required; intermediate packing and coefficient bounds are derived by induction. -/
theorem indexedScheduleUnitary_coefficient_packed (r : IndexedStepRegisters) (n start count : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (hphase : v.phase=.coefficient) (hsign : v.sign=false) (hcount : count≤v.lQ)
    (hlayout : ∀ offset<count, IndexedStepLayout r n (start+offset))
    (hwindows : ∀ offset<count,
      (certifiedActiveWindows n (start+offset)).quotientSwap.start ≤ v.lT+(v.lQ-offset)+1 ∧
      v.lT+(v.lQ-offset)+1 ≤ (certifiedActiveWindows n (start+offset)).quotientSwap.stop ∧
      v.lT+1 ∈ quotientSwapLabels 1 (certifiedActiveWindows n (start+offset)).coefficient.stop)
    (hqmeta : v.lT+v.lQ+1 < 2^r.lengthQ.length)
    (htmeta : v.lT+1 < 2^r.lengthT.length)
    (hR : v.lRPrime≤n+3)
    (hupper : n+3-v.lRPrime-v.shift < 2^r.lengthT.length)
    (hspan : v.shift+count+v.lT ≤ n+3-v.lRPrime)
    (ht : v.t<2^v.lT) (htp : v.tPrime<2^(n+3-v.lRPrime))
    (hbound : v.tPrime<2^v.shift*v.t) (hq : v.q<2^v.lQ)
    (hr : v.r<2^(n+3-(v.lT+v.lQ+1)))
    (hswidth : 0<r.lengthS.length) (hscap : v.shift+count<2^r.lengthS.length)
    (hrcap : v.lRPrime<2^r.lengthRPrime.length) :
    let next := coefficientMicrostep^[count] v
    IndexedPackedState r n (run (indexedScheduleUnitary r n start count) s) next ∧
    next.q<2^next.lQ ∧ next.tPrime<2^(n+3-next.lRPrime) ∧
    next.tPrime<2^next.shift*next.t ∧
    next.tPrime+2^next.shift*next.t*next.q = v.tPrime+2^v.shift*v.t*v.q ∧
    next.lQ=v.lQ-count ∧ next.shift=v.shift+count ∧
    (count=v.lQ → next.q=0 ∧ next.tPrime=v.tPrime+2^v.shift*v.t*v.q) := by
  suffices hall : ∀ k≤count,
      let next := coefficientMicrostep^[k] v
      IndexedPackedState r n (run (indexedScheduleUnitary r n start k) s) next ∧
      next.q<2^next.lQ ∧ next.tPrime<2^(n+3-next.lRPrime) ∧
      next.tPrime<2^next.shift*next.t ∧
      next.tPrime+2^next.shift*next.t*next.q = v.tPrime+2^v.shift*v.t*v.q by
    obtain ⟨hpack,hqnext,htpnext,hbnext,hsnext⟩ := hall count (by omega)
    have hc := coefficient_coordinates v count
    refine ⟨hpack,hqnext,htpnext,hbnext,hsnext,hc.2.2.2.2.2.2.1,hc.2.2.2.2.2.2.2.1,?_⟩
    intro he
    have hQ : (coefficientMicrostep^[count] v).lQ = 0 := by
      rw [hc.2.2.2.2.2.2.1,he,Nat.sub_self]
    have hzero : (coefficientMicrostep^[count] v).q = 0 := by
      rw [hQ] at hqnext
      simpa only [Nat.pow_zero,Nat.lt_one_iff] using hqnext
    exact ⟨hzero,by simpa only [hzero,mul_zero,add_zero] using hsnext⟩
  intro k
  induction k with
  | zero =>
    intro _
    change IndexedPackedState r n s v ∧ _
    exact ⟨hp,hq,htp,hbound,rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hpk,hqk,htpk,hbk,hsk⟩ := ih (by omega)
    obtain ⟨htt,hTT,hrr,hrpr,hRR,hii,hQQ,hSS,hqq⟩ := coefficient_coordinates v k
    have hactive := coefficient_still_active v k hphase hsign (by omega)
    have hw := hwindows k (by omega)
    have hrfit : (coefficientMicrostep^[k] v).r <
        2^(n+3-((coefficientMicrostep^[k] v).lT+(coefficientMicrostep^[k] v).lQ+1)) := by
      rw [hrr,hTT,hQQ]
      exact lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega))
    have hstep := indexedStepUnitary_coefficient_packed r n (start+k)
      (run (indexedScheduleUnitary r n start k) s) (coefficientMicrostep^[k] v)
      (hlayout k (by omega)) hpk hactive.1 hactive.2
      (by rw [hQQ]; omega)
      (by rw [hTT,hQQ]; omega)
      (by simpa only [hTT,hQQ] using hw.1)
      (by simpa only [hTT,hQQ] using hw.2.1)
      (by simpa only [hTT] using htmeta)
      (by rw [hRR,hSS]; omega)
      (by rw [hRR,hSS]; omega)
      (by simpa only [hTT] using hw.2.2)
      (by simpa only [htt,hTT] using ht) htpk
      (by rw [hSS,hTT,hRR]; omega) hbk hqk hrfit hswidth
      (by rw [hSS]; omega) (by simpa only [hRR] using hrcap)
    obtain ⟨hpack,hqnext,htpnext,hbnext,hsnext⟩ := hstep
    rw [indexedScheduleUnitary_snoc,Classical.run_append,Function.iterate_succ_apply']
    exact ⟨hpack,hqnext,htpnext,hbnext,hsnext.trans hsk⟩
end ShorECDLP.Paper2607_13816
