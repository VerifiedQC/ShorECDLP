import ShorECDLP.Submission.«2607_13816».EEA.SwapIteration
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
private theorem coefficient_lower_interval (S Q t q tp : Nat) (hQ : 0<Q)
    (hq : Q=q.size) :
    2^(S+Q-1)*t ≤ tp+2^S*t*q := by
  have hlow : 2^(Q-1)≤q := by
    by_contra hn
    have hh : q<2^(Q-1) := by omega
    have hs := Nat.size_le.mpr hh
    omega
  have he : S+Q-1=S+(Q-1) := by omega
  rw [he,Nat.pow_add]
  calc
    (2^S*2^(Q-1))*t = (2^S*t)*2^(Q-1) := by ac_rfl
    _ ≤ (2^S*t)*q := Nat.mul_le_mul_left _ hlow
    _ ≤ tp+2^S*t*q := Nat.le_add_left _ _

/-- A complete coefficient phase enters swap with a tight coefficient interval.
The quotient's true bit length derives the lower bound; no intermediate states
or final phase decisions are assumed. -/
theorem indexedScheduleUnitary_coefficient_complete (r : IndexedStepRegisters) (n start : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (hphase : v.phase=.coefficient) (hsign : v.sign=false)
    (hlayout : ∀ offset<v.lQ, IndexedStepLayout r n (start+offset))
    (hwindows : ∀ offset<v.lQ,
      (certifiedActiveWindows n (start+offset)).quotientSwap.start ≤ v.lT+(v.lQ-offset)+1 ∧
      v.lT+(v.lQ-offset)+1 ≤ (certifiedActiveWindows n (start+offset)).quotientSwap.stop ∧
      v.lT+1 ∈ quotientSwapLabels 1 (certifiedActiveWindows n (start+offset)).coefficient.stop)
    (hqmeta : v.lT+v.lQ+1 < 2^r.lengthQ.length)
    (htmeta : v.lT+1 < 2^r.lengthT.length)
    (hR : v.lRPrime≤n+3)
    (hupper : n+3-v.lRPrime-v.shift < 2^r.lengthT.length)
    (hspan : v.shift+v.lQ+v.lT ≤ n+3-v.lRPrime)
    (ht : v.t<2^v.lT) (htp : v.tPrime<2^(n+3-v.lRPrime))
    (hbound : v.tPrime<2^v.shift*v.t) (hq : v.q<2^v.lQ)
    (hr : v.r<2^(n+3-(v.lT+v.lQ+1)))
    (hswidth : 0<r.lengthS.length) (hscap : v.shift+v.lQ<2^r.lengthS.length)
    (hrcap : v.lRPrime<2^r.lengthRPrime.length)
    (hpositive : 0<v.lQ) (hcanonical : v.lQ=v.q.size) (hRpositive : 0<v.lRPrime) :
    let next := coefficientMicrostep^[v.lQ] v
    IndexedPackedState r n (run (indexedScheduleUnitary r n start v.lQ) s) next ∧
      next.phase=.swap ∧ next.sign=true ∧ next.q=0 ∧ next.lQ=0 ∧
      next.shift=v.shift+v.lQ ∧ next.tPrime=v.tPrime+2^v.shift*v.t*v.q ∧
      2^(next.shift-1)*next.t≤next.tPrime ∧ next.tPrime<2^next.shift*next.t ∧
      next.tPrime.size≤v.shift+v.lQ+v.lT := by
  have hall := indexedScheduleUnitary_coefficient_packed r n start v.lQ s v hp
    hphase hsign (by omega) hlayout hwindows hqmeta htmeta hR hupper hspan ht htp
    hbound hq hr hswidth hscap hrcap
  obtain ⟨hpack,hqnext,htpnext,hbnext,hcons,hQnext,hSnext,hfinish⟩ := hall
  obtain ⟨hqzero,hclosed⟩ := hfinish rfl
  obtain ⟨htt,hTT,hrr,hrpr,hRR,hii,hQQ,hSS,hqq⟩ := coefficient_coordinates v v.lQ
  have hcoords := coefficient_coordinates v (v.lQ-1)
  have hlastQ : (coefficientMicrostep^[v.lQ-1] v).lQ=1 := by
    rw [hcoords.2.2.2.2.2.2.1]
    omega
  have hlastR : (coefficientMicrostep^[v.lQ-1] v).lRPrime≠0 := by
    rw [hcoords.2.2.2.2.1]
    omega
  have hiter : coefficientMicrostep^[v.lQ] v =
      coefficientMicrostep (coefficientMicrostep^[v.lQ-1] v) := by
    conv_lhs => rw [← show v.lQ-1+1=v.lQ by omega]
    rw [Function.iterate_succ_apply']
  have hphaseEnd : (coefficientMicrostep^[v.lQ] v).phase=.swap ∧
      (coefficientMicrostep^[v.lQ] v).sign=true := by
    rw [hiter]
    simp only [coefficientMicrostep,hlastQ,hlastR,decide_true,decide_false,
      Bool.not_false,Bool.and_self,if_true,and_self]
  have hlower : 2^((coefficientMicrostep^[v.lQ] v).shift-1)*
      (coefficientMicrostep^[v.lQ] v).t≤(coefficientMicrostep^[v.lQ] v).tPrime := by
    rw [hSS,htt,hclosed]
    exact coefficient_lower_interval v.shift v.lQ v.t v.q v.tPrime hpositive hcanonical
  have hsize : (coefficientMicrostep^[v.lQ] v).tPrime.size≤v.shift+v.lQ+v.lT := by
    apply Nat.size_le.mpr
    have hb := hbnext
    rw [hSS,htt] at hb
    calc
      (coefficientMicrostep^[v.lQ] v).tPrime < 2^(v.shift+v.lQ)*v.t := hb
      _ ≤ 2^(v.shift+v.lQ)*2^v.lT := Nat.mul_le_mul_left _ (Nat.le_of_lt ht)
      _ = 2^(v.shift+v.lQ+v.lT) := (Nat.pow_add _ _ _).symm
  exact ⟨hpack,hphaseEnd.1,hphaseEnd.2,hqzero,by simpa only [Nat.sub_self] using hQnext,
    hSnext,hclosed,hlower,hbnext,hsize⟩

/-- The actual coefficient and swap schedules compose without assumed
intermediate packing, phase decisions, or coefficient bounds. -/
theorem indexedScheduleUnitary_coefficient_swap_packed (r : IndexedStepRegisters) (n start : Nat)
    (s : BasisState) (v : EEAState) (hp : IndexedPackedState r n s v)
    (hphase : v.phase=.coefficient) (hsign : v.sign=false)
    (hlayout : ∀ offset<v.lQ, IndexedStepLayout r n (start+offset))
    (hwindows : ∀ offset<v.lQ,
      (certifiedActiveWindows n (start+offset)).quotientSwap.start ≤ v.lT+(v.lQ-offset)+1 ∧
      v.lT+(v.lQ-offset)+1 ≤ (certifiedActiveWindows n (start+offset)).quotientSwap.stop ∧
      v.lT+1 ∈ quotientSwapLabels 1 (certifiedActiveWindows n (start+offset)).coefficient.stop)
    (hqmeta : v.lT+v.lQ+1 < 2^r.lengthQ.length)
    (htmeta : v.lT+1 < 2^r.lengthT.length)
    (hR : v.lRPrime≤n+3)
    (hupper : n+3-v.lRPrime-v.shift < 2^r.lengthT.length)
    (hspan : v.shift+v.lQ+v.lT+1 ≤ n+3-v.lRPrime)
    (ht : v.t<2^v.lT) (htp : v.tPrime<2^(n+3-v.lRPrime))
    (hbound : v.tPrime<2^v.shift*v.t) (hq : v.q<2^v.lQ)
    (hr : v.r<2^(n+3-(v.lT+v.lQ+1)))
    (hswidth : 0<r.lengthS.length) (hscap : v.shift+v.lQ<2^r.lengthS.length)
    (hrcap : v.lRPrime<2^r.lengthRPrime.length)
    (hpositive : 0<v.lQ) (hcanonical : v.lQ=v.q.size) (hRpositive : 0<v.lRPrime)
    (hcapacity : n+3<2^r.lengthT.length)
    (hT : v.lT=v.t.size) (hRP : v.lRPrime=v.rPrime.size) (hsmaller : v.r<v.rPrime)
    (hswapLayout : ∀ offset<v.shift+v.lQ, IndexedStepLayout r n (start+v.lQ+offset))
    (hswapWindows : ∀ offset<v.shift+v.lQ, n+3-v.lRPrime-(v.shift+v.lQ-offset) ∈
      quotientSwapLabels 1 (certifiedActiveWindows n (start+v.lQ+offset)).coefficient.stop)
    (hstep : (start+v.lQ+(v.shift+v.lQ-1))%4=0)
    (hboundary4 : (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).k4 ≤ n+3-v.lRPrime ∧
      n+3-v.lRPrime ≤ (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).K4)
    (hboundary5 : (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).k5 ≤ (v.tPrime+2^v.shift*v.t*v.q).size+2 ∧
      (v.tPrime+2^v.shift*v.t*v.q).size+2 ≤ (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).K5Decode n)
    (htWindow : (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).k4 ≤ v.t.size ∧
      v.t.size ≤ (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).K4)
    (htpWindow : (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).k4 ≤ (v.tPrime+2^v.shift*v.t*v.q).size ∧
      (v.tPrime+2^v.shift*v.t*v.q).size ≤ (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).K4)
    (hrWindow : v.r ≠ 0 → (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).k5 ≤ n+4-v.r.size ∧
      n+4-v.r.size ≤ (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).K5Decode n)
    (hrpWindow : (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).k5 ≤ n+4-v.rPrime.size ∧
      n+4-v.rPrime.size ≤ (endIterationWindowsAt n (start+v.lQ+(v.shift+v.lQ-1))).K5Decode n) :
    let mid := coefficientMicrostep^[v.lQ] v
    let next := endpointMicrostep (swapBeforeEndpointMicrostep^[v.shift+v.lQ] mid)
    IndexedPackedState r n (run (indexedScheduleUnitary r n start (v.lQ+(v.shift+v.lQ))) s) next ∧
      next.Canonical ∧ next.rPrime<v.rPrime := by
  let u := coefficientMicrostep^[v.lQ] v
  let mid := run (indexedScheduleUnitary r n start v.lQ) s
  have hc := indexedScheduleUnitary_coefficient_complete r n start s v hp hphase hsign
    hlayout hwindows hqmeta htmeta hR hupper (by omega) ht htp hbound hq hr
    hswidth hscap hrcap hpositive hcanonical hRpositive
  obtain ⟨hpack,hphaseU,hsignU,hqU,hQU,hSU,htpU,hlowerU,hupperU,hsizeU⟩ := hc
  obtain ⟨htt,hTT,hrr,hrpr,hRR,hii,hQQ,hSS,hqq⟩ := coefficient_coordinates v v.lQ
  have hguardU : u.tPrime.size+1+u.lRPrime≤n+3 := by
    change (coefficientMicrostep^[v.lQ] v).tPrime.size+1+_≤_
    rw [hRR]
    omega
  have htBU : u.t<2^(n+3-u.lRPrime-u.shift) := by
    change (coefficientMicrostep^[v.lQ] v).t<_
    rw [htt,hRR,hSS]
    exact ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have htpFit : u.tPrime<2^(n+3-u.lRPrime) := by
    exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hrFit : u.r<2^u.lRPrime := by
    change (coefficientMicrostep^[v.lQ] v).r<_
    rw [hrr,hRR,hRP]
    exact hsmaller.trans (Nat.lt_size_self _)
  have hmonoU : u.lT≤u.tPrime.size := by
    change (coefficientMicrostep^[v.lQ] v).lT≤_
    rw [hTT,hT]
    apply Nat.size_le_size
    have hle : u.t≤u.tPrime := by
      calc
        u.t = 1*u.t := by simp only [one_mul]
        _ ≤ 2^(u.shift-1)*u.t := Nat.mul_le_mul_right _ (Nat.one_le_two_pow)
        _ ≤ u.tPrime := hlowerU
    simpa only [u,htt] using hle
  have hs := indexedScheduleUnitary_swap_packed r n (start+v.lQ) mid u hpack hphaseU hsignU
    (by change 0<(coefficientMicrostep^[v.lQ] v).shift; rw [hSS]; omega)
    (by simpa only [u,hSS] using hswapLayout)
    (by simpa only [u,hRR,hSS] using hswapWindows) hcapacity
    (by change (coefficientMicrostep^[v.lQ] v).lT+1+_≤_; rw [hTT,hRR]; omega)
    (by change (coefficientMicrostep^[v.lQ] v).lRPrime+_≤_; rw [hRR,hSS]; omega)
    (by simpa only [u,htt,hTT] using ht) htBU htpFit hrFit hswidth
    (by simpa only [u,hSS] using hscap) (by simpa only [u,hRR] using hRpositive)
    (by simpa only [u,hRR] using hrcap) hQU hupperU hlowerU
    (by simpa only [u,hSS] using hstep)
    (by simpa only [u,hTT,htt] using hT) (by simpa only [u,hRR,hrpr] using hRP)
    (by simpa only [u,hrr,hrpr] using hsmaller) hmonoU hguardU
    (by simpa only [u,hRR,hSS] using hboundary4)
    (by simpa only [u,htpU,hSS] using hboundary5)
    (by simpa only [u,htt,hSS] using htWindow)
    (by simpa only [u,htpU,hSS] using htpWindow)
    (by simpa only [u,hrr,hSS] using hrWindow)
    (by simpa only [u,hrpr,hSS] using hrpWindow)
  dsimp only at hs ⊢
  rw [indexedScheduleUnitary_append,Classical.run_append]
  simpa only [u,mid,hSS,hrpr] using hs

end ShorECDLP.Paper2607_13816
