import ShorECDLP.Submission.«2607_13816».EEA.CoefficientState
import ShorECDLP.Submission.«2607_13816».EEA.Schedule
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem swap_coordinates (v : EEAState) (count : Nat) :
    let w := swapBeforeEndpointMicrostep^[count] v
    w.t=v.t ∧ w.lT=v.lT ∧ w.q=v.q ∧ w.lQ=v.lQ ∧ w.r=v.r ∧
    w.tPrime=v.tPrime ∧ w.rPrime=v.rPrime ∧ w.lRPrime=v.lRPrime ∧
    w.iter=v.iter ∧ w.shift=v.shift-count ∧ (0<count → w.sign=false) := by
  induction count with
  | zero => simp
  | succ k ih =>
    dsimp only at ih ⊢
    obtain ⟨ht,hT,hq,hQ,hr,htp,hrp,hR,hi,hS,_⟩ := ih
    simp only [Function.iterate_succ_apply',swapBeforeEndpointMicrostep,
      ht,hT,hq,hQ,hr,htp,hrp,hR,hi,hS,Nat.sub_sub,and_self,
      implies_true]

private theorem swap_comparison (v : EEAState) (count : Nat)
    (hs : v.sign=true) (hc : count<v.shift)
    (hupper : v.tPrime<2^v.shift*v.t)
    (hlower : 2^(v.shift-1)*v.t≤v.tPrime) :
    let w := swapBeforeEndpointMicrostep^[count] v
    (w.sign ^^ decide (w.t*2^w.shift≤w.tPrime))=true := by
  have hw := swap_coordinates v count
  dsimp only at hw ⊢
  rw [hw.1,hw.2.2.2.2.2.1,hw.2.2.2.2.2.2.2.2.2.1]
  by_cases hz : count=0
  · subst count
    simp only [Function.iterate_zero_apply,hs,Nat.sub_zero]
    have hn : ¬v.t*2^v.shift≤v.tPrime := by rw [Nat.mul_comm]; omega
    simp only [decide_eq_false hn,Bool.xor_false]
  · rw [hw.2.2.2.2.2.2.2.2.2.2 (by omega)]
    have hp : v.t*2^(v.shift-count)≤v.tPrime := by
      rw [Nat.mul_comm]
      exact (Nat.mul_le_mul_right v.t (Nat.pow_le_pow_right (by decide) (by omega))).trans hlower
    simp only [decide_eq_true hp,Bool.false_xor]

/-- The tight coefficient interval forces every positive-shift swap comparison
onto the swap path and returns to the remainder phase exactly at zero shift. -/
theorem swap_iteration_phase (v : EEAState) (count : Nat)
    (hp : v.phase=.swap) (hs : v.sign=true) (hc : count≤v.shift)
    (hpositive : 0<v.shift) (hupper : v.tPrime<2^v.shift*v.t)
    (hlower : 2^(v.shift-1)*v.t≤v.tPrime) :
    (swapBeforeEndpointMicrostep^[count] v).phase =
      (if count=v.shift then .remainder else .swap) := by
  cases count with
  | zero => simpa only [Function.iterate_zero_apply,if_neg (by omega : ¬0=v.shift)] using hp
  | succ k =>
    have hcmp := swap_comparison v k hs (by omega) hupper hlower
    have hS := (swap_coordinates v k).2.2.2.2.2.2.2.2.2.1
    rw [Function.iterate_succ_apply']
    change (if (swapBeforeEndpointMicrostep^[k] v).shift=1 then
      (if (swapBeforeEndpointMicrostep^[k] v).sign ^^ decide ((swapBeforeEndpointMicrostep^[k] v).t*2^(swapBeforeEndpointMicrostep^[k] v).shift≤(swapBeforeEndpointMicrostep^[k] v).tPrime) then EEAPhase.remainder else .quotient)
      else if (swapBeforeEndpointMicrostep^[k] v).sign ^^ decide ((swapBeforeEndpointMicrostep^[k] v).t*2^(swapBeforeEndpointMicrostep^[k] v).shift≤(swapBeforeEndpointMicrostep^[k] v).tPrime) then .swap else .coefficient) = _
    rw [hcmp]
    simp only [if_true,hS]
    have he : v.shift-k=1 ↔ k+1=v.shift := by omega
    simp only [he]

/-- Every nonfinal step of the actual swap schedule preserves packing. The tight
coefficient interval derives all intermediate phase decisions. -/
theorem indexedScheduleUnitary_swap_prefix_packed (r : IndexedStepRegisters)
    (n start count : Nat) (s : BasisState) (v : EEAState)
    (hp : IndexedPackedState r n s v) (hphase : v.phase=.swap) (hsign : v.sign=true)
    (hcount : count<v.shift)
    (hlayout : ∀ offset<count, IndexedStepLayout r n (start+offset))
    (hwindows : ∀ offset<count, n+3-v.lRPrime-(v.shift-offset) ∈
      quotientSwapLabels 1 (certifiedActiveWindows n (start+offset)).coefficient.stop)
    (hcapacity : n+3<2^r.lengthT.length) (hspan : v.lT+1+v.lRPrime≤n+3)
    (hlo : v.lRPrime+v.shift≤n+3)
    (ht : v.t<2^v.lT) (htB : v.t<2^(n+3-v.lRPrime-v.shift))
    (htp : v.tPrime<2^(n+3-v.lRPrime)) (hrem : v.r<2^v.lRPrime)
    (hswidth : 0<r.lengthS.length) (hsfit : v.shift<2^r.lengthS.length)
    (hR : 0<v.lRPrime) (hrfit : v.lRPrime<2^r.lengthRPrime.length)
    (hQ : v.lQ=0) (hupper : v.tPrime<2^v.shift*v.t)
    (hlower : 2^(v.shift-1)*v.t≤v.tPrime) :
    IndexedPackedState r n (run (indexedScheduleUnitary r n start count) s)
      (swapBeforeEndpointMicrostep^[count] v) := by
  suffices hall : ∀ k≤count, IndexedPackedState r n
      (run (indexedScheduleUnitary r n start k) s) (swapBeforeEndpointMicrostep^[k] v) by
    exact hall count (by omega)
  intro k
  induction k with
  | zero => intro _; exact hp
  | succ k ih =>
    intro hk
    have hpk := ih (by omega)
    obtain ⟨htt,hTT,hqq,hQQ,hrr,htpt,hrpr,hRR,hii,hSS,_⟩ := swap_coordinates v k
    have hphasek := swap_iteration_phase v k hphase hsign (by omega) (by omega) hupper hlower
    rw [if_neg (by omega : k≠v.shift)] at hphasek
    have htBk : (swapBeforeEndpointMicrostep^[k] v).t <
        2^(n+3-(swapBeforeEndpointMicrostep^[k] v).lRPrime-(swapBeforeEndpointMicrostep^[k] v).shift) := by
      rw [htt,hRR,hSS]
      exact htB.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hstep := indexedStepUnitary_swap_packed r n (start+k)
      (run (indexedScheduleUnitary r n start k) s) (swapBeforeEndpointMicrostep^[k] v)
      (hlayout k (by omega)) hpk hphasek (by simpa only [hQQ] using hQ)
      (by rw [hTT]; omega) (by simpa only [hTT,hRR] using hspan)
      (by rw [hSS]; omega) (by rw [hRR,hSS]; omega)
      (by rw [hRR,hSS]; omega)
      (by simpa only [hRR,hSS] using hwindows k (by omega))
      (by simpa only [htt,hTT] using ht) htBk
      (by simpa only [htpt,hRR] using htp) (by simpa only [hrr,hRR] using hrem)
      hswidth (by rw [hSS]; omega) (by simpa only [hRR] using hR)
      (by simpa only [hRR] using hrfit)
    have hnonfinal : (swapBeforeEndpointMicrostep^[k] v).shift ≠ 1 := by rw [hSS]; omega
    have heq : swapInteriorMicrostep (swapBeforeEndpointMicrostep^[k] v) =
        swapBeforeEndpointMicrostep (swapBeforeEndpointMicrostep^[k] v) := by
      simp only [swapInteriorMicrostep,swapBeforeEndpointMicrostep,if_neg hnonfinal]
    rw [indexedScheduleUnitary_snoc,Classical.run_append,Function.iterate_succ_apply']
    rw [heq] at hstep
    exact hstep

/-- The complete swap phase returns the actual scheduled circuit to a canonical
packed boundary with a strictly smaller second remainder. -/
theorem indexedScheduleUnitary_swap_packed (r : IndexedStepRegisters)
    (n start : Nat) (s : BasisState) (v : EEAState)
    (hp : IndexedPackedState r n s v) (hphase : v.phase=.swap) (hsign : v.sign=true)
    (hpositive : 0<v.shift)
    (hlayout : ∀ offset<v.shift, IndexedStepLayout r n (start+offset))
    (hwindows : ∀ offset<v.shift, n+3-v.lRPrime-(v.shift-offset) ∈
      quotientSwapLabels 1 (certifiedActiveWindows n (start+offset)).coefficient.stop)
    (hcapacity : n+3<2^r.lengthT.length) (hspan : v.lT+1+v.lRPrime≤n+3)
    (hlo : v.lRPrime+v.shift≤n+3)
    (ht : v.t<2^v.lT) (htB : v.t<2^(n+3-v.lRPrime-v.shift))
    (htp : v.tPrime<2^(n+3-v.lRPrime)) (hrem : v.r<2^v.lRPrime)
    (hswidth : 0<r.lengthS.length) (hsfit : v.shift<2^r.lengthS.length)
    (hR : 0<v.lRPrime) (hrfit : v.lRPrime<2^r.lengthRPrime.length)
    (hQ : v.lQ=0) (hupper : v.tPrime<2^v.shift*v.t)
    (hlower : 2^(v.shift-1)*v.t≤v.tPrime)
    (hstep : (start+(v.shift-1)) % 4 = 0)
    (hT : v.lT = v.t.size) (hRP : v.lRPrime = v.rPrime.size)
    (hsmaller : v.r < v.rPrime) (hmono : v.lT ≤ v.tPrime.size)
    (hguard : v.tPrime.size+1+v.lRPrime ≤ n+3)
    (hboundary4 : (endIterationWindowsAt n (start+(v.shift-1))).k4 ≤ n+3-v.lRPrime ∧
      n+3-v.lRPrime ≤ (endIterationWindowsAt n (start+(v.shift-1))).K4)
    (hboundary5 : (endIterationWindowsAt n (start+(v.shift-1))).k5 ≤ v.tPrime.size+2 ∧
      v.tPrime.size+2 ≤ (endIterationWindowsAt n (start+(v.shift-1))).K5Decode n)
    (htWindow : (endIterationWindowsAt n (start+(v.shift-1))).k4 ≤ v.t.size ∧
      v.t.size ≤ (endIterationWindowsAt n (start+(v.shift-1))).K4)
    (htpWindow : (endIterationWindowsAt n (start+(v.shift-1))).k4 ≤ v.tPrime.size ∧
      v.tPrime.size ≤ (endIterationWindowsAt n (start+(v.shift-1))).K4)
    (hrWindow : v.r ≠ 0 → (endIterationWindowsAt n (start+(v.shift-1))).k5 ≤ n+4-v.r.size ∧
      n+4-v.r.size ≤ (endIterationWindowsAt n (start+(v.shift-1))).K5Decode n)
    (hrpWindow : (endIterationWindowsAt n (start+(v.shift-1))).k5 ≤ n+4-v.rPrime.size ∧
      n+4-v.rPrime.size ≤ (endIterationWindowsAt n (start+(v.shift-1))).K5Decode n) :
    let next := endpointMicrostep (swapBeforeEndpointMicrostep^[v.shift] v)
    IndexedPackedState r n (run (indexedScheduleUnitary r n start v.shift) s) next ∧
      next.Canonical ∧ next.rPrime<v.rPrime := by
  let k := v.shift-1
  let mid := run (indexedScheduleUnitary r n start k) s
  let w := swapBeforeEndpointMicrostep^[k] v
  have hk : k+1=v.shift := by dsimp only [k]; omega
  have hpack := indexedScheduleUnitary_swap_prefix_packed r n start k s v hp hphase hsign
    (by dsimp only [k]; omega) (fun off ho => hlayout off (by omega))
    (fun off ho => hwindows off (by omega)) hcapacity hspan hlo ht htB htp hrem
    hswidth hsfit hR hrfit hQ hupper hlower
  obtain ⟨htt,hTT,hqq,hQQ,hrr,htpt,hrpr,hRR,hii,hSS,_⟩ := swap_coordinates v k
  have hphasek := swap_iteration_phase v k hphase hsign (by omega) hpositive hupper hlower
  rw [if_neg (by omega : k≠v.shift)] at hphasek
  have htBk : w.t<2^(n+3-w.lRPrime-w.shift) := by
    change (swapBeforeEndpointMicrostep^[k] v).t<_
    rw [htt,hRR,hSS]
    exact htB.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hlast := indexedStepUnitary_swap_endpoint_packed r n (start+k) mid w
    (hlayout k (by omega)) hpack hphasek (by simpa only [w,hQQ] using hQ)
    (by change (swapBeforeEndpointMicrostep^[k] v).lT+1<_; rw [hTT]; omega)
    (by simpa only [w,hTT,hRR] using hspan)
    (by change (swapBeforeEndpointMicrostep^[k] v).shift=1; rw [hSS]; omega)
    (by change (swapBeforeEndpointMicrostep^[k] v).lRPrime+_≤_; rw [hRR,hSS]; omega)
    (by change n+3-(swapBeforeEndpointMicrostep^[k] v).lRPrime-_<_; rw [hRR,hSS]; omega)
    (by simpa only [w,hRR,hSS] using hwindows k (by omega))
    (by simpa only [w,htt,hTT] using ht) htBk
    (by simpa only [w,htpt,hRR] using htp) (by simpa only [w,hrr,hRR] using hrem)
    hswidth (by change (swapBeforeEndpointMicrostep^[k] v).shift<_; rw [hSS]; omega)
    (by simpa only [w,hRR] using hR) (by simpa only [w,hRR] using hrfit) hstep
    (by simpa only [w,hTT,htt] using hT) (by simpa only [w,hRR,hrpr] using hRP)
    (by simpa only [w,hrr,hrpr] using hsmaller) (by simpa only [w,hTT,htpt] using hmono)
    (by simpa only [w,htpt,hRR] using hguard) hcapacity
    (by simpa only [w,hRR] using hboundary4) (by simpa only [w,htpt] using hboundary5)
    (by simpa only [w,htt] using htWindow) (by simpa only [w,htpt] using htpWindow)
    (by simpa only [w,hrr] using hrWindow) (by simpa only [w,hrpr] using hrpWindow)
  have hphysical : IndexedPackedState r n (run (indexedScheduleUnitary r n start v.shift) s)
      (endpointMicrostep (swapBeforeEndpointMicrostep^[v.shift] v)) := by
    rw [← hk,indexedScheduleUnitary_snoc,Classical.run_append,Function.iterate_succ_apply']
    exact hlast
  have hphaseEnd := swap_iteration_phase v v.shift hphase hsign (by omega) hpositive hupper hlower
  simp only [if_true] at hphaseEnd
  have hcoords := swap_coordinates v v.shift
  have hsignEnd := hcoords.2.2.2.2.2.2.2.2.2.2 hpositive
  refine ⟨hphysical,?_,?_⟩
  · simp only [EEAState.Canonical,endpointMicrostep,hphaseEnd,hsignEnd,and_self]
  · change (swapBeforeEndpointMicrostep^[v.shift] v).r<v.rPrime
    rw [hcoords.2.2.2.2.1]
    exact hsmaller

end ShorECDLP.Paper2607_13816
