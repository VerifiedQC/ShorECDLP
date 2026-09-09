import ShorECDLP.Submission.«2607_13816».EEA.QuotientSwap
import ShorECDLP.Submission.«2607_13816».EEA.LengthBlocks
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep

/-! # Logical quotient/sign routing in physical work-bank coordinates -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem quotient_length_sum (width T Q : Nat) :
    (truthMinusOneValue width T + truthMinusOneValue width Q + 3) % 2^width =
      (T+Q+1)%2^width := by
  cases width with
  | zero => simp only [Nat.pow_zero,Nat.mod_one]
  | succ width =>
    have hm : 1 < 2^(width+1) := Nat.one_lt_two_pow (by omega)
    change (((T+2^(width+1)-1%2^(width+1))%2^(width+1))+
      ((Q+2^(width+1)-1%2^(width+1))%2^(width+1))+3)%2^(width+1) = _
    rw [Nat.mod_eq_of_lt hm]
    have he := ((Nat.mod_modEq (T+2^(width+1)-1) (2^(width+1))).add
      (Nat.mod_modEq (Q+2^(width+1)-1) (2^(width+1)))).add_right 3
    change _ % _ = _ % _ at he
    rw [he,show T+2^(width+1)-1+(Q+2^(width+1)-1)+3 = T+Q+1+2*2^(width+1) by omega]
    simp only [Nat.add_mul_mod_self_right]
/-- Truth-minus-one length inputs route the actual quotient/sign swap to the
logical boundary label T+Q+1, with all preparation restored. -/
theorem run_quotientSwapUnitary_logical (r : QuotientSwapRegisters) (k K T Q : Nat)
    (state : BasisState) (h : QuotientSwapLayout r k K) (hc : QuotientSwapReady r state)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length Q)
    (hfit : T+Q+1 < 2^r.lengthQ.length) (hlo : k ≤ T+Q+1) (hhi : T+Q+1 ≤ K) :
    run (quotientSwapUnitary r k K) state = quotientSwapState r k (T+Q+1) (state r.control) state := by
  have hp := quotientSwap_prepared_value r state h hc
  dsimp only at hp
  rw [ht,hq,quotient_length_sum,Nat.mod_eq_of_lt hfit] at hp
  have hr := quotientSwapUnitary_correct_in_range r state h hc
  dsimp only at hr
  rw [hp] at hr
  have hm : T+Q+1 ∈ quotientSwapLabels k K := by
    simp only [quotientSwapLabels,List.mem_range']
    exact ⟨T+Q+1-k,by omega,by omega⟩
  exact hr hm

/-- The one-based quotient selector boundary is the full-bank wire T+Q. -/
theorem run_indexedQuotientSwap_logical (r : IndexedStepRegisters) (w : ActiveWindow) (T Q : Nat)
    (state : BasisState) (h : QuotientSwapLayout (r.quotient w) w.start w.stop)
    (hc : QuotientSwapReady (r.quotient w) state) (hw : 1 ≤ w.start)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length Q)
    (hfit : T+Q+1 < 2^r.lengthQ.length) (hlo : w.start ≤ T+Q+1) (hhi : T+Q+1 ≤ w.stop) :
    run (quotientSwapUnitary (r.quotient w) w.start w.stop) state =
      if state r.control then state[r.sign ↦ state (r.work1.getD (T+Q) 0)]
        [r.work1.getD (T+Q) 0 ↦ state r.sign] else state := by
  have hr := run_quotientSwapUnitary_logical (r.quotient w) w.start w.stop T Q state h hc ht hq hfit hlo hhi
  have hi : T+Q+1-w.start < (r.quotient w).work1.length := by rw [h.work1_length]; omega
  have hs : ((r.work1.drop (w.start-1)).take (w.stop-w.start+1)).length = w.stop-w.start+1 := h.work1_length
  have hb : T+Q < r.work1.length := by simp only [List.length_take,List.length_drop] at hs; omega
  have he : (r.quotient w).workAt w.start (T+Q+1) = r.work1.getD (T+Q) 0 := by
    unfold QuotientSwapRegisters.workAt
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hb]
    change ((r.work1.drop (w.start-1)).take (w.stop-w.start+1))[T+Q+1-w.start] = _
    simp only [List.getElem_take,List.getElem_drop]
    congr 1
    omega
  rw [hr]
  simp only [quotientSwapState,he]
  rfl

end ShorECDLP.Paper2607_13816
