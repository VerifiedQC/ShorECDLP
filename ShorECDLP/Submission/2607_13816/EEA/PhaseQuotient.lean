import ShorECDLP.Submission.«2607_13816».EEA.QuotientLogical

/-! # Logical routing under the source phase controls -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem wrapper_swap (p1 p2 control sign target : Wire) (circuit : Circuit)
    (s : BasisState) (hc : s control = false)
    (hp1c : p1 ≠ control) (hp2c : p2 ≠ control)
    (hsc : sign ≠ control) (htc : target ≠ control)
    (hp1s : p1 ≠ sign) (hp2s : p2 ≠ sign)
    (hp1t : p1 ≠ target) (hp2t : p2 ≠ target)
    (hr : run circuit s[control ↦ (s p1 ^^ s p2)] =
      if s p1 ^^ s p2 then
        s[control ↦ (s p1 ^^ s p2)][sign ↦ s target][target ↦ s sign]
      else s[control ↦ (s p1 ^^ s p2)]) :
    run ([.CX p1 control,.CX p2 control] ++ circuit ++ [.CX p2 control,.CX p1 control]) s =
      if s p1 ^^ s p2 then s[sign ↦ s target][target ↦ s sign] else s := by
  have hpre : run [.CX p1 control,.CX p2 control] s = s[control ↦ (s p1 ^^ s p2)] := by
    funext w
    by_cases hw : w = control <;> simp [run_cons,applyGate,upd,hp2c,hc,hw]
  rw [run_append,run_append,hpre,hr]
  apply funext
  intro w
  cases h1 : s p1 <;> cases h2 : s p2 <;>
    by_cases hw : w = control <;>
    simp [h1,h2,run_cons,applyGate,upd,hp1c,hp2c,hp1s,hp2s,hp1t,hp2t,
      Ne.symm hsc,Ne.symm htc,hw,hc]
/-- The actual phase-controlled selector swaps sign with the logical quotient
boundary exactly in the two unequal-phase cases, restoring all other wires. -/
theorem blockD2Forward_logical (r : IndexedStepRegisters) (n index T Q : Nat)
    (w : ActiveWindow) (s : BasisState) (h : IndexedStepLayout r n index)
    (hqL : QuotientSwapLayout (r.quotient w) w.start w.stop)
    (hc : Clean r.aux s) (hw : 1 ≤ w.start)
    (ht : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length Q)
    (hfit : T+Q+1 < 2^r.lengthQ.length) (hlo : w.start ≤ T+Q+1) (hhi : T+Q+1 ≤ w.stop) :
    run (blockD2Forward r w) s =
      if s r.phase1 ^^ s r.phase2 then
        s[r.sign ↦ s (r.work1.getD (T+Q) 0)][r.work1.getD (T+Q) 0 ↦ s r.sign] else s := by
  change run ([.CX r.phase1 r.control,.CX r.phase2 r.control] ++
    quotientSwapUnitary (r.quotient w) w.start w.stop ++
    [.CX r.phase2 r.control,.CX r.phase1 r.control]) s = _
  let payload := [r.phase1,r.phase2,r.iter,r.sign] ++ r.work1 ++ r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime
  have hp : (payload ++ r.aux).Nodup := by
    simpa only [payload,IndexedStepRegisters.allWires,List.append_assoc] using h.physical
  have hcMem : r.control ∈ r.aux := by
    change r.aux.getD 0 0 ∈ r.aux
    rw [List.getD_eq_getElem r.aux 0 (by rw [h.aux_length]; decide)]
    exact List.getElem_mem _
  have hnc (wire : Wire) (hm : wire ∈ payload) : wire ≠ r.control :=
    (List.nodup_append.mp hp).2.2 wire hm r.control hcMem
  have htlen : T+Q < r.work1.length := by
    have he := hqL.work1_length
    change ((r.work1.drop (w.start-1)).take (w.stop-w.start+1)).length = _ at he
    simp only [List.length_take,List.length_drop] at he
    omega
  let target := r.work1.getD (T+Q) 0
  have htMem : target ∈ r.work1 := by
    dsimp only [target]
    rw [List.getD_eq_getElem _ _ htlen]
    exact List.getElem_mem _
  have hp1c := hnc r.phase1 (by simp [payload])
  have hp2c := hnc r.phase2 (by simp [payload])
  have hsc := hnc r.sign (by simp [payload])
  have htc := hnc target (by simp [payload,htMem])
  have hall := h.physical
  simp only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append,List.nodup_cons] at hall
  have hp1s : r.phase1 ≠ r.sign := by intro he; apply hall.1; simp [he]
  have hp2s : r.phase2 ≠ r.sign := by intro he; apply hall.2.1; simp [he]
  have hp1t : r.phase1 ≠ target := by intro he; apply hall.1; simp [he,htMem]
  have hp2t : r.phase2 ≠ target := by intro he; apply hall.2.1; simp [he,htMem]
  let enabled := s[r.control ↦ (s r.phase1 ^^ s r.phase2)]
  have hwords (ws : List Wire) (hm : ∀ wire ∈ ws, wire ∈ payload) : wireValues ws enabled = wireValues ws s := by
    apply List.map_congr_left
    intro wire hw'
    simp only [enabled,upd,hnc wire (hm wire hw'),if_false]
  have het : boolWordToNat (wireValues r.lengthT enabled) = truthMinusOneValue r.lengthQ.length T := by
    rw [hwords r.lengthT (by intro wire hm; simp [payload,hm])]
    exact ht
  have heq : boolWordToNat (wireValues r.lengthQ enabled) = truthMinusOneValue r.lengthQ.length Q := by
    rw [hwords r.lengthQ (by intro wire hm; simp [payload,hm])]
    exact hq
  have hec : QuotientSwapReady (r.quotient w) enabled := by
    intro wire hm
    have hpq := hqL.physical
    rw [QuotientSwapRegisters.allWires] at hpq
    have hn : wire ≠ r.control := by
      intro he
      exact (List.nodup_append.mp hpq).2.2 (r.quotient w).control (by simp)
        wire (by simp [hm]) he.symm
    have haux : wire ∈ r.aux := by
      have hs := List.mem_of_mem_take hm
      exact List.mem_of_mem_take (List.mem_of_mem_drop hs)
    simp only [enabled,upd,hn,if_false]
    exact hc wire haux
  have hr := run_indexedQuotientSwap_logical r w T Q enabled hqL hec hw het heq hfit hlo hhi
  apply wrapper_swap r.phase1 r.phase2 r.control r.sign target _ s (hc r.control hcMem)
    hp1c hp2c hsc htc hp1s hp2s hp1t hp2t
  dsimp only [target] at htc
  simpa only [enabled,target,upd,hsc,htc,if_false,if_true] using hr
end ShorECDLP.Paper2607_13816
