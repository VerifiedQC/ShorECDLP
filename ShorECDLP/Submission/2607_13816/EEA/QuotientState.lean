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
end ShorECDLP.Paper2607_13816
