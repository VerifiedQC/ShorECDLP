import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledAdd
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledLT
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantModular
namespace ShorECDLP.Paper2607_13816
open Classical
def uncontrolledConstantModularAddIdealState (target : List Wire) (constant correction : List Bool)
    (p : Nat) (f : Wire) (s : BasisState) : BasisState :=
  let low := gidneyUncontrolledAddIdealState target constant s
  let carried := upd low f (Bool.xor (low f) (decide (boolWordToNat (wireValues target low)<boolWordToNat constant)))
  let flagged := upd carried f (Bool.xor (carried f) (decide (p≤boolWordToNat (wireValues target carried))))
  let mid := gidneyAddIdealState target correction f flagged
  upd mid f (Bool.xor (mid f) (decide (boolWordToNat (wireValues target mid)<boolWordToNat constant)))

private theorem word_upd_outside (target : List Wire) (s : BasisState) (f : Wire) (b : Bool)
    (hf : f ∉ target) : wireValues target (upd s f b)=wireValues target s := by
  apply List.map_congr_left
  intro w hw
  have hn : w≠f := fun he => hf (he ▸ hw)
  simp [upd,hn]

theorem uncontrolledConstantModularAddIdealState_correct (target : List Wire) (constant correction : List Bool)
    (p : Nat) (f : Wire) (s : BasisState)
    (hk : target.length=constant.length) (hr : target.length=correction.length)
    (hn : target.Nodup) (hf : f ∉ target)
    (hclean : s f=false) (hp : p<2^target.length)
    (hx : boolWordToNat constant<p) (hy : boolWordToNat (wireValues target s)<p)
    (hcorrection : boolWordToNat correction=2^target.length-p) :
    boolWordToNat (wireValues target (uncontrolledConstantModularAddIdealState target constant correction p f s))=
      (boolWordToNat (wireValues target s)+boolWordToNat constant)%p ∧
    ∀ w, w ∉ target → uncontrolledConstantModularAddIdealState target constant correction p f s w=s w := by
  let low := gidneyUncontrolledAddIdealState target constant s
  let carried := upd low f (Bool.xor (low f) (decide (boolWordToNat (wireValues target low)<boolWordToNat constant)))
  let flagged := upd carried f (Bool.xor (carried f) (decide (p≤boolWordToNat (wireValues target carried))))
  let mid := gidneyAddIdealState target correction f flagged
  have hl := gidneyUncontrolledAddIdealState_correct target constant s hk hn
  have hlf : low f=false := (hl.2 f hf).trans hclean
  have hcw : wireValues target carried=wireValues target low := word_upd_outside target low f _ hf
  have hfw : wireValues target flagged=wireValues target low := (word_upd_outside target carried f _ hf).trans hcw
  let total := boolWordToNat (wireValues target s)+boolWordToNat constant
  let flag := Bool.xor (decide (2^target.length≤total)) (decide (p≤total%2^target.length))
  have hflag : flagged f=flag := by
    simp only [flagged,upd_same,hcw]
    simp only [carried,upd_same]
    rw [hlf,hl.1]
    simp only [Bool.false_xor]
    have ho := constantAddition_overflow (2^target.length) p _ _ true hp hx hy
    simp only [Bool.true_and,if_true] at ho
    rw [ho]
  have hm := gidneyAddIdealState_correct target correction f flagged hr hn
  have hmath := modularCorrection_correct (2^target.length) p (boolWordToNat constant)
    (boolWordToNat (wireValues target s)) true hp hx hy
  simp only [Bool.true_and,if_true] at hmath
  have hmvalue : boolWordToNat (wireValues target mid)=total%p := by
    rw [hm.1,hfw,hl.1,hflag,hcorrection]
    exact hmath.1
  have hmflag : mid f=flag := (hm.2 f hf).trans hflag
  have hclear : Bool.xor (mid f) (decide (boolWordToNat (wireValues target mid)<boolWordToNat constant))=false := by
    rw [hmflag,hmvalue]
    have hh := hmath.2.2
    rw [hmath.1] at hh
    simpa only [Bool.true_and] using hh
  change boolWordToNat (wireValues target (upd mid f _))=_ ∧ ∀ w, w ∉ target → upd mid f _ w=s w
  rw [hclear]
  constructor
  · rw [word_upd_outside target mid f false hf,hmvalue]
  · intro w hw
    by_cases he : w=f
    · subst w
      simp only [upd_same,hclean]
    · have hh := hm.2 w hw
      have hlw := hl.2 w hw
      rw [upd_other _ _ _ he]
      calc
        mid w=flagged w := hh
        _=low w := by simp only [flagged,carried,upd,if_neg he]
        _=s w := hlw



def uncontrolledConstantModularAdd (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (c r t f : Wire) : Quantum.AdaptiveCircuit :=
  (gidneyAddConst target (dirty.take (target.length-1)) constant c r t).seq
    ((gidneyCompareLT target dirty (boolWordToNat constant) c r t f).seq
      ((gidneyCompareGE target dirty p c r t f).seq
        ((controlledGidneyAddConst target (dirty.take (target.length-1)) correction f c r t).seq
          (gidneyCompareLT target dirty (boolWordToNat constant) c r t f))))

private theorem uncontrolledConstant_layout (target dirty : List Wire) (c r t f : Wire)
    (hnd : ([c,r,t,f]++target++dirty).Nodup) :
    ([c,r,t]++target++dirty.take (target.length-1)).Nodup ∧
    ([f,c,r,t]++target++dirty.take (target.length-1)).Nodup ∧
    ([c,r,t,f]++target++dirty).Nodup := by
  let q := ([c,r,t,f]++target++dirty).sum+1
  have hq : q ∉ [c,r,t,f]++target++dirty := by
    intro h
    exact (Nat.not_succ_le_self _) (List.le_sum_of_mem h)
  have hh := constantModular_layout target dirty q c r t f (List.nodup_cons.mpr ⟨hq,hnd⟩)
  exact ⟨(List.nodup_cons.mp hh.1).2,hh.2⟩

theorem uncontrolledConstantModularAdd_wellFormed (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (c r t f : Wire) (hk : target.length=constant.length) (hr : target.length=correction.length)
    (hd : target.length=dirty.length) (hne : 0<target.length)
    (hnd : ([c,r,t,f]++target++dirty).Nodup) :
    (uncontrolledConstantModularAdd target dirty constant correction p c r t f).WellFormed := by
  have hl := uncontrolledConstant_layout target dirty c r t f hnd
  have ht : target.length=(dirty.take (target.length-1)).length+1 := by simp only [List.length_take]; omega
  exact (gidneyAddConst_wellFormed target _ constant c r t hk ht hl.1).seq
    ((gidneyCompareLT_wellFormed target dirty _ c r t f hd hnd).seq
      ((gidneyCompareGE_wellFormed target dirty p c r t f hd hl.2.2).seq
        ((controlledGidneyAddConst_wellFormed target _ correction f c r t hr ht hl.2.1).seq
          (gidneyCompareLT_wellFormed target dirty _ c r t f hd hnd))))

theorem uncontrolledConstantModularAdd_branch_correct (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (c r t f : Wire) (s : BasisState)
    (hk : target.length=constant.length) (hr : target.length=correction.length)
    (hd : target.length=dirty.length) (hne : 0<target.length)
    (hnd : ([c,r,t,f]++target++dirty).Nodup)
    (hc : s c=false) (hr0 : s r=false) (ht0 : s t=false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (uncontrolledConstantModularAdd target dirty constant correction p c r t f).run) :
    branch.kraus (Quantum.ket s)=Quantum.registerXResetMagnitude branch.history.length •
      Quantum.ket (uncontrolledConstantModularAddIdealState target constant correction p f s) := by
  have hl := uncontrolledConstant_layout target dirty c r t f hnd
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by simp only [List.length_take]; omega
  have hn := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  have hnot (w : Wire) (hw : w ∈ [c,r,t,f]) : w ∉ target := by
    intro h; exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 w hw w h rfl
  have hcf : c≠f := by intro h; subst c; simp at hnd
  have hrf : r≠f := by intro h; subst r; simp at hnd
  have htf : t≠f := by intro h; subst t; simp at hnd
  let low := gidneyUncontrolledAddIdealState target constant s
  let carried := upd low f (Bool.xor (low f) (decide (boolWordToNat (wireValues target low)<boolWordToNat constant)))
  let flagged := upd carried f (Bool.xor (carried f) (decide (p≤boolWordToNat (wireValues target carried))))
  let mid := gidneyAddIdealState target correction f flagged
  have hlow (w : Wire) (hw : w ∉ target) : low w=s w := (gidneyUncontrolledAddIdealState_correct target constant s hk hn).2 w hw
  have hcarried (w : Wire) (hw : w ∉ target) (hf : w≠f) : carried w=s w := by
    simp only [carried,upd,if_neg hf,hlow w hw]
  have hflagged (w : Wire) (hw : w ∉ target) (hf : w≠f) : flagged w=s w := by
    simp only [flagged,upd,if_neg hf,hcarried w hw hf]
  have hmid (w : Wire) (hw : w ∉ target) (hf : w≠f) : mid w=s w :=
    ((gidneyAddIdealState_correct target correction f flagged hr hn).2 w hw).trans (hflagged w hw hf)
  apply horner_seq_branch _ _ s low _ ?_ ?_ branch hb
  · intro b hb
    exact gidneyAddConst_branch_correct target _ constant c r t s hk htake hl.1 hc hr0 ht0 b hb
  · intro b hb
    apply horner_seq_branch _ _ low carried _ ?_ ?_ b hb
    · intro b hb
      have hh := gidneyCompareLT_branch_correct target dirty _ c r t f low hd hnd
        ((hlow c (hnot c (by simp))).trans hc) ((hlow r (hnot r (by simp))).trans hr0)
        ((hlow t (hnot t (by simp))).trans ht0) b hb
      rw [hh.1]; exact hh.2
    · intro b hb
      apply horner_seq_branch _ _ carried flagged _ ?_ ?_ b hb
      · intro b hb
        have hh := gidneyCompareGE_branch_correct target dirty p c r t f carried hd hl.2.2
          ((hcarried c (hnot c (by simp)) hcf).trans hc) ((hcarried r (hnot r (by simp)) hrf).trans hr0)
          ((hcarried t (hnot t (by simp)) htf).trans ht0) b hb
        rw [hh.1]; exact hh.2
      · intro b hb
        apply horner_seq_branch _ _ flagged mid _ ?_ ?_ b hb
        · intro b hb
          have hh := controlledGidneyAddConst_branch_correct target _ correction f c r t flagged hr htake hl.2.1
            ((hflagged c (hnot c (by simp)) hcf).trans hc) ((hflagged r (hnot r (by simp)) hrf).trans hr0)
            ((hflagged t (hnot t (by simp)) htf).trans ht0) b hb
          rw [hh.1]; exact hh.2
        · intro b hb
          have hh := gidneyCompareLT_branch_correct target dirty _ c r t f mid hd hnd
            ((hmid c (hnot c (by simp)) hcf).trans hc) ((hmid r (hnot r (by simp)) hrf).trans hr0)
            ((hmid t (hnot t (by simp)) htf).trans ht0) b hb
          rw [hh.1]; exact hh.2
end ShorECDLP.Paper2607_13816
