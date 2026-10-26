import ShorECDLP.Submission.«2607_13816».Challenge.RegisterEquality
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

def equalityCells {n : Nat} (a target : Fin n → Wire) : List (Wire × Wire) :=
  List.ofFn fun i => (a i, target i)

theorem pairEqual_ofFn {n : Nat} (a target : Fin n → Wire) (st : BasisState) :
    pairEqual (equalityCells a target) st = decide (st ∘ target = st ∘ a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [pairEqual, equalityCells, List.all_eq_true, List.mem_ofFn,
    forall_exists_index, forall_apply_eq_imp_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    exact (h i).symm
  · intro h i
    exact (congrFun h i).symm

structure EndpointGeometry {n : Nat} (a b target : Fin n → Wire) (flag : Wire) (scratch : List Wire) : Prop where
  targetInjective : Function.Injective target
  inputsApart : ∀ i j, a i ≠ target j ∧ b i ≠ target j
  flagApart : ∀ i, flag ≠ a i ∧ flag ≠ b i ∧ flag ≠ target i
  equalityLayout : EqConstLayout (List.ofFn target) flag scratch
  scratchApart : ∀ w ∈ scratch, ∀ i, w ≠ a i ∧ w ≠ b i ∧ w ≠ target i

theorem equalityCells_run {n : Nat} (a target : Fin n → Wire) (flag : Wire)
    (scratch : List Wire) (st : BasisState)
    (ht : Function.Injective target) (hi : ∀ i j, a i ≠ target j)
    (hf : ∀ i, flag ≠ a i ∧ flag ≠ target i)
    (hl : EqConstLayout (List.ofFn target) flag scratch)
    (hsc : ∀ w ∈ scratch, ∀ i, w ≠ a i ∧ w ≠ target i)
    (hc : Clean scratch st) :
    Classical.run (registerEqualCircuit (equalityCells a target) flag scratch) st =
      st[flag ↦ xor (st flag) (decide (st ∘ target = st ∘ a))] := by
  have hs : xorSeparated (equalityCells a target) := by
    intro c hc d hd
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact hi i j
  have hm : (equalityCells a target).map Prod.snd = List.ofFn target := by
    simp only [equalityCells, List.map_ofFn]; rfl
  have hn : ((equalityCells a target).map Prod.snd).Nodup := by
    rw [hm]; exact List.nodup_ofFn.mpr ht
  have hout (w : Wire) (h : ∀ i, w ≠ a i ∧ w ≠ target i) :
      w ∉ xorWordSupport (equalityCells a target) := by
    intro hw
    obtain ⟨c, hc, hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, (h i).1, (h i).2] at hw
  rw [registerEqualCircuit_run _ flag scratch st hs hn (hm.symm ▸ hl)
    (hout flag hf) (fun w hw => hout w (hsc w hw)) hc, pairEqual_ofFn]

theorem word_update_outside {n : Nat} (row : Fin n → Wire) (st : BasisState)
    (flag : Wire) (value : Bool) (h : ∀ i, row i ≠ flag) :
    st[flag ↦ value] ∘ row = st ∘ row := by
  funext i
  exact upd_other st flag value (h i)

def endpointTests {n : Nat} (a b target : Fin n → Wire) (flag : Wire) (scratch : List Wire) : Circuit :=
  registerEqualCircuit (equalityCells a target) flag scratch ++
    registerEqualCircuit (equalityCells b target) flag scratch

theorem endpointTests_run {n : Nat} (a b target : Fin n → Wire) (flag : Wire)
    (scratch : List Wire) (g : EndpointGeometry a b target flag scratch)
    (st : BasisState) (hc : Clean scratch st) :
    Classical.run (endpointTests a b target flag scratch) st =
      st[flag ↦ xor (st flag) (endpointFlag (st ∘ a) (st ∘ b) (st ∘ target))] := by
  let first : Bool := xor (st flag) (decide (st ∘ target = st ∘ a))
  have hf : flag ∉ scratch := (List.nodup_cons.mp (List.nodup_append.mp g.equalityLayout.2).2.1).1
  have hclean : Clean scratch (st[flag ↦ first]) := by
    intro w hw
    rw [upd_other st flag first (by intro he; exact hf (he ▸ hw))]
    exact hc w hw
  have ha := equalityCells_run a target flag scratch st g.targetInjective
    (fun i j => (g.inputsApart i j).1)
    (fun i => ⟨(g.flagApart i).1, (g.flagApart i).2.2⟩) g.equalityLayout
    (fun w hw i => ⟨(g.scratchApart w hw i).1, (g.scratchApart w hw i).2.2⟩) hc
  have hb := equalityCells_run b target flag scratch (st[flag ↦ first]) g.targetInjective
    (fun i j => (g.inputsApart i j).2)
    (fun i => ⟨(g.flagApart i).2.1, (g.flagApart i).2.2⟩) g.equalityLayout
    (fun w hw i => ⟨(g.scratchApart w hw i).2.1, (g.scratchApart w hw i).2.2⟩) hclean
  rw [word_update_outside target st flag first (fun i => ((g.flagApart i).2.2).symm),
    word_update_outside b st flag first (fun i => ((g.flagApart i).2.1).symm), upd_same] at hb
  simp only [endpointTests, Classical.run_append]
  rw [ha]
  change Classical.run (registerEqualCircuit (equalityCells b target) flag scratch) (st[flag ↦ first]) = _
  rw [hb]
  funext w
  by_cases hw : w = flag
  · subst w
    simp only [upd_same, first, endpointFlag]
    cases st flag <;> cases (decide (st ∘ target = st ∘ a)) <;>
      cases (decide (st ∘ target = st ∘ b)) <;> rfl
  · simp only [upd_other _ _ _ hw]

def endpointUpdateCells {n : Nat} (a b target : Fin n → Wire) : List (Wire × Wire × Wire) :=
  List.ofFn fun i => (a i, b i, target i)

def endpointTranspositionCircuit {n : Nat} (a b target : Fin n → Wire) (flag : Wire) (scratch : List Wire) : Circuit :=
  endpointTests a b target flag scratch ++ endpointWordCircuit flag (endpointUpdateCells a b target) ++
    endpointTests a b target flag scratch

theorem endpointTransposition_correct {n : Nat} (a b target : Fin n → Wire) (flag : Wire)
    (scratch : List Wire) (g : EndpointGeometry a b target flag scratch)
    (st : BasisState) (hc : Clean scratch st) (hz : st flag = false) :
    let out := Classical.run (endpointTranspositionCircuit a b target flag scratch) st
    out ∘ target = Equiv.swap (st ∘ a) (st ∘ b) (st ∘ target) ∧
      out flag = false ∧ ∀ w, (∀ i, w ≠ target i) → out w = st w := by
  let guard := endpointFlag (st ∘ a) (st ∘ b) (st ∘ target)
  let ready := st[flag ↦ guard]
  let moved := Classical.run (endpointWordCircuit flag (endpointUpdateCells a b target)) ready
  have hr (row : Fin n → Wire) (h : ∀ i, flag ≠ row i) : ready ∘ row = st ∘ row :=
    word_update_outside row st flag guard (fun i => (h i).symm)
  have hra := hr a (fun i => (g.flagApart i).1)
  have hrb := hr b (fun i => (g.flagApart i).2.1)
  have hrt := hr target (fun i => (g.flagApart i).2.2)
  have hsep : endpointSeparated flag (endpointUpdateCells a b target) := by
    intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    refine ⟨(g.flagApart j).2.2, ?_⟩
    intro d hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact g.inputsApart i j
  have hguard : ready flag = endpointFlag (ready ∘ a) (ready ∘ b) (ready ∘ target) := by
    rw [hra, hrb, hrt]; exact upd_same _ _ _
  have ht := endpointWordCircuit_swap flag a b target ready hsep g.targetInjective hguard
  rw [hra, hrb, hrt] at ht
  change moved ∘ target = Equiv.swap (st ∘ a) (st ∘ b) (st ∘ target) at ht
  have hm (w : Wire) (h : ∀ i, w ≠ target i) : moved w = ready w := by
    apply endpointWordCircuit_frame
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact h i
  have hma : moved ∘ a = st ∘ a := by
    funext i
    change moved (a i) = st (a i)
    rw [show moved (a i) = ready (a i) from hm (a i) (fun j => (g.inputsApart i j).1)]
    exact congrFun hra i
  have hmb : moved ∘ b = st ∘ b := by
    funext i
    change moved (b i) = st (b i)
    rw [show moved (b i) = ready (b i) from hm (b i) (fun j => (g.inputsApart i j).2)]
    exact congrFun hrb i
  have hmf : moved flag = guard :=
    (hm flag (fun i => (g.flagApart i).2.2)).trans (upd_same _ _ _)
  have hfs : flag ∉ scratch :=
    (List.nodup_cons.mp (List.nodup_append.mp g.equalityLayout.2).2.1).1
  have hcm : Clean scratch moved := by
    intro w hw
    rw [hm w (fun i => (g.scratchApart w hw i).2.2),
      show ready w = st w from upd_other st flag guard (by intro he; exact hfs (he ▸ hw))]
    exact hc w hw
  have hfirst : Classical.run (endpointTests a b target flag scratch) st = ready := by
    rw [endpointTests_run a b target flag scratch g st hc, hz, Bool.false_xor]
  have hlast : Classical.run (endpointTests a b target flag scratch) moved = moved[flag ↦ false] := by
    rw [endpointTests_run a b target flag scratch g moved hcm, hma, hmb, ht, endpointFlag_swap, hmf]
    change moved[flag ↦ xor guard guard] = _
    rw [Bool.xor_self]
  simp only [endpointTranspositionCircuit, Classical.run_append, hfirst]
  change (Classical.run (endpointTests a b target flag scratch) moved) ∘ target = _ ∧ _
  rw [hlast]
  refine ⟨?_, upd_same _ _ _, ?_⟩
  · rw [word_update_outside target moved flag false (fun i => ((g.flagApart i).2.2).symm)]
    exact ht
  · intro w hw
    by_cases he : w = flag
    · subst w; rw [upd_same, hz]
    · rw [upd_other _ _ _ he, hm w hw]
      exact upd_other st flag guard he

theorem equalityCells_outside {n : Nat} (a target : Fin n → Wire) (w : Wire)
    (h : ∀ i, w ≠ a i ∧ w ≠ target i) : w ∉ xorWordSupport (equalityCells a target) := by
  intro hw
  obtain ⟨c, hc, hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  simp only [List.mem_cons, List.not_mem_nil, or_false, (h i).1, (h i).2] at hw

theorem registerEqualCircuit_HPFree (cells : List (Wire × Wire)) (flag : Wire) (scratch : List Wire) :
    Classical.HPFree (registerEqualCircuit cells flag scratch) := by
  simp only [registerEqualCircuit, Classical.hpFree_append, xorWordCircuit_HPFree,
    computeEqConst_HPFree, and_self]

def endpointTestsAdaptive {n : Nat} (a b target : Fin n → Wire) (flag : Wire) (scratch : List Wire) : AdaptiveCircuit :=
  (registerEqualAdaptive (equalityCells a target) flag scratch).seq
    (registerEqualAdaptive (equalityCells b target) flag scratch)

theorem endpointTests_HPFree {n : Nat} (a b target : Fin n → Wire) (flag : Wire) (scratch : List Wire) :
    Classical.HPFree (endpointTests a b target flag scratch) := by
  exact (Classical.hpFree_append _ _).mpr
    ⟨registerEqualCircuit_HPFree _ _ _, registerEqualCircuit_HPFree _ _ _⟩

theorem EndpointGeometry.flag_not_scratch {n : Nat} {a b target : Fin n → Wire} {flag : Wire}
    {scratch : List Wire} (g : EndpointGeometry a b target flag scratch) : flag ∉ scratch :=
  (List.nodup_cons.mp (List.nodup_append.mp g.equalityLayout.2).2.1).1

theorem endpointTests_coherent {n : Nat} (a b target : Fin n → Wire) (flag : Wire)
    (scratch : List Wire) (g : EndpointGeometry a b target flag scratch) :
    CoherentlyImplementsOn (endpointTestsAdaptive a b target flag scratch)
      (Quantum.run (endpointTests a b target flag scratch)) (Clean scratch) := by
  have hl (row : Fin n → Wire) : EqConstLayout ((equalityCells row target).map Prod.snd) flag scratch := by
    simpa only [equalityCells, List.map_ofFn] using g.equalityLayout
  have hA := registerEqualAdaptive_coherent (equalityCells a target) flag scratch (hl a)
    (fun w hw => equalityCells_outside a target w (fun i => ⟨(g.scratchApart w hw i).1, (g.scratchApart w hw i).2.2⟩))
  have hB := registerEqualAdaptive_coherent (equalityCells b target) flag scratch (hl b)
    (fun w hw => equalityCells_outside b target w (fun i => (g.scratchApart w hw i).2))
  apply coherentSequenceCircuits hA hB (registerEqualCircuit_HPFree _ _ _)
  intro st hc w hw
  rw [equalityCells_run a target flag scratch st g.targetInjective
    (fun i j => (g.inputsApart i j).1) (fun i => ⟨(g.flagApart i).1, (g.flagApart i).2.2⟩)
    g.equalityLayout (fun v hv i => ⟨(g.scratchApart v hv i).1, (g.scratchApart v hv i).2.2⟩) hc]
  rw [upd_other _ _ _ (by intro he; exact g.flag_not_scratch (he ▸ hw))]
  exact hc w hw

theorem endpointTests_clean {n : Nat} (a b target : Fin n → Wire) (flag : Wire)
    (scratch : List Wire) (g : EndpointGeometry a b target flag scratch)
    (st : BasisState) (hc : Clean scratch st) :
    Clean scratch (Classical.run (endpointTests a b target flag scratch) st) := by
  intro w hw
  rw [endpointTests_run a b target flag scratch g st hc,
    upd_other _ _ _ (by intro he; exact g.flag_not_scratch (he ▸ hw))]
  exact hc w hw

def endpointTranspositionAdaptive {n : Nat} (a b target : Fin n → Wire) (flag : Wire) (scratch : List Wire) : AdaptiveCircuit :=
  (endpointTestsAdaptive a b target flag scratch).seq
    (.unitary (endpointWordCircuit flag (endpointUpdateCells a b target))
      (endpointTestsAdaptive a b target flag scratch))

theorem endpointTransposition_coherent {n : Nat} (a b target : Fin n → Wire) (flag : Wire)
    (scratch : List Wire) (g : EndpointGeometry a b target flag scratch) :
    CoherentlyImplementsOn (endpointTranspositionAdaptive a b target flag scratch)
      (Quantum.run (endpointTranspositionCircuit a b target flag scratch)) (Clean scratch) := by
  have htests := endpointTests_coherent a b target flag scratch g
  have hupdate : ∀ st, Clean scratch st →
      Clean scratch (Classical.run (endpointWordCircuit flag (endpointUpdateCells a b target)) st) := by
    intro st hc w hw
    rw [endpointWordCircuit_frame]
    · exact hc w hw
    · intro c hc
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      exact (g.scratchApart w hw i).2.2
  have htail := coherentSequenceCircuits
    (CoherentlyImplementsOn.unitary (endpointWordCircuit flag (endpointUpdateCells a b target)) (Clean scratch))
    htests (endpointWordCircuit_HPFree _ _) hupdate
  have hall := coherentSequenceCircuits htests htail (endpointTests_HPFree _ _ _ _ _)
    (endpointTests_clean a b target flag scratch g)
  simpa only [endpointTranspositionAdaptive, endpointTranspositionCircuit,
    AdaptiveCircuit.seq, List.append_assoc] using hall

/-- The flag is computed twice around the word update; there is no data-dependent control flow. -/
def endpointTranspositionProgram {k : Nat} (n start : Nat)
    (a b target : Fin k → Wire) (flag : Wire) (scratch : List Wire) :
    (count : Nat) × Straight n start (start+count) :=
  let first := registerEqualProgram n start (equalityCells a target) flag scratch
  let second := registerEqualProgram n (start+first.1) (equalityCells b target) flag scratch
  let update := endpointWordCircuit flag (List.ofFn fun i => (a i, b i, target i))
  let prepared := appendCompiled first second
  let againA := registerEqualProgram n (start+prepared.1) (equalityCells a target) flag scratch
  let againB := registerEqualProgram n (start+prepared.1+againA.1) (equalityCells b target) flag scratch
  appendCompiled prepared (prependCompiled update (appendCompiled againA againB))


theorem endpointTranspositionProgram_run {k : Nat} (n start : Nat)
    (a b target : Fin k → Wire) (flag : Wire) (scratch : List Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (endpointTranspositionProgram n start a b target flag scratch) read history =
      (endpointTranspositionAdaptive a b target flag scratch).run := by
  unfold endpointTranspositionProgram endpointTranspositionAdaptive endpointTestsAdaptive
  dsimp only
  apply appendCompiled_run_eq
  · apply appendCompiled_run_eq
    · exact registerEqualProgram_run n start _ flag scratch read history
    · intro h
      exact registerEqualProgram_run n _ _ flag scratch read h
  · intro h
    apply prependCompiled_run_eq
    apply appendCompiled_run_eq
    · exact registerEqualProgram_run n _ _ flag scratch read h
    · intro hnext
      exact registerEqualProgram_run n _ _ flag scratch read hnext

theorem endpointTranspositionProgram_tCount {k : Nat} (n start : Nat)
    (a b target : Fin k → Wire) (flag : Wire) (scratch : List Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (endpointTranspositionProgram n start a b target flag scratch) read history =
      (endpointTranspositionAdaptive a b target flag scratch).tCount := by
  unfold endpointTranspositionProgram endpointTranspositionAdaptive endpointTestsAdaptive
  dsimp only
  apply appendCompiled_tCount_eq
  · apply appendCompiled_tCount_eq
    · exact registerEqualProgram_tCount n start _ flag scratch read history
    · intro h
      exact registerEqualProgram_tCount n _ _ flag scratch read h
  · intro h
    apply prependCompiled_tCount_eq
    apply appendCompiled_tCount_eq
    · exact registerEqualProgram_tCount n _ _ flag scratch read h
    · intro hnext
      exact registerEqualProgram_tCount n _ _ flag scratch read hnext

end ShorECDLP.Paper2607_13816.ChallengeMigration
