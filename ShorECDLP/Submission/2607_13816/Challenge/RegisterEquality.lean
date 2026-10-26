import ShorECDLP.Submission.«2607_13816».Challenge.EndpointSwap
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP

def xorWordCircuit (cells : List (Wire × Wire)) : Circuit :=
  cells.map fun c => .CX c.1 c.2

def xorSeparated (cells : List (Wire × Wire)) : Prop :=
  ∀ c ∈ cells, ∀ d ∈ cells, d.1 ≠ c.2

theorem xorWordCircuit_frame (cells : List (Wire × Wire)) (st : BasisState) (w : Wire)
    (hw : ∀ c ∈ cells, w ≠ c.2) : Classical.run (xorWordCircuit cells) st w = st w := by
  induction cells generalizing st with
  | nil => rfl
  | cons c cs ih =>
    change Classical.run (xorWordCircuit cs) (Classical.applyGate (.CX c.1 c.2) st) w = _
    rw [ih _ (fun d hd => hw d (by simp [hd]))]
    exact upd_other st c.2 _ (hw c (by simp))

theorem xorWordCircuit_bit (cells : List (Wire × Wire))
    (hs : xorSeparated cells) (hn : (cells.map Prod.snd).Nodup)
    (st : BasisState) (c : Wire × Wire) (hc : c ∈ cells) :
    Classical.run (xorWordCircuit cells) st c.2 = xor (st c.2) (st c.1) := by
  induction cells generalizing st with
  | nil => simp at hc
  | cons d ds ih =>
    have hd : d ∈ d :: ds := by simp
    have htail : xorSeparated ds := fun e he f hf => hs e (by simp [he]) f (by simp [hf])
    have hnd := List.nodup_cons.mp hn
    change Classical.run (xorWordCircuit ds) (st[d.2 ↦ xor (st d.2) (st d.1)]) c.2 = _
    rcases List.mem_cons.mp hc with hcd | hc
    · subst c
      rw [xorWordCircuit_frame]
      · exact upd_same _ _ _
      · intro e he heq
        exact hnd.1 (List.mem_map.mpr ⟨e, he, heq.symm⟩)
    · rw [ih htail hnd.2 _ hc]
      have ht : c.2 ≠ d.2 := by
        intro heq
        exact hnd.1 (List.mem_map.mpr ⟨c, hc, heq⟩)
      simp only [upd_other _ _ _ ht, upd_other _ _ _ (hs d hd c (by simp [hc]))]

theorem xorWordCircuit_twice (cells : List (Wire × Wire))
    (hs : xorSeparated cells) (hn : (cells.map Prod.snd).Nodup) (st : BasisState) :
    Classical.run (xorWordCircuit cells) (Classical.run (xorWordCircuit cells) st) = st := by
  funext w
  by_cases hw : ∃ c ∈ cells, c.2 = w
  · obtain ⟨c, hc, rfl⟩ := hw
    rw [xorWordCircuit_bit cells hs hn _ c hc, xorWordCircuit_bit cells hs hn st c hc,
      xorWordCircuit_frame cells st c.1 (fun d hd => hs d hd c hc)]
    cases st c.1 <;> cases st c.2 <;> rfl
  · have hout : ∀ c ∈ cells, w ≠ c.2 := by
      intro c hc he; exact hw ⟨c, hc, he.symm⟩
    rw [xorWordCircuit_frame cells _ w hout, xorWordCircuit_frame cells st w hout]


def xorWordSupport (cells : List (Wire × Wire)) : List Wire :=
  cells.flatMap fun c => [c.1, c.2]

theorem xorWordCircuit_usesOnly (cells : List (Wire × Wire)) :
    PaperCircuitUsesOnly (xorWordSupport cells) (xorWordCircuit cells) := by
  intro g hg w hw
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
  apply List.mem_flatMap.mpr
  exact ⟨c, hc, hw⟩

def pairEqual (cells : List (Wire × Wire)) (st : BasisState) : Bool :=
  cells.all fun c => st c.1 == st c.2

theorem registerMatchesFrom_xor (cells : List (Wire × Wire)) (bit : Nat)
    (st after : BasisState)
    (h : ∀ c ∈ cells, after c.2 = xor (st c.2) (st c.1)) :
    registerMatchesFrom (cells.map Prod.snd) 0 bit after = pairEqual cells st := by
  induction cells generalizing bit with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, registerMatchesFrom, h c (by simp),
      Nat.zero_testBit, pairEqual, List.all_cons]
    rw [ih (bit+1) (fun d hd => h d (by simp [hd]))]
    cases st c.1 <;> cases st c.2 <;> rfl

def registerEqualCircuit (cells : List (Wire × Wire)) (flag : Wire) (scratch : List Wire) : Circuit :=
  xorWordCircuit cells ++ computeEqConst (cells.map Prod.snd) 0 flag scratch ++ xorWordCircuit cells

theorem registerEqualCircuit_run (cells : List (Wire × Wire)) (flag : Wire)
    (scratch : List Wire) (st : BasisState)
    (hs : xorSeparated cells) (hn : (cells.map Prod.snd).Nodup)
    (hl : EqConstLayout (cells.map Prod.snd) flag scratch)
    (hf : flag ∉ xorWordSupport cells)
    (hsc : ∀ w ∈ scratch, w ∉ xorWordSupport cells)
    (hclean : Clean scratch st) :
    Classical.run (registerEqualCircuit cells flag scratch) st =
      st[flag ↦ xor (st flag) (pairEqual cells st)] := by
  have huses := xorWordCircuit_usesOnly cells
  have hc : Clean scratch (Classical.run (xorWordCircuit cells) st) := by
    intro w hw
    rw [huses.preservesOutside st (hsc w hw)]
    exact hclean w hw
  have hm : registerMatches (cells.map Prod.snd) 0
      (Classical.run (xorWordCircuit cells) st) = pairEqual cells st :=
    registerMatchesFrom_xor cells 0 st _ (xorWordCircuit_bit cells hs hn st)
  simp only [registerEqualCircuit, Classical.run_append]
  rw [run_computeEqConst _ 0 flag scratch _ hl hc, hm,
    huses.run_upd_outside flag _ _ hf, xorWordCircuit_twice cells hs hn st,
    huses.preservesOutside st hf]


theorem xorWordCircuit_HPFree (cells : List (Wire × Wire)) : Classical.HPFree (xorWordCircuit cells) := by
  intro g hg
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
  trivial

theorem coherentSequenceCircuits
    {first second : Quantum.AdaptiveCircuit} {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : Quantum.CoherentlyImplementsOn first (Quantum.run firstCircuit) FirstValid)
    (hsecond : Quantum.CoherentlyImplementsOn second (Quantum.run secondCircuit) SecondValid)
    (hclassical : Classical.HPFree firstCircuit)
    (hvalid : ∀ st, FirstValid st → SecondValid (Classical.run firstCircuit st)) :
    Quantum.CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have h := hfirst.seq hsecond (by
    intro st hs
    rw [Quantum.run_ket_agrees_classical firstCircuit st hclassical]
    exact Quantum.supportedOn_ket SecondValid _ (hvalid st hs))
  apply h.congrIdeal
  intro st _
  exact (Quantum.run_append firstCircuit secondCircuit (Quantum.ket st)).symm

open Quantum ShorECDLP.Challenge

def registerEqualAdaptive (cells : List (Wire × Wire)) (flag : Wire) (scratch : List Wire) : AdaptiveCircuit :=
  .unitary (xorWordCircuit cells)
    ((computeEqConstAdaptive (cells.map Prod.snd) 0 flag scratch).seq (.unitary (xorWordCircuit cells) .done))

theorem registerEqualAdaptive_coherent (cells : List (Wire × Wire)) (flag : Wire) (scratch : List Wire)
    (hl : EqConstLayout (cells.map Prod.snd) flag scratch)
    (hsc : ∀ w ∈ scratch, w ∉ xorWordSupport cells) :
    CoherentlyImplementsOn (registerEqualAdaptive cells flag scratch)
      (Quantum.run (registerEqualCircuit cells flag scratch)) (Clean scratch) := by
  have hclean : ∀ st, Clean scratch st → Clean scratch (Classical.run (xorWordCircuit cells) st) := by
    intro st hc w hw
    rw [(xorWordCircuit_usesOnly cells).preservesOutside st (hsc w hw)]
    exact hc w hw
  have hfirst := coherentSequenceCircuits
    (CoherentlyImplementsOn.unitary (xorWordCircuit cells) (Clean scratch))
    (computeEqConstAdaptive_coherent (cells.map Prod.snd) 0 flag scratch hl)
    (xorWordCircuit_HPFree cells) hclean
  have hall := coherentSequenceCircuits hfirst
    (CoherentlyImplementsOn.unitary (xorWordCircuit cells) (fun _ => True))
    ((Classical.hpFree_append _ _).mpr ⟨xorWordCircuit_HPFree cells, computeEqConst_HPFree _ _ _ _⟩)
    (fun _ _ => trivial)
  simpa only [registerEqualAdaptive, registerEqualCircuit, AdaptiveCircuit.seq] using hall

def registerEqualProgram (n start : Nat) (cells : List (Wire × Wire)) (flag : Wire) (scratch : List Wire) :
    (count : Nat) × Straight n start (start+count) :=
  surroundCompiled (xorWordCircuit cells) (xorWordCircuit cells)
    (equalityProgram n start (cells.map Prod.snd) 0 flag scratch)

theorem registerEqualProgram_run (n start : Nat) (cells : List (Wire × Wire)) (flag : Wire)
    (scratch : List Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (registerEqualProgram n start cells flag scratch) read history =
      (registerEqualAdaptive cells flag scratch).run := by
  exact surroundCompiled_run _ _ _ _ read history (equalityProgram_run n start _ 0 flag scratch read history)

theorem registerEqualProgram_tCount (n start : Nat) (cells : List (Wire × Wire)) (flag : Wire)
    (scratch : List Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (registerEqualProgram n start cells flag scratch) read history =
      (registerEqualAdaptive cells flag scratch).tCount := by
  exact surroundCompiled_tCount _ _ _ _ read history (equalityProgram_tCount n start _ 0 flag scratch read history)

end ShorECDLP.Paper2607_13816.ChallengeMigration
