import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
namespace ShorECDLP.Paper2607_13816
open Classical
/-- A controlled flip selected by two register equalities, reusing one equality
flag and its clean v-chain scratch across all three selectors. -/
def twoRegisterControlledFlip (q target f g : Wire) (A B : List Wire)
    (a b : Nat) (scratch : List Wire) : Circuit :=
  let first := toggleEqConstUnderControl q A a f g scratch
  (first ++ toggleEqConstUnderControl f B b target g scratch) ++ first
private theorem matches_upd (R : List Wire) (v : Nat) (s : BasisState) (w : Wire) (b : Bool)
    (hw : w ∉ R) : registerMatches R v s[w ↦ b]=registerMatches R v s :=
  registerMatchesFrom_upd_not_mem R v 0 s w b hw

theorem run_twoRegisterControlledFlip (q target f g : Wire) (A B : List Wire)
    (a b : Nat) (scratch : List Wire) (s : BasisState)
    (hA : EqControlLayout q A f g scratch)
    (hB : EqControlLayout f B target g scratch)
    (htA : target ∉ A) (htq : target≠q)
    (hc : Clean (f::g::scratch) s) :
    run (twoRegisterControlledFlip q target f g A B a b scratch) s=
      s[target ↦ Bool.xor (s target) ((s q && registerMatches A a s) && registerMatches B b s)] := by
  have hq : q ∉ f::A++g::scratch := (List.nodup_cons.mp hA.2).1
  have hfA : f ∉ A++g::scratch := (List.nodup_cons.mp (List.nodup_cons.mp hA.2).2).1
  have hfB : f ∉ target::B++g::scratch := (List.nodup_cons.mp hB.2).1
  have ht : target ∉ B++g::scratch := (List.nodup_cons.mp (List.nodup_cons.mp hB.2).2).1
  have hqf : q≠f := by intro h; exact hq (by simp [h])
  have htf : target≠f := by intro h; exact hfB (by simp [h])
  have hfg : f≠g := by intro h; exact hfA (by simp [h])
  have htg : target≠g := by intro h; exact ht (by simp [h])
  have hfAn : f ∉ A := by intro h; exact hfA (by simp [h])
  have hfBn : f ∉ B := by intro h; exact hfB (by simp [h])
  have hfS : f ∉ scratch := by intro h; exact hfA (by simp [h])
  have htS : target ∉ scratch := by intro h; exact ht (by simp [h])
  let hit := s q && registerMatches A a s
  let s₁ := s[f ↦ hit]
  let value := Bool.xor (s target) (hit && registerMatches B b s)
  let s₂ := s₁[target ↦ value]
  have hc₀ : Clean (g::scratch) s := by intro w hw; exact hc w (by simp [hw])
  have hc₁ : Clean (g::scratch) s₁ := by
    intro w hw
    have hne : w≠f := by intro h; subst w; simp [hfg,hfS] at hw
    simpa [s₁,upd,hne] using hc₀ w hw
  have hc₂ : Clean (g::scratch) s₂ := by
    intro w hw
    have hne : w≠target := by intro h; subst w; simp [htg,htS] at hw
    simpa [s₂,upd,hne] using hc₁ w hw
  have h₁ : run (toggleEqConstUnderControl q A a f g scratch) s=s₁ := by
    rw [run_toggleEqConstUnderControl q A a f g scratch s hA hc₀]
    simp [s₁,hit,hc f (by simp)]
  have h₂ : run (toggleEqConstUnderControl f B b target g scratch) s₁=s₂ := by
    rw [run_toggleEqConstUnderControl f B b target g scratch s₁ hB hc₁]
    simp only [value,s₂,s₁,matches_upd B b s f hit hfBn,upd_same,upd_other s f hit htf]
  have h₃ : run (toggleEqConstUnderControl q A a f g scratch) s₂=s[target ↦ value] := by
    rw [run_toggleEqConstUnderControl q A a f g scratch s₂ hA hc₂]
    have hm : registerMatches A a s₂=registerMatches A a s := by
      dsimp only [s₂]
      rw [matches_upd A a s₁ target value htA]
      exact matches_upd A a s f hit hfAn
    rw [hm]
    funext w
    by_cases hwf : w=f
    · subst w; simp [s₂,s₁,upd,Ne.symm htf,hc f (by simp),hit,hqf,Ne.symm htq]
    · by_cases hwt : w=target
      · subst w; simp [s₂,s₁,upd,htf]
      · simp [s₂,s₁,upd,hwf,hwt]
  rw [twoRegisterControlledFlip,run_append,run_append,h₁,h₂,h₃]
theorem twoRegisterControlledFlip_HPFree (q target f g : Wire) (A B : List Wire)
    (a b : Nat) (scratch : List Wire) :
    HPFree (twoRegisterControlledFlip q target f g A B a b scratch) := by
  simp [twoRegisterControlledFlip]
theorem twoRegisterControlledFlip_wellFormed (q target f g : Wire) (A B : List Wire)
    (a b : Nat) (scratch : List Wire)
    (hA : EqControlLayout q A f g scratch) (hB : EqControlLayout f B target g scratch) :
    CircuitWellFormed (twoRegisterControlledFlip q target f g A B a b scratch) := by
  simp only [twoRegisterControlledFlip,circuitWellFormed_append]
  exact ⟨⟨toggleEqConstUnderControl_wellFormed q A a f g scratch hA,
    toggleEqConstUnderControl_wellFormed f B b target g scratch hB⟩,
    toggleEqConstUnderControl_wellFormed q A a f g scratch hA⟩
theorem twoRegisterControlledFlip_usesOnly (q target f g : Wire) (A B : List Wire)
    (a b : Nat) (scratch : List Wire) :
    PaperCircuitUsesOnly (q::target::f::g::A++B++scratch)
      (twoRegisterControlledFlip q target f g A B a b scratch) := by
  have hA := (toggleEqConstUnderControl_usesOnly q A a f g scratch).mono
    (show q::f::A++g::scratch ⊆ q::target::f::g::A++B++scratch by
      intro w hw; simp only [List.mem_cons,List.mem_append] at hw ⊢; aesop)
  have hB := (toggleEqConstUnderControl_usesOnly f B b target g scratch).mono
    (show f::target::B++g::scratch ⊆ q::target::f::g::A++B++scratch by
      intro w hw; simp only [List.mem_cons,List.mem_append] at hw ⊢; aesop)
  exact (hA.append hB).append hA
theorem twoRegisterControlledFlip_tCount (q target f g : Wire) (A B : List Wire)
    (a b : Nat) (scratch : List Wire)
    (hA : A.length-2≤scratch.length) (hB : B.length-2≤scratch.length) :
    ShorECDLP.tCount (twoRegisterControlledFlip q target f g A B a b scratch)=
      28*mcxVChainToffoliCost A.length+14*mcxVChainToffoliCost B.length+21 := by
  simp only [twoRegisterControlledFlip,tCount_append,
    toggleEqConstUnderControl_tCount q A a f g scratch hA,
    toggleEqConstUnderControl_tCount f B b target g scratch hB]
  omega
end ShorECDLP.Paper2607_13816
