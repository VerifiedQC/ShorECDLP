import ShorECDLP.Submission.Arithmetic.Contracts
import ShorECDLP.Submission.Arithmetic.RippleAdder

/-
# Reusable clean reversible-circuit primitives

This module contains the small, implementation-neutral leaves shared by the arithmetic
milestones: aligned register copying, circuit-support composition, and cancellation of a
well-formed H/P-free circuit by its reverse.  Keeping them here prevents the modular
multiplication and exponentiation layers from growing divergent local copies.
-/

namespace ShorECDLP
namespace Arithmetic

open Classical

theorem Clean.mono {xs ys : List Wire} {st : BasisState} (h : Clean xs st)
    (hsub : ∀ w ∈ ys, w ∈ xs) : Clean ys st := by
  intro w hw
  exact h w (hsub w hw)

theorem Clean.regValue_eq_zero {ws : List Wire} {st : BasisState} (h : Clean ws st) :
    regValue ws st = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      rw [regValue_cons, h w (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem w hx))]
      simp

theorem AgreesOn.regValue {ws : List Wire} {before after : BasisState}
    (h : AgreesOn ws before after) : regValue ws after = regValue ws before :=
  regValue_congr ws after before h

/-- CNOT-copy aligned source bits into a clean destination register. -/
def copyReg : List Wire → List Wire → Circuit
  | s :: src, d :: dst => Gate.CX s d :: copyReg src dst
  | _, _ => []

@[simp]
theorem copyReg_tCount (src dst : List Wire) : tCount (copyReg src dst) = 0 := by
  induction src generalizing dst with
  | nil => simp [copyReg]
  | cons s src ih =>
      cases dst with
      | nil => simp [copyReg]
      | cons d dst => simp [copyReg, ih, tCost]

@[simp]
theorem copyReg_HPFree (src dst : List Wire) : HPFree (copyReg src dst) := by
  induction src generalizing dst with
  | nil => simp [copyReg]
  | cons s src ih =>
      cases dst with
      | nil => simp [copyReg]
      | cons d dst => simp [copyReg, ih]

theorem copyReg_usesOnly (src dst ws : List Wire)
    (hsrc : ∀ w ∈ src, w ∈ ws) (hdst : ∀ w ∈ dst, w ∈ ws) :
    CircuitUsesOnly ws (copyReg src dst) := by
  intro g hg
  induction src generalizing dst with
  | nil => simp [copyReg] at hg
  | cons s src ih =>
      cases dst with
      | nil => simp [copyReg] at hg
      | cons d dst =>
          simp only [copyReg, List.mem_cons] at hg
          cases hg with
          | inl heq =>
              subst g
              exact ⟨hsrc s (List.mem_cons_self ..), hdst d (List.mem_cons_self ..)⟩
          | inr htail =>
              exact ih dst (fun w hw => hsrc w (List.mem_cons_of_mem _ hw))
                (fun w hw => hdst w (List.mem_cons_of_mem _ hw)) htail

/-- Copying changes only destination wires. -/
theorem copyReg_other (w : Wire) :
    ∀ (src dst : List Wire) (st : BasisState), w ∉ dst →
      run (copyReg src dst) st w = st w := by
  intro src
  induction src with
  | nil => intro dst st _; simp [copyReg]
  | cons s src ih =>
      intro dst st hw
      cases dst with
      | nil => simp [copyReg]
      | cons d dst =>
          simp only [List.mem_cons, not_or] at hw
          rw [copyReg, run_cons, ih dst (applyGate (Gate.CX s d) st) hw.2]
          exact upd_other st d (Bool.xor (st d) (st s)) hw.1

/-- CNOT-copy correctness on duplicate-free, disjoint aligned registers. -/
theorem copyReg_correct :
    ∀ (src dst : List Wire) (st : BasisState),
      dst.length = src.length → (src ++ dst).Nodup → Clean dst st →
      regValue dst (run (copyReg src dst) st) = regValue src st := by
  intro src
  induction src with
  | nil =>
      intro dst st hlen _ _
      have : dst = [] := List.length_eq_zero_iff.mp hlen
      subst dst
      rfl
  | cons s src ih =>
      intro dst st hlen hnd hclean
      cases dst with
      | nil => simp at hlen
      | cons d dst =>
          have hlenTail : dst.length = src.length := by simpa using hlen
          obtain ⟨hsrcNd, hdstNd, hcross⟩ := List.nodup_append.mp hnd
          obtain ⟨_, hsrcTailNd⟩ := List.nodup_cons.mp hsrcNd
          obtain ⟨hdDst, hdstTailNd⟩ := List.nodup_cons.mp hdstNd
          have htailNd : (src ++ dst).Nodup := List.nodup_append.mpr
            ⟨hsrcTailNd, hdstTailNd,
              fun a ha b hb => hcross a (List.mem_cons_of_mem s ha) b (List.mem_cons_of_mem d hb)⟩
          have hdSrc : d ∉ src := by
            intro hd
            exact (hcross d (List.mem_cons_of_mem s hd) d (List.mem_cons_self ..)) rfl
          let st₁ := applyGate (Gate.CX s d) st
          have hcleanTail : Clean dst st₁ := by
            intro w hw
            change st[d ↦ Bool.xor (st d) (st s)] w = false
            have hwd : w ≠ d := by
              intro e
              subst w
              exact hdDst hw
            rw [upd_other _ _ _ hwd]
            exact hclean w (List.mem_cons_of_mem d hw)
          have hih := ih dst st₁ hlenTail htailNd hcleanTail
          have hsrcKeep : regValue src st₁ = regValue src st := by
            exact regValue_upd_not_mem src st d (Bool.xor (st d) (st s)) hdSrc
          have hdFinal : run (copyReg src dst) st₁ d = st s := by
            rw [copyReg_other d src dst st₁ hdDst]
            simp [st₁, applyGate, hclean d (List.mem_cons_self ..)]
          rw [copyReg, run_cons, regValue_cons, hdFinal, hih, hsrcKeep, regValue_cons]

theorem copyReg_wellFormed :
    ∀ (src dst : List Wire), (src ++ dst).Nodup → CircuitWellFormed (copyReg src dst) := by
  intro src
  induction src with
  | nil => intro dst _; simp [copyReg]
  | cons s src ih =>
      intro dst hnd
      cases dst with
      | nil => simp [copyReg]
      | cons d dst =>
          obtain ⟨hsrcNd, hdstNd, hcross⟩ := List.nodup_append.mp hnd
          obtain ⟨_, hsrcTailNd⟩ := List.nodup_cons.mp hsrcNd
          obtain ⟨_, hdstTailNd⟩ := List.nodup_cons.mp hdstNd
          have htailNd : (src ++ dst).Nodup := List.nodup_append.mpr
            ⟨hsrcTailNd, hdstTailNd,
              fun a ha b hb => hcross a (List.mem_cons_of_mem s ha) b (List.mem_cons_of_mem d hb)⟩
          rw [copyReg, circuitWellFormed_cons]
          exact ⟨hcross s (List.mem_cons_self ..) d (List.mem_cons_self ..), ih dst htailNd⟩

theorem usesOnly_append {ws : List Wire} {c₁ c₂ : Circuit}
    (h₁ : CircuitUsesOnly ws c₁) (h₂ : CircuitUsesOnly ws c₂) :
    CircuitUsesOnly ws (c₁ ++ c₂) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h₁ g hg
  · exact h₂ g hg

theorem usesOnly_mono {xs ys : List Wire} {c : Circuit}
    (h : CircuitUsesOnly xs c) (hsub : ∀ w ∈ xs, w ∈ ys) : CircuitUsesOnly ys c := by
  intro g hg
  have hgate := h g hg
  cases g <;> simp_all [Gate.UsesOnly]

theorem usesOnly_reverse {ws : List Wire} {c : Circuit}
    (h : CircuitUsesOnly ws c) : CircuitUsesOnly ws c.reverse := by
  intro g hg
  exact h g (by simpa using hg)

theorem hpFree_reverse {c : Circuit} (h : HPFree c) : HPFree c.reverse := by
  intro g hg
  exact h g (by simpa using hg)

theorem wellFormed_reverse {c : Circuit} (h : CircuitWellFormed c) :
    CircuitWellFormed c.reverse := by
  intro g hg
  exact h g (by simpa using hg)

theorem tCount_reverse (c : Circuit) : tCount c.reverse = tCount c := by
  simp [tCount]

/-- A circuit's values on its declared support depend only on the initial values there. -/
theorem CircuitUsesOnly.run_congr {ws : List Wire} {c : Circuit}
    (hc : CircuitUsesOnly ws c) {st₁ st₂ : BasisState}
    (hst : ∀ w ∈ ws, st₁ w = st₂ w) :
    ∀ w ∈ ws, run c st₁ w = run c st₂ w := by
  induction c generalizing st₁ st₂ with
  | nil => exact hst
  | cons g c ih =>
      rw [run_cons, run_cons]
      apply ih (fun g' hg' => hc g' (List.mem_cons_of_mem g hg'))
      intro w hw
      have hg := hc g (List.mem_cons_self ..)
      cases g with
      | X t =>
          simp only [Gate.UsesOnly] at hg
          by_cases hwt : w = t
          · subst w
            simp [applyGate, upd, hst t hg]
          · simp [applyGate, upd, hwt, hst w hw]
      | H _ => exact hst w hw
      | CX control target =>
          simp only [Gate.UsesOnly] at hg
          by_cases hwt : w = target
          · subst w
            simp [applyGate, upd, hst target hg.2, hst control hg.1]
          · simp [applyGate, upd, hwt, hst w hw]
      | CCX control₁ control₂ target =>
          simp only [Gate.UsesOnly] at hg
          by_cases hwt : w = target
          · subst w
            simp [applyGate, upd, hst target hg.2.2, hst control₁ hg.1,
              hst control₂ hg.2.1]
          · simp [applyGate, upd, hwt, hst w hw]
      | P _ _ => exact hst w hw

/-- A well-formed classical primitive gate is self-inverse. -/
theorem applyGate_twice (g : Gate) (st : BasisState)
    (hc : IsClassicalGate g) (hwf : g.WellFormed) : applyGate g (applyGate g st) = st := by
  funext w
  cases g with
  | X t =>
      by_cases h : w = t
      · subst w; simp [applyGate, upd]
      · simp [applyGate, upd, h]
  | H _ => simp at hc
  | CX c t =>
      by_cases h : w = t
      · subst w
        simp only [Gate.WellFormed] at hwf
        simp [applyGate, upd, hwf]
      · simp [applyGate, upd, h]
  | CCX a b t =>
      by_cases h : w = t
      · subst w
        simp only [Gate.WellFormed] at hwf
        simp [applyGate, upd, hwf]
      · simp [applyGate, upd, h]
  | P _ _ => simp at hc

/-- Reversing a well-formed H/P-free circuit cancels its classical action. -/
theorem run_reverse_cancel (c : Circuit) (st : BasisState)
    (hc : HPFree c) (hwf : CircuitWellFormed c) : run c.reverse (run c st) = st := by
  induction c generalizing st with
  | nil => rfl
  | cons g c ih =>
      simp only [hpFree_cons] at hc
      simp only [circuitWellFormed_cons] at hwf
      rw [run_cons, List.reverse_cons, run_append]
      rw [ih (applyGate g st) hc.2 hwf.2]
      simpa [run_cons, run_nil] using applyGate_twice g st hc.1 hwf.1

end Arithmetic
end ShorECDLP
