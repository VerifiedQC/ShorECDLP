import ShorECDLP.Submission.«2607_13816».Window.RawDeferred
import ShorECDLP.Submission.«2607_13816».Fourier.Kernel
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
/-- Concatenating measured registers retains feedback from the first output. -/
theorem fourierBranch_append (dir : PhaseDir) (xs ys : List Wire)
    (prior bs cs : List Bool) (hl : bs.length = xs.length) :
    fourierBranch dir (xs++ys) prior (bs++cs) =
      (fourierBranch dir ys (bs.reverse++prior) cs).comp (fourierBranch dir xs prior bs) := by
  induction xs generalizing prior bs with
  | nil =>
    have he : bs = [] := List.length_eq_zero_iff.mp hl
    subst bs
    simp [fourierBranch]
  | cons w ws ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.cons_append, fourierBranch]
      rw [ih (b::prior) bs (by simpa using hl)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append, LinearMap.comp_assoc]

/-- Fixed Fourier branches on disjoint registers commute, even with distinct
already-fixed classical feedback. -/
theorem fourierBranch_disjoint_commute (dir dir' : PhaseDir) (xs ys : List Wire)
    (prior prior' bs cs : List Bool) (hl : cs.length=ys.length) (hd : List.Disjoint xs ys)
    (ψ : State) :
    fourierBranch dir' ys prior' cs (fourierBranch dir xs prior bs ψ) =
      fourierBranch dir xs prior bs (fourierBranch dir' ys prior' cs ψ) := by
  have hs : (semiclassicalFourier dir' ys prior').wires ⊆ ys := by
    rw [← fourierContinue_done]
    exact fourierContinue_support dir' ys prior' (fun _ => .done) ys
      (by intro w hw; exact hw) (by simp [AdaptiveCircuit.wires])
  apply adaptiveBranch_fourier_commute (semiclassicalFourier dir' ys prior') dir xs prior bs
    (by intro w hw hm; exact List.disjoint_left.mp hd hw (hs hm))
    ⟨cs, fourierBranch dir' ys prior' cs⟩
  rw [semiclassicalFourier_run]
  exact List.mem_map.mpr ⟨cs, (fourierOutcomes_mem _ _).mpr hl, rfl⟩

/-- The physical measurement order is MSB-first within each successive bank. -/
def streamFourierWires (calls : List (Nat × AdaptiveCircuit)) : List Wire :=
  calls.flatMap (fun c => (List.range' (windowBankStart c.1) 16).reverse)

/-- A path keeps Fourier bits separate while retaining the chronological full
record. Its map contains arithmetic and the final tail, but no Fourier maps. -/
structure StreamArithmeticPath where
  fourierBits : List Bool
  history : List Bool
  arithmetic : State →ₗ[ℂ] State

def streamArithmeticPaths : List (Nat × AdaptiveCircuit) → AdaptiveCircuit → List StreamArithmeticPath
  | [], tail => tail.run.map (fun b => ⟨[], b.history, b.kraus⟩)
  | (k,call)::calls, tail =>
    (call.relabel (streamBankPerm k)).run.flatMap (fun a =>
      (fourierOutcomes 16).flatMap (fun bs =>
        (streamArithmeticPaths calls tail).map (fun next =>
          ⟨bs ++ next.fourierBits, a.history ++ bs ++ next.history, next.arithmetic.comp a.kraus⟩)))

theorem streamArithmeticPaths_length (calls : List (Nat × AdaptiveCircuit)) (tail : AdaptiveCircuit)
    (p : StreamArithmeticPath) (hp : p ∈ streamArithmeticPaths calls tail) :
    p.fourierBits.length = (streamFourierWires calls).length := by
  induction calls generalizing p with
  | nil =>
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    rfl
  | cons c calls ih =>
    obtain ⟨a, ha, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨bs, hbs, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hp
    have hl := (fourierOutcomes_mem 16 bs).mp hbs
    simpa only [streamFourierWires, List.flatMap_cons, List.length_append,
      List.length_reverse, List.length_range', hl] using congrArg (16+·) (ih next hn)

private theorem bank_disjoint (i j : Nat) (h : i≠j) :
    List.Disjoint (List.range' (windowBankStart i) 16).reverse
      (List.range' (windowBankStart j) 16).reverse := by
  apply List.disjoint_left.mpr
  intro w hw hv
  simp only [List.mem_reverse, List.mem_range'_1, windowBankStart] at hw hv
  omega

/-- Every deferred path is one contiguous Fourier branch after its arithmetic
map. The tag is the actual Fourier output subsequence, not arithmetic outcomes. -/
theorem deferredStreamAxis_kernel (calls : List (Nat × AdaptiveCircuit))
    (prior : List Bool) (tail : AdaptiveCircuit) (hd : (calls.map Prod.fst).Nodup) :
    deferredStreamAxis calls prior tail =
      (streamArithmeticPaths calls tail).map (fun p =>
        ⟨p.history, (fourierBranch .inverse (streamFourierWires calls) prior p.fourierBits).comp p.arithmetic⟩) := by
  induction calls generalizing prior with
  | nil => simp [deferredStreamAxis, streamArithmeticPaths, streamFourierWires, Function.comp_def, fourierBranch]
  | cons c calls ih =>
    have hn := List.nodup_cons.mp hd
    simp only [deferredStreamAxis, streamArithmeticPaths, List.map_flatMap, List.map_map]
    apply List.flatMap_congr
    intro a ha
    apply List.flatMap_congr
    intro bs hbs
    rw [ih (bs.reverse++prior) hn.2]
    simp only [List.map_map]
    apply List.map_congr_left
    intro next hnext
    have hl : bs.length = (List.range' (windowBankStart c.1) 16).reverse.length := by
      simpa only [List.length_reverse, List.length_range'] using (fourierOutcomes_mem 16 bs).mp hbs
    have hdis : List.Disjoint (List.range' (windowBankStart c.1) 16).reverse (streamFourierWires calls) := by
      apply List.disjoint_left.mpr
      intro w hw hv
      obtain ⟨d, hd, hv⟩ := List.mem_flatMap.mp hv
      apply List.disjoint_left.mp (bank_disjoint c.1 d.1 _) hw hv
      intro he
      exact hn.1 (List.mem_map.mpr ⟨d, hd, he.symm⟩)
    simp only [Function.comp_apply, streamFourierWires, List.flatMap_cons]
    rw [fourierBranch_append _ _ _ _ _ _ hl]
    congr 1
    apply LinearMap.ext
    intro ψ
    simp only [LinearMap.comp_apply]
    exact (fourierBranch_disjoint_commute .inverse .inverse _ _ prior (bs.reverse++prior)
      bs next.fourierBits (streamArithmeticPaths_length calls tail next hnext) hdis _).symm

theorem streamFourierWires_nodup (calls : List (Nat × AdaptiveCircuit))
    (hd : (calls.map Prod.fst).Nodup) : (streamFourierWires calls).Nodup := by
  induction calls with
  | nil => simp [streamFourierWires]
  | cons c calls ih =>
    have hn := List.nodup_cons.mp hd
    rw [streamFourierWires, List.flatMap_cons, List.nodup_append]
    refine ⟨by simpa only [List.nodup_reverse] using (List.nodup_range' (s:=windowBankStart c.1) (n:=16)), ih hn.2, ?_⟩
    intro w hw v hv he
    subst v
    obtain ⟨d, hd, hv⟩ := List.mem_flatMap.mp hv
    apply List.disjoint_left.mp (bank_disjoint c.1 d.1 _) hw hv
    intro he
    exact hn.1 (List.mem_map.mpr ⟨d, hd, he.symm⟩)

/-- Identify the contiguous branch with the mathematical Fourier row, preserving
all amplitudes before taking probabilities. -/
theorem deferredStreamAxis_measuredKernel (calls : List (Nat × AdaptiveCircuit))
    (tail : AdaptiveCircuit) (hd : (calls.map Prod.fst).Nodup) :
    deferredStreamAxis calls List.nil tail =
      (streamArithmeticPaths calls tail).map (fun p =>
        ⟨p.history, (measuredFourierKernel .inverse (streamFourierWires calls) p.fourierBits).comp p.arithmetic⟩) := by
  rw [deferredStreamAxis_kernel calls List.nil tail hd]
  apply List.map_congr_left
  intro p hp
  rw [fourierBranch_eq_kernel _ _ (streamFourierWires_nodup calls hd) _
    (streamArithmeticPaths_length calls tail p hp)]

/-- Arithmetic paths retain commutation with a disjoint measured register. -/
theorem streamArithmeticPath_fourier_commute (calls : List (Nat × AdaptiveCircuit))
    (tail : AdaptiveCircuit) (dir : PhaseDir) (ws : List Wire) (prior bs : List Bool)
    (hc : ∀ c ∈ calls, ∀ w ∈ ws, w ∉ (c.2.relabel (streamBankPerm c.1)).wires)
    (ht : ∀ w ∈ ws, w ∉ tail.wires)
    (p : StreamArithmeticPath) (hp : p ∈ streamArithmeticPaths calls tail) (ψ : State) :
    p.arithmetic (fourierBranch dir ws prior bs ψ) =
      fourierBranch dir ws prior bs (p.arithmetic ψ) := by
  induction calls generalizing p ψ with
  | nil =>
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    exact adaptiveBranch_fourier_commute tail dir ws prior bs ht b hb ψ
  | cons c calls ih =>
    obtain ⟨a, ha, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨cs, hcs, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hp
    change next.arithmetic (a.kraus (fourierBranch _ _ _ _ ψ)) =
      fourierBranch _ _ _ _ (next.arithmetic (a.kraus ψ))
    rw [adaptiveBranch_fourier_commute _ dir ws prior bs (hc c (by simp)) a ha,
      ih (by intro d hd; exact hc d (by simp [hd])) next hn]

end
end ShorECDLP.Paper2607_13816
