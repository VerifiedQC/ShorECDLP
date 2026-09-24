import ShorECDLP.Submission.«2607_13816».Window.StreamKernel
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
/-- All arithmetic precedes the two mathematical Fourier rows; the path labels
still store the original chronological measurement records. -/
def streamTwoKernelBody (left right : List (Nat × AdaptiveCircuit)) (tail : AdaptiveCircuit) : Instrument :=
  (streamArithmeticPaths left .done).flatMap (fun l =>
    (streamArithmeticPaths right tail).map (fun r =>
      ⟨l.history ++ r.history,
        (measuredFourierKernel .inverse (streamFourierWires right) r.fourierBits).comp
          ((measuredFourierKernel .inverse (streamFourierWires left) l.fourierBits).comp
            (r.arithmetic.comp l.arithmetic))⟩))

theorem deferredTwoAxis_kernel (left right : List (Nat × AdaptiveCircuit)) (tail : AdaptiveCircuit)
    (hl : (left.map Prod.fst).Nodup) (hr : (right.map Prod.fst).Nodup)
    (hd : ∀ l ∈ left, ∀ r ∈ right, l.1 ≠ r.1)
    (hc : ∀ r ∈ right, r.2.wires ⊆ streamAllocation)
    (ht : ∀ w ∈ streamFourierWires left, w ∉ tail.wires) :
    (deferredStreamAxis left List.nil .done).seq (deferredStreamAxis right List.nil tail) =
      streamTwoKernelBody left right tail := by
  rw [deferredStreamAxis_measuredKernel left .done hl, deferredStreamAxis_measuredKernel right tail hr]
  simp only [Instrument.seq, streamTwoKernelBody, List.flatMap_map, List.map_map]
  apply List.flatMap_congr
  intro l hleft
  apply List.map_congr_left
  intro r hright
  have he : ∀ ψ, r.arithmetic
      (measuredFourierKernel .inverse (streamFourierWires left) l.fourierBits ψ) =
      measuredFourierKernel .inverse (streamFourierWires left) l.fourierBits (r.arithmetic ψ) := by
    rw [← fourierBranch_eq_kernel _ _ (streamFourierWires_nodup left hl) _
      (streamArithmeticPaths_length left .done l hleft)]
    apply streamArithmeticPath_fourier_commute right tail .inverse _ List.nil _ _ ht r hright
    intro c hcr w hw
    obtain ⟨d, hdl, hw⟩ := List.mem_flatMap.mp hw
    exact streamRelabel_bank_disjoint c.2 (hc c hcr) c.1 d.1 (hd d hdl c hcr)
      w (List.mem_reverse.mp hw)
  simp only [Function.comp_apply, InstrumentBranch.seq]
  congr 1
  apply LinearMap.ext
  intro ψ
  simp only [LinearMap.comp_apply, he]
end
end ShorECDLP.Paper2607_13816
