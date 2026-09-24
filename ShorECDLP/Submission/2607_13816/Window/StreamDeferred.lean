import ShorECDLP.Submission.«2607_13816».Window.StreamFourierCommute
import ShorECDLP.Submission.«2607_13816».Fourier.Relabel
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
/-- Explicitly distinguish this block's Fourier results from arithmetic records. -/
theorem parkedStreamBody_run (call : AdaptiveCircuit) (k : Nat) (prior : List Bool) :
    (parkedStreamBody call k prior).run =
      (call.relabel (streamBankPerm k)).run.flatMap (fun a =>
        (fourierOutcomes 16).map (fun bs => InstrumentBranch.seq a
          ⟨bs, fourierBranch .inverse (List.range' (windowBankStart k) 16).reverse prior bs⟩)) := by
  simp only [parkedStreamBody, AdaptiveCircuit.relabel_seq, semiclassicalFourier_relabel,
    List.map_reverse, streamBankPerm_full, AdaptiveCircuit.run_seq, Instrument.seq,
    semiclassicalFourier_run, List.length_reverse, List.length_range', List.map_map, Function.comp_def]

/-- An algebraic instrument with the original chronological transcript but each
Fourier map moved after its remaining axis. This is not a new physical schedule. -/
def deferredStreamAxis : List (Nat × AdaptiveCircuit) → List Bool → AdaptiveCircuit → Instrument
  | [], _, tail => tail.run
  | (k,call)::calls, prior, tail =>
    (call.relabel (streamBankPerm k)).run.flatMap (fun a =>
      (fourierOutcomes 16).flatMap (fun bs =>
        (deferredStreamAxis calls (bs.reverse ++ prior) tail).map (fun next =>
          ⟨a.history ++ bs ++ next.history,
            (fourierBranch .inverse (List.range' (windowBankStart k) 16).reverse prior bs).comp
              (next.kraus.comp a.kraus)⟩)))

/-- Defer all Fourier maps across the actual remaining axis, preserving the
ordered full transcript and every Kraus map on arbitrary inputs. -/
theorem unpreparedStreamAxis_deferred (calls : List (Nat × AdaptiveCircuit))
    (prior : List Bool) (tail : AdaptiveCircuit) (hd : (calls.map Prod.fst).Nodup)
    (hc : ∀ c ∈ calls, c.2.wires ⊆ streamAllocation)
    (ht : ∀ c ∈ calls, ∀ w ∈ List.range' (windowBankStart c.1) 16, w ∉ tail.wires) :
    unpreparedStreamAxis calls prior tail = deferredStreamAxis calls prior tail := by
  induction calls generalizing prior with
  | nil => rfl
  | cons c calls ih =>
    have hn := List.nodup_cons.mp hd
    simp only [unpreparedStreamAxis, parkedStreamBody_run, List.flatMap_assoc,
      List.flatMap_map, deferredStreamAxis]
    apply List.flatMap_congr
    intro a ha
    apply List.flatMap_congr
    intro bs hbs
    have hl : bs.length = 16 := (fourierOutcomes_mem 16 bs).mp hbs
    have hh : (InstrumentBranch.seq a
        ⟨bs, fourierBranch .inverse (List.range' (windowBankStart c.1) 16).reverse prior bs⟩).history.reverse.take 16 = bs.reverse := by
      simp only [InstrumentBranch.seq, List.reverse_append]
      rw [← hl, ← List.length_reverse (as:=bs), List.take_left]
    rw [hh, ← ih (bs.reverse ++ prior) hn.2
      (by intro d hd; exact hc d (by simp [hd]))
      (by intro d hd; exact ht d (by simp [hd]))]
    apply List.map_congr_left
    intro next hnext
    simp only [InstrumentBranch.seq, List.append_assoc]
    congr 1
    apply LinearMap.ext
    intro ψ
    change next.kraus (fourierBranch _ _ _ _ (a.kraus ψ)) =
        fourierBranch _ _ _ _ (next.kraus (a.kraus ψ))
    apply unpreparedStreamAxis_fourier_commute calls (bs.reverse ++ prior) tail c.1
        (by intro d hd; exact hc d (by simp [hd])) _ (ht c (by simp))
        .inverse prior bs next hnext
    intro d hd he
    exact hn.1 (List.mem_map.mpr ⟨d, hd, he.symm⟩)
end
end ShorECDLP.Paper2607_13816
