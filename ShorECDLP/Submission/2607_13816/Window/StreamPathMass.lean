import ShorECDLP.Submission.«2607_13816».Window.PreparedEntry
import ShorECDLP.Submission.«2607_13816».Window.StreamRecords
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem outcomes_add (n m : Nat) : fourierOutcomes (n+m)=
    (fourierOutcomes n).flatMap (fun a => (fourierOutcomes m).map (fun b => a++b)) := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [Nat.succ_add,fourierOutcomes,ih,List.flatMap_append,List.flatMap_map,
      List.map_flatMap,List.map_map,Function.comp_def,List.cons_append]
private theorem sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → ℝ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    rw [List.sum_map_add]

private theorem flat_sum {α : Type} (xs : List α) (f : α → List ℝ) :
    (xs.flatMap f).sum=(xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons,ih]

/-- All relocated arithmetic calls, with Fourier outcomes omitted from the transcript. -/
def streamArithmeticBulk (calls : List (Nat × AdaptiveCircuit)) (tail : AdaptiveCircuit) : AdaptiveCircuit :=
  calls.foldr (fun c next => (c.2.relabel (streamBankPerm c.1)).seq next) tail

/-- Reorder finite path contributions without deduplicating any measurement branch. -/
theorem streamArithmeticPaths_sum (calls : List (Nat × AdaptiveCircuit)) (tail : AdaptiveCircuit)
    (f : List Bool → (State →ₗ[ℂ] State) → ℝ) :
    ((streamArithmeticPaths calls tail).map (fun p => f p.fourierBits p.arithmetic)).sum =
      ((streamArithmeticBulk calls tail).run.map (fun b =>
        ((fourierOutcomes (16*calls.length)).map (fun bs => f bs b.kraus)).sum)).sum := by
  induction calls generalizing f with
  | nil => simp [streamArithmeticPaths,streamArithmeticBulk,fourierOutcomes,List.map_map,Function.comp_def]
  | cons c calls ih =>
    simp only [streamArithmeticPaths,List.map_flatMap,List.map_map,flat_sum,
      streamArithmeticBulk,List.foldr_cons,AdaptiveCircuit.run_seq,Instrument.seq,List.length_cons]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_def]
    have hi (bs : List Bool) := ih (fun bits m => f (bs++bits) (m.comp a.kraus))
    simp only [streamArithmeticBulk] at hi
    simp_rw [hi]
    rw [sum_swap]
    simp only [InstrumentBranch.seq]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    rw [show 16*(calls.length+1)=16+16*calls.length by omega,outcomes_add]
    simp only [List.map_flatMap,List.map_map,flat_sum,Function.comp_def]

/-- Separate both Fourier output lists from the complete sequential arithmetic instrument. -/
theorem streamTwoArithmeticPaths_sum (left right : List (Nat × AdaptiveCircuit)) (tail : AdaptiveCircuit)
    (f : List Bool → List Bool → (State →ₗ[ℂ] State) → ℝ) :
    ((streamArithmeticPaths left .done).map (fun l =>
      ((streamArithmeticPaths right tail).map (fun r =>
        f l.fourierBits r.fourierBits (r.arithmetic.comp l.arithmetic))).sum)).sum =
    (((streamArithmeticBulk left .done).seq (streamArithmeticBulk right tail)).run.map (fun b =>
      ((fourierOutcomes (16*left.length)).map (fun ls =>
        ((fourierOutcomes (16*right.length)).map (fun rs => f ls rs b.kraus)).sum)).sum)).sum := by
  have hr (l : StreamArithmeticPath) := streamArithmeticPaths_sum right tail
    (fun rs m => f l.fourierBits rs (m.comp l.arithmetic))
  simp_rw [hr]
  rw [streamArithmeticPaths_sum left .done (fun ls m =>
    ((streamArithmeticBulk right tail).run.map (fun b =>
      ((fourierOutcomes (16*right.length)).map (fun rs => f ls rs (b.kraus.comp m))).sum)).sum)]
  simp only [AdaptiveCircuit.run_seq,Instrument.seq,List.map_flatMap,List.map_map,
    flat_sum,Function.comp_def,InstrumentBranch.seq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  exact sum_swap _ _ _

/-- Selected Fourier rows on an arbitrary unnormalized state. -/
def streamFourierKernelEventMass (P Q : Point) (accept : List Bool × List Bool → Bool)
    (ψ : State) : ℝ :=
  ((fourierOutcomes 256).map (fun ls => ((fourierOutcomes 208).map (fun rs =>
    if accept (ls,rs) then normSq (measuredFourierKernel .inverse
      (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) rs
      (measuredFourierKernel .inverse
        (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) ls ψ))
    else 0)).sum)).sum

/-- The actual record acceptance mass uses one fixed Fourier event after every
arithmetic branch. This is an exact rearrangement, not a positive success bound. -/
theorem streamRawFourierEventMass_bulk (P Q : Point) (accept : List Bool × List Bool → Bool) :
    streamRawFourierEventMass P Q accept =
    (((streamArithmeticBulk (indexedStreamCalls 1 (streamRawLeftCalls P Q)) .done).seq
      (streamArithmeticBulk (indexedStreamCalls 17 (streamRawRightCalls Q))
        (.unitary [.X 836] .done))).run.map (fun b =>
      streamFourierKernelEventMass P Q accept (b.kraus (streamPreparedEntry P Q)))).sum := by
  rw [streamRawFourierEventMass_paths]
  have h := streamTwoArithmeticPaths_sum (indexedStreamCalls 1 (streamRawLeftCalls P Q))
    (indexedStreamCalls 17 (streamRawRightCalls Q)) (.unitary [.X 836] .done)
    (fun ls rs m => if accept (ls,rs) then normSq (measuredFourierKernel .inverse
      (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) rs
      (measuredFourierKernel .inverse
        (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) ls
        (m (streamPreparedEntry P Q)))) else 0)
  simpa only [LinearMap.comp_apply,streamPreparedEntry,streamFourierKernelEventMass,indexedStreamCalls,
    List.length_map,List.length_zipIdx,streamRawLeftCalls,streamRawRightCalls,
    List.length_cons,List.length_reverse,List.length_range] using h
end
end ShorECDLP.Paper2607_13816
