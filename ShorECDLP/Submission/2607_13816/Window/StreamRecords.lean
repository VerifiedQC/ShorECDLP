import ShorECDLP.Submission.«2607_13816».Window.RawKernel
import ShorECDLP.Submission.«2607_13816».Window.RawTerminal

namespace ShorECDLP.Paper2607_13816
open Quantum ShorECDLP.Secp256k1
noncomputable section

/-- Parse chronological records using the arithmetic branch tree, then the 16
Fourier measurements of each bank. Return the Fourier subsequence and suffix.
The tail's own measurements are consumed but never treated as Fourier bits. -/
def consumeStreamFourier : List (Nat × AdaptiveCircuit) → AdaptiveCircuit →
    List Bool → Option (List Bool × List Bool)
  | [], tail, hist => (consumeAdaptiveHistory tail hist).map (fun rest => ([], rest))
  | (k,call)::calls, tail, hist => do
    let rest ← consumeAdaptiveHistory (call.relabel (streamBankPerm k)) hist
    if 16 ≤ rest.length then
      let next ← consumeStreamFourier calls tail (rest.drop 16)
      return (rest.take 16 ++ next.1, next.2)
    else none

/-- Every enumerated path is parsed from its actual history, with arbitrary
suffix. No uniqueness or deduplication of paths is required. -/
theorem consumeStreamFourier_path (calls : List (Nat × AdaptiveCircuit))
    (tail : AdaptiveCircuit) (p : StreamArithmeticPath)
    (hp : p ∈ streamArithmeticPaths calls tail) (suffix : List Bool) :
    consumeStreamFourier calls tail (p.history ++ suffix) = some (p.fourierBits, suffix) := by
  induction calls generalizing p with
  | nil =>
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    simp only [consumeStreamFourier, consumeAdaptiveHistory_run tail b hb suffix, Option.map_some]
  | cons c calls ih =>
    obtain ⟨a, ha, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨bs, hbs, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨next, hn, rfl⟩ := List.mem_map.mp hp
    have hl := (fourierOutcomes_mem 16 bs).mp hbs
    simp only [consumeStreamFourier, List.append_assoc,
      consumeAdaptiveHistory_run _ a ha]
    dsimp only [Bind.bind, Option.bind]
    have hlen : 16 ≤ (bs ++ (next.history ++ suffix)).length := by
      simp only [List.length_append, hl]; omega
    rw [if_pos hlen]
    have ht : (bs ++ (next.history ++ suffix)).take 16 = bs := by
      rw [← hl, List.take_left]
    have hd : (bs ++ (next.history ++ suffix)).drop 16 = next.history ++ suffix := by
      rw [← hl, List.drop_left]
    rw [ht, hd, ih next hn]
    rfl

/-- Decode only the two Fourier subsequences of a complete actual trial record.
Malformed records (including an unconsumed suffix) are rejected. -/
def decodeStreamRawFourier (P Q : Point) (hist : List Bool) :
    Option (List Bool × List Bool) := do
  let left ← consumeStreamFourier (indexedStreamCalls 1 (streamRawLeftCalls P Q)) .done hist
  let right ← consumeStreamFourier (indexedStreamCalls 17 (streamRawRightCalls Q))
    (.unitary [.X 836] .done) left.2
  if right.2 = [] then return (left.1, right.1) else none

theorem decodeStreamRawFourier_paths (P Q : Point) (l r : StreamArithmeticPath)
    (hl : l ∈ streamArithmeticPaths (indexedStreamCalls 1 (streamRawLeftCalls P Q)) .done)
    (hr : r ∈ streamArithmeticPaths (indexedStreamCalls 17 (streamRawRightCalls Q))
      (.unitary [.X 836] .done)) :
    decodeStreamRawFourier P Q (l.history ++ r.history) = some (l.fourierBits, r.fourierBits) := by
  unfold decodeStreamRawFourier
  rw [consumeStreamFourier_path _ _ l hl r.history]
  dsimp only [Bind.bind, Option.bind]
  rw [show r.history = r.history ++ [] by simp, consumeStreamFourier_path _ _ r hr ([])]
  rfl

/-- A nonempty suffix after a complete record is rejected, rather than silently
ignored or passed to the public-point decoder. -/
theorem decodeStreamRawFourier_paths_trailing (P Q : Point) (l r : StreamArithmeticPath)
    (hl : l ∈ streamArithmeticPaths (indexedStreamCalls 1 (streamRawLeftCalls P Q)) .done)
    (hr : r ∈ streamArithmeticPaths (indexedStreamCalls 17 (streamRawRightCalls Q))
      (.unitary [.X 836] .done)) (suffix : List Bool) (hs : suffix ≠ []) :
    decodeStreamRawFourier P Q ((l.history ++ r.history) ++ suffix) = none := by
  unfold decodeStreamRawFourier
  rw [List.append_assoc, consumeStreamFourier_path _ _ l hl (r.history ++ suffix)]
  dsimp only [Bind.bind, Option.bind]
  rw [consumeStreamFourier_path _ _ r hr suffix]
  dsimp only [Bind.bind, Option.bind]
  exact if_neg hs

/-- Bit counts and order are those of the mathematical Fourier rows: the parser
returns the path bits unchanged, without reversing or mixing arithmetic bits. -/
theorem decodeStreamRawFourier_paths_lengths (P Q : Point) (l r : StreamArithmeticPath)
    (hl : l ∈ streamArithmeticPaths (indexedStreamCalls 1 (streamRawLeftCalls P Q)) .done)
    (hr : r ∈ streamArithmeticPaths (indexedStreamCalls 17 (streamRawRightCalls Q))
      (.unitary [.X 836] .done)) : l.fourierBits.length = 256 ∧ r.fourierBits.length = 208 := by
  exact ⟨(streamArithmeticPaths_length _ _ l hl).trans (streamRawKernel_precisions P Q).1,
    (streamArithmeticPaths_length _ _ r hr).trans (streamRawKernel_precisions P Q).2⟩

/-- Every actual trial branch has a well-formed decoding with the two promised
precisions. This uses the complete ordered instrument correspondence. -/
theorem streamRawTrial_decode (P Q : Point) (b : InstrumentBranch)
    (hb : b ∈ (streamRawTrial P Q).run) :
    ∃ left right, decodeStreamRawFourier P Q b.history = some (left, right) ∧
      left.length = 256 ∧ right.length = 208 := by
  have hm : (b.history, b.kraus (ket zeroBasisState)) ∈
      (streamRawTrial P Q).run.map (fun b => (b.history, b.kraus (ket zeroBasisState))) :=
    List.mem_map.mpr ⟨b, hb, rfl⟩
  rw [streamRawTrial_kernel P Q] at hm
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
  change k ∈ streamTwoKernelBody _ _ _ at hk
  obtain ⟨l, hl, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
  have hh := congrArg Prod.fst he
  change l.history ++ r.history = b.history at hh
  refine ⟨l.fourierBits, r.fourierBits, ?_, decodeStreamRawFourier_paths_lengths P Q l r hl hr⟩
  rw [← hh]
  exact decodeStreamRawFourier_paths P Q l r hl hr

/-- Acceptance is a predicate on the raw chronological record. -/
def streamRawHistoryAccept (P Q : Point) (accept : List Bool × List Bool → Bool)
    (hist : List Bool) : Bool := ((decodeStreamRawFourier P Q hist).map accept).getD false

theorem streamRawHistoryAccept_paths (P Q : Point) (accept : List Bool × List Bool → Bool)
    (l r : StreamArithmeticPath)
    (hl : l ∈ streamArithmeticPaths (indexedStreamCalls 1 (streamRawLeftCalls P Q)) .done)
    (hr : r ∈ streamArithmeticPaths (indexedStreamCalls 17 (streamRawRightCalls Q))
      (.unitary [.X 836] .done)) :
    streamRawHistoryAccept P Q accept (l.history ++ r.history) =
      accept (l.fourierBits, r.fourierBits) := by
  simp only [streamRawHistoryAccept, decodeStreamRawFourier_paths P Q l r hl hr,
    Option.map_some, Option.getD_some]

/-- Unconditional event mass of the actual 855-wire trial on zero input.
Filtering a list preserves all branch multiplicities, including equal histories. -/
def streamRawFourierEventMass (P Q : Point) (accept : List Bool × List Bool → Bool) : ℝ :=
  Instrument.bornMass ((streamRawTrial P Q).run.filter
    (fun b => streamRawHistoryAccept P Q accept b.history)) (ket zeroBasisState)

private theorem selected_sum {α : Type} (xs : List α) (accept : α → Bool) (f : α → ℝ) :
    ((xs.filter accept).map f).sum = (xs.map (fun x => if accept x then f x else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : accept x <;> simp [h, ih]

private theorem sum_flatMap {α : Type} (xs : List α) (f : α → List ℝ) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Exact path sum for any decoded event, with left then right Fourier output.
Every list occurrence contributes its own squared norm: neither histories nor
paths are deduplicated, and amplitudes of distinct measurement branches are not
added before squaring. No arithmetic-correctness hypothesis is needed here. -/
theorem streamRawFourierEventMass_paths (P Q : Point) (accept : List Bool × List Bool → Bool) :
    streamRawFourierEventMass P Q accept =
      ((streamArithmeticPaths (indexedStreamCalls 1 (streamRawLeftCalls P Q)) .done).map
        (fun l => ((streamArithmeticPaths (indexedStreamCalls 17 (streamRawRightCalls Q))
          (.unitary [.X 836] .done)).map (fun r =>
            if accept (l.fourierBits, r.fourierBits) then
              normSq (measuredFourierKernel .inverse
                (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) r.fourierBits
                (measuredFourierKernel .inverse
                  (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls P Q))) l.fourierBits
                  (r.arithmetic (l.arithmetic (Quantum.run (streamRawPreparation P Q)
                    (ket (scalarRootFlip zeroBasisState)))))))
            else 0)).sum)).sum := by
  have he := congrArg (fun (xs : List (List Bool × State)) =>
    ((xs.filter (fun x => streamRawHistoryAccept P Q accept x.1)).map
      (fun x => normSq x.2)).sum) (streamRawTrial_kernel P Q)
  simp only [List.filter_map, List.map_map, Function.comp_def] at he
  unfold streamRawFourierEventMass Instrument.bornMass
  rw [he, selected_sum]
  simp only [streamRawKernelBody, streamTwoKernelBody, List.map_flatMap,
    List.map_map, Function.comp_def, sum_flatMap, LinearMap.comp_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  rw [streamRawHistoryAccept_paths P Q accept l r hl hr]

/-- The existing public-point-checked mathematical decoder now consumes an
actual streaming record. This is a specification, not an efficient executable
classical decoder. -/
def streamRawPublicDecode (Q : Point) (hist : List Bool) : Option (ZMod order) :=
  (decodeStreamRawFourier G Q hist).bind (reducedRawPublicDecode Q)

/-- Accepted candidates are correct even for arbitrary supplied records. -/
theorem streamRawPublicDecode_sound (Q : Point) (d : Nat) (hQd : Q=d • G)
    (hist : List Bool) (c : ZMod order) (hc : streamRawPublicDecode Q hist = some c) :
    c = (d : ZMod order) := by
  unfold streamRawPublicDecode at hc
  cases he : decodeStreamRawFourier G Q hist with
  | none => simp [he] at hc
  | some bits =>
    simp only [he, Option.bind_some] at hc
    exact reducedRawPublicDecode_sound Q d hQd bits c hc

/-- The actual-history acceptance event is exactly public decoder acceptance. -/
theorem streamRawPublicDecode_accept (Q : Point) (hist : List Bool) :
    streamRawHistoryAccept G Q (reducedRawDecoderAccept Q) hist =
      (streamRawPublicDecode Q hist).isSome := by
  unfold streamRawHistoryAccept streamRawPublicDecode
  cases decodeStreamRawFourier G Q hist <;> rfl

/-- On a promised public point, the same event means return of the correct scalar. -/
theorem streamRawPublicDecode_correct (Q : Point) (d : Nat) (hQd : Q=d • G)
    (hist : List Bool) :
    streamRawHistoryAccept G Q (reducedRawDecoderAccept Q) hist = true ↔
      streamRawPublicDecode Q hist = some (d : ZMod order) := by
  rw [streamRawPublicDecode_accept]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
    rw [streamRawPublicDecode_sound Q d hQd hist c hc] at hc
    exact hc
  · intro h
    simp [h]

/-- The event mass used by the path-sum theorem is exactly acceptance by the
public-point decoder on actual trial records, not on auxiliary path labels. -/
theorem streamRawPublicDecode_eventMass (Q : Point) :
    Instrument.bornMass ((streamRawTrial G Q).run.filter
      (fun b => (streamRawPublicDecode Q b.history).isSome)) (ket zeroBasisState) =
      streamRawFourierEventMass G Q (reducedRawDecoderAccept Q) := by
  unfold streamRawFourierEventMass
  simp only [streamRawPublicDecode_accept]

end
end ShorECDLP.Paper2607_13816
