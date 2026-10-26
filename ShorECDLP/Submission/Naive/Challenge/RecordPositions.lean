import ShorECDLP.Submission.Naive.Challenge.RepeatedEntry

namespace ShorECDLP.NaiveChallenge
open Quantum Challenge

/-- Reading consecutive absolute positions equals decoding the corresponding slice. -/
theorem readWord_range (history : List Bool) (start width : Nat)
    (h : start + width ≤ history.length) :
    readWord history (List.range' start width) =
      some (bitsValue ((history.drop start).take width)) := by
  induction width generalizing start with
  | zero => simp [readWord, bitsValue]
  | succ width ih =>
    have hs : start < history.length := by omega
    have ht : start + 1 + width ≤ history.length := by omega
    rw [List.range'_succ, readWord, List.getElem?_eq_getElem hs, ih (start+1) ht]
    rw [List.drop_eq_getElem_cons hs]
    simp only [List.take_succ_cons, bitsValue]
    rfl

/-- The repeated success flag selects an actual absolute round slice. -/
theorem repeatFailed_success_iff (width count : Nat) (accept : List Bool → Bool)
    (history : List Bool) :
    (!repeatFailed width accept count history) = true ↔
      ∃ t < count, accept ((history.drop (t*width)).take width) = true := by
  induction count generalizing history with
  | zero => simp [repeatFailed]
  | succ count ih =>
    simp only [repeatFailed, Bool.not_and, Bool.not_not, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact ⟨0, by omega, by simpa using h⟩
      · refine ⟨t+1, by omega, ?_⟩
        simpa only [List.drop_drop, Nat.add_mul, Nat.one_mul, Nat.add_comm] using h
    · rintro ⟨t, ht, h⟩
      cases t with
      | zero => left; simpa using h
      | succ t =>
        right
        refine ⟨t, by omega, ?_⟩
        simpa only [List.drop_drop, Nat.succ_mul, Nat.add_comm] using h

theorem fixedRepeatedSuccess_iff (d : Nat) (history : List Bool) :
    fixedRepeatedSuccess d history = true ↔
      ∃ t : Fin 26, naiveEvent d ((history.drop (repeatedSampleStart t)).take 512) = true := by
  rw [fixedRepeatedSuccess, repeatFailed_success_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨⟨t, ht⟩, by simpa [repeatedSampleStart, List.take_take] using h⟩
  · rintro ⟨t, h⟩
    exact ⟨t.val, t.isLt, by simpa [repeatedSampleStart, List.take_take] using h⟩

def repeatedDecoderParams : DecoderParams := ⟨256, 256, by omega, by omega, by omega, by omega⟩

def repeatedTrialPositions (t : Fin 26) : TrialPositions repeatedDecoderParams where
  left := ⟨(List.range' (repeatedSampleStart t) 256).toArray, by simp [repeatedDecoderParams]⟩
  right := ⟨(List.range' (repeatedSampleStart t + 256) 256).toArray, by simp [repeatedDecoderParams]⟩

theorem repeatedTrialPositions_read (history : List Bool) (hl : history.length = 5385536)
    (t : Fin 26) :
    readWord history (repeatedTrialPositions t).left.toList =
      some (bitsValue ((history.drop (repeatedSampleStart t)).take 256)) ∧
    readWord history (repeatedTrialPositions t).right.toList =
      some (bitsValue ((history.drop (repeatedSampleStart t + 256)).take 256)) := by
  have ht := t.isLt
  have hs : repeatedSampleStart t + 512 ≤ history.length := by
    dsimp only [repeatedSampleStart]
    omega
  simp only [repeatedTrialPositions, Vector.toList, List.toList_toArray]
  exact ⟨readWord_range history _ _ (by omega), readWord_range history _ _ (by omega)⟩

theorem naiveRepeatedEntry_history_length (Q : Secp256k1.Point)
    (ho : order • Q = 0) (b : InstrumentBranch)
    (hb : b ∈ (naiveRepeatedEntry.instantiate Q).run) : b.history.length = 5385536 := by
  rw [naiveRepeatedEntry_run Q ho] at hb
  exact fixedRepeated_history_length Q b hb

/-- A successful branch supplies actual words at the fixed absolute decoder positions. -/
theorem fixedRepeatedSuccess_actualWords (d : Nat) (history : List Bool)
    (hl : history.length = 5385536) (hs : fixedRepeatedSuccess d history = true) :
    ∃ t : Fin 26, ∃ left right : Nat,
      readWord history (repeatedTrialPositions t).left.toList = some left ∧
      readWord history (repeatedTrialPositions t).right.toList = some right ∧
      recoveredPair d left right = true := by
  obtain ⟨t, ht⟩ := (fixedRepeatedSuccess_iff d history).mp hs
  obtain ⟨ha, hb⟩ := repeatedTrialPositions_read history hl t
  refine ⟨t, _, _, ha, hb, ?_⟩
  simpa only [naiveEvent, pairEvent, List.take_take, List.drop_take, List.drop_drop,
    Nat.min_eq_left (by omega : 256 ≤ 512), show 512-256=256 from rfl] using ht

end ShorECDLP.NaiveChallenge
