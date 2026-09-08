import ShorECDLP.Submission.«2607_13816».EEA.RouteBounds

/-! # Operational invariant for the terminal EEA suffix -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
local notation "R" => indexedStepProductionRegisters
attribute [local irreducible] indexedStepUnitary indexedStepRoutedState

/-- Terminal boundary encoding after the stated number of padding steps. It is an
entry condition here; reaching the first terminal boundary requires active-phase refinement. -/
structure Secp256k1TerminalState (padding : Nat) (state : BasisState) : Prop where
  ready : IndexedStepReady R state
  epochEncoded : IndexedStepEpochEncoded R state
  phase1 : state (R).phase1 = false
  phase2 : state (R).phase2 = false
  remainder : wireAnd (R).lengthRPrime state = true
  low : boolWordToNat (wireValues (R).lengthS state) = terminalShiftLow padding
  epoch : state (R).shiftEpoch = terminalShiftEpoch padding

private theorem terminal_source_raw (padding : Nat) (hp : padding ≤ 596) :
    terminalShiftLow padding + 512 * (terminalShiftEpoch padding).toNat = (511 + padding) % 1024 := by
  by_cases h : 1 ≤ padding ∧ padding ≤ 512
  · rw [show terminalShiftEpoch padding = true from decide_eq_true h]
    simp only [terminalShiftLow, Bool.toNat_true, Nat.mul_one]
    omega
  · rw [show terminalShiftEpoch padding = false from decide_eq_false h]
    simp only [terminalShiftLow, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    omega
private theorem terminal_source_next (padding : Nat) (hp : padding < 596) :
    (1 + terminalShiftLow padding) % 512 = terminalShiftLow (padding + 1) ∧
    Bool.xor (terminalShiftEpoch padding) (decide ((1 + terminalShiftLow padding) % 512 = 0)) =
      terminalShiftEpoch (padding + 1) := by
  constructor
  · simp only [terminalShiftLow]; omega
  · by_cases h0 : padding = 0
    · subst padding; decide
    by_cases hlt : padding < 512
    · have h1 : 1 ≤ padding ∧ padding ≤ 512 := by omega
      have h2 : 1 ≤ padding + 1 ∧ padding + 1 ≤ 512 := by omega
      have hn : (1 + terminalShiftLow padding) % 512 ≠ 0 := by simp only [terminalShiftLow]; omega
      rw [show terminalShiftEpoch padding = true from decide_eq_true h1,
        show terminalShiftEpoch (padding + 1) = true from decide_eq_true h2]
      simp [hn]
    by_cases he : padding = 512
    · subst padding; decide
    have h1 : ¬(1 ≤ padding ∧ padding ≤ 512) := by omega
    have h2 : ¬(1 ≤ padding + 1 ∧ padding + 1 ≤ 512) := by omega
    have hn : (1 + terminalShiftLow padding) % 512 ≠ 0 := by simp only [terminalShiftLow]; omega
    rw [show terminalShiftEpoch padding = false from decide_eq_false h1,
      show terminalShiftEpoch (padding + 1) = false from decide_eq_false h2]
    simp [hn]
private theorem counter_horizon (modulus steps : Nat) (hmod : 0 < modulus)
    (hsteps : steps + 1 < 2 * modulus) :
    (1 + ((modulus - 1 + steps) % (2 * modulus))) % (2 * modulus) ≠ modulus - 1 := by
  intro he
  have hm : modulus - 1 < 2 * modulus := by omega
  have hsum : (modulus - 1 + (steps + 1)) % (2 * modulus) = modulus - 1 := by
    rw [show modulus - 1 + (steps + 1) = 1 + (modulus - 1 + steps) by omega]
    simpa only [Nat.add_mod, Nat.mod_mod] using he
  have hc : Nat.ModEq (2 * modulus) (modulus - 1 + (steps + 1)) (modulus - 1 + 0) := by
    simpa only [Nat.ModEq, Nat.add_zero, Nat.mod_eq_of_lt hm] using hsum
  have hcan := Nat.ModEq.add_left_cancel' (modulus - 1) hc
  have hz : (steps + 1) % (2 * modulus) = 0 := hcan
  rw [Nat.mod_eq_of_lt hsteps] at hz
  omega

private def terminalPadded (state : BasisState) : BasisState :=
  (terminalPaddingForwardState (R).terminalPadding state[(R).terminal ↦ true])[(R).terminal ↦ false]

private theorem terminal_frame (state : BasisState) {wire : Wire}
    (hw : wire ∈ [(R).phase1, (R).phase2] ++ (R).lengthRPrime) :
    terminalPadded state wire = state wire := by
  have hgeometry : ∀ wire ∈ [(R).phase1, (R).phase2] ++ (R).lengthRPrime,
      wire ≠ (R).terminal ∧ wire ∉ (R).work2 ∧ wire ∉ (R).lengthS ∧ wire ≠ (R).shiftEpoch := by decide
  obtain ⟨ht, hwork, hlength, hepoch⟩ := hgeometry wire hw
  unfold terminalPadded
  rw [upd_other _ _ _ ht, terminalPaddingForwardState_preserves _ _ hwork hlength hepoch,
    upd_other _ _ _ ht]

private theorem terminal_values_frame (state : BasisState) :
    wireValues (R).lengthS state[(R).terminal ↦ true] = wireValues (R).lengthS state := by
  apply List.map_congr_left
  intro wire hw
  have ht : (R).terminal ∉ (R).lengthS := by decide
  exact upd_other _ _ _ (by intro he; subst wire; exact ht hw)

private theorem terminal_output_values (state : BasisState) :
    wireValues (R).lengthS (terminalPadded state) =
      wireValues (R).lengthS (terminalPaddingForwardState (R).terminalPadding state[(R).terminal ↦ true]) := by
  apply List.map_congr_left
  intro wire hw
  have ht : (R).terminal ∉ (R).lengthS := by decide
  exact upd_other _ _ _ (by intro he; subst wire; exact ht hw)

private theorem terminal_wireAnd_frame (wires : List Wire) (before after : BasisState)
    (h : ∀ wire ∈ wires, after wire = before wire) : wireAnd wires after = wireAnd wires before := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
    simp only [wireAnd, h wire (by simp), ih (by intro w hw; exact h w (by simp [hw]))]

private theorem schedule_layout_at {registers : IndexedStepRegisters} {n start count : Nat}
    (hlayout : IndexedScheduleLayout registers n start count) (offset : Nat) (ho : offset < count) :
    IndexedStepLayout registers n (start + offset) := by
  induction hlayout generalizing offset with
  | done => omega
  | @step start count head tail ih =>
    cases offset with
    | zero => simpa using head
    | succ offset =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih offset (by omega)

private theorem production_layout (T : Nat) (hT : 1 ≤ T) (hmax : T ≤ 1620) :
    IndexedStepLayout R 256 T := by
  have h := schedule_layout_at secp256k1ScheduleLayout_production (T - 1) (by
    change T - 1 < 1620
    omega)
  simpa [show 1 + (T - 1) = T by omega] using h


/-- The production terminal encoding is preserved by one actual routed step throughout the
proved logical padding range. The active prefix must still establish the entry encoding. -/
theorem Secp256k1TerminalState.step {padding T : Nat} {state : BasisState}
    (hstate : Secp256k1TerminalState padding state) (hp : padding < 596)
    (hT : 1 ≤ T) (hmax : T ≤ 1620) :
    Secp256k1TerminalState (padding + 1) (indexedStepRoutedState R 256 T state) := by
  have hlayout := production_layout T hT hmax
  have hroutes := secp256k1IndexedStepRoutesValid T hT hmax state
  let routes := indexedStepEndRoutes R 256 T state
  have hbounds : (endIterationWindowsAt 256 T).k4 ≤ routes.1 ∧
      routes.1 ≤ (endIterationWindowsAt 256 T).K4 ∧
      (endIterationWindowsAt 256 T).k5 ≤ routes.2 ∧
      routes.2 ≤ (endIterationWindowsAt 256 T).K5Decode 256 := hroutes
  have hbound : (1 + (boolWordToNat (wireValues (R).lengthS state) +
        2^(R).lengthS.length * (state (R).shiftEpoch).toNat)) %
      2^((R).lengthS.length + 1) ≠ 2^(R).lengthS.length - 1 := by
    change (1 + (boolWordToNat (wireValues (R).lengthS state) +
      512 * (state (R).shiftEpoch).toNat)) % 1024 ≠ 511
    rw [hstate.low, hstate.epoch, terminal_source_raw padding (by omega)]
    exact counter_horizon 512 padding (by decide) (by omega)
  have hfull := indexedStepUnitary_terminal_counter_correct R 256 T routes.1 routes.2
    ⟨hbounds.1, hbounds.2.1⟩ ⟨hbounds.2.2.1, hbounds.2.2.2⟩
    state hlayout hstate.ready hstate.epochEncoded (fun _ ↦ rfl)
    hstate.phase1 hstate.phase2 hstate.remainder hbound
  have hrun := indexedStepUnitary_correct_routed R 256 T state hlayout
    hstate.ready hstate.epochEncoded hroutes
  have hpadded : indexedStepRoutedState R 256 T state = terminalPadded state :=
    hrun.1.symm.trans hfull.1
  have hcounter := terminalPaddingForwardState_counter (R).terminalPadding
    state[(R).terminal ↦ true] hlayout.terminalPadding (by rfl)
  change (boolWordToNat (wireValues (R).lengthS
      (terminalPaddingForwardState (R).terminalPadding state[(R).terminal ↦ true])) =
      (1 + boolWordToNat (wireValues (R).lengthS state[(R).terminal ↦ true])) % 512) ∧
    ((terminalPaddingForwardState (R).terminalPadding state[(R).terminal ↦ true]) (R).shiftEpoch =
      Bool.xor (state[(R).terminal ↦ true] (R).shiftEpoch)
        (decide ((1 + boolWordToNat (wireValues (R).lengthS state[(R).terminal ↦ true])) % 512 = 0))) at hcounter
  have he : (R).shiftEpoch ≠ (R).terminal := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hfull.2.1
    rw [hrun.1] at h
    exact h
  · have h := hfull.2.2
    rw [hrun.1] at h
    exact h
  · rw [hpadded, terminal_frame state (wire := (R).phase1) (by simp)]
    exact hstate.phase1
  · rw [hpadded, terminal_frame state (wire := (R).phase2) (by simp)]
    exact hstate.phase2
  · rw [hpadded, terminal_wireAnd_frame (R).lengthRPrime state _ (by
      intro wire hw; exact terminal_frame state (by simp [hw]))]
    exact hstate.remainder
  · rw [hpadded, terminal_output_values, hcounter.1]
    rw [terminal_values_frame, hstate.low]
    exact (terminal_source_next padding hp).1
  · rw [hpadded]
    unfold terminalPadded
    rw [upd_other _ _ _ he, hcounter.2]
    rw [upd_other _ _ _ he, terminal_values_frame, hstate.low, hstate.epoch]
    exact (terminal_source_next padding hp).2

/-- Every terminal suffix of at most 596 total padding steps satisfies the actual production
schedule invariant and retains the terminal counter encoding. This starts from an explicitly
encoded terminal boundary; the active arithmetic prefix is not proved here. -/
theorem secp256k1TerminalScheduleInvariant (start count padding : Nat) (state : BasisState)
    (hstart : 1 ≤ start) (hstop : start + count ≤ 1621) (hp : padding + count ≤ 596)
    (hstate : Secp256k1TerminalState padding state) :
    IndexedScheduleInvariant R 256 start count state ∧
      Secp256k1TerminalState (padding + count) (indexedScheduleState R 256 start count state) := by
  induction count generalizing start padding state with
  | zero => exact ⟨.done _ _ hstate.ready, by simpa [indexedScheduleState] using hstate⟩
  | succ count ih =>
    have hnext := hstate.step (by omega : padding < 596) hstart (by omega : start ≤ 1620)
    have htail := ih (start + 1) (padding + 1) _ (by omega) (by omega) (by omega) hnext
    refine ⟨.step hstate.ready hstate.epochEncoded
      (secp256k1IndexedStepRoutesValid start hstart (by omega) state) htail.1, ?_⟩
    simpa [indexedScheduleState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail.2

end
end ShorECDLP.Paper2607_13816
