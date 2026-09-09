import ShorECDLP.Submission.«2607_13816».EEA.TerminalTrace
import ShorECDLP.Submission.«2607_13816».EEA.InitialEncoding

/-! # Operational invariant through the active EEA prefix -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
local notation "R" => indexedStepProductionRegisters
attribute [local irreducible] indexedStepUnitary indexedStepRoutedState indexedStepEndRoutes eeaPreprocessIdealState

private theorem active_layout_prefix {r : IndexedStepRegisters} {n start total : Nat}
    (hl : IndexedScheduleLayout r n start total) (count : Nat) (hc : count ≤ total) :
    IndexedScheduleLayout r n start count := by
  induction hl generalizing count with
  | done start =>
    have h : count = 0 := by omega
    subst count
    exact .done start
  | @step start total head tail ih =>
    cases count with
    | zero => exact .done start
    | succ count => exact .step head (ih count (by omega))

private theorem production_active_trace (start count : Nat)
    (hl : IndexedScheduleLayout R 256 start count) (state : BasisState)
    (hstart : 1 ≤ start) (hstop : start + count ≤ 1621)
    (hready : IndexedStepReady R state) (hencoded : IndexedStepEpochEncoded R state)
    (hclean : Clean (R).aux state)
    (hactive : ∀ offset < count,
      wireAnd (R).lengthRPrime (indexedScheduleState R 256 start offset state) = false) :
    IndexedScheduleInvariant R 256 start count state ∧
      Clean (R).aux (indexedScheduleState R 256 start count state) ∧
      IndexedStepEpochEncoded R (indexedScheduleState R 256 start count state) := by
  induction hl generalizing state with
  | done start => exact ⟨.done _ _ hready, hclean, hencoded⟩
  | @step start count head tail ih =>
    have hroutes := secp256k1IndexedStepRoutesValid start hstart (by omega) state
    have hstep := indexedStepUnitary_correct_routed R 256 start state head hready hencoded hroutes
    have hnext := hstep.2
    rw [hstep.1] at hnext
    have hrp : wireAnd (R).lengthRPrime state = false := hactive 0 (by omega)
    let routes := indexedStepEndRoutes R 256 start state
    have hb : (endIterationWindowsAt 256 start).k4 ≤ routes.1 ∧
        routes.1 ≤ (endIterationWindowsAt 256 start).K4 ∧
        (endIterationWindowsAt 256 start).k5 ≤ routes.2 ∧
        routes.2 ≤ (endIterationWindowsAt 256 start).K5Decode 256 := hroutes
    have hc := indexedStepUnitary_active_clean R 256 start routes.1 routes.2
      ⟨hb.1, hb.2.1⟩ ⟨hb.2.2.1, hb.2.2.2⟩ state head hclean hrp (fun _ => rfl)
    have he := indexedStepUnitary_active_encoded R 256 start routes.1 routes.2
      ⟨hb.1, hb.2.1⟩ ⟨hb.2.2.1, hb.2.2.2⟩ state head hclean hrp (fun _ => rfl)
    rw [hstep.1] at hc he
    have ht := ih _ (by omega) (by omega) hnext he hc (by
      intro offset hoffset
      exact hactive (offset + 1) (by omega))
    exact ⟨.step hready hencoded hroutes ht.1, ht.2⟩

/-- Every nonterminal input along an initialized active segment supplies the next
step's scratch and epoch premises. The final output may already be terminal.
The nonterminal trace condition remains an arithmetic reachability obligation. -/
theorem eeaPreprocess_activeSchedule_correct (count : Nat) (hcount : count ≤ 1620)
    (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < 2 ^ 256 - 2 ^ 32 - 977)
    (hactive : ∀ offset < count, wireAnd (R).lengthRPrime
      (indexedScheduleState R 256 1 offset (eeaPreprocessIdealState state)) = false) :
    IndexedScheduleInvariant R 256 1 count (eeaPreprocessIdealState state) ∧
    run (indexedScheduleUnitary R 256 1 count) (eeaPreprocessIdealState state) =
      indexedScheduleState R 256 1 count (eeaPreprocessIdealState state) ∧
    Clean (R).aux (run (indexedScheduleUnitary R 256 1 count) (eeaPreprocessIdealState state)) ∧
    IndexedStepEpochEncoded R
      (run (indexedScheduleUnitary R 256 1 count) (eeaPreprocessIdealState state)) := by
  have hl := active_layout_prefix secp256k1ScheduleLayout_production count hcount
  have hi := eeaPreprocess_initial_ready state hclean hx hxp
  have hp := eeaPreprocessIdealState_correct state hclean hx hxp
  dsimp only at hp
  have ha : Clean (R).aux (eeaPreprocessIdealState state) := by
    intro wire hw
    exact hp.2.2.2.2.2.2.2.2.2.2.2.2.1 wire (by
      simp only [List.mem_append]
      exact Or.inr hw)
  have ht := production_active_trace 1 count hl _ (by decide) (by omega)
    hi.1 hi.2 ha hactive
  have hc := indexedScheduleUnitary_correct R 256 1 count _ hl ht.1
  refine ⟨ht.1, hc.1, ?_, ?_⟩
  · rw [hc.1]; exact ht.2.1
  · rw [hc.1]; exact ht.2.2


private theorem active_invariant_append {r : IndexedStepRegisters} {n start count : Nat}
    {state : BasisState} (hfirst : IndexedScheduleInvariant r n start count state)
    (rest : Nat)
    (hlast : IndexedScheduleInvariant r n (start + count) rest
      (indexedScheduleState r n start count state)) :
    IndexedScheduleInvariant r n start (count + rest) state := by
  induction hfirst with
  | done start state hready => simpa [indexedScheduleState] using hlast
  | @step start count state hready hencoded hroutes htail ih =>
    have hs : IndexedScheduleInvariant r n (start + 1 + count) rest
        (indexedScheduleState r n (start + 1) count (indexedStepRoutedState r n start state)) := by
      simpa [indexedScheduleState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlast
    have h := IndexedScheduleInvariant.step hready hencoded hroutes (ih hs)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The complete initialized schedule needs only arithmetic stopping-boundary facts:
nonterminal inputs before `stop`, then phase 00, terminal remainder and zero shift.
Scratch and epoch conditions throughout the 1,620 steps are derived. -/
theorem eeaPreprocess_scheduleInvariant_of_terminalEntry
    (stop : Nat) (hstop : 1024 ≤ stop ∧ stop ≤ 1620) (state : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) state)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) state))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) state) < 2 ^ 256 - 2 ^ 32 - 977)
    (hactive : ∀ offset < stop, wireAnd (R).lengthRPrime
      (indexedScheduleState R 256 1 offset (eeaPreprocessIdealState state)) = false)
    (hentry : let after := indexedScheduleState R 256 1 stop (eeaPreprocessIdealState state)
      after (R).phase1 = false ∧ after (R).phase2 = false ∧
      wireAnd (R).lengthRPrime after = true ∧
      boolWordToNat (wireValues (R).lengthS after) = 511) :
    Secp256k1ScheduleInvariant R (eeaPreprocessIdealState state) := by
  let after := indexedScheduleState R 256 1 stop (eeaPreprocessIdealState state)
  have ha := eeaPreprocess_activeSchedule_correct stop hstop.2 state hclean hx hxp hactive
  have hl := active_layout_prefix secp256k1ScheduleLayout_production stop hstop.2
  have hr := (indexedScheduleUnitary_correct R 256 1 stop _ hl ha.1).2
  rw [ha.2.1] at hr
  have hc := ha.2.2.1
  have he := ha.2.2.2
  rw [ha.2.1] at hc he
  have ht : Secp256k1TerminalState 0 after := by
    refine ⟨hr, he, hentry.1, hentry.2.1, hentry.2.2.1, ?_, ?_⟩
    · exact hentry.2.2.2
    · change after 559 = false
      exact hc 559 (by decide)
  have hs := secp256k1TerminalScheduleInvariant (1 + stop) (1620 - stop) 0 after
    (by omega) (by omega) (by omega) ht
  have hfull := active_invariant_append ha.1 (1620 - stop) hs.1
  simpa [show stop + (1620 - stop) = 1620 by omega, secp256k1ScheduleLength] using hfull

end
end ShorECDLP.Paper2607_13816
