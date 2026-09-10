import ShorECDLP.Submission.«2607_13816».EEA.InitialProduction
import ShorECDLP.Submission.«2607_13816».EEA.TerminalTrace
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem terminal_word {ws : List Wire} {s : BasisState}
    (h : boolWordToNat (wireValues ws s)=truthMinusOneValue ws.length 0) :
    wireValues ws s=constantBits ws.length (truthMinusOneValue ws.length 0) := by
  apply boolWordToNat_injective_of_length
  · simp only [wireValues,List.length_map,constantBits_length]
  · rw [h,boolWordToNat_constantBits]
    have hb := boolWordToNat_lt_pow_two (wireValues ws s)
    rw [h] at hb
    simp only [wireValues,List.length_map] at hb
    exact (Nat.mod_eq_of_lt hb).symm
/-- A canonical zero-remainder packed state enters the operational padding invariant. -/
theorem secp256k1TerminalState_of_packed {v : EEAState} {s : BasisState}
    (hc : v.Canonical) (hr : v.rPrime=0)
    (h : IndexedPackedState indexedStepProductionRegisters 256 s v) :
    Secp256k1TerminalState 0 s := by
  let R := indexedStepProductionRegisters
  obtain ⟨_,hQ,hS,hphase,_,_,hRP⟩ := hc
  have hRP0 : v.lRPrime=0 := by rw [hRP,hr]; rfl
  have hq := h.lengthQ
  rw [hQ] at hq
  have hqw := terminal_word hq
  have haux : Clean (List.range' 558 22) s := h.clean
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    have hsub : ∀ w∈indexedStepProductionRegisters.sharedScratch,w∈List.range' 558 22 := by decide
    exact haux w (hsub w hw)
  · unfold IndexedStepEpochEncoded
    split
    · change wireValues (List.range' 531 9) s=constantBits 9 511 at hqw
      have hb := congrArg (fun bits : List Bool => bits.headD false) hqw
      change s 531=(constantBits 9 511).headD false at hb
      exact hb
    · exact haux 559 (by decide)
  · simpa [hphase,EEAPhase.bits] using h.phase1
  · simpa [hphase,EEAPhase.bits] using h.phase2
  · rw [wireAnd_eq_numeric_allOnes,h.lengthRP,hRP0]
    rfl
  · have hs := h.lengthS
    rw [hS] at hs
    exact hs
  · exact haux 559 (by decide)
private theorem schedule_layout_drop {r : IndexedStepRegisters} {n start count : Nat}
    (hl : IndexedScheduleLayout r n start count) (skip : Nat) (hs : skip≤count) :
    IndexedScheduleLayout r n (start+skip) (count-skip) := by
  induction skip generalizing start count with
  | zero => simpa using hl
  | succ k ih =>
    cases hl with
    | done => omega
    | @step start count head tail =>
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih tail (by omega)

/-- The complete 1,620-step production schedule reaches its proved terminal-padding encoding. -/
theorem secp256k1EEAForward_terminalState (s : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) s)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p) :
    let initial := paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))
    Secp256k1TerminalState (paperPadding initial)
      (run (secp256k1EEAForwardUnitary indexedStepProductionRegisters) (eeaPreprocessIdealState s)) := by
  let x := boolWordToNat (wireValues (List.range' 263 256) s)
  let initial := paperInitial ShorECDLP.p x
  let active := paperMicrosteps initial
  let padding := paperPadding initial
  let after := run (indexedScheduleUnitary indexedStepProductionRegisters 256 1 active)
    (eeaPreprocessIdealState s)
  have hp := eeaPreprocess_active_paperRun s hclean hx hxp
  have hcanonical := (paperRun_preservesInvariant
    (paperInitial_invariant ShorECDLP.Secp256k1.p_prime hx hxp)).canonical
  have hterminal := secp256k1TerminalState_of_packed hcanonical (paperRun_zero_remainder _) hp
  change Secp256k1TerminalState 0 after at hterminal
  have hbound := secp256k1_paperMicrosteps_le_1620 hx hxp
  change active≤1620 at hbound
  have hweight : paperQuotientWeight initial≤405 := by
    change 4*paperQuotientWeight initial≤1620 at hbound
    omega
  have hclock : active+padding=1620 := paperMicrosteps_add_padding hweight
  have hpad : padding≤596 := secp256k1_paperPadding_le_596 hx hxp
  have hsuffix := secp256k1TerminalScheduleInvariant (active+1) padding 0 after
    (by omega) (by omega) (by omega) hterminal
  have hl := schedule_layout_drop secp256k1ScheduleLayout_production active hbound
  have hremain : secp256k1ScheduleLength-active=padding := by
    change 1620-active=padding
    omega
  rw [hremain,Nat.add_comm 1 active] at hl
  have hrun := indexedScheduleUnitary_correct indexedStepProductionRegisters 256 (active+1)
    padding after hl hsuffix.1
  change Secp256k1TerminalState padding
    (run (indexedScheduleUnitary indexedStepProductionRegisters 256 1 1620) (eeaPreprocessIdealState s))
  rw [←hclock,indexedScheduleUnitary_append,Classical.run_append]
  change Secp256k1TerminalState padding
    (run (indexedScheduleUnitary indexedStepProductionRegisters 256 (1+active) padding) after)
  rw [Nat.add_comm 1 active,hrun.1]
  simpa only [Nat.zero_add] using hsuffix.2

end ShorECDLP.Paper2607_13816
