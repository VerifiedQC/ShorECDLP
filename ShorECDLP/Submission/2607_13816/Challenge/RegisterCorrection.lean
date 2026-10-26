import ShorECDLP.Submission.«2607_13816».Challenge.Lookup

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- Deferred arithmetic corrections use only fixed, already-existing record indices. -/
def registerCorrectionProgram {n s e : Nat} :
    List Wire → List (Fin s) → Straight n s e → Straight n s e
  | w :: ws, i :: is, next => recordGates i (pauliZ w) (registerCorrectionProgram ws is next)
  | _, _, next => next

theorem registerCorrectionProgram_run {n s e : Nat} (ws : List Wire)
    (indices : List (Fin s)) (next : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((registerCorrectionProgram ws indices next).instantiate read history).run =
      (.unitary (registerZCorrection ws (indices.map history))
        (next.instantiate read history) : AdaptiveCircuit).run := by
  induction ws generalizing indices with
  | nil =>
      simp only [registerCorrectionProgram, registerZCorrection, AdaptiveCircuit.run]
      symm
      apply List.map_id'
  | cons w ws ih =>
    cases indices with
    | nil =>
        simp only [registerCorrectionProgram, List.map_nil, registerZCorrection, AdaptiveCircuit.run]
        symm
        apply List.map_id'
    | cons i is =>
      simp only [registerCorrectionProgram, recordGates_run, AdaptiveCircuit.run, ih,
        List.map_cons, registerZCorrection]
      simp only [List.map_map]
      congr 1
      funext b
      cases b with
      | mk h k =>
        change InstrumentBranch.mk h ((k.comp _).comp _) = InstrumentBranch.mk h (k.comp _)
        rw [Quantum.run_append_map, LinearMap.comp_assoc]

theorem registerCorrectionProgram_slots {n s e : Nat} (ws : List Wire)
    (indices : List (Fin s)) (next : Straight n s e) :
    (registerCorrectionProgram ws indices next).gateSlots =
      3 * min ws.length indices.length + next.gateSlots := by
  induction ws generalizing indices with
  | nil => simp [registerCorrectionProgram]
  | cons w ws ih =>
    cases indices with
    | nil => simp [registerCorrectionProgram]
    | cons i is =>
      simp only [registerCorrectionProgram, pauliZ, recordGates, Straight.gateSlots, ih,
        List.length_cons]
      omega

theorem literalProgram_append_run {n s e : Nat} (gs : Circuit) (next : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (((literalProgram gs).append next).instantiate read history).run =
      (.unitary gs (next.instantiate read history) : AdaptiveCircuit).run := by
  induction gs with
  | nil =>
    simp only [literalProgram, List.map_nil, gateProgram, Straight.append, AdaptiveCircuit.run]
    symm
    apply List.map_id'
  | cons g gs ih =>
    simp only [literalProgram, List.map_cons, gateProgram, Straight.append,
      Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.run] at ih ⊢
    rw [ih]
    simp only [List.map_map]
    congr 1

/-- Fixed carry-cell schedule: unitary cells followed by one measurement each. -/
def deferredCorrectionCircuit (targets : List Wire) (cleanup : Circuit) :
    List (Circuit × Wire) → List Bool → AdaptiveCircuit
  | [], outcomes => .unitary
      (registerZCorrection targets outcomes ++ cleanup ++ registerZCorrection targets outcomes) .done
  | (gs,w) :: cells, outcomes => .unitary gs (.xMeasureReset w
      (deferredCorrectionCircuit targets cleanup cells (outcomes ++ [false]))
      (deferredCorrectionCircuit targets cleanup cells (outcomes ++ [true])))

def deferredCorrectionProgram (n : Nat) (targets : List Wire) (cleanup : Circuit) :
    (cells : List (Circuit × Wire)) → (start : Nat) → List (Fin start) →
      Straight n start (start + cells.length)
  | [], _, prior => registerCorrectionProgram targets prior
      ((literalProgram cleanup).append (registerCorrectionProgram targets prior .done))
  | (gs,w) :: cells, start, prior => castFinish (by simp; omega)
      ((literalProgram gs).append (.measure w
        (deferredCorrectionProgram n targets cleanup cells (start+1)
          (prior.map Fin.castSucc ++ [Fin.last start]))))

theorem deferredCorrectionProgram_run (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((deferredCorrectionProgram n targets cleanup cells start prior).instantiate read history).run =
      (deferredCorrectionCircuit targets cleanup cells (prior.map history)).run := by
  induction cells generalizing start with
  | nil =>
    simp only [deferredCorrectionProgram, registerCorrectionProgram_run,
      literalProgram_append_run, AdaptiveCircuit.run, deferredCorrectionCircuit, List.map_map]
    congr 1
    funext b
    cases b with
    | mk h k =>
      change InstrumentBranch.mk h (((k.comp _).comp _).comp _) =
        InstrumentBranch.mk h (k.comp _)
      simp only [Quantum.run_append_map, LinearMap.comp_assoc]
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    simp only [deferredCorrectionProgram, castFinish_instantiate, literalProgram_append_run,
      Straight.instantiate, AdaptiveCircuit.run, ih, deferredCorrectionCircuit]
    simp [List.map_append, List.map_map, Function.comp_def]

theorem deferredCorrectionProgram_records (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((deferredCorrectionProgram n targets cleanup cells start prior).instantiate read history).run) :
    b.history.length = cells.length := by
  have h := straight_history_length
    (deferredCorrectionProgram n targets cleanup cells start prior) read history b hb
  simpa using h

theorem literalProgram_slots {n s : Nat} (gs : Circuit) :
    (literalProgram (n := n) (s := s) gs).gateSlots = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change 1 + (literalProgram (n := n) (s := s) gs).gateSlots = gs.length + 1
    omega

def deferredCorrectionSlots (targetCount cleanupCount : Nat) : Nat → List (Circuit × Wire) → Nat
  | prior, [] => 6 * min targetCount prior + cleanupCount
  | prior, (gs,_) :: cells => gs.length + deferredCorrectionSlots targetCount cleanupCount (prior+1) cells

theorem deferredCorrectionProgram_slots (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (start : Nat) (prior : List (Fin start)) :
    (deferredCorrectionProgram n targets cleanup cells start prior).gateSlots =
      deferredCorrectionSlots targets.length cleanup.length prior.length cells := by
  induction cells generalizing start with
  | nil =>
    simp only [deferredCorrectionProgram, registerCorrectionProgram_slots,
      Straight.gateSlots_append, literalProgram_slots, Straight.gateSlots, deferredCorrectionSlots]
    omega
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    simp [deferredCorrectionProgram, Straight.gateSlots_append, literalProgram_slots,
      Straight.gateSlots, ih, deferredCorrectionSlots]

theorem registerZCorrection_tCount (targets : List Wire) (outcomes : List Bool) :
    ShorECDLP.tCount (registerZCorrection targets outcomes) = 0 := by
  induction targets generalizing outcomes with
  | nil => rfl
  | cons w ws ih =>
    cases outcomes with
    | nil => rfl
    | cons b bs =>
      cases b <;> simp only [registerZCorrection, Bool.false_eq_true, ↓reduceIte,
        ShorECDLP.tCount_append, ih]
      all_goals rfl

theorem registerCorrectionProgram_tCount {n s e : Nat} (ws : List Wire)
    (indices : List (Fin s)) (next : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((registerCorrectionProgram ws indices next).instantiate read history).tCount =
      (next.instantiate read history).tCount := by
  induction ws generalizing indices with
  | nil => rfl
  | cons w ws ih =>
    cases indices with
    | nil => rfl
    | cons i is =>
      rw [registerCorrectionProgram, recordGates_tCount, ih]
      cases history i <;> simp [pauliZ, ShorECDLP.tCount, ShorECDLP.tCost]

theorem literalProgram_append_tCount {n s e : Nat} (gs : Circuit) (next : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (((literalProgram gs).append next).instantiate read history).tCount =
      ShorECDLP.tCount gs + (next.instantiate read history).tCount := by
  induction gs with
  | nil => simp [literalProgram, gateProgram, Straight.append, ShorECDLP.tCount]
  | cons g gs ih =>
    simp only [literalProgram, List.map_cons, gateProgram, Straight.append,
      Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount] at ih ⊢
    rw [ih]
    simp [ShorECDLP.tCount, Nat.add_assoc]

def deferredCorrectionT (cleanup : Circuit) : List (Circuit × Wire) → Nat
  | [] => ShorECDLP.tCount cleanup
  | (gs,_) :: cells => ShorECDLP.tCount gs + deferredCorrectionT cleanup cells

theorem deferredCorrectionCircuit_tCount (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (outcomes : List Bool) :
    (deferredCorrectionCircuit targets cleanup cells outcomes).tCount = deferredCorrectionT cleanup cells := by
  induction cells generalizing outcomes with
  | nil => simp [deferredCorrectionCircuit, deferredCorrectionT, AdaptiveCircuit.tCount,
      ShorECDLP.tCount_append, registerZCorrection_tCount]
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    simp [deferredCorrectionCircuit, deferredCorrectionT, AdaptiveCircuit.tCount, ih]

theorem deferredCorrectionProgram_tCount (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((deferredCorrectionProgram n targets cleanup cells start prior).instantiate read history).tCount =
      deferredCorrectionT cleanup cells := by
  induction cells generalizing start with
  | nil => simp only [deferredCorrectionProgram, registerCorrectionProgram_tCount,
      literalProgram_append_tCount, Straight.instantiate, AdaptiveCircuit.tCount, Nat.add_zero,
      deferredCorrectionT]
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    simp only [deferredCorrectionProgram, castFinish_instantiate, literalProgram_append_tCount,
      Straight.instantiate, AdaptiveCircuit.tCount, ih, Nat.max_self, deferredCorrectionT]

end ShorECDLP.Paper2607_13816.ChallengeMigration
