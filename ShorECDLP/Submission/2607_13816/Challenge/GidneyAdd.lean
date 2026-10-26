import ShorECDLP.Submission.«2607_13816».Challenge.RegisterCorrection
import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyAdd

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The source carry tail, as a fixed list of gates and measured wires. -/
def gidneyCarryCells (q current spare ancilla : Wire) :
    List Wire → List Wire → List Bool → List (Circuit × Wire)
  | [a], [], [k] => [(((if k then [.CX q a] else []) ++ [.CX current a]), current)]
  | a :: as, d :: ds, k :: ks =>
      (gidneyAddCarryCell q current spare ancilla a d k, current) ::
        gidneyCarryCells q spare current ancilla as ds ks
  | _, _, _ => []

theorem gidneyCarryCells_source (q current spare ancilla : Wire)
    (input dirty : List Wire) (constant : List Bool) (targets : List Wire)
    (cleanup : Circuit) (outcomes : List Bool)
    (hd : input.length = dirty.length + 1) (hk : constant.length = input.length) :
    gidneyAddTail q current spare ancilla
      (fun bs => registerZCorrection targets bs ++ cleanup ++ registerZCorrection targets bs)
      outcomes input dirty constant =
      deferredCorrectionCircuit targets cleanup
        (gidneyCarryCells q current spare ancilla input dirty constant) outcomes := by
  induction input generalizing current spare dirty constant outcomes with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases as with
      | nil =>
        have hdirty : dirty = [] := List.eq_nil_of_length_eq_zero (by simp_all)
        have hks : ks = [] := List.eq_nil_of_length_eq_zero (by simp_all)
        subst dirty
        subst ks
        rfl
      | cons b bs =>
        cases dirty with
        | nil => simp at hd
        | cons d ds =>
          simp only [gidneyAddTail, gidneyCarryCells, deferredCorrectionCircuit]
          rw [ih spare current ds ks (outcomes ++ [false]) (by simpa using hd) (by simpa using hk),
              ih spare current ds ks (outcomes ++ [true]) (by simpa using hd) (by simpa using hk)]

theorem gidneyCarryCells_length (q current spare ancilla : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hd : input.length = dirty.length + 1) (hk : constant.length = input.length) :
    (gidneyCarryCells q current spare ancilla input dirty constant).length = input.length := by
  induction input generalizing current spare dirty constant with
  | nil => simp at hd
  | cons a as ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases as with
      | nil =>
        have hdirty : dirty = [] := List.eq_nil_of_length_eq_zero (by simp_all)
        have hks : ks = [] := List.eq_nil_of_length_eq_zero (by simp_all)
        subst dirty
        subst ks
        rfl
      | cons b bs =>
        cases dirty with
        | nil => simp at hd
        | cons d ds =>
          simp only [gidneyCarryCells, List.length_cons]
          rw [ih spare current ds ks (by simpa using hd) (by simpa using hk)]
          rfl

/-- Complete nontrivial source adder, with its first carry cell and deferred tail. -/
def gidneyNontrivialProgram (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool) :
    Straight n start (start + (gidneyCarryCells q spare carry ancilla as ds ks).length) :=
  (literalProgram (gidneyAddCarryCell q carry spare ancilla a d k)).append
    (deferredCorrectionProgram n (d :: ds)
      (gidneyAddCleanup (a :: as) (d :: ds) (k :: ks) q carry)
      (gidneyCarryCells q spare carry ancilla as ds ks) start List.nil)

theorem gidneyNontrivialProgram_run (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool)
    (hd : as.length = ds.length + 1) (hk : ks.length = as.length)
    (hnz : (k :: ks).all (fun b => !b) = false)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks).instantiate read history).run =
      (controlledGidneyAddConst (a :: as) (d :: ds) (k :: ks) q carry spare ancilla).run := by
  simp only [gidneyNontrivialProgram, literalProgram_append_run, AdaptiveCircuit.run,
    deferredCorrectionProgram_run, List.map_nil]
  rw [← gidneyCarryCells_source q spare carry ancilla as ds ks (d :: ds)
    (gidneyAddCleanup (a :: as) (d :: ds) (k :: ks) q carry) List.nil hd hk]
  simp only [controlledGidneyAddConst, hnz, Bool.false_eq_true, ↓reduceIte]
  cases as with
  | nil => simp at hd
  | cons b bs => rfl

theorem gidneyNontrivialProgram_records (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool)
    (hd : as.length = ds.length + 1) (hk : ks.length = as.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks).instantiate read history).run) :
    b.history.length = as.length := by
  have h := straight_history_length
    (gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks) read history b hb
  simpa [gidneyCarryCells_length q spare carry ancilla as ds ks hd hk] using h

theorem gidneyNontrivialProgram_tCount (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool)
    (hd : as.length = ds.length + 1) (hk : ks.length = as.length)
    (hnz : (k :: ks).all (fun b => !b) = false)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks).instantiate read history).tCount =
      (controlledGidneyAddConst (a :: as) (d :: ds) (k :: ks) q carry spare ancilla).tCount := by
  rw [gidneyNontrivialProgram, literalProgram_append_tCount, deferredCorrectionProgram_tCount]
  cases as with
  | nil => simp at hd
  | cons b bs =>
    simp only [controlledGidneyAddConst, hnz, Bool.false_eq_true, ↓reduceIte, AdaptiveCircuit.tCount]
    rw [gidneyCarryCells_source q spare carry ancilla (b :: bs) ds ks (d :: ds)
      (gidneyAddCleanup (a :: b :: bs) (d :: ds) (k :: ks) q carry) List.nil hd hk,
      deferredCorrectionCircuit_tCount]

/-- The record count is computed from the fixed input lists, never from measurement data. -/
def gidneyProgram (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) : (count : Nat) × Straight n start (start + count) :=
  if constant.all (fun k => !k) then ⟨0, .done⟩ else
  match input, dirty, constant with
  | [a], [], [k] => ⟨0, literalProgram (if k then [.CX q a] else [])⟩
  | a :: as, d :: ds, k :: ks =>
      ⟨(gidneyCarryCells q spare carry ancilla as ds ks).length,
        gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks⟩
  | _, _, _ => ⟨0, .done⟩

attribute [local irreducible] gidneyNontrivialProgram literalProgram

noncomputable def compiledRun {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) : Instrument :=
  (p.2.instantiate read history).run

theorem gidneyProgram_run (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire)
    (hd : input.length = dirty.length + 1) (hk : constant.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((gidneyProgram n start input dirty constant q carry spare ancilla).2.instantiate read history).run =
      (controlledGidneyAddConst input dirty constant q carry spare ancilla).run := by
  change compiledRun (gidneyProgram n start input dirty constant q carry spare ancilla) read history = _
  by_cases hz : constant.all (fun k => !k) = true
  · simp only [gidneyProgram, hz, ↓reduceIte]
    simp only [compiledRun, controlledGidneyAddConst, hz, ↓reduceIte]
    rfl
  · have hnz : constant.all (fun k => !k) = false := Bool.eq_false_iff.mpr hz
    cases input with
    | nil => simp at hd
    | cons a as =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have ha : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
          subst as
          have hks : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk)
          subst ks
          simp only [gidneyProgram, hnz, Bool.false_eq_true, ↓reduceIte]
          simp only [compiledRun, controlledGidneyAddConst, hnz, Bool.false_eq_true, ↓reduceIte]
          exact literalProgram_run _ read history
        | cons d ds =>
          simp only [gidneyProgram, hnz, Bool.false_eq_true, ↓reduceIte]
          simp only [compiledRun]
          exact gidneyNontrivialProgram_run n start a d q carry spare ancilla as ds k ks
            (by simpa using hd) (by simpa using hk) hnz read history

def compiledTCount {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) : Nat :=
  (p.2.instantiate read history).tCount

theorem gidneyProgram_tCount (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire)
    (hd : input.length = dirty.length + 1) (hk : constant.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((gidneyProgram n start input dirty constant q carry spare ancilla).2.instantiate read history).tCount =
      (controlledGidneyAddConst input dirty constant q carry spare ancilla).tCount := by
  change compiledTCount (gidneyProgram n start input dirty constant q carry spare ancilla) read history = _
  by_cases hz : constant.all (fun k => !k) = true
  · simp only [gidneyProgram, hz, ↓reduceIte]
    simp only [compiledTCount, controlledGidneyAddConst, hz, ↓reduceIte]
    rfl
  · have hnz : constant.all (fun k => !k) = false := Bool.eq_false_iff.mpr hz
    cases input with
    | nil => simp at hd
    | cons a as =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have ha : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
          subst as
          have hks : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk)
          subst ks
          simp only [gidneyProgram, hnz, Bool.false_eq_true, ↓reduceIte]
          simp only [compiledTCount, controlledGidneyAddConst, hnz, Bool.false_eq_true, ↓reduceIte]
          simp only [literalProgram, gateProgram_tCount, literal_gates, AdaptiveCircuit.tCount, Nat.add_zero]
        | cons d ds =>
          simp only [gidneyProgram, hnz, Bool.false_eq_true, ↓reduceIte]
          simp only [compiledTCount]
          exact gidneyNontrivialProgram_tCount n start a d q carry spare ancilla as ds k ks
            (by simpa using hd) (by simpa using hk) hnz read history

theorem gidneyProgram_records (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (b : InstrumentBranch)
    (hb : b ∈ ((gidneyProgram n start input dirty constant q carry spare ancilla).2.instantiate read history).run) :
    b.history.length = (gidneyProgram n start input dirty constant q carry spare ancilla).1 := by
  have h := straight_history_length
    (gidneyProgram n start input dirty constant q carry spare ancilla).2 read history b hb
  simpa using h

end ShorECDLP.Paper2607_13816.ChallengeMigration
