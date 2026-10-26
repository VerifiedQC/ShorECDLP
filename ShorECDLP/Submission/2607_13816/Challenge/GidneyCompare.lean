import ShorECDLP.Submission.«2607_13816».Challenge.ConstantStraight
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledCompare

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem unitary_nil_run (p : AdaptiveCircuit) : (AdaptiveCircuit.unitary [] p).run = p.run := by
  simp only [AdaptiveCircuit.run]
  apply List.map_id'

/-- The final comparison carry is also measured, after the last input cell. -/
def compareCarryCells (q current spare ancilla flag : Wire) :
    List Wire → List Wire → List Bool → List (Circuit × Wire)
  | [], [], [] => [(List.nil, current)]
  | a :: input, d :: dirty, k :: constant =>
      (gidneyCompareCarryCell q current spare ancilla a d flag k input.isEmpty, current) ::
        compareCarryCells q spare current ancilla flag input dirty constant
  | _, _, _ => []

theorem compareCarryCells_source (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (targets : List Wire)
    (cleanup : Circuit) (outcomes : List Bool)
    (hd : input.length = dirty.length) (hk : constant.length = input.length) :
    (gidneyCompareTail q current spare ancilla flag
      (fun bs => registerZCorrection targets bs ++ cleanup ++ registerZCorrection targets bs)
      outcomes input dirty constant).run =
      (deferredCorrectionCircuit targets cleanup
        (compareCarryCells q current spare ancilla flag input dirty constant) outcomes).run := by
  induction input generalizing current spare dirty constant outcomes with
  | nil =>
    have hd' : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant = [] := List.eq_nil_of_length_eq_zero hk
    subst dirty
    subst constant
    simp only [gidneyCompareTail, compareCarryCells, deferredCorrectionCircuit, unitary_nil_run]
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        simp only [gidneyCompareTail, compareCarryCells, deferredCorrectionCircuit, AdaptiveCircuit.run]
        rw [ih spare current ds ks (outcomes ++ [false]) (by simpa using hd) (by simpa using hk),
            ih spare current ds ks (outcomes ++ [true]) (by simpa using hd) (by simpa using hk)]

theorem compareCarryCells_length (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hd : input.length = dirty.length) (hk : constant.length = input.length) :
    (compareCarryCells q current spare ancilla flag input dirty constant).length = input.length + 1 := by
  induction input generalizing current spare dirty constant with
  | nil =>
    have hd' : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant = [] := List.eq_nil_of_length_eq_zero hk
    subst dirty
    subst constant
    rfl
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        simp only [compareCarryCells, List.length_cons]
        rw [ih spare current ds ks (by simpa using hd) (by simpa using hk)]

theorem compareCarryCells_tCount (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (targets : List Wire)
    (cleanup : Circuit) (outcomes : List Bool)
    (hd : input.length = dirty.length) (hk : constant.length = input.length) :
    (gidneyCompareTail q current spare ancilla flag
      (fun bs => registerZCorrection targets bs ++ cleanup ++ registerZCorrection targets bs)
      outcomes input dirty constant).tCount =
      deferredCorrectionT cleanup (compareCarryCells q current spare ancilla flag input dirty constant) := by
  induction input generalizing current spare dirty constant outcomes with
  | nil =>
    have hd' : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant = [] := List.eq_nil_of_length_eq_zero hk
    subst dirty
    subst constant
    simp [gidneyCompareTail, compareCarryCells, deferredCorrectionT, AdaptiveCircuit.tCount,
      ShorECDLP.tCount_append, registerZCorrection_tCount]
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        simp only [gidneyCompareTail, compareCarryCells, deferredCorrectionT, AdaptiveCircuit.tCount]
        rw [ih spare current ds ks (outcomes ++ [false]) (by simpa using hd) (by simpa using hk),
            ih spare current ds ks (outcomes ++ [true]) (by simpa using hd) (by simpa using hk)]
        rw [Nat.max_self]

def compareCarryProgram (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool) :
    Straight n start (start + (compareCarryCells q spare carry ancilla flag input dirty constant).length) :=
  (literalProgram (gidneyCompareCarryCell q carry spare ancilla a d flag k input.isEmpty)).append
    (deferredCorrectionProgram n (d :: dirty)
      (controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q carry)
      (compareCarryCells q spare carry ancilla flag input dirty constant) start List.nil)

theorem compareCarryProgram_run (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length = dirty.length) (hk : constant.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant).instantiate read history).run =
      (controlledGidneyCompareCarry (a :: input) (d :: dirty) (k :: constant) q carry spare ancilla flag).run := by
  simp only [compareCarryProgram, literalProgram_append_run, AdaptiveCircuit.run,
    deferredCorrectionProgram_run, List.map_nil, controlledGidneyCompareCarry]
  rw [compareCarryCells_source q spare carry ancilla flag input dirty constant (d :: dirty)
    (controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q carry) List.nil hd hk]

theorem compareCarryProgram_tCount (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length = dirty.length) (hk : constant.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant).instantiate read history).tCount =
      (controlledGidneyCompareCarry (a :: input) (d :: dirty) (k :: constant) q carry spare ancilla flag).tCount := by
  simp only [compareCarryProgram, literalProgram_append_tCount, deferredCorrectionProgram_tCount,
    controlledGidneyCompareCarry, AdaptiveCircuit.tCount]
  rw [compareCarryCells_tCount q spare carry ancilla flag input dirty constant (d :: dirty)
    (controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q carry) List.nil hd hk]

theorem compareCarryProgram_records (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length = dirty.length) (hk : constant.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant).instantiate read history).run) :
    b.history.length = input.length + 1 := by
  have h := straight_history_length
    (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant) read history b hb
  simpa [compareCarryCells_length q spare carry ancilla flag input dirty constant hd hk] using h

def compareCoreProgram (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) : (count : Nat) × Straight n start (start + count) :=
  match input, dirty, constant with
  | a :: input, d :: dirty, k :: constant =>
      ⟨(compareCarryCells q spare carry ancilla flag input dirty constant).length,
        compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant⟩
  | _, _, _ => ⟨0, .done⟩

theorem compareCoreProgram_run (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) (hd : input.length = dirty.length) (hk : constant.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (compareCoreProgram n start input dirty constant q carry spare ancilla flag) read history =
      (controlledGidneyCompareCarry input dirty constant q carry spare ancilla flag).run := by
  cases input with
  | nil => rfl
  | cons a input =>
    cases dirty with
    | nil => rfl
    | cons d dirty =>
      cases constant with
      | nil => rfl
      | cons k constant =>
        exact compareCarryProgram_run n start a d q carry spare ancilla flag input dirty k constant
          (by simpa using hd) (by simpa using hk) read history

theorem compareCoreProgram_tCount (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) (hd : input.length = dirty.length) (hk : constant.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (compareCoreProgram n start input dirty constant q carry spare ancilla flag) read history =
      (controlledGidneyCompareCarry input dirty constant q carry spare ancilla flag).tCount := by
  cases input with
  | nil => rfl
  | cons a input =>
    cases dirty with
    | nil => rfl
    | cons d dirty =>
      cases constant with
      | nil => rfl
      | cons k constant =>
        exact compareCarryProgram_tCount n start a d q carry spare ancilla flag input dirty k constant
          (by simpa using hd) (by simpa using hk) read history

def compareGEProgram (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) : (count : Nat) × Straight n start (start + count) :=
  if threshold = 0 then ⟨0, literalProgram [.CX q flag]⟩
  else if 2 ^ input.length ≤ threshold then ⟨0, .done⟩
  else compareCoreProgram n start input dirty
    ((List.range input.length).map (Nat.testBit (2 ^ input.length - threshold))) q carry spare ancilla flag

theorem compareGEProgram_run (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length = dirty.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (compareGEProgram n start input dirty threshold q carry spare ancilla flag) read history =
      (controlledGidneyCompareGE input dirty threshold q carry spare ancilla flag).run := by
  unfold compareGEProgram controlledGidneyCompareGE
  split
  · exact literalProgram_run _ read history
  · split
    · rfl
    · exact compareCoreProgram_run n start input dirty _ q carry spare ancilla flag hd
        (by simp) read history

theorem compareGEProgram_tCount (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length = dirty.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (compareGEProgram n start input dirty threshold q carry spare ancilla flag) read history =
      (controlledGidneyCompareGE input dirty threshold q carry spare ancilla flag).tCount := by
  unfold compareGEProgram controlledGidneyCompareGE
  split
  · rfl
  · split
    · rfl
    · exact compareCoreProgram_tCount n start input dirty _ q carry spare ancilla flag hd
        (by simp) read history

theorem compareGEProgram_records (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (b : InstrumentBranch)
    (hb : b ∈ compiledRun (compareGEProgram n start input dirty threshold q carry spare ancilla flag) read history) :
    b.history.length = (compareGEProgram n start input dirty threshold q carry spare ancilla flag).1 := by
  have h := straight_history_length
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2 read history b hb
  simpa using h

theorem compareCarryCells_constant_source (control q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (targets : List Wire)
    (cleanup : Circuit) (outcomes : List Bool)
    (hd : input.length = dirty.length) (hk : constant.length = input.length) :
    (constantControlProgram control (gidneyCompareTail q current spare ancilla flag
      (fun bs => registerZCorrection targets bs ++ cleanup ++ registerZCorrection targets bs)
      outcomes input dirty constant)).run =
      (constantControlProgram control (deferredCorrectionCircuit targets cleanup
        (compareCarryCells q current spare ancilla flag input dirty constant) outcomes)).run := by
  induction input generalizing current spare dirty constant outcomes with
  | nil =>
    have hd' : dirty = [] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant = [] := List.eq_nil_of_length_eq_zero hk
    subst dirty
    subst constant
    simp only [gidneyCompareTail, compareCarryCells, deferredCorrectionCircuit, constantControlProgram, List.map_nil, unitary_nil_run]
  | cons a as ih =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        simp only [gidneyCompareTail, compareCarryCells, deferredCorrectionCircuit, constantControlProgram, AdaptiveCircuit.run]
        rw [ih spare current ds ks (outcomes ++ [false]) (by simpa using hd) (by simpa using hk),
            ih spare current ds ks (outcomes ++ [true]) (by simpa using hd) (by simpa using hk)]

theorem compareCarryProgram_constant_run (control : Wire) (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length = dirty.length) (hk : constant.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((constantStraight control (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant)).instantiate read history).run =
      (constantControlProgram control (controlledGidneyCompareCarry (a :: input) (d :: dirty) (k :: constant) q carry spare ancilla flag)).run := by
  simp only [compareCarryProgram, constantStraight_literal, literalProgram_append_run,
    AdaptiveCircuit.run, constantStraight_deferred_run, List.map_nil, controlledGidneyCompareCarry,
    constantControlProgram]
  rw [compareCarryCells_constant_source control q spare carry ancilla flag input dirty constant (d :: dirty)
    (controlledConstCarryXor (a :: input) (d :: dirty) (k :: constant) q carry) List.nil hd hk]

noncomputable def constantCompiledRun {n start : Nat} (q : Wire)
    (p : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) : Instrument :=
  ((constantStraight q p.2).instantiate read history).run

theorem compareCoreProgram_constant_run (control : Wire) (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) (hd : input.length = dirty.length) (hk : constant.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    constantCompiledRun control (compareCoreProgram n start input dirty constant q carry spare ancilla flag) read history =
      (constantControlProgram control (controlledGidneyCompareCarry input dirty constant q carry spare ancilla flag)).run := by
  cases input with
  | nil => rfl
  | cons a input =>
    cases dirty with
    | nil => rfl
    | cons d dirty =>
      cases constant with
      | nil => rfl
      | cons k constant =>
        exact compareCarryProgram_constant_run control n start a d q carry spare ancilla flag input dirty k constant
          (by simpa using hd) (by simpa using hk) read history

theorem compareGEProgram_constant_run (control : Wire) (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length = dirty.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    constantCompiledRun control (compareGEProgram n start input dirty threshold q carry spare ancilla flag) read history =
      (constantControlProgram control (controlledGidneyCompareGE input dirty threshold q carry spare ancilla flag)).run := by
  unfold compareGEProgram controlledGidneyCompareGE
  split
  · rfl
  · split
    · rfl
    · exact compareCoreProgram_constant_run control n start input dirty _ q carry spare ancilla flag hd
        (by simp) read history

def uncontrolledCompareProgram (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (carry spare ancilla flag : Wire) : (count : Nat) × Straight n start (start + count) :=
  let q := gidneyCompareVirtualControl input dirty carry spare ancilla flag
  let p := compareGEProgram n start input dirty threshold q carry spare ancilla flag
  ⟨p.1, constantStraight q p.2⟩

theorem uncontrolledCompareProgram_run (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (carry spare ancilla flag : Wire) (hd : input.length = dirty.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (uncontrolledCompareProgram n start input dirty threshold carry spare ancilla flag) read history =
      (gidneyCompareGE input dirty threshold carry spare ancilla flag).run := by
  exact compareGEProgram_constant_run
    (gidneyCompareVirtualControl input dirty carry spare ancilla flag) n start input dirty threshold
    (gidneyCompareVirtualControl input dirty carry spare ancilla flag) carry spare ancilla flag hd read history

theorem uncontrolledCompareProgram_tCount (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (carry spare ancilla flag : Wire) (hd : input.length = dirty.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (uncontrolledCompareProgram n start input dirty threshold carry spare ancilla flag) read history =
      (gidneyCompareGE input dirty threshold carry spare ancilla flag).tCount := by
  unfold uncontrolledCompareProgram compiledTCount gidneyCompareGE
  dsimp only
  rw [constantStraight_tCount, constantControlProgram_tCount]
  exact compareGEProgram_tCount n start input dirty threshold _ carry spare ancilla flag hd read history

theorem uncontrolledCompareProgram_records (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (carry spare ancilla flag : Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (b : InstrumentBranch)
    (hb : b ∈ compiledRun (uncontrolledCompareProgram n start input dirty threshold carry spare ancilla flag) read history) :
    b.history.length = (uncontrolledCompareProgram n start input dirty threshold carry spare ancilla flag).1 := by
  have h := straight_history_length
    (uncontrolledCompareProgram n start input dirty threshold carry spare ancilla flag).2 read history b hb
  simpa using h

end ShorECDLP.Paper2607_13816.ChallengeMigration
