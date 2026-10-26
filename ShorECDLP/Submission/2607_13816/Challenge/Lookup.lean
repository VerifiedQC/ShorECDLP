import ShorECDLP.Submission.«2607_13816».Challenge.Fourier
import ShorECDLP.Submission.«2607_13816».Challenge.Gates
import ShorECDLP.Submission.«2607_13816».Window.DirectPointLookup

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem append_run_fixed {n a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n → Bool) (history : Fin a → Bool) (target : AdaptiveCircuit)
    (hq : ∀ h, (q.instantiate read h).run = target.run) :
    ((p.append q).instantiate read history).run =
      ((p.instantiate read history).seq target).run := by
  induction p with
  | done => exact hq history
  | gate g p ih => simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq,
      AdaptiveCircuit.run, ih q _ hq]
  | recordGate i v g p ih => simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq,
      AdaptiveCircuit.run, ih q _ hq]
  | measure w p ih => simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq,
      AdaptiveCircuit.run, ih q _ hq]

def literalProgram {n s : Nat} (gs : Circuit) : Straight n s s :=
  gateProgram (gs.map TemplateGate.literal)

theorem literalProgram_run {n s : Nat} (gs : Circuit) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    ((literalProgram gs).instantiate read history).run = (.unitary gs .done : AdaptiveCircuit).run := by
  rw [literalProgram, gateProgram_run]
  congr 2
  induction gs with
  | nil => rfl
  | cons g gs ih => simpa [TemplateGate.instantiate] using congrArg (List.cons g) ih

def recordGates {n s e : Nat} (i : Fin s) : Circuit → Straight n s e → Straight n s e
  | [], next => next
  | g :: gs, next => .recordGate i true g (recordGates i gs next)

theorem recordGates_run {n s e : Nat} (i : Fin s) (gs : Circuit) (next : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((recordGates i gs next).instantiate read history).run =
      (.unitary (if history i then gs else []) (next.instantiate read history) : AdaptiveCircuit).run := by
  induction gs with
  | nil =>
    simp only [recordGates, ite_self, AdaptiveCircuit.run]
    symm; apply List.map_id'
  | cons g gs ih =>
    simp only [recordGates, Straight.instantiate, AdaptiveCircuit.run, ih]
    cases history i <;> simp [List.map_map]
    all_goals intro a ha; cases a; rfl

def andEraseProgram (n start : Nat) (a b t : Wire) : Straight n start (start+1) :=
  .measure t (recordGates (Fin.last start) (controlledZ a b) .done)

theorem andEraseProgram_run (n start : Nat) (a b t : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((andEraseProgram n start a b t).instantiate read history).run = (measuredAndErase a b t).run := by
  simp [andEraseProgram, Straight.instantiate, AdaptiveCircuit.run, recordGates_run,
    measuredAndErase, measureResetWithCorrection, measuredAndCorrection]

/-- A compiler-local flat schedule; no submitted classical callbacks. -/
inductive LookupOp (n : Nat) where
  | gates (gs : List (TemplateGate n))
  | erase (a b t : Wire)

def lookupMeasurements {n : Nat} : List (LookupOp n) → Nat
  | [] => 0
  | .gates _ :: ops => lookupMeasurements ops
  | .erase _ _ _ :: ops => 1 + lookupMeasurements ops

def lookupProgram (n : Nat) : (ops : List (LookupOp n)) →
    (start : Nat) → Straight n start (start + lookupMeasurements ops)
  | [], _ => .done
  | .gates gs :: ops, start => (gateProgram gs).append (lookupProgram n ops start)
  | .erase a b t :: ops, start => castFinish (by simp [lookupMeasurements]; omega)
      ((andEraseProgram n start a b t).append (lookupProgram n ops (start+1)))

def lookupCircuit {n : Nat} (read : ConstantBit n → Bool) : List (LookupOp n) → AdaptiveCircuit
  | [] => .done
  | .gates gs :: ops => .unitary (gs.flatMap (TemplateGate.instantiate read)) (lookupCircuit read ops)
  | .erase a b t :: ops => (measuredAndErase a b t).seq (lookupCircuit read ops)

theorem lookupProgram_run (n : Nat) (ops : List (LookupOp n)) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((lookupProgram n ops start).instantiate read history).run = (lookupCircuit read ops).run := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs =>
      simp only [lookupProgram, lookupCircuit]
      rw [append_run_fixed _ _ _ _ _ (ih start), AdaptiveCircuit.run_seq, gateProgram_run]
      exact (AdaptiveCircuit.run_seq _ _).symm
    | erase a b t =>
      simp only [lookupProgram, castFinish_instantiate, lookupCircuit]
      rw [append_run_fixed _ _ _ _ _ (ih (start+1)), AdaptiveCircuit.run_seq,
        andEraseProgram_run, ← AdaptiveCircuit.run_seq]

theorem lookupProgram_history_length (n : Nat) (ops : List (LookupOp n)) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((lookupProgram n ops start).instantiate read history).run) :
    b.history.length = lookupMeasurements ops := by
  have h := straight_history_length (lookupProgram n ops start) read history b hb
  simpa using h

theorem adaptive_seq_assoc (a b c : AdaptiveCircuit) : (a.seq b).seq c = a.seq (b.seq c) := by
  induction a with
  | done => rfl
  | unitary gs a ih => simp only [AdaptiveCircuit.seq, ih]
  | xMeasureReset w a b iha ihb => simp only [AdaptiveCircuit.seq, iha, ihb]

theorem adaptive_seq_done (a : AdaptiveCircuit) : a.seq .done = a := by
  induction a with
  | done => rfl
  | unitary gs a ih => simp only [AdaptiveCircuit.seq, ih]
  | xMeasureReset w a b iha ihb => simp only [AdaptiveCircuit.seq, iha, ihb]

theorem lookupCircuit_append {n : Nat} (read : ConstantBit n → Bool) (xs ys : List (LookupOp n)) :
    lookupCircuit read (xs ++ ys) = (lookupCircuit read xs).seq (lookupCircuit read ys) := by
  induction xs with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [lookupCircuit, ih, AdaptiveCircuit.seq, adaptive_seq_assoc]

def ordinaryOp {n : Nat} (gs : Circuit) : LookupOp n := .gates (gs.map TemplateGate.literal)

@[simp] theorem literal_gates {n : Nat} (gs : Circuit) (read : ConstantBit n → Bool) :
    (gs.map (TemplateGate.literal (tableSize := n))).flatMap (TemplateGate.instantiate read) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [TemplateGate.instantiate, ih]

/-- Fixed traversal order; labels select submitted leaf data before execution. -/
def unaryLookupOps {n : Nat} (leaf : Nat → Wire → List (TemplateGate n)) :
    UnaryActionTree → Wire → List Wire → List (LookupOp n)
  | .leaf label, q, _ => [.gates (leaf label q)]
  | .node bit zero one, q, path :: rest =>
      [ordinaryOp (computeZeroAnd q bit path)] ++ unaryLookupOps leaf zero path rest ++
      [ordinaryOp [.CX q path]] ++ unaryLookupOps leaf one path rest ++
      [ordinaryOp [.CX q path], ordinaryOp [.X bit], .erase q bit path, ordinaryOp [.X bit]]
  | .node _ _ _, _, [] => []

theorem unaryLookupOps_circuit {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) (read : ConstantBit n → Bool) :
    lookupCircuit read (unaryLookupOps leaf tree q anc) =
      unaryAction .inc (fun l w => (leaf l w).flatMap (TemplateGate.instantiate read)) tree q anc := by
  induction tree generalizing q anc with
  | leaf l => rfl
  | node bit zero one ihz iho =>
    cases anc with
    | nil => rfl
    | cons path rest =>
      simp [unaryLookupOps, lookupCircuit_append, lookupCircuit, ordinaryOp, ihz, iho,
        unaryAction, eraseZeroAnd, TemplateGate.instantiate, AdaptiveCircuit.seq]

theorem lookupMeasurements_append {n : Nat} (xs ys : List (LookupOp n)) :
    lookupMeasurements (xs ++ ys) = lookupMeasurements xs + lookupMeasurements ys := by
  induction xs with
  | nil => simp [lookupMeasurements]
  | cons op ops ih => cases op <;> simp [lookupMeasurements, ih, Nat.add_assoc]

/-- A valid path bank makes one measurement at every internal tree node. -/
theorem unaryLookupOps_measurements {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) (hl : tree.Layout q anc) :
    lookupMeasurements (unaryLookupOps leaf tree q anc) = tree.internalNodes := by
  induction hl with
  | leaf l q anc hn => rfl
  | node bit q path zero one rest hn hz ho ihz iho =>
    simp [unaryLookupOps, lookupMeasurements_append, lookupMeasurements, ordinaryOp,
      UnaryActionTree.internalNodes, ihz, iho]
    omega

theorem adaptive_tCount_seq (p q : AdaptiveCircuit) :
    (p.seq q).tCount = p.tCount + q.tCount := by
  induction p with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount]
  | unitary gs p ih => simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount, ih, Nat.add_assoc]
  | xMeasureReset w a b iha ihb =>
    simp only [AdaptiveCircuit.seq, AdaptiveCircuit.tCount, iha, ihb]
    omega

theorem append_tCount_fixed {n a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n → Bool) (history : Fin a → Bool) (m : Nat)
    (hq : ∀ h, (q.instantiate read h).tCount = m) :
    ((p.append q).instantiate read history).tCount = (p.instantiate read history).tCount + m := by
  induction p with
  | done => simpa [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount] using hq history
  | gate g p ih => simp [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount, ih q _ hq, Nat.add_assoc]
  | recordGate i v g p ih => simp [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount, ih q _ hq, Nat.add_assoc]
  | measure w p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount, ih q _ hq]
    omega

theorem gateProgram_tCount {n s : Nat} (gs : List (TemplateGate n))
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((gateProgram gs).instantiate read history).tCount = ShorECDLP.tCount (gs.flatMap (TemplateGate.instantiate read)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [gateProgram, Straight.instantiate, AdaptiveCircuit.tCount, ShorECDLP.tCount_append, ih]

theorem recordGates_tCount {n s e : Nat} (i : Fin s) (gs : Circuit) (next : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((recordGates i gs next).instantiate read history).tCount =
      ShorECDLP.tCount (if history i then gs else []) + (next.instantiate read history).tCount := by
  induction gs with
  | nil => simp [recordGates, ShorECDLP.tCount]
  | cons g gs ih =>
    simp only [recordGates, Straight.instantiate, AdaptiveCircuit.tCount, ih]
    cases history i <;> simp [ShorECDLP.tCount, Nat.add_assoc]

theorem andEraseProgram_tCount (n start : Nat) (a b t : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((andEraseProgram n start a b t).instantiate read history).tCount = 0 := by
  simp [andEraseProgram, Straight.instantiate, AdaptiveCircuit.tCount, recordGates_tCount,
    controlledZ, ShorECDLP.tCount, ShorECDLP.tCost]

theorem lookupProgram_tCount (n : Nat) (ops : List (LookupOp n)) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((lookupProgram n ops start).instantiate read history).tCount = (lookupCircuit read ops).tCount := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs =>
      simp only [lookupProgram, lookupCircuit]
      rw [append_tCount_fixed _ _ _ _ _ (ih start), gateProgram_tCount]
      rfl
    | erase a b t =>
      simp only [lookupProgram, castFinish_instantiate, lookupCircuit]
      rw [append_tCount_fixed _ _ _ _ _ (ih (start+1)), andEraseProgram_tCount, adaptive_tCount_seq]
      simp [measuredAndErase, measureResetWithCorrection, measuredAndCorrection,
        AdaptiveCircuit.tCount, controlledZ, ShorECDLP.tCount, ShorECDLP.tCost]

end ShorECDLP.Paper2607_13816.ChallengeMigration
