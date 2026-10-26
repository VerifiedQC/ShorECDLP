import ShorECDLP.Submission.Naive.Challenge.StaticResources

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge

theorem straight_append_constant {n s e f : Nat} (p : Straight n s e) (q : Straight n e f)
    (read : ConstantBit n → Bool) (a : AdaptiveCircuit)
    (hq : ∀ history, q.instantiate read history = a) (history : Fin s → Bool) :
    (p.append q).instantiate read history = (p.instantiate read history).seq a := by
  induction p with
  | done => exact hq history
  | gate g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq]
    rw [ih q hq history]
  | recordGate r b g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq]
    rw [ih q hq history]
  | measure w p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.seq]
    rw [ih q hq _, ih q hq _]

def gateNative {n : Nat} (read : ConstantBit n → Bool) : List (TemplateGate n) → AdaptiveCircuit
  | [] => .done
  | g :: gs => .unitary (g.instantiate read) (gateNative read gs)

theorem constantGateProgram_instantiate {n : Nat} (gs : List (TemplateGate n)) (cursor : Nat)
    (read : ConstantBit n → Bool) (history : Fin cursor → Bool) :
    (constantGateProgram gs cursor).instantiate read history = gateNative read gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change AdaptiveCircuit.unitary (g.instantiate read)
      ((constantGateProgram gs cursor).instantiate read history) = _
    rw [ih]
    rfl

def observedNative (read : ConstantBit 512 → Bool) : AdaptiveCircuit :=
  (gateNative read trialGates).seq (zObserve (bitcoinAReg ++ bitcoinBReg))

theorem observedTrialProgram_instantiate (cursor : Nat) (read : ConstantBit 512 → Bool)
    (history : Fin cursor → Bool) :
    (observedTrialProgram cursor).instantiate read history = observedNative read := by
  rw [observedTrialProgram, trialProgram, constantGateProgram_append_instantiate,
    constantGateProgram_instantiate, observeWires_instantiate]
  rfl

def roundNative (read : ConstantBit 512 → Bool) : AdaptiveCircuit :=
  (observedNative read).seq (resetNative fixedResetWires)

def roundProgramRaw (cursor : Nat) :
    Straight 512 cursor ((cursor + (bitcoinAReg ++ bitcoinBReg).length) + fixedResetWires.length) :=
  (observedTrialProgram cursor).append
    (resetWireProgram fixedResetWires (cursor + (bitcoinAReg ++ bitcoinBReg).length))

theorem roundEnd (cursor : Nat) :
    ((cursor + (bitcoinAReg ++ bitcoinBReg).length) + fixedResetWires.length) = cursor+207136 := by
  have hl : (bitcoinAReg ++ bitcoinBReg).length = 512 := by
    simp only [List.length_append, bitcoinAReg, bitcoinBReg, List.length_range']
  have hf : fixedResetWires.length = 206624 := by
    simp only [fixedResetWires, List.length_range, bitcoinQubitCount]
  omega

def roundProgram (cursor : Nat) : Straight 512 cursor (cursor+207136) :=
  castFinish (roundEnd cursor) (roundProgramRaw cursor)

theorem roundProgram_instantiate (cursor : Nat) (read : ConstantBit 512 → Bool)
    (history : Fin cursor → Bool) :
    (roundProgram cursor).instantiate read history = roundNative read := by
  rw [roundProgram, instantiate_castFinish, roundProgramRaw, straight_append_constant _ _ read
    (resetNative fixedResetWires) (fun h => resetWireProgram_instantiate _ _ read h),
    observedTrialProgram_instantiate]
  rfl

theorem roundNative_run (Q : Point) (h : order • Q = 0) :
    (roundNative (readConstant naivePowerCoefficient Q)).run = (fixedResetTrial Q).run := by
  rw [roundNative, AdaptiveCircuit.run_seq, resetNative_run]
  have ho := observedTrialProgram_run Q h 0 Fin.elim0
  rw [observedTrialProgram_instantiate] at ho
  rw [ho, fixedResetTrial, AdaptiveCircuit.run_seq]

def repeatedProgram : (count cursor : Nat) → Straight 512 cursor (cursor+count*207136)
  | 0, cursor => castFinish (by omega) .done
  | count+1, cursor => castFinish (by omega)
      ((roundProgram cursor).append (repeatedProgram count (cursor+207136)))

theorem repeatedProgram_instantiate (count cursor : Nat) (read : ConstantBit 512 → Bool)
    (history : Fin cursor → Bool) :
    (repeatedProgram count cursor).instantiate read history = repeatFixed (roundNative read) count := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
    rw [repeatedProgram, instantiate_castFinish, straight_append_constant _ _ read
      (repeatFixed (roundNative read) count) (fun h => ih _ h), roundProgram_instantiate]
    rfl

theorem repeatFixed_run_congr (a b : AdaptiveCircuit) (h : a.run = b.run) (count : Nat) :
    (repeatFixed a count).run = (repeatFixed b count).run := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [repeatFixed, AdaptiveCircuit.run_seq, h, ih]

theorem repeatedProgram_run (Q : Point) (h : order • Q = 0) (cursor : Nat)
    (history : Fin cursor → Bool) :
    ((repeatedProgram 26 cursor).instantiate (readConstant naivePowerCoefficient Q) history).run =
      (fixedRepeated Q).run := by
  rw [repeatedProgram_instantiate]
  exact repeatFixed_run_congr _ _ (roundNative_run Q h) 26

def castTable {n m s e : Nat} (h : n = m) (p : Straight n s e) : Straight m s e := h ▸ p

theorem castTable_instantiate {n m s e : Nat} (h : n = m) (p : Straight n s e)
    (read : ConstantBit m → Bool) (history : Fin s → Bool) :
    (castTable h p).instantiate read history =
      p.instantiate (fun r => read ⟨Fin.cast h r.point, r.field, r.bit⟩) history := by
  subst m
  rfl

theorem castTable_wellFormed {n m s e : Nat} (h : n = m) (p : Straight n s e) :
    (castTable h p).WellFormed = p.WellFormed := by subst m; rfl

def naiveRepeatedEntry : StraightEntry where
  coefficients := naivePowerTable
  finalCursor := 0+26*207136
  program := castTable naivePowerTable_length.symm (repeatedProgram 26 0)

theorem naivePowerTable_read (Q : Point) :
    (fun r : ConstantBit 512 => readConstant naivePowerTable.get Q
      ⟨Fin.cast naivePowerTable_length.symm r.point, r.field, r.bit⟩) =
      readConstant naivePowerCoefficient Q := by
  funext r
  have hg : naivePowerTable.get (Fin.cast naivePowerTable_length.symm r.point) =
      naivePowerCoefficient r.point := naivePowerTable_get r.point
  simp only [readConstant]
  rw [hg]

theorem naiveRepeatedEntry_instantiate (Q : Point) :
    naiveRepeatedEntry.instantiate Q = repeatFixed (roundNative (readConstant naivePowerCoefficient Q)) 26 := by
  dsimp only [StraightEntry.instantiate, naiveRepeatedEntry]
  rw [castTable_instantiate, naivePowerTable_read, repeatedProgram_instantiate]

theorem naiveRepeatedEntry_run (Q : Point) (h : order • Q = 0) :
    (naiveRepeatedEntry.instantiate Q).run = (fixedRepeated Q).run := by
  rw [naiveRepeatedEntry_instantiate]
  exact repeatFixed_run_congr _ _ (roundNative_run Q h) 26

attribute [local irreducible] fixedResetWires trialGates Straight.WellFormed

theorem castFinish_WF {n s e f : Nat} (h : e = f) (p : Straight n s e)
    (hp : p.WellFormed) : (castFinish h p).WellFormed :=
  Eq.mpr (wellFormed_castFinish h p) hp

theorem roundProgram_wellFormed (cursor : Nat) : (roundProgram cursor).WellFormed := by
  have hr := resetWireProgram_wellFormed (n := 512) fixedResetWires
    (cursor+(bitcoinAReg++bitcoinBReg).length)
  have ha := straight_append_wellFormed (observedTrialProgram cursor)
    (resetWireProgram fixedResetWires (cursor+(bitcoinAReg++bitcoinBReg).length))
    (observedTrialProgram_wellFormed cursor) hr
  have hc := castFinish_WF (roundEnd cursor) (roundProgramRaw cursor) ha
  exact hc

theorem repeatedProgram_wellFormed (count cursor : Nat) : (repeatedProgram count cursor).WellFormed := by
  induction count generalizing cursor with
  | zero =>
    exact castFinish_WF (by omega) (.done : Straight 512 cursor cursor) (by unfold Straight.WellFormed; trivial)
  | succ count ih =>
    have ha := straight_append_wellFormed (roundProgram cursor) (repeatedProgram count (cursor+207136))
      (roundProgram_wellFormed cursor) (ih (cursor+207136))
    have hc := castFinish_WF (by omega : cursor + 207136 + count * 207136 = cursor + (count+1)*207136)
      ((roundProgram cursor).append (repeatedProgram count (cursor+207136))) ha
    exact hc

attribute [local irreducible] repeatedProgram naivePowerTable

theorem naiveRepeatedEntry_wellFormed : naiveRepeatedEntry.program.WellFormed := by
  have h := Eq.mpr (castTable_wellFormed naivePowerTable_length.symm (repeatedProgram 26 0))
    (repeatedProgram_wellFormed 26 0)
  exact h

theorem naiveRepeatedEntry_success (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    (99/100 : ℝ) ≤ Instrument.bornMass ((naiveRepeatedEntry.instantiate Q).run.filter
      (fun b => fixedRepeatedSuccess d b.history)) (ket zeroBasisState) := by
  have ho : order • Q = 0 := by rw [hQ]; exact dlogPoint_order d
  rw [naiveRepeatedEntry_run Q ho]
  exact fixedRepeated_success Q d hQ hn

/-- Bounds for the entire 26-round submitted syntax, including every reset. -/
def repeatedStaticBounds : Bounds :=
  ⟨(straightWires naiveRepeatedEntry.program).dedup.length,
    straightT naiveRepeatedEntry.program, 5385536⟩

theorem naiveRepeatedEntry_resources (Q : Point) :
    (resources (naiveRepeatedEntry.instantiate Q)).qubits ≤ repeatedStaticBounds.qubits ∧
    (resources (naiveRepeatedEntry.instantiate Q)).tModel ≤ repeatedStaticBounds.tModel ∧
    (resources (naiveRepeatedEntry.instantiate Q)).measurements = 5385536 := by
  dsimp only [resources, repeatedStaticBounds, StraightEntry.instantiate]
  refine ⟨straight_qubit_bound naiveRepeatedEntry.program
    (readConstant naiveRepeatedEntry.coefficients.get Q) Fin.elim0,
    straight_t_bound naiveRepeatedEntry.program
    (readConstant naiveRepeatedEntry.coefficients.get Q) Fin.elim0, ?_⟩
  rw [Straight.measurementCount]
  rfl

/-- The recorded sample in round t starts after t complete observation/reset rounds. -/
def repeatedSampleStart (t : Fin 26) : Nat := t.val * 207136

theorem repeatedSampleStart_bound (t : Fin 26) (i : Fin 512) :
    repeatedSampleStart t + i.val < naiveRepeatedEntry.finalCursor := by
  have ht := t.isLt
  have hi := i.isLt
  dsimp only [repeatedSampleStart, naiveRepeatedEntry]
  omega

end ShorECDLP.NaiveChallenge
