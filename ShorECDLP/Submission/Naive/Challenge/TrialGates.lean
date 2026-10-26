import ShorECDLP.Submission.Naive.Challenge.PointGates

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge

def scalarGates {n : Nat} (pointReg : List Wire) (workStart : Wire) :
    List Wire → List (Fin n) → List (TemplateGate n)
  | c :: cs, r :: rs => controlledPointGates r c pointReg workStart ++
      scalarGates pointReg workStart cs rs
  | _, _ => []

theorem scalarGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (pointReg : List Wire) (workStart : Wire) (controls : List Wire) (rows : List (Fin n)) :
    (scalarGates pointReg workStart controls rows).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      scalarMulCore pointReg workStart controls (rows.map (fun r => constantPoint Q (coeffs r))) := by
  induction controls generalizing rows with
  | nil => cases rows <;> rfl
  | cons c cs ih =>
    cases rows with
    | nil => rfl
    | cons r rs => simp only [scalarGates, List.flatMap_append, controlledPointGates_source,
        ih, List.map_cons, scalarMulCore]

def gPowerRows : List (Fin 512) := List.ofFn fun i : Fin 256 => ⟨i.val, by omega⟩
def qPowerRows : List (Fin 512) := List.ofFn fun i : Fin 256 => ⟨256+i.val, by omega⟩

theorem gPowerRows_source (Q : Point) :
    gPowerRows.map (fun r => constantPoint Q (naivePowerCoefficient r)) =
      Precompute.doublingTable 256 G := by
  simp only [gPowerRows, List.map_ofFn, Precompute.doublingTable]
  apply congrArg List.ofFn
  funext i
  exact naivePowerCoefficient_g Q i

theorem qPowerRows_source (Q : Point) (h : order • Q = 0) :
    qPowerRows.map (fun r => constantPoint Q (naivePowerCoefficient r)) =
      Precompute.doublingTable 256 Q := by
  simp only [qPowerRows, List.map_ofFn, Precompute.doublingTable]
  apply congrArg List.ofFn
  funext i
  exact naivePowerCoefficient_q Q h i

def trialGates : List (TemplateGate 512) :=
  (PhaseEstimation.hadamards (bitcoinAReg ++ bitcoinBReg)).map TemplateGate.literal ++
    scalarGates bitcoinPointReg bitcoinWorkStart bitcoinAReg gPowerRows ++
    scalarGates bitcoinPointReg bitcoinWorkStart bitcoinBReg qPowerRows ++
    (iqft bitcoinAReg bitcoinQFTAncilla ++ iqft bitcoinBReg bitcoinQFTAncilla).map TemplateGate.literal

theorem trialGates_source (Q : Point) (h : order • Q = 0) :
    trialGates.flatMap (TemplateGate.instantiate (readConstant naivePowerCoefficient Q)) =
      ecdlpTrial bitcoinAReg bitcoinBReg bitcoinPointReg bitcoinWorkStart bitcoinQFTAncilla Q := by
  have ha : bitcoinAReg.length = 256 := by simp only [bitcoinAReg, List.length_range']
  have hb : bitcoinBReg.length = 256 := by simp only [bitcoinBReg, List.length_range']
  simp only [trialGates, List.flatMap_append, literalGates_instantiate, scalarGates_source,
    gPowerRows_source, qPowerRows_source Q h, ecdlpTrial, ecdlpOracle, scalarMul, scalarMulTable,
    ha, hb, List.append_assoc]

def trialProgram (cursor : Nat) : Straight 512 cursor cursor := constantGateProgram trialGates cursor

theorem trialProgram_run (Q : Point) (h : order • Q = 0) (cursor : Nat)
    (history : Fin cursor → Bool) :
    ((trialProgram cursor).instantiate (readConstant naivePowerCoefficient Q) history).run =
      (AdaptiveCircuit.unitary
        (ecdlpTrial bitcoinAReg bitcoinBReg bitcoinPointReg bitcoinWorkStart bitcoinQFTAncilla Q) .done).run := by
  rw [trialProgram, constantGateProgram_run, trialGates_source Q h]

theorem constantGateProgram_append_instantiate {n s e : Nat} (gs : List (TemplateGate n))
    (next : Straight n s e) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((constantGateProgram gs s).append next).instantiate read history =
      ((constantGateProgram gs s).instantiate read history).seq (next.instantiate read history) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change AdaptiveCircuit.unitary (g.instantiate read)
      (((constantGateProgram gs s).append next).instantiate read history) = _
    rw [ih]
    rfl

def observedTrialProgram (cursor : Nat) : Straight 512 cursor (cursor + (bitcoinAReg ++ bitcoinBReg).length) :=
  (trialProgram cursor).append (observeWires (bitcoinAReg ++ bitcoinBReg) cursor)

theorem observedTrialProgram_run (Q : Point) (h : order • Q = 0) (cursor : Nat)
    (history : Fin cursor → Bool) :
    ((observedTrialProgram cursor).instantiate (readConstant naivePowerCoefficient Q) history).run =
      (naiveObserved Q).run := by
  rw [observedTrialProgram, trialProgram, constantGateProgram_append_instantiate,
    observeWires_instantiate, AdaptiveCircuit.run_seq, constantGateProgram_run,
    trialGates_source Q h, ← AdaptiveCircuit.run_seq]
  rw [naiveObserved, observedTrial, naive_program_value]
  rfl

end ShorECDLP.NaiveChallenge
