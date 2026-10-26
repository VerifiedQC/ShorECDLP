import ShorECDLP.Submission.Naive.Challenge.Certificate

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge Arithmetic
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

def templateT {n : Nat} (gs : List (TemplateGate n)) : Nat :=
  (gs.map (fun g => tCost (slotGate g))).sum

@[simp] theorem templateT_append {n : Nat} (a b : List (TemplateGate n)) :
    templateT (a++b) = templateT a + templateT b := by simp [templateT]
@[simp] theorem templateT_reverse {n : Nat} (gs : List (TemplateGate n)) :
    templateT gs.reverse = templateT gs := by simp [templateT, List.map_reverse]
@[simp] theorem templateT_literal {n : Nat} (c : Circuit) :
    templateT (c.map (TemplateGate.literal (tableSize := n))) = tCount c := by
  simp only [templateT, tCount, List.map_map]
  rfl

@[simp] theorem templateT_fieldLoad {n : Nat} (row : Fin n) (f : PointField)
    (ws : List Wire) (i : Nat) : templateT (fieldLoadGates row f ws i) = 0 := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    simp only [fieldLoadGates, templateT_append, ih, Nat.add_zero]
    split <;> simp [templateT, slotGate, tCost]

@[simp] theorem fieldLoad_tCount {n : Nat} (row : Fin n) (f : PointField)
    (read : ConstantBit n → Bool) (ws : List Wire) (i : Nat) :
    tCount ((fieldLoadGates row f ws i).flatMap (TemplateGate.instantiate read)) = 0 := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    simp only [fieldLoadGates, List.flatMap_append, tCount_append, ih, Nat.add_zero]
    split
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TemplateGate.instantiate]
      split <;> simp [tCount, tCost]
    · rfl

@[simp] theorem templateT_packedLoad {n : Nat} (row : Fin n) (ws : List Wire) (i : Nat) :
    templateT (packedLoadGates row ws i) = 0 := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    simp only [packedLoadGates, templateT_append, ih, Nat.add_zero]
    unfold packedGate
    split
    · simp [templateT, slotGate, tCost]
    · split
      · simp [templateT, slotGate, tCost]
      · split <;> simp [templateT, slotGate, tCost]

@[simp] theorem packedLoad_tCount {n : Nat} (row : Fin n) (read : ConstantBit n → Bool)
    (ws : List Wire) (i : Nat) :
    tCount ((packedLoadGates row ws i).flatMap (TemplateGate.instantiate read)) = 0 := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    simp only [packedLoadGates, List.flatMap_append, tCount_append, ih, Nat.add_zero]
    unfold packedGate
    split
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TemplateGate.instantiate]
      split <;> simp [tCount, tCost]
    · split
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TemplateGate.instantiate]
        split <;> simp [tCount, tCost]
      · split
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TemplateGate.instantiate]
          split <;> simp [tCount, tCost]
        · rfl

/-- Before the infinity guard, only zero-T X loads depend on constant bits. -/
theorem finiteOut_templateT {n : Nat} (row : Fin n) (control : Wire)
    (pointReg outReg : List Wire) (workStart : Wire) (read : ConstantBit n → Bool) :
    templateT (finiteControlledOutGates row control pointReg outReg workStart) =
    tCount ((finiteControlledOutGates row control pointReg outReg workStart).flatMap
      (TemplateGate.instantiate read)) := by
  simp only [finiteControlledOutGates, finiteComputeGates, pointFlagGates,
    genericBranchGates, genericPointGates, infinityBranchGates, fieldSubConstGates,
    templateT_append, templateT_reverse, templateT_literal, templateT_fieldLoad,
    templateT_packedLoad, List.flatMap_append, template_reverse, literalGates_instantiate,
    tCount_append, tCount_reverse, fieldLoad_tCount, packedLoad_tCount]

@[simp] theorem templateT_guard {n : Nat} (row : Fin n) (gs : List (TemplateGate n)) :
    templateT (gs.map (guardSlot row)) = templateT gs := by
  unfold templateT
  rw [List.map_map]
  congr 2
  funext g
  cases g <;> rfl

@[simp] theorem templateT_reindex {m n : Nat} (f : ConstantBit m → ConstantBit n)
    (gs : List (TemplateGate m)) : templateT (gs.map (reindexSlot f)) = templateT gs := by
  unfold templateT
  rw [List.map_map]
  congr 2
  funext g
  cases g <;> rfl

@[simp] theorem templateT_copy {n : Nat} (ref : ConstantBit n) (b : Bool)
    (src dst : List Wire) :
    templateT ((copyReg src dst).map (fun g => TemplateGate.whenBit ref b g)) = 0 := by
  induction src generalizing dst with
  | nil => rfl
  | cons s src ih =>
    cases dst with
    | nil => rfl
    | cons d dst =>
      simpa only [copyReg, List.map_cons, templateT, List.sum_cons, slotGate, tCost, Nat.zero_add] using ih dst

theorem controlledOut_templateT {n : Nat} (row : Fin n) (control : Wire)
    (pointReg outReg : List Wire) (workStart : Wire) (read : ConstantBit n → Bool)
    (hr : read ⟨row, .infinity, 0⟩ = false) :
    templateT (controlledOutGates row control pointReg outReg workStart) =
    tCount ((controlledOutGates row control pointReg outReg workStart).flatMap
      (TemplateGate.instantiate read)) := by
  simp only [controlledOutGates, templateT_append, templateT_guard, templateT_copy,
    Nat.add_zero, List.flatMap_append, tCount_append, guardSlot_finite row read hr]
  have hc : ((copyReg pointReg outReg).map
      (fun g => TemplateGate.whenBit ⟨row, .infinity, 0⟩ true g)).flatMap
        (TemplateGate.instantiate read) = [] := by
    simp [List.flatMap_map, TemplateGate.instantiate, hr]
  rw [hc]
  simpa using finiteOut_templateT row control pointReg outReg workStart read

theorem controlledPoint_templateT {n : Nat} (row : Fin n) (control : Wire)
    (pointReg : List Wire) (workStart : Wire) (hlen : pointReg.length = pointWidth) :
    templateT (controlledPointGates row control pointReg workStart) = 669924831604 := by
  let read := readConstant (fun _ : Fin n => qCoefficient) G
  have hr : read ⟨row, .infinity, 0⟩ = false := by
    simp [read, readConstant, qCoefficient_point, fieldValue, pointCoordinates, G]
  have hn : (fun r => read (negRowRef row r)) ⟨0, .infinity, 0⟩ = false := hr
  have h := controlledPointGates_source (fun _ : Fin n => qCoefficient) G row control pointReg workStart
  have ht := congrArg tCount h
  simp only [controlledPointGates, List.flatMap_append, tCount_append, template_reverse,
    tCount_reverse, literalGates_instantiate, negControlledOutGates, reindexSlot_source] at ht
  rw [← controlledOut_templateT row _ _ _ _ read hr,
    ← controlledOut_templateT (0 : Fin 1) _ _ _ _ (fun r => read (negRowRef row r)) hn] at ht
  simpa only [controlledPointGates, templateT_append, templateT_literal, templateT_reverse,
    negControlledOutGates, templateT_reindex, qCoefficient_point,
    controlledPointAdd_tCount_of_ne_zero _ _ _ G G_ne_zero hlen] using ht

theorem scalarGates_templateT {n : Nat} (pointReg : List Wire) (workStart : Wire)
    (hlen : pointReg.length = pointWidth) (cs : List Wire) (rs : List (Fin n)) :
    templateT (scalarGates pointReg workStart cs rs) = min cs.length rs.length * 669924831604 := by
  induction cs generalizing rs with
  | nil => cases rs <;> simp [scalarGates, templateT]
  | cons c cs ih =>
    cases rs with
    | nil => simp [scalarGates, templateT]
    | cons r rs =>
      simp only [scalarGates, templateT_append, controlledPoint_templateT r c pointReg workStart hlen,
        ih, List.length_cons]
      omega

theorem templateT_trial : templateT trialGates = 343001514760448 := by
  have hh (ws : List Wire) : tCount (PhaseEstimation.hadamards ws) = 0 := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simpa [PhaseEstimation.hadamards, tCount, tCost] using ih
  have hp : bitcoinPointReg.length = pointWidth := by simp [bitcoinPointReg, pointWidth]
  simp only [trialGates, templateT_append, templateT_literal, hh,
    scalarGates_templateT _ _ hp, tCount_append, tCount_iqft,
    bitcoinAReg, bitcoinBReg, List.length_range', gPowerRows, qPowerRows, List.length_ofFn]
  norm_num

@[simp] theorem straightT_append {n a b c : Nat} (p : Straight n a b) (q : Straight n b c) :
    straightT (p.append q) = straightT p + straightT q := by
  induction p with
  | done => simp only [Straight.append, straightT, Nat.zero_add]
  | gate g p ih => simpa only [Straight.append, straightT, Nat.add_assoc] using congrArg (fun x => tCost (slotGate g) + x) (ih q)
  | recordGate r b g p ih => simpa only [Straight.append, straightT, Nat.add_assoc] using congrArg (fun x => tCost g + x) (ih q)
  | measure w p ih => exact ih q

@[simp] theorem straightT_castFinish {n s e f : Nat} (h : e=f) (p : Straight n s e) :
    straightT (castFinish h p) = straightT p := by subst f; rfl
@[simp] theorem straightT_castTable {n m s e : Nat} (h : n=m) (p : Straight n s e) :
    straightT (castTable h p) = straightT p := by subst m; rfl

@[simp] theorem straightT_constant {n : Nat} (gs : List (TemplateGate n)) (cursor : Nat) :
    straightT (constantGateProgram gs cursor) = templateT gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change tCost (slotGate g) + straightT (constantGateProgram gs cursor) = _
    rw [ih]
    rfl

@[simp] theorem straightT_observe {n : Nat} (ws : List Wire) (cursor : Nat) :
    straightT (observeWires (n := n) ws cursor) = 0 := by
  induction ws generalizing cursor with
  | nil => rfl
  | cons w ws ih => simp only [observeWires, straightT_castFinish, straightT, slotGate, tCost, Nat.zero_add, ih]

@[simp] theorem straightT_reset {n : Nat} (ws : List Wire) (cursor : Nat) :
    straightT (resetWireProgram (n := n) ws cursor) = 0 := by
  induction ws generalizing cursor with
  | nil => rfl
  | cons w ws ih => simp only [resetWireProgram, straightT_castFinish, straightT, ih]

attribute [local irreducible] trialGates fixedResetWires naivePowerTable

theorem straightT_round (cursor : Nat) : straightT (roundProgram cursor) = 343001514760448 := by
  simp only [roundProgram, straightT_castFinish, roundProgramRaw, straightT_append,
    observedTrialProgram, trialProgram, straightT_constant, straightT_observe, straightT_reset,
    templateT_trial, Nat.add_zero]

theorem straightT_repeated (count cursor : Nat) :
    straightT (repeatedProgram count cursor) = count * 343001514760448 := by
  induction count generalizing cursor with
  | zero => simp only [repeatedProgram, straightT_castFinish, straightT, Nat.zero_mul]
  | succ count ih =>
    simp only [repeatedProgram, straightT_castFinish, straightT_append, straightT_round, ih]
    omega

attribute [local irreducible] repeatedProgram

theorem repeatedStaticBounds_tModel : repeatedStaticBounds.tModel = 8918039383771648 := by
  dsimp only [repeatedStaticBounds, naiveRepeatedEntry]
  rw [straightT_castTable, straightT_repeated]

theorem naiveRepeatedEntry_tModel_bound (Q : Point) :
    (resources (naiveRepeatedEntry.instantiate Q)).tModel ≤ 8918039383771648 := by
  have h := (naiveRepeatedEntry_resources Q).2.1
  rw [repeatedStaticBounds_tModel] at h
  exact h

end ShorECDLP.NaiveChallenge
