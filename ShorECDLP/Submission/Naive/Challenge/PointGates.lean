import ShorECDLP.Submission.Naive.Challenge.Constants

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge Arithmetic

theorem template_reverse {n : Nat} (read : ConstantBit n → Bool)
    (gs : List (TemplateGate n)) :
    gs.reverse.flatMap (TemplateGate.instantiate read) =
      (gs.flatMap (TemplateGate.instantiate read)).reverse := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.reverse_append, ih]
    congr 1
    cases g with
    | literal g => rfl
    | whenBit ref b g => simp only [TemplateGate.instantiate]; split <;> rfl

/-- Generic affine branch with fixed field references. -/
def genericPointGates {n : Nat} (row : Fin n) (workStart : Wire) : List (TemplateGate n) :=
  let offset := pointAddArithmeticOffset workStart
  let x := pointAddX workStart
  let y := pointAddY workStart
  let t0 := pointAddT0 workStart
  let t1 := pointAddT1 workStart
  let t2 := pointAddT2 workStart
  let t3 := pointAddT3 workStart
  let t4 := pointAddT4 workStart
  let numerator := fieldSubConstGates row .y offset y t0
  let denominator := fieldSubConstGates row .x offset x t1
  let inverse := (fieldInv offset t1 t2).map TemplateGate.literal
  let slope := (fieldMul offset t0 t2 t3).map TemplateGate.literal
  let slopeSq := (fieldMul offset t3 t3 t0).map TemplateGate.literal
  let minusX := (fieldSub offset t0 x t1).map TemplateGate.literal
  let xOut := fieldSubConstGates row .x offset t1 t2
  let xDifference := (fieldSub offset x t2 t0).map TemplateGate.literal
  let yProduct := (fieldMul offset t3 t0 t1).map TemplateGate.literal
  let yOut := (fieldSub offset t1 y t4).map TemplateGate.literal
  numerator ++ denominator ++ inverse ++ slope ++ inverse.reverse ++ denominator.reverse ++
    numerator.reverse ++ slopeSq ++ minusX ++ xOut ++ minusX.reverse ++ slopeSq.reverse ++
    xDifference ++ yProduct ++ yOut

theorem genericPointGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (workStart : Wire) :
    (genericPointGates row workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      genericPointCompute workStart (pointCoordinates (constantPoint Q (coeffs row))).2.1
        (pointCoordinates (constantPoint Q (coeffs row))).2.2 := by
  simp only [genericPointGates, List.flatMap_append, template_reverse,
    literalGates_instantiate, fieldSubConstGates_source, fieldValue, genericPointCompute,
    List.append_assoc]

def pointFlagGates {n : Nat} (row : Fin n) (pointReg : List Wire)
    (workStart : Wire) : List (TemplateGate n) :=
  let constReg := pointAddConst workStart
  let infinityFlag := pointAddInfinityFlag workStart
  let xEqFlag := pointAddXEqFlag workStart
  let yNegFlag := pointAddYNegFlag workStart
  let genericFlag := pointAddGenericFlag workStart
  let pairFlag := pointAddPairFlag workStart
  let doubleFlag := pointAddDoubleFlag workStart
  (zeroFlag (PointRegister.tag pointReg) infinityFlag (pointAddZeroHistory workStart)).map
    TemplateGate.literal ++
  fieldLoadGates row .x constReg 0 ++
  (equalFlag (PointRegister.x pointReg) constReg xEqFlag
    (pointAddXDifference workStart) (pointAddXHistory workStart)).map TemplateGate.literal ++
  fieldLoadGates row .x constReg 0 ++
  fieldLoadGates row .negY constReg 0 ++
  (equalFlag (PointRegister.y pointReg) constReg yNegFlag
    (pointAddYDifference workStart) (pointAddYHistory workStart)).map TemplateGate.literal ++
  fieldLoadGates row .negY constReg 0 ++
  ([.X infinityFlag, .X xEqFlag, .CCX infinityFlag xEqFlag genericFlag,
    .X xEqFlag, .X infinityFlag, .X yNegFlag, .CCX xEqFlag yNegFlag pairFlag,
    .X yNegFlag, .X infinityFlag, .CCX infinityFlag pairFlag doubleFlag,
    .X infinityFlag] : Circuit).map TemplateGate.literal

theorem pointFlagGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (pointReg : List Wire) (workStart : Wire) :
    (pointFlagGates row pointReg workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      pointAddFlags pointReg workStart (pointCoordinates (constantPoint Q (coeffs row))).2.1
        (pointCoordinates (constantPoint Q (coeffs row))).2.2 := by
  simp only [pointFlagGates, List.flatMap_append, literalGates_instantiate,
    fieldLoadGates_source, fieldValue, pointAddFlags, List.append_assoc]

theorem packed_x_bit (P : Point) (i : Fin 256) :
    (fieldValue P .x).testBit i.val = (encode P).val.testBit (i.val+1) := by
  cases P with
  | zero =>
    change Nat.testBit 0 _ = Nat.testBit 0 _
    simp
  | @some x y h =>
    have hx := congrArg (fun k : Nat => k.testBit i.val) (xBits_encode_some h)
    simp only [xBits, Nat.testBit_mod_two_pow, decide_eq_true i.isLt,
      Bool.true_and, Nat.testBit_div_two] at hx
    exact hx.symm

theorem packed_y_bit (P : Point) (i : Fin 256) :
    (fieldValue P .y).testBit i.val = (encode P).val.testBit (i.val+257) := by
  cases P with
  | zero =>
    change Nat.testBit 0 _ = Nat.testBit 0 _
    simp
  | @some x y h =>
    have hy := congrArg (fun k : Nat => k.testBit i.val) (yBits_encode_some h)
    simp only [yBits, Nat.testBit_div_two_pow, Nat.testBit_div_two, Nat.add_assoc] at hy
    exact hy.symm

def packedGate {n : Nat} (row : Fin n) (w : Wire) (i : Nat) : List (TemplateGate n) :=
  if i = 0 then [.whenBit ⟨row, .infinity, 0⟩ false (.X w)]
  else if h : i < 257 then [.whenBit ⟨row, .x, ⟨i-1, by omega⟩⟩ true (.X w)]
  else if h : i < 513 then [.whenBit ⟨row, .y, ⟨i-257, by omega⟩⟩ true (.X w)]
  else []

theorem packedGate_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (w : Wire) (i : Nat) :
    (packedGate row w i).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      if (encode (constantPoint Q (coeffs row))).val.testBit i = true then [.X w] else [] := by
  let P := constantPoint Q (coeffs row)
  change (packedGate row w i).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      if (encode P).val.testBit i = true then [.X w] else []
  by_cases hz : i = 0
  · subst i
    simp only [packedGate, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, TemplateGate.instantiate, readConstant]
    change (if (fieldValue P .infinity).testBit 0 = false then _ else _) = _
    cases P with
    | zero => rfl
    | @some x y h =>
      have ht := finiteFlag_encode_some h
      change (encode (.some h)).val % 2 = 1 at ht
      change (if Nat.testBit 0 0 = false then _ else _) = _
      simp only [Nat.testBit_zero, ht]
      rfl
  · by_cases hx : i < 257
    · have he := packed_x_bit P ⟨i-1, by omega⟩
      have hi : i-1+1=i := by omega
      simp only [hi] at he
      simp only [packedGate, if_neg hz, dif_pos hx, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, TemplateGate.instantiate, readConstant]
      change (if (fieldValue P .x).testBit (i-1) = true then _ else _) = _
      rw [he]
    · by_cases hy : i < 513
      · have he := packed_y_bit P ⟨i-257, by omega⟩
        have hi : i-257+257=i := by omega
        simp only [hi] at he
        simp only [packedGate, if_neg hz, dif_neg hx, dif_pos hy, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, TemplateGate.instantiate, readConstant]
        change (if (fieldValue P .y).testBit (i-257) = true then _ else _) = _
        rw [he]
      · have hb : (encode P).val.testBit i = false := Nat.testBit_eq_false_of_lt
          ((encode P).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by
            change 513 ≤ i; omega)))
        simp only [packedGate, if_neg hz, dif_neg hx, dif_neg hy,
          List.flatMap_nil, hb, Bool.false_eq_true, if_false]

def packedLoadGates {n : Nat} (row : Fin n) : List Wire → Nat → List (TemplateGate n)
  | [], _ => []
  | w :: ws, i => packedGate row w i ++ packedLoadGates row ws (i+1)

theorem packedLoadGates_source_aux {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (ws : List Wire) (i : Nat) :
    (packedLoadGates row ws i).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      loadConst ws ((encode (constantPoint Q (coeffs row))).val / 2^i) := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    simp only [packedLoadGates, List.flatMap_append, packedGate_source, ih,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, loadConst,
      Nat.div_div_eq_div_mul, pow_succ]

theorem packedLoadGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (ws : List Wire) :
    (packedLoadGates row ws 0).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      loadConst ws (encode (constantPoint Q (coeffs row))).val := by
  simpa only [pow_zero, Nat.div_one] using packedLoadGates_source_aux coeffs Q row ws 0

def genericBranchGates {n : Nat} (row : Fin n) (workStart : Wire) : List (TemplateGate n) :=
  let compute := genericPointGates row workStart
  let pack := packFinitePoint (pointAddT2 workStart) (pointAddT4 workStart)
    (pointAddCandidate workStart)
  compute ++ pack.map TemplateGate.literal ++
    (controlledCopyReg (pointAddGenericFlag workStart) (pointAddCandidate workStart)
      (pointAddSelected workStart)).map TemplateGate.literal ++
    pack.reverse.map TemplateGate.literal ++ compute.reverse

theorem genericBranchGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (workStart : Wire) :
    (genericBranchGates row workStart).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      genericPointBranch workStart (pointCoordinates (constantPoint Q (coeffs row))).2.1
        (pointCoordinates (constantPoint Q (coeffs row))).2.2 := by
  simp only [genericBranchGates, List.flatMap_append, template_reverse,
    literalGates_instantiate, genericPointGates_source, genericPointBranch, List.append_assoc]

def infinityBranchGates {n : Nat} (row : Fin n) (workStart : Wire) : List (TemplateGate n) :=
  let load := packedLoadGates row (pointAddCandidate workStart) 0
  load ++ (controlledCopyReg (pointAddInfinityFlag workStart) (pointAddCandidate workStart)
    (pointAddSelected workStart)).map TemplateGate.literal ++ load

theorem infinityBranchGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (workStart : Wire) :
    (infinityBranchGates row workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      infinityPointBranch workStart (constantPoint Q (coeffs row)) := by
  simp only [infinityBranchGates, List.flatMap_append, packedLoadGates_source,
    literalGates_instantiate, infinityPointBranch, List.append_assoc]

def finiteComputeGates {n : Nat} (row : Fin n) (pointReg : List Wire) (workStart : Wire) :
    List (TemplateGate n) :=
  (pointAddCoordinateCopies pointReg workStart).map TemplateGate.literal ++
    pointFlagGates row pointReg workStart ++ genericBranchGates row workStart ++
    (doublePointBranch workStart).map TemplateGate.literal ++ infinityBranchGates row workStart

theorem finiteComputeGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (pointReg : List Wire) (workStart : Wire)
    {x y : Fp} (h : curve.toAffine.Nonsingular x y)
    (hp : constantPoint Q (coeffs row) = .some h) :
    (finiteComputeGates row pointReg workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      pointAddFiniteCompute pointReg workStart h := by
  simp only [finiteComputeGates, List.flatMap_append, literalGates_instantiate,
    pointFlagGates_source, genericBranchGates_source, infinityBranchGates_source,
    hp, pointCoordinates, pointAddFiniteCompute, pointAddSetup, pointAddBranches,
    List.append_assoc]

def finiteControlledOutGates {n : Nat} (row : Fin n) (control : Wire)
    (pointReg outReg : List Wire) (workStart : Wire) : List (TemplateGate n) :=
  let choice := controlledPointAddChoice workStart
  let pointWorkStart := controlledPointAddPointWorkStart workStart
  let compute := finiteComputeGates row pointReg pointWorkStart ++
    (selectPoint control pointReg (pointAddSelected pointWorkStart) choice).map TemplateGate.literal
  compute ++ (copyReg choice outReg).map TemplateGate.literal ++ compute.reverse

theorem finiteControlledOutGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (control : Wire) (pointReg outReg : List Wire) (workStart : Wire)
    {x y : Fp} (h : curve.toAffine.Nonsingular x y)
    (hp : constantPoint Q (coeffs row) = .some h) :
    (finiteControlledOutGates row control pointReg outReg workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      controlledPointAddOut control pointReg outReg workStart (constantPoint Q (coeffs row)) := by
  simp only [finiteControlledOutGates, List.flatMap_append, template_reverse,
    literalGates_instantiate, finiteComputeGates_source coeffs Q row _ _ h hp,
    hp, controlledPointAddOut, List.append_assoc]

def guardSlot {n : Nat} (row : Fin n) : TemplateGate n → TemplateGate n
  | .literal g => .whenBit ⟨row, .infinity, 0⟩ false g
  | .whenBit r b g => .whenBit r b g

def variableCircuit {n : Nat} (read : ConstantBit n → Bool) (gs : List (TemplateGate n)) : Circuit :=
  gs.flatMap fun g => match g with
    | .literal _ => []
    | .whenBit r b g => TemplateGate.instantiate read (.whenBit r b g)

theorem guardSlot_finite {n : Nat} (row : Fin n) (read : ConstantBit n → Bool)
    (h : read ⟨row, .infinity, 0⟩ = false) (gs : List (TemplateGate n)) :
    (gs.map (guardSlot row)).flatMap (TemplateGate.instantiate read) =
      gs.flatMap (TemplateGate.instantiate read) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.flatMap_cons, ih]
    congr 1
    cases g <;> simp [guardSlot, TemplateGate.instantiate, h]

theorem guardSlot_zero {n : Nat} (row : Fin n) (read : ConstantBit n → Bool)
    (h : read ⟨row, .infinity, 0⟩ = true) (gs : List (TemplateGate n)) :
    (gs.map (guardSlot row)).flatMap (TemplateGate.instantiate read) = variableCircuit read gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.flatMap_cons, ih, variableCircuit]
    cases g <;> simp [guardSlot, TemplateGate.instantiate, h]

@[simp] theorem variableCircuit_append {n : Nat} (read : ConstantBit n → Bool)
    (a b : List (TemplateGate n)) :
    variableCircuit read (a++b) = variableCircuit read a ++ variableCircuit read b :=
  List.flatMap_append

@[simp] theorem variableCircuit_literal {n : Nat} (read : ConstantBit n → Bool) (c : Circuit) :
    variableCircuit read (c.map TemplateGate.literal) = [] := by
  induction c with
  | nil => rfl
  | cons g gs ih => simp [variableCircuit, List.flatMap_map]

@[simp] theorem variableCircuit_reverse {n : Nat} (read : ConstantBit n → Bool)
    (gs : List (TemplateGate n)) :
    variableCircuit read gs.reverse = (variableCircuit read gs).reverse := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.reverse_cons, variableCircuit_append, ih]
    have hc : variableCircuit read (g :: gs) =
        variableCircuit read (g :: []) ++ variableCircuit read gs := by
      simp [variableCircuit]
    rw [hc]
    rw [List.reverse_append]
    congr 1
    cases g with
    | literal g => rfl
    | whenBit r b g =>
      simp only [variableCircuit, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        TemplateGate.instantiate]
      split <;> rfl

@[simp] theorem variableCircuit_fieldLoad {n : Nat} (read : ConstantBit n → Bool)
    (row : Fin n) (field : PointField) (ws : List Wire) (i : Nat) :
    variableCircuit read (fieldLoadGates row field ws i) =
      (fieldLoadGates row field ws i).flatMap (TemplateGate.instantiate read) := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    simp only [fieldLoadGates, variableCircuit_append, List.flatMap_append, ih]
    congr 1
    split <;> rfl

@[simp] theorem variableCircuit_packedLoad {n : Nat} (read : ConstantBit n → Bool)
    (row : Fin n) (ws : List Wire) (i : Nat) :
    variableCircuit read (packedLoadGates row ws i) =
      (packedLoadGates row ws i).flatMap (TemplateGate.instantiate read) := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    simp only [packedLoadGates, variableCircuit_append, List.flatMap_append, ih]
    congr 1
    unfold packedGate
    split
    · rfl
    · split
      · rfl
      · split <;> rfl

theorem loadConst_zero (ws : List Wire) : loadConst ws 0 = [] := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa only [loadConst, Nat.zero_mod, Nat.zero_div, Nat.zero_ne_one,
      if_false, List.nil_append] using ih

theorem finiteControlledOutGates_variables_zero {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (control : Wire) (pointReg outReg : List Wire) (workStart : Wire)
    (hp : constantPoint Q (coeffs row) = 0) :
    variableCircuit (readConstant coeffs Q)
      (finiteControlledOutGates row control pointReg outReg workStart) = [] := by
  simp only [finiteControlledOutGates, finiteComputeGates, pointFlagGates, genericBranchGates,
    genericPointGates, infinityBranchGates, fieldSubConstGates,
    variableCircuit_append, variableCircuit_reverse, variableCircuit_literal,
    variableCircuit_fieldLoad, variableCircuit_packedLoad,
    fieldLoadGates_source, packedLoadGates_source, hp]
  change _ = []
  simp only [fieldValue, pointCoordinates, neg_zero, ZMod.val_zero, encode_val, encodeNat_zero,
    loadConst_zero, List.nil_append, List.reverse_nil]

def controlledOutGates {n : Nat} (row : Fin n) (control : Wire)
    (pointReg outReg : List Wire) (workStart : Wire) : List (TemplateGate n) :=
  (finiteControlledOutGates row control pointReg outReg workStart).map (guardSlot row) ++
    (copyReg pointReg outReg).map (fun g => TemplateGate.whenBit ⟨row, .infinity, 0⟩ true g)

theorem controlledOutGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (control : Wire) (pointReg outReg : List Wire) (workStart : Wire) :
    (controlledOutGates row control pointReg outReg workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      controlledPointAddOut control pointReg outReg workStart (constantPoint Q (coeffs row)) := by
  generalize hp : constantPoint Q (coeffs row) = P
  cases P with
  | zero =>
    have hr : readConstant coeffs Q ⟨row, .infinity, 0⟩ = true := by
      simp only [readConstant, hp, fieldValue, pointCoordinates]
      rfl
    simp only [controlledOutGates, List.flatMap_append, guardSlot_zero row _ hr,
      finiteControlledOutGates_variables_zero coeffs Q row control pointReg outReg workStart hp,
      List.nil_append, controlledPointAddOut]
    induction copyReg pointReg outReg with
    | nil => rfl
    | cons g gs ih => simp [TemplateGate.instantiate, hr, ih]
  | @some x y h =>
    have hr : readConstant coeffs Q ⟨row, .infinity, 0⟩ = false := by
      simp only [readConstant, hp, fieldValue, pointCoordinates]
      rfl
    simp only [controlledOutGates, List.flatMap_append, guardSlot_finite row _ hr,
      finiteControlledOutGates_source coeffs Q row control pointReg outReg workStart h hp, hp]
    have hz : ((copyReg pointReg outReg).map
      (fun g => TemplateGate.whenBit ⟨row, .infinity, 0⟩ true g)).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) = [] := by
      induction copyReg pointReg outReg with
      | nil => rfl
      | cons g gs ih => simp [TemplateGate.instantiate, hr, ih]
    rw [hz, List.append_nil]

theorem controlledOutProgram_run {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (control : Wire) (pointReg outReg : List Wire) (workStart cursor : Nat)
    (history : Fin cursor → Bool) :
    ((constantGateProgram (controlledOutGates row control pointReg outReg workStart) cursor).instantiate (readConstant coeffs Q) history).run =
    (AdaptiveCircuit.unitary
      (controlledPointAddOut control pointReg outReg workStart (constantPoint Q (coeffs row))) .done).run := by
  rw [constantGateProgram_run, controlledOutGates_source]

def negPointField : PointField → PointField
  | .y => .negY
  | .negY => .y
  | f => f

theorem fieldValue_neg (P : Point) (f : PointField) : fieldValue (-P) f =
    fieldValue P (negPointField f) := by
  cases P with
  | zero =>
    change fieldValue (-(0 : Point)) f = fieldValue 0 (negPointField f)
    rw [neg_zero]
    cases f <;> simp [fieldValue, pointCoordinates, negPointField]
  | @some x y h =>
    cases f <;> simp [fieldValue, pointCoordinates, negPointField,
      WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.negY, curve]

def reindexSlot {m n : Nat} (f : ConstantBit m → ConstantBit n) : TemplateGate m → TemplateGate n
  | .literal g => .literal g
  | .whenBit r b g => .whenBit (f r) b g

theorem reindexSlot_source {m n : Nat} (f : ConstantBit m → ConstantBit n)
    (read : ConstantBit n → Bool) (gs : List (TemplateGate m)) :
    (gs.map (reindexSlot f)).flatMap (TemplateGate.instantiate read) =
      gs.flatMap (TemplateGate.instantiate (fun r => read (f r))) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.flatMap_cons, ih]
    congr 1
    cases g <;> rfl

def negRowRef {n : Nat} (row : Fin n) (r : ConstantBit 1) : ConstantBit n :=
  ⟨row, negPointField r.field, r.bit⟩

theorem negRowRef_read {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) :
    (fun r => readConstant coeffs Q (negRowRef row r)) =
      readConstant (fun _ : Fin 1 => qCoefficient) (-(constantPoint Q (coeffs row))) := by
  funext r
  simp only [readConstant, negRowRef, qCoefficient_point, fieldValue_neg]

def negControlledOutGates {n : Nat} (row : Fin n) (control : Wire)
    (pointReg outReg : List Wire) (workStart : Wire) : List (TemplateGate n) :=
  (controlledOutGates (0 : Fin 1) control pointReg outReg workStart).map
    (reindexSlot (negRowRef row))

theorem negControlledOutGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (control : Wire) (pointReg outReg : List Wire) (workStart : Wire) :
    (negControlledOutGates row control pointReg outReg workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      controlledPointAddOut control pointReg outReg workStart (-(constantPoint Q (coeffs row))) := by
  rw [negControlledOutGates, reindexSlot_source, negRowRef_read, controlledOutGates_source,
    qCoefficient_point]

def controlledPointGates {n : Nat} (row : Fin n) (control : Wire)
    (pointReg : List Wire) (workStart : Wire) : List (TemplateGate n) :=
  let temp := controlledPointAddTemp workStart
  let auxStart := controlledPointAddAuxStart workStart
  controlledOutGates row control pointReg temp auxStart ++
    (pointSwapReg pointReg temp).map TemplateGate.literal ++
    (negControlledOutGates row control pointReg temp auxStart).reverse

theorem controlledPointGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (control : Wire) (pointReg : List Wire) (workStart : Wire) :
    (controlledPointGates row control pointReg workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      controlledPointAdd control pointReg workStart (constantPoint Q (coeffs row)) := by
  simp only [controlledPointGates, List.flatMap_append, controlledOutGates_source,
    literalGates_instantiate, template_reverse, negControlledOutGates_source,
    controlledPointAdd, List.append_assoc]

theorem controlledPointProgram_run {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (control : Wire) (pointReg : List Wire) (workStart cursor : Nat)
    (history : Fin cursor → Bool) :
    ((constantGateProgram (controlledPointGates row control pointReg workStart) cursor).instantiate
      (readConstant coeffs Q) history).run =
    (AdaptiveCircuit.unitary
      (controlledPointAdd control pointReg workStart (constantPoint Q (coeffs row))) .done).run := by
  rw [constantGateProgram_run, controlledPointGates_source]

def gPowerCoefficient (i : Nat) : PointCoeff :=
  ⟨⟨2^i % order, Nat.mod_lt _ (by decide)⟩, ⟨0, by decide⟩⟩
def qPowerCoefficient (i : Nat) : PointCoeff :=
  ⟨⟨0, by decide⟩, ⟨2^i % order, Nat.mod_lt _ (by decide)⟩⟩

theorem nsmul_mod_order (P : Point) (h : order • P = 0) (k : Nat) :
    (k % order) • P = k • P := by
  have hs : (k % order) • P + (order * (k / order)) • P = k • P := by
    rw [← add_nsmul, Nat.mod_add_div]
  have hz : (order * (k / order)) • P = 0 := by
    rw [mul_nsmul, h, nsmul_zero]
  simpa only [hz, add_zero] using hs

theorem gPowerCoefficient_point (Q : Point) (i : Nat) :
    constantPoint Q (gPowerCoefficient i) = (2^i) • G := by
  simp only [constantPoint, gPowerCoefficient, zero_nsmul, add_zero]
  exact nsmul_mod_order G generator_nsmul_eq_zero _

theorem qPowerCoefficient_point (Q : Point) (h : order • Q = 0) (i : Nat) :
    constantPoint Q (qPowerCoefficient i) = (2^i) • Q := by
  simp only [constantPoint, qPowerCoefficient, zero_nsmul, zero_add]
  exact nsmul_mod_order Q h _

/-- All 256 G powers followed by all 256 Q powers, fixed before Q is known. -/
def naivePowerCoefficient (row : Fin 512) : PointCoeff :=
  if row.val < 256 then gPowerCoefficient row.val else qPowerCoefficient (row.val-256)
def naivePowerTable : List PointCoeff := List.ofFn naivePowerCoefficient

theorem naivePowerTable_length : naivePowerTable.length = 512 := by
  simp only [naivePowerTable, List.length_ofFn]

theorem naivePowerCoefficient_g (Q : Point) (i : Fin 256) :
    constantPoint Q (naivePowerCoefficient ⟨i.val, by omega⟩) = (2^i.val) • G := by
  simp only [naivePowerCoefficient, if_pos i.isLt, gPowerCoefficient_point]

theorem naivePowerCoefficient_q (Q : Point) (h : order • Q = 0) (i : Fin 256) :
    constantPoint Q (naivePowerCoefficient ⟨256+i.val, by omega⟩) = (2^i.val) • Q := by
  simp only [naivePowerCoefficient, show ¬256+i.val<256 by omega, if_false,
    Nat.add_sub_cancel_left, qPowerCoefficient_point Q h]

theorem dlogPoint_order (d : Nat) : order • (d • G) = 0 := by
  rw [smul_comm, generator_nsmul_eq_zero, nsmul_zero]

theorem naivePowerTable_get (i : Fin 512) :
    naivePowerTable.get ⟨i.val, by rw [naivePowerTable_length]; exact i.isLt⟩ =
      naivePowerCoefficient i := by
  simp only [naivePowerTable, List.get_ofFn]
  rfl

theorem gPowerProgram_run (Q : Point) (i : Fin 256) (control : Wire)
    (pointReg : List Wire) (workStart cursor : Nat) (history : Fin cursor → Bool) :
    ((constantGateProgram (controlledPointGates ⟨i.val, by omega⟩ control pointReg workStart)
      cursor).instantiate (readConstant naivePowerCoefficient Q) history).run =
      (AdaptiveCircuit.unitary (controlledPointAdd control pointReg workStart ((2^i.val) • G)) .done).run := by
  rw [controlledPointProgram_run, naivePowerCoefficient_g]

theorem qPowerProgram_run (Q : Point) (h : order • Q = 0) (i : Fin 256) (control : Wire)
    (pointReg : List Wire) (workStart cursor : Nat) (history : Fin cursor → Bool) :
    ((constantGateProgram (controlledPointGates ⟨256+i.val, by omega⟩ control pointReg workStart)
      cursor).instantiate (readConstant naivePowerCoefficient Q) history).run =
      (AdaptiveCircuit.unitary (controlledPointAdd control pointReg workStart ((2^i.val) • Q)) .done).run := by
  rw [controlledPointProgram_run, naivePowerCoefficient_q Q h]

end ShorECDLP.NaiveChallenge
