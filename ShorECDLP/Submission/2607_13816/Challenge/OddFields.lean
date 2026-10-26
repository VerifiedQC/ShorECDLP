import ShorECDLP.Submission.«2607_13816».Challenge.PointTable
import ShorECDLP.Submission.«2607_13816».Window.RawCoordinate

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
local instance : NeZero ShorECDLP.p := ⟨by decide⟩

/-- Exactly the fifteen remaining G windows and thirteen Q windows. -/
inductive OddWindow where
  | left (index : Fin 15)
  | right (index : Fin 13)

def oddCoefficient (j a : Nat) : Nat :=
  (2 * (a % 32768) + 1) * 2^(16*j) * ((order+1)/2)

theorem oddCoefficient_point (P : Point) (j a : Nat) :
    oddCoefficient j a • P = oddWindowPoint P j a := by
  simp [oddCoefficient, oddWindowPoint, signedWindowHalfPoint, mul_smul]

def oddWindowCoefficients : OddWindow → Fin 32768 → PointCoeff
  | .left j, a => coefficients (oddCoefficient j.val a.val) 0
  | .right j, a => coefficients 0 (oddCoefficient j.val a.val)

def oddWindowCoefficientTable (w : OddWindow) : List PointCoeff := List.ofFn (oddWindowCoefficients w)

theorem oddWindowCoefficientTable_length (w : OddWindow) :
    (oddWindowCoefficientTable w).length = 32768 := List.length_ofFn

def windowPoint (Q : Point) : OddWindow → Nat → Point
  | .left j, a => oddWindowPoint G j.val a
  | .right j, a => oddWindowPoint Q j.val a

theorem oddWindowCoefficients_point (w : OddWindow) (a : Fin 32768) (Q : Point) (hQ : order • Q = 0) :
    constantPoint Q (oddWindowCoefficients w a) = windowPoint Q w a.val := by
  cases w <;> simp [oddWindowCoefficients, coefficients_point _ _ Q hQ, oddCoefficient_point, windowPoint]

def fieldRefs {n : Nat} (row : Fin n) (field : PointField) : List (ConstantBit n) :=
  List.ofFn (fun i : Fin 256 => ⟨row, field, i⟩)

theorem fieldRefs_read {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (field : PointField) :
    (fieldRefs row field).map (readConstant coeffs Q) =
      constantBits 256 (fieldValue (constantPoint Q (coeffs row)) field) := by
  simp only [fieldRefs, List.map_ofFn, constantBits_ofFn, Function.comp_def, readConstant]

def fieldLeaf {n : Nat} (row : Fin n) (field : PointField) (q : Wire) : List (TemplateGate n) :=
  lookupLeafGates q ((fieldRefs row field).zip (List.range' 7 256))

theorem fieldLeaf_instantiate {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (field : PointField) (q : Wire) :
    (fieldLeaf row field q).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      tableXorGates q (tableWordMask (List.range' 7 256) (fieldValue (constantPoint Q (coeffs row)) field)) := by
  rw [fieldLeaf, lookupLeafGates_instantiate]
  rw [show (fun p : ConstantBit n × Wire => Gate.CX q p.2) =
    (Gate.CX q) ∘ Prod.snd from rfl, ← List.map_map, filtered_zip_mask, fieldRefs_read]
  simp only [tableXorGates, tableWordMask, List.length_range']

/-- One shared load program for all twenty-eight windows and all protected fields. -/
def fieldLoadOps (field : PointField) : List (LookupOp 32768) :=
  unaryLookupOps (fun l q => fieldLeaf ⟨l % 32768, Nat.mod_lt _ (by decide)⟩ field q)
    (tableAddressTree pointLookupAddress 0 1) 836 pointLookupPath

theorem fieldLoadOps_circuit (w : OddWindow) (field : PointField) (Q : Point) (hQ : order • Q = 0) :
    lookupCircuit (readConstant (oddWindowCoefficients w) Q) (fieldLoadOps field) =
    tableLookupProgram (fun l => tableWordMask (List.range' 7 256) (fieldValue (windowPoint Q w l) field))
      pointLookupAddress 836 pointLookupPath := by
  rw [fieldLoadOps, unaryLookupOps_circuit]
  unfold tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  obtain ⟨i, hi, he⟩ := tableAddressTree_label _ 0 1 l hl
  have hlt : l < 32768 := by simpa [he, pointLookupAddress] using hi
  rw [fieldLeaf_instantiate]
  simp only [Nat.mod_eq_of_lt hlt, oddWindowCoefficients_point w _ Q hQ]

theorem fieldLoadOps_measurements (field : PointField) : lookupMeasurements (fieldLoadOps field) = 32767 := by
  rw [fieldLoadOps, unaryLookupOps_measurements _ _ _ _
    (tableAddressTree_layout _ _ _ _ _ (by decide) (by decide))]
  have h := tableAddressTree_nodes pointLookupAddress 0 1
  simp only [pointLookupAddress, List.length_range'] at h ⊢
  omega

def fieldLoadProgram (field : PointField) (start : Nat) : Straight 32768 start (start+32767) :=
  castFinish (by rw [fieldLoadOps_measurements]) (lookupProgram 32768 (fieldLoadOps field) start)

theorem fieldLoadProgram_run (w : OddWindow) (field : PointField) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    ((fieldLoadProgram field start).instantiate (readConstant (oddWindowCoefficients w) Q) history).run =
      (tableLookupProgram (fun l => tableWordMask (List.range' 7 256) (fieldValue (windowPoint Q w l) field))
        pointLookupAddress 836 pointLookupPath).run := by
  rw [fieldLoadProgram, castFinish_instantiate, lookupProgram_run, fieldLoadOps_circuit w field Q hQ]

theorem fieldLoadProgram_records (field : PointField) (start : Nat) (read : ConstantBit 32768 → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((fieldLoadProgram field start).instantiate read history).run) : b.history.length = 32767 := by
  have h := straight_history_length (fieldLoadProgram field start) read history b hb
  simpa using h

theorem fieldLoadProgram_tCount (w : OddWindow) (field : PointField) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    ((fieldLoadProgram field start).instantiate (readConstant (oddWindowCoefficients w) Q) history).tCount = 229369 := by
  rw [fieldLoadProgram, castFinish_instantiate, lookupProgram_tCount, fieldLoadOps_circuit w field Q hQ,
    tableLookupProgram_tCount _ _ _ _ (by decide) (by decide)]
  rfl

theorem oddWindow_coordinates (P : Point) (j a : Nat) :
    (pointCoordinates (oddWindowPoint P j a)).2 = (oddWindowX P j a, oddWindowY P j a) := by
  unfold oddWindowX oddWindowY
  generalize oddWindowPoint P j a = R
  cases R <;> rfl

theorem oddWindow_field_x (P : Point) (j a : Nat) :
    fieldValue (oddWindowPoint P j a) .x = (oddWindowX P j a).val := by
  simp only [fieldValue, oddWindow_coordinates]

theorem oddWindow_field_y (P : Point) (j a : Nat) :
    fieldValue (oddWindowPoint P j a) .y = (oddWindowY P j a).val := by
  simp only [fieldValue, oddWindow_coordinates]

theorem oddWindow_field_negX (P : Point) (j a : Nat) :
    fieldValue (oddWindowPoint P j a) .negX = (ShorECDLP.p - (oddWindowX P j a).val) % ShorECDLP.p := by
  simp only [fieldValue, oddWindow_coordinates, ZMod.neg_val']

theorem oddWindow_field_negY (P : Point) (j a : Nat) :
    fieldValue (oddWindowPoint P j a) .negY = (ShorECDLP.p - (oddWindowY P j a).val) % ShorECDLP.p := by
  simp only [fieldValue, oddWindow_coordinates, ZMod.neg_val']

theorem oddWindow_field_tripleX (P : Point) (j a : Nat) :
    fieldValue (oddWindowPoint P j a) .tripleX = (3 * (oddWindowX P j a).val) % ShorECDLP.p := by
  simp only [fieldValue, oddWindow_coordinates, ZMod.val_mul]
  have h : (3 : ShorECDLP.Fp).val = 3 := by norm_num [ZMod.val_ofNat, ShorECDLP.p]
  rw [h]

/-- The five fixed source queries, retaining their original order and multiplicity. -/
def rawQueryFields : List PointField := [.negX, .negY, .tripleX, .x, .negY]

theorem rawQueryFields_values (P : Point) (j a : Nat) :
    rawQueryFields.map (fieldValue (oddWindowPoint P j a)) =
      [(ShorECDLP.p - (oddWindowX P j a).val) % ShorECDLP.p,
       (ShorECDLP.p - (oddWindowY P j a).val) % ShorECDLP.p,
       (3 * (oddWindowX P j a).val) % ShorECDLP.p,
       (oddWindowX P j a).val % ShorECDLP.p,
       (ShorECDLP.p - (oddWindowY P j a).val) % ShorECDLP.p] := by
  simp only [rawQueryFields, List.map_cons, List.map_nil, oddWindow_field_negX,
    oddWindow_field_negY, oddWindow_field_tripleX, oddWindow_field_x]
  rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]

/-- All submitted coefficients are data in this finite list. -/
theorem oddWindowCoefficientTable_get (w : OddWindow) (i : Fin 32768) :
    (oddWindowCoefficientTable w)[i.val]'(by rw [oddWindowCoefficientTable_length]; exact i.isLt) =
      oddWindowCoefficients w i := by
  simp only [oddWindowCoefficientTable, List.getElem_ofFn]

end ShorECDLP.Paper2607_13816.ChallengeMigration
