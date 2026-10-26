import ShorECDLP.Submission.Naive.Challenge.FixedReset
import Mathlib.Data.Nat.Bitwise

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge

/-- Fixed wire order and fixed field reference. Bits beyond the protected 256-bit
field are zero, including the 257th wire of the Naive arithmetic register. -/
def fieldLoadGates {n : Nat} (row : Fin n) (field : PointField) :
    List Wire → Nat → List (TemplateGate n)
  | [], _ => []
  | w :: ws, i =>
    (if h : i < 256 then [.whenBit ⟨row, field, ⟨i, h⟩⟩ true (.X w)] else []) ++
      fieldLoadGates row field ws (i+1)

theorem fieldLoadGates_instantiate {n : Nat} (row : Fin n) (field : PointField)
    (read : ConstantBit n → Bool) (c : Nat) (hc : c < 2^256)
    (hr : ∀ i : Fin 256, read ⟨row, field, i⟩ = c.testBit i.val)
    (ws : List Wire) (i : Nat) :
    (fieldLoadGates row field ws i).flatMap (TemplateGate.instantiate read) =
      loadConst ws (c / 2^i) := by
  induction ws generalizing i with
  | nil => simp [fieldLoadGates, loadConst]
  | cons w ws ih =>
    have hd : c / 2^i / 2 = c / 2^(i+1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
    by_cases hi : i < 256
    · simp [fieldLoadGates, hi, TemplateGate.instantiate, hr,
        Nat.testBit_eq_decide_div_mod_eq, loadConst, hd, ih]
    · have hb : c.testBit i = false := Nat.testBit_eq_false_of_lt
        (hc.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      have hz : ¬ c / 2^i % 2 = 1 := by
        simpa [Nat.testBit_eq_decide_div_mod_eq] using hb
      simp [fieldLoadGates, hi, loadConst, hz, hd, ih]

theorem fieldValue_lt (P : Point) (field : PointField) : fieldValue P field < 2^256 := by
  have hp : p < 2^256 := by decide
  cases field <;> simp only [fieldValue]
  all_goals first | exact (ZMod.val_lt _).trans hp | split <;> norm_num

theorem fieldLoadGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (field : PointField) (ws : List Wire) :
    (fieldLoadGates row field ws 0).flatMap
        (TemplateGate.instantiate (readConstant coeffs Q)) =
      loadConst ws (fieldValue (constantPoint Q (coeffs row)) field) := by
  have h := fieldLoadGates_instantiate row field (readConstant coeffs Q)
    (fieldValue (constantPoint Q (coeffs row)) field)
    (fieldValue_lt _ _) (fun _ => rfl) ws 0
  simpa only [pow_zero, Nat.div_one] using h

/-- The exact constant-subtraction block used in point addition. The two loads
share a fixed table reference; all arithmetic gates are independent of Q. -/
def fieldSubConstGates {n : Nat} (row : Fin n) (field : PointField)
    (offset : Wire) (lhs out : List Wire) : List (TemplateGate n) :=
  let a := shiftWires offset (Secp256k1Instance.reg 0).wires
  let b := shiftWires offset (Secp256k1Instance.reg 1).wires
  let r := shiftWires offset (Secp256k1Instance.reg 2).wires
  let core := shiftCircuit offset (modSub
    (Secp256k1Instance.reg 0).wires
    (Secp256k1Instance.reg 1).wires
    (Secp256k1Instance.reg 2).wires
    (Secp256k1Instance.reg 3).wires
    (Secp256k1Instance.reg 4).wires
    (Secp256k1Instance.reg 5).wires
    (Secp256k1Instance.bitWire 6)
    (Secp256k1Instance.reg 7).wires
    (Secp256k1Instance.bitWire 8)
    (Secp256k1Instance.reg 9).wires p)
  (Arithmetic.copyReg lhs a).map TemplateGate.literal ++
    fieldLoadGates row field b 0 ++
    (core ++ Arithmetic.copyReg r out ++ core.reverse).map TemplateGate.literal ++
    fieldLoadGates row field b 0 ++
    (Arithmetic.copyReg lhs a).map TemplateGate.literal

theorem literalGates_instantiate {n : Nat} (read : ConstantBit n → Bool) (c : Circuit) :
    (c.map TemplateGate.literal).flatMap (TemplateGate.instantiate read) = c := by
  induction c with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, List.flatMap_cons,
      TemplateGate.instantiate, List.singleton_append, ih]

theorem fieldSubConstGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (field : PointField) (offset : Wire) (lhs out : List Wire) :
    (fieldSubConstGates row field offset lhs out).flatMap
        (TemplateGate.instantiate (readConstant coeffs Q)) =
      fieldSubConst offset lhs (fieldValue (constantPoint Q (coeffs row)) field) out := by
  simp only [fieldSubConstGates, List.flatMap_append, literalGates_instantiate,
    fieldLoadGates_source, fieldSubConst, List.append_assoc]
  rfl

/-- One fixed coefficient row selecting Q. This is submission data, not a
point-valued callback. -/
def qCoefficient : PointCoeff := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

theorem qCoefficient_point (Q : Point) : constantPoint Q qCoefficient = Q := by
  have ho : 1 % order = 1 := Nat.mod_eq_of_lt (by decide)
  simp [constantPoint, qCoefficient, ho]

/-- A concrete protected coordinate-subtraction block. Arbitrary offsets and
registers are fixed before the evaluator receives Q. -/
def qFieldSubGates (field : PointField) (offset : Wire) (lhs out : List Wire) :
    List (TemplateGate 1) := fieldSubConstGates 0 field offset lhs out

theorem qFieldSubGates_source (Q : Point) (field : PointField)
    (offset : Wire) (lhs out : List Wire) :
    (qFieldSubGates field offset lhs out).flatMap
        (TemplateGate.instantiate (readConstant (fun _ : Fin 1 => qCoefficient) Q)) =
      fieldSubConst offset lhs (fieldValue Q field) out := by
  simpa only [qFieldSubGates, qCoefficient_point] using
    fieldSubConstGates_source (fun _ : Fin 1 => qCoefficient) Q 0 field offset lhs out

def constantGateProgram {n : Nat} (gs : List (TemplateGate n)) (cursor : Nat) :
    Straight n cursor cursor := gs.foldr Straight.gate .done

theorem constantGateProgram_slots {n : Nat} (gs : List (TemplateGate n)) (cursor : Nat) :
    (constantGateProgram gs cursor).gateSlots = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      change 1 + (constantGateProgram gs cursor).gateSlots = gs.length + 1
      omega

theorem constantGateProgram_wellFormed {n : Nat} (gs : List (TemplateGate n)) (cursor : Nat)
    (h : ∀ g ∈ gs, g.WellFormed) : (constantGateProgram gs cursor).WellFormed := by
  induction gs with
  | nil => trivial
  | cons g gs ih => exact ⟨h g List.mem_cons_self,
      ih (fun g hg => h g (List.mem_cons_of_mem _ hg))⟩

theorem constantGateProgram_run {n : Nat} (gs : List (TemplateGate n)) (cursor : Nat)
    (read : ConstantBit n → Bool) (history : Fin cursor → Bool) :
    ((constantGateProgram gs cursor).instantiate read history).run =
      (AdaptiveCircuit.unitary (gs.flatMap (TemplateGate.instantiate read)) .done).run := by
  induction gs with
  | nil =>
    change AdaptiveCircuit.done.run = (AdaptiveCircuit.unitary [] .done).run
    rw [AdaptiveCircuit.run_unitary_done]
    rfl
  | cons g gs ih =>
    change (AdaptiveCircuit.unitary (g.instantiate read)
      ((constantGateProgram gs cursor).instantiate read history)).run = _
    rw [show AdaptiveCircuit.unitary (g.instantiate read)
      ((constantGateProgram gs cursor).instantiate read history) =
      (AdaptiveCircuit.unitary (g.instantiate read) .done).seq
        ((constantGateProgram gs cursor).instantiate read history) from rfl]
    rw [AdaptiveCircuit.run_seq, ih]
    simp only [AdaptiveCircuit.run_unitary_done, List.flatMap_cons]
    simp only [Instrument.seq, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, List.append_nil, InstrumentBranch.seq]
    congr 2
    apply LinearMap.ext
    intro ψ
    exact (Quantum.run_append _ _ ψ).symm

theorem qFieldSubProgram_run (Q : Point) (field : PointField)
    (offset : Wire) (lhs out : List Wire) (cursor : Nat) (history : Fin cursor → Bool) :
    ((constantGateProgram (qFieldSubGates field offset lhs out) cursor).instantiate
      (readConstant (fun _ : Fin 1 => qCoefficient) Q) history).run =
      (AdaptiveCircuit.unitary (fieldSubConst offset lhs (fieldValue Q field) out) .done).run := by
  rw [constantGateProgram_run, qFieldSubGates_source]

end ShorECDLP.NaiveChallenge
