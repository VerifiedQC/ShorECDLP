import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstCarry
import ShorECDLP.Framework.Quantum.MeasurementUncompute

/-!
# Shared facts for measured carry arithmetic

The constant adder and comparator use the same measurement coefficients, paired borrowed
register phase correction, branch decomposition, carry erasure and adaptive gate metrics.
These facts apply directly to the existing adaptive-circuit semantics.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false

def gidneyRecordedPhase : List Bool → List Bool → ℂ
  | outcome :: outcomes, bit :: bits =>
      (if outcome && bit then -1 else 1) * gidneyRecordedPhase outcomes bits
  | _, _ => 1

private theorem gidneyRegisterPhase (wires : List Wire) (outcomes : List Bool) (s : BasisState) :
    Quantum.registerXPhase wires outcomes s = gidneyRecordedPhase outcomes (wireValues wires s) := by
  induction wires generalizing outcomes with
  | nil => cases outcomes <;> rfl
  | cons w ws ih => cases outcomes <;> simp [Quantum.registerXPhase,gidneyRecordedPhase,wireValues,ih]

private theorem gidneyRecordedPhase_square (outcomes bits : List Bool) :
    gidneyRecordedPhase outcomes bits * gidneyRecordedPhase outcomes bits = 1 := by
  induction outcomes generalizing bits with
  | nil => simp [gidneyRecordedPhase]
  | cons outcome outcomes ih =>
    cases bits with
    | nil => simp [gidneyRecordedPhase]
    | cons bit bits =>
      have ht := ih bits
      cases outcome <;> cases bit <;> simp_all [gidneyRecordedPhase]

private theorem gidneyRecordedPhase_xor (outcomes bits carries : List Bool)
    (hlen : bits.length = carries.length) :
    gidneyRecordedPhase outcomes (List.zipWith Bool.xor bits carries) *
      gidneyRecordedPhase outcomes bits = gidneyRecordedPhase outcomes carries := by
  induction outcomes generalizing bits carries with
  | nil => simp [gidneyRecordedPhase]
  | cons outcome outcomes ih =>
    cases bits with
    | nil => cases carries <;> simp_all [gidneyRecordedPhase]
    | cons bit bits =>
      cases carries with
      | nil => simp at hlen
      | cons carry carries =>
        have ht := ih bits carries (by simpa using hlen)
        cases outcome <;> cases bit <;> cases carry <;>
          simp_all [gidneyRecordedPhase,mul_assoc,mul_left_comm,mul_comm]

theorem gidneyBorrowedPhaseCancellation (dirty : List Wire) (outcomes carries : List Bool)
    (before after : BasisState) (hlen : dirty.length = carries.length)
    (hxor : wireValues dirty before = List.zipWith Bool.xor (wireValues dirty after) carries) :
    gidneyRecordedPhase outcomes carries * Quantum.registerXPhase dirty outcomes before *
      Quantum.registerXPhase dirty outcomes after = 1 := by
  rw [gidneyRegisterPhase,gidneyRegisterPhase,hxor,mul_assoc,
    gidneyRecordedPhase_xor outcomes (wireValues dirty after) carries (by simpa [wireValues] using hlen)]
  exact gidneyRecordedPhase_square outcomes carries

noncomputable def gidneyRawCoefficient : List Bool → List Bool → ℂ
  | [], [] => 1
  | outcome :: outcomes, carry :: carries =>
      Quantum.xResetCoeff outcome carry * gidneyRawCoefficient outcomes carries
  | _, _ => 0

theorem gidneyRawCoefficient_phase (outcomes carries : List Bool)
    (hlen : outcomes.length = carries.length) :
    gidneyRawCoefficient outcomes carries =
      Quantum.registerXResetMagnitude outcomes.length * gidneyRecordedPhase outcomes carries := by
  induction outcomes generalizing carries with
  | nil => cases carries <;> simp_all [gidneyRawCoefficient,Quantum.registerXResetMagnitude,gidneyRecordedPhase]
  | cons outcome outcomes ih =>
    cases carries with
    | nil => simp at hlen
    | cons carry carries =>
      rw [gidneyRawCoefficient,ih carries (by simpa using hlen)]
      cases outcome <;> cases carry <;>
        simp [Quantum.xResetCoeff,Quantum.registerXResetMagnitude,gidneyRecordedPhase,
          pow_succ,mul_assoc,mul_left_comm,mul_comm]

theorem gidneyUnitaryBranch (circuit : Circuit) (next : Quantum.AdaptiveCircuit)
    (branch : Quantum.InstrumentBranch) (hb : branch ∈ (Quantum.AdaptiveCircuit.unitary circuit next).run) :
    ∃ rest ∈ next.run, branch.history = rest.history ∧
      ∀ psi, branch.kraus psi = rest.kraus (Quantum.run circuit psi) := by
  simp only [Quantum.AdaptiveCircuit.run,List.mem_map] at hb
  obtain ⟨rest,hr,rfl⟩ := hb
  exact ⟨rest,hr,rfl,fun _ => rfl⟩

theorem gidneyMeasureBranch (target : Wire) (onFalse onTrue : Quantum.AdaptiveCircuit)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (Quantum.AdaptiveCircuit.xMeasureReset target onFalse onTrue).run) :
    ∃ outcome, ∃ rest ∈ (if outcome then onTrue else onFalse).run,
      branch.history = outcome :: rest.history ∧
        ∀ psi, branch.kraus psi = rest.kraus (Quantum.xResetKraus target outcome psi) := by
  simp only [Quantum.AdaptiveCircuit.run,List.mem_append,List.mem_map] at hb
  rcases hb with ⟨rest,hr,rfl⟩ | ⟨rest,hr,rfl⟩
  · exact ⟨false,rest,hr,rfl,fun _ => rfl⟩
  · exact ⟨true,rest,hr,rfl,fun _ => rfl⟩

theorem gidneyDoneBranch (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ Quantum.AdaptiveCircuit.done.run) :
    branch.history = [] ∧ ∀ psi, branch.kraus psi = psi := by
  simp only [Quantum.AdaptiveCircuit.run,List.mem_singleton] at hb
  subst branch
  exact ⟨rfl,fun _ => rfl⟩

theorem gidneyCarryBits_length (input constant : List Bool) (carry : Bool)
    (hlen : input.length = constant.length) :
    (constantCarryBits carry input constant).length = input.length := by
  induction input generalizing constant carry with
  | nil => cases constant <;> simp_all [constantCarryBits]
  | cons a as ih =>
    cases constant with
    | nil => simp at hlen
    | cons k ks => simp [constantCarryBits,ih ks _ (by simpa using hlen)]

theorem gidneyXorWord_cancel (bits carries : List Bool) (hlen : bits.length = carries.length) :
    List.zipWith Bool.xor (List.zipWith Bool.xor bits carries) carries = bits := by
  induction bits generalizing carries with
  | nil => cases carries <;> simp_all
  | cons b bs ih =>
    cases carries with
    | nil => simp at hlen
    | cons c cs => simp [ih cs (by simpa using hlen),Bool.xor_assoc]

theorem gidneyCarryXor_HPFree (input dirty : List Wire) (constant : List Bool)
    (q c : Wire) (hk : input.length = constant.length) (hd : input.length = dirty.length) :
    HPFree (controlledConstCarryXor input dirty constant q c) := by
  cases input with
  | nil => simp [controlledConstCarryXor]
  | cons a as =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      exact (controlledConstCarryXor_counts a as dirty k ks q c (by simpa using hk) hd).1

/-- Worst-case count of a chosen unitary gate cost across the adaptive branches. -/
def gidneyGateCount (cost : Gate → Nat) : Quantum.AdaptiveCircuit → Nat
  | .done => 0
  | .unitary gates next => (gates.map cost).sum + gidneyGateCount cost next
  | .xMeasureReset _ left right => max (gidneyGateCount cost left) (gidneyGateCount cost right)

theorem gidneyGateCount_tCount (program : Quantum.AdaptiveCircuit) :
    gidneyGateCount tCost program = program.tCount := by
  induction program with
  | done => rfl
  | unitary gates next ih => simp [gidneyGateCount,Quantum.AdaptiveCircuit.tCount,tCount,ih]
  | xMeasureReset w left right ihl ihr => simp [gidneyGateCount,Quantum.AdaptiveCircuit.tCount,ihl,ihr]

theorem gidneyZ_cost (cost : Gate → Nat) (hX : ∀ w, cost (.X w) = 0)
    (hH : ∀ w, cost (.H w) = 0) (dirty : List Wire) (outcomes : List Bool) :
    ((Quantum.registerZCorrection dirty outcomes).map cost).sum = 0 := by
  induction dirty generalizing outcomes with
  | nil => simp [Quantum.registerZCorrection]
  | cons d ds ih =>
    cases outcomes with
    | nil => simp [Quantum.registerZCorrection]
    | cons b bs => cases b <;> simp [Quantum.registerZCorrection,Quantum.pauliZ,hX,hH,ih]

/-- Worst-case number of Toffoli gates in the actual adaptive program. -/
def gidneyToffoliCount := gidneyGateCount (fun g => match g with | .CCX _ _ _ => 1 | _ => 0)

/-- Worst-case number of CNOT gates in the actual adaptive program. -/
def gidneyCnotCount := gidneyGateCount (fun g => match g with | .CX _ _ => 1 | _ => 0)

theorem gidneyZ_usesOnly (dirty : List Wire) (outcomes : List Bool) :
    ∀ w ∈ circuitWires (Quantum.registerZCorrection dirty outcomes), w ∈ dirty := by
  induction dirty generalizing outcomes with
  | nil => simp [Quantum.registerZCorrection,circuitWires]
  | cons d ds ih =>
    cases outcomes with
    | nil => simp [Quantum.registerZCorrection,circuitWires]
    | cons b bs =>
      intro w hw
      have ht := ih bs w
      cases b with
      | false =>
        simp only [Quantum.registerZCorrection,Bool.false_eq_true,↓reduceIte,List.nil_append] at hw
        exact List.mem_cons_of_mem d (ht hw)
      | true =>
        simp only [Quantum.registerZCorrection,↓reduceIte,circuitWires,List.flatMap_append,
          Quantum.pauliZ,List.flatMap_cons,List.flatMap_nil,gateWires,List.mem_append,
          List.mem_cons,List.not_mem_nil,or_false] at hw
        change (w = d ∨ w = d ∨ w = d) ∨ w ∈ circuitWires (Quantum.registerZCorrection ds bs) at hw
        rcases hw with (h | h | h) | h
        · simp [h]
        · simp [h]
        · simp [h]
        · exact List.mem_cons_of_mem d (ht h)

end ShorECDLP.Paper2607_13816
