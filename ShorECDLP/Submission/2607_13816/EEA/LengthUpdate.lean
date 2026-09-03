import ShorECDLP.Submission.«2607_13816».EEA.Ripple

/-!
# Borrowed-work XOR writers for EEA length updates

Figures 12--13 of the pinned supplement write a decoded length by using the other Work
register as arbitrary dirty storage.  Algebraically, one selected bit is implemented by

`CX dirty target; CX selector dirty; CX dirty target; CX selector dirty`.

The dirty value cancels, the selector is XORed into the target, and both borrowed/control
wires are restored.  This file proves that identity once and lifts it to encoded constants and
lists of decoder lanes.  These are local normal-form formulas only: the production aggregate
still requires the grouped write/zero-map/write/zero-map composition from Figures 12--13.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

set_option linter.unusedSimpArgs false

/-- One commuted normal-form lane of the paired dirty-controlled writes in Figures 12--13. -/
def borrowedXorBit (dirty selector target : Wire) : Circuit :=
  [.CX dirty target, .CX selector dirty,
    .CX dirty target, .CX selector dirty]

/-- The borrowed-bit sandwich is exactly one clean selector-controlled XOR, for an arbitrary
initial dirty bit. -/
theorem run_borrowedXorBit
    (dirty selector target : Wire) (state : BasisState)
    (hnd : [dirty, selector, target].Nodup) :
    run (borrowedXorBit dirty selector target) state =
      run [.CX selector target] state := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  rcases hnd with ⟨⟨hds, hdt⟩, ⟨hst, _⟩⟩
  have hsd : selector ≠ dirty := Ne.symm hds
  have htd : target ≠ dirty := Ne.symm hdt
  have hts : target ≠ selector := Ne.symm hst
  funext wire
  by_cases hwd : wire = dirty
  · subst wire
    cases hd : state dirty <;> cases hs : state selector <;>
      cases ht : state target <;>
      simp [borrowedXorBit, run, applyGate, upd,
        hds, hdt, hsd, htd, hst, hts, hd, hs, ht]
  · by_cases hwt : wire = target
    · subst wire
      cases hd : state dirty <;> cases hs : state selector <;>
        cases ht : state target <;>
        simp [borrowedXorBit, run, applyGate, upd,
          hds, hdt, hsd, htd, hst, hts, hd, hs, ht]
    · simp [borrowedXorBit, run, applyGate, upd, hwd, hwt]

@[simp]
theorem borrowedXorBit_HPFree (dirty selector target : Wire) :
    HPFree (borrowedXorBit dirty selector target) := by
  simp [borrowedXorBit]

theorem borrowedXorBit_wellFormed
    (dirty selector target : Wire)
    (hnd : [dirty, selector, target].Nodup) :
    CircuitWellFormed (borrowedXorBit dirty selector target) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  rcases hnd with ⟨⟨hds, hdt⟩, ⟨hst, _⟩⟩
  simp [borrowedXorBit, CircuitWellFormed, Gate.WellFormed,
    hds, hdt, hst, Ne.symm hds, Ne.symm hdt, Ne.symm hst]

theorem borrowedXorBit_usesOnly (dirty selector target : Wire) :
    PaperCircuitUsesOnly [dirty, selector, target]
      (borrowedXorBit dirty selector target) := by
  simp [borrowedXorBit, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

@[simp]
theorem borrowedXorBit_toffoliCount (dirty selector target : Wire) :
    eeaToffoliCount (borrowedXorBit dirty selector target) = 0 := rfl

@[simp]
theorem borrowedXorBit_cnotCount (dirty selector target : Wire) :
    eeaCnotCount (borrowedXorBit dirty selector target) = 4 := rfl

@[simp]
theorem borrowedXorBit_tCount (dirty selector target : Wire) :
    ShorECDLP.tCount (borrowedXorBit dirty selector target) = 0 := rfl

/-- XOR the low `targets.length` bits of `value` under one ordinary control. -/
def controlledXorConstant (control : Wire) : List Wire → Nat → Circuit
  | [], _ => []
  | target :: targets, value =>
      (if value.testBit 0 then [.CX control target] else []) ++
        controlledXorConstant control targets (value / 2)

/-- The same encoded XOR, with every selected target bit implemented through one arbitrary
borrowed wire. -/
def borrowedXorConstant (dirty selector : Wire) : List Wire → Nat → Circuit
  | [], _ => []
  | target :: targets, value =>
      (if value.testBit 0 then borrowedXorBit dirty selector target else []) ++
        borrowedXorConstant dirty selector targets (value / 2)

def BorrowedConstantLayout
    (dirty selector : Wire) (targets : List Wire) : Prop :=
  ∀ target ∈ targets, [dirty, selector, target].Nodup

/-- Gate-independent Boolean action of a selector-controlled constant XOR. -/
def xorConstantState (enabled : Bool) : List Wire → Nat → BasisState → BasisState
  | [], _, state => state
  | target :: targets, value, state =>
      let next := if value.testBit 0 then
          state[target ↦ Bool.xor (state target) enabled]
        else state
      xorConstantState enabled targets (value / 2) next

theorem run_controlledXorConstant
    (control : Wire) (targets : List Wire) (value : Nat)
    (state : BasisState)
    (hlayout : ∀ target ∈ targets, control ≠ target) :
    run (controlledXorConstant control targets value) state =
      xorConstantState (state control) targets value state := by
  induction targets generalizing value state with
  | nil => rfl
  | cons target targets ih =>
      have hhead := hlayout target (by simp)
      have htail : ∀ wire ∈ targets, control ≠ wire := by
        intro wire hwire
        exact hlayout wire (by simp [hwire])
      by_cases hbit : value.testBit 0
      · rw [controlledXorConstant, if_pos hbit, run_append]
        have hcontrol :
            (run [.CX control target] state) control = state control := by
          simp [run, applyGate, upd, hhead]
        rw [ih (value / 2) _ htail, hcontrol]
        simp [xorConstantState, hbit, run, applyGate]
      · rw [controlledXorConstant, if_neg hbit]
        simpa [xorConstantState, hbit] using ih (value / 2) state htail

/-- Direct basis-state semantics of an encoded borrowed write: it is exactly the ordinary
selector-controlled constant XOR and restores the arbitrary borrowed bit. -/
theorem run_borrowedXorConstant
    (dirty selector : Wire) (targets : List Wire) (value : Nat)
    (state : BasisState)
    (hlayout : BorrowedConstantLayout dirty selector targets) :
    run (borrowedXorConstant dirty selector targets value) state =
      run (controlledXorConstant selector targets value) state := by
  induction targets generalizing value state with
  | nil => rfl
  | cons target targets ih =>
      have hhead := hlayout target (by simp)
      have htail : BorrowedConstantLayout dirty selector targets := by
        intro wire hwire
        exact hlayout wire (by simp [hwire])
      by_cases hbit : value.testBit 0
      · simp only [borrowedXorConstant, controlledXorConstant, hbit, if_true,
          run_append]
        rw [run_borrowedXorBit dirty selector target state hhead,
          ih (value / 2) _ htail]
      · simp only [borrowedXorConstant, controlledXorConstant, hbit, if_false,
          List.nil_append]
        exact ih (value / 2) state htail

@[simp]
theorem controlledXorConstant_HPFree
    (control : Wire) (targets : List Wire) (value : Nat) :
    HPFree (controlledXorConstant control targets value) := by
  induction targets generalizing value with
  | nil => simp [controlledXorConstant]
  | cons target targets ih =>
      by_cases hbit : value.testBit 0 <;>
        simp [controlledXorConstant, hbit, ih]

@[simp]
theorem borrowedXorConstant_HPFree
    (dirty selector : Wire) (targets : List Wire) (value : Nat) :
    HPFree (borrowedXorConstant dirty selector targets value) := by
  induction targets generalizing value with
  | nil => simp [borrowedXorConstant]
  | cons target targets ih =>
      by_cases hbit : value.testBit 0 <;>
        simp [borrowedXorConstant, hbit, ih]

private theorem controlledXorConstant_preservesOutside
    (control : Wire) (targets : List Wire) (value : Nat)
    (state : BasisState) (wire : Wire) (hwire : wire ∉ targets) :
    run (controlledXorConstant control targets value) state wire = state wire := by
  induction targets generalizing value state with
  | nil => rfl
  | cons target targets ih =>
      simp only [List.mem_cons, not_or] at hwire
      by_cases hbit : value.testBit 0
      · rw [controlledXorConstant, if_pos hbit, run_append,
          ih (value / 2)]
        · simp [run, applyGate, upd, hwire.1]
        · exact hwire.2
      · rw [controlledXorConstant, if_neg hbit, List.nil_append]
        exact ih (value / 2) state hwire.2

private theorem controlledXorConstant_wellFormed
    (control : Wire) (targets : List Wire) (value : Nat)
    (hlayout : ∀ target ∈ targets, control ≠ target) :
    CircuitWellFormed (controlledXorConstant control targets value) := by
  induction targets generalizing value with
  | nil => simp [controlledXorConstant, CircuitWellFormed]
  | cons target targets ih =>
      have hhead := hlayout target (by simp)
      have htail : ∀ wire ∈ targets, control ≠ wire := by
        intro wire hwire
        exact hlayout wire (by simp [hwire])
      by_cases hbit : value.testBit 0
      · rw [controlledXorConstant, if_pos hbit, circuitWellFormed_append]
        exact ⟨by simp [CircuitWellFormed, Gate.WellFormed, hhead],
          ih (value / 2) htail⟩
      · rw [controlledXorConstant, if_neg hbit]
        exact ih (value / 2) htail

theorem borrowedXorConstant_wellFormed
    (dirty selector : Wire) (targets : List Wire) (value : Nat)
    (hlayout : BorrowedConstantLayout dirty selector targets) :
    CircuitWellFormed (borrowedXorConstant dirty selector targets value) := by
  induction targets generalizing value with
  | nil => simp [borrowedXorConstant, CircuitWellFormed]
  | cons target targets ih =>
      have hhead := hlayout target (by simp)
      have htail : BorrowedConstantLayout dirty selector targets := by
        intro wire hwire
        exact hlayout wire (by simp [hwire])
      by_cases hbit : value.testBit 0
      · rw [borrowedXorConstant, if_pos hbit, circuitWellFormed_append]
        exact ⟨borrowedXorBit_wellFormed dirty selector target hhead,
          ih (value / 2) htail⟩
      · rw [borrowedXorConstant, if_neg hbit]
        exact ih (value / 2) htail

theorem controlledXorConstant_usesOnly
    (control : Wire) (targets : List Wire) (value : Nat) :
    PaperCircuitUsesOnly (control :: targets)
      (controlledXorConstant control targets value) := by
  induction targets generalizing value with
  | nil => simp [controlledXorConstant, PaperCircuitUsesOnly]
  | cons target targets ih =>
      by_cases hbit : value.testBit 0
      · rw [controlledXorConstant, if_pos hbit]
        apply PaperCircuitUsesOnly.append
        · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
        · apply (ih (value / 2)).mono
          simp only [List.mem_cons]
          aesop
      · rw [controlledXorConstant, if_neg hbit]
        apply (ih (value / 2)).mono
        simp only [List.mem_cons]
        aesop

theorem borrowedXorConstant_usesOnly
    (dirty selector : Wire) (targets : List Wire) (value : Nat) :
    PaperCircuitUsesOnly (dirty :: selector :: targets)
      (borrowedXorConstant dirty selector targets value) := by
  induction targets generalizing value with
  | nil => simp [borrowedXorConstant, PaperCircuitUsesOnly]
  | cons target targets ih =>
      by_cases hbit : value.testBit 0
      · rw [borrowedXorConstant, if_pos hbit]
        apply PaperCircuitUsesOnly.append
        · apply (borrowedXorBit_usesOnly dirty selector target).mono
          simp only [List.mem_cons]
          aesop
        · apply (ih (value / 2)).mono
          simp only [List.mem_cons]
          aesop
      · rw [borrowedXorConstant, if_neg hbit]
        apply (ih (value / 2)).mono
        simp only [List.mem_cons]
        aesop

/-- Number of set bits among the low `width` bits of `value`. -/
def lowBitCount : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, value =>
      (if value.testBit 0 then 1 else 0) + lowBitCount width (value / 2)

theorem borrowedXorConstant_cnotCount
    (dirty selector : Wire) (targets : List Wire) (value : Nat) :
    eeaCnotCount (borrowedXorConstant dirty selector targets value) =
      4 * lowBitCount targets.length value := by
  induction targets generalizing value with
  | nil => rfl
  | cons target targets ih =>
      by_cases hbit : value.testBit 0
      · rw [borrowedXorConstant, if_pos hbit, eeaCnotCount_append, ih]
        simp [lowBitCount, hbit]
        omega
      · rw [borrowedXorConstant, if_neg hbit]
        simpa [lowBitCount, hbit] using ih (value / 2)

theorem borrowedXorConstant_toffoliCount
    (dirty selector : Wire) (targets : List Wire) (value : Nat) :
    eeaToffoliCount (borrowedXorConstant dirty selector targets value) = 0 := by
  induction targets generalizing value with
  | nil => rfl
  | cons target targets ih =>
      by_cases hbit : value.testBit 0 <;>
        simp [borrowedXorConstant, hbit, eeaToffoliCount_append, ih]

theorem borrowedXorConstant_tCount
    (dirty selector : Wire) (targets : List Wire) (value : Nat) :
    ShorECDLP.tCount (borrowedXorConstant dirty selector targets value) = 0 := by
  induction targets generalizing value with
  | nil => rfl
  | cons target targets ih =>
      by_cases hbit : value.testBit 0 <;>
        simp [borrowedXorConstant, hbit, tCount_append, ih]

/-- One decoded length contribution: `selector` chooses `value`, while `dirty` is borrowed
from the opposite Work register. -/
structure BorrowedWriteLane where
  dirty : Wire
  selector : Wire
  value : Nat
deriving DecidableEq, Repr

def BorrowedWriteLane.support (lane : BorrowedWriteLane) : List Wire :=
  [lane.dirty, lane.selector]

def BorrowedWriteLane.Layout (lane : BorrowedWriteLane)
    (targets : List Wire) : Prop :=
  BorrowedConstantLayout lane.dirty lane.selector targets

def borrowedXorWriter (targets : List Wire) : List BorrowedWriteLane → Circuit
  | [] => []
  | lane :: lanes =>
      borrowedXorConstant lane.dirty lane.selector targets lane.value ++
        borrowedXorWriter targets lanes

/-- Ideal clean-control meaning of the borrowed writer. -/
def selectedXorWriter (targets : List Wire) : List BorrowedWriteLane → Circuit
  | [] => []
  | lane :: lanes =>
      controlledXorConstant lane.selector targets lane.value ++
        selectedXorWriter targets lanes

/-- Gate-independent Boolean action of all decoded writer lanes, in source order. -/
def selectedXorWriterState (targets : List Wire) :
    List BorrowedWriteLane → BasisState → BasisState
  | [], state => state
  | lane :: lanes, state =>
      selectedXorWriterState targets lanes
        (xorConstantState (state lane.selector) targets lane.value state)

def BorrowedWriterLayout (targets : List Wire)
    (lanes : List BorrowedWriteLane) : Prop :=
  ∀ lane ∈ lanes, lane.Layout targets

/-- Complete named support of a borrowed-work writer. -/
def borrowedXorWriterSupport (targets : List Wire)
    (lanes : List BorrowedWriteLane) : List Wire :=
  targets ++ lanes.flatMap BorrowedWriteLane.support

/-- Whole-state refinement of every borrowed length writer to its clean-selector meaning. -/
theorem run_borrowedXorWriter
    (targets : List Wire) (lanes : List BorrowedWriteLane)
    (state : BasisState) (hlayout : BorrowedWriterLayout targets lanes) :
    run (borrowedXorWriter targets lanes) state =
      run (selectedXorWriter targets lanes) state := by
  induction lanes generalizing state with
  | nil => rfl
  | cons lane lanes ih =>
      have hhead := hlayout lane (by simp)
      have htail : BorrowedWriterLayout targets lanes := by
        intro next hnext
        exact hlayout next (by simp [hnext])
      rw [borrowedXorWriter, selectedXorWriter, run_append, run_append,
        run_borrowedXorConstant lane.dirty lane.selector targets lane.value state hhead,
        ih _ htail]

/-- Direct whole-state Boolean semantics of the decoded borrowed-work writer. -/
theorem run_borrowedXorWriter_state
    (targets : List Wire) (lanes : List BorrowedWriteLane)
    (state : BasisState) (hlayout : BorrowedWriterLayout targets lanes) :
    run (borrowedXorWriter targets lanes) state =
      selectedXorWriterState targets lanes state := by
  rw [run_borrowedXorWriter targets lanes state hlayout]
  induction lanes generalizing state with
  | nil => rfl
  | cons lane lanes ih =>
      have hhead := hlayout lane (by simp)
      have htail : BorrowedWriterLayout targets lanes := by
        intro next hnext
        exact hlayout next (by simp [hnext])
      have hselector : ∀ target ∈ targets, lane.selector ≠ target := by
        intro target htarget
        have hnd := hhead target htarget
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
          or_false, not_or] at hnd
        exact hnd.2.1
      rw [selectedXorWriter, run_append,
        run_controlledXorConstant lane.selector targets lane.value state hselector,
        ih _ htail]
      rfl

@[simp]
theorem borrowedXorWriter_HPFree
    (targets : List Wire) (lanes : List BorrowedWriteLane) :
    HPFree (borrowedXorWriter targets lanes) := by
  induction lanes with
  | nil => simp [borrowedXorWriter]
  | cons lane lanes ih => simp [borrowedXorWriter, ih]

theorem borrowedXorWriter_wellFormed
    (targets : List Wire) (lanes : List BorrowedWriteLane)
    (hlayout : BorrowedWriterLayout targets lanes) :
    CircuitWellFormed (borrowedXorWriter targets lanes) := by
  induction lanes with
  | nil => simp [borrowedXorWriter, CircuitWellFormed]
  | cons lane lanes ih =>
      rw [borrowedXorWriter, circuitWellFormed_append]
      constructor
      · exact borrowedXorConstant_wellFormed lane.dirty lane.selector targets lane.value
          (hlayout lane (by simp))
      · exact ih (by
          intro next hnext
          exact hlayout next (by simp [hnext]))

theorem borrowedXorWriter_usesOnly
    (targets : List Wire) (lanes : List BorrowedWriteLane) :
    PaperCircuitUsesOnly (borrowedXorWriterSupport targets lanes)
      (borrowedXorWriter targets lanes) := by
  induction lanes with
  | nil => simp [borrowedXorWriter, PaperCircuitUsesOnly]
  | cons lane lanes ih =>
      rw [borrowedXorWriter]
      apply PaperCircuitUsesOnly.append
      · apply (borrowedXorConstant_usesOnly
          lane.dirty lane.selector targets lane.value).mono
        intro wire hwire
        simp only [borrowedXorWriterSupport, BorrowedWriteLane.support,
          List.flatMap_cons, List.mem_cons, List.mem_append] at hwire ⊢
        aesop
      · apply ih.mono
        intro wire hwire
        simp only [borrowedXorWriterSupport, BorrowedWriteLane.support,
          List.flatMap_cons, List.mem_append] at hwire ⊢
        aesop

/-- Every basis wire outside the declared writer footprint is unchanged. -/
theorem borrowedXorWriter_preservesOutside
    (targets : List Wire) (lanes : List BorrowedWriteLane)
    (state : BasisState) (wire : Wire)
    (hwire : wire ∉ borrowedXorWriterSupport targets lanes) :
    run (borrowedXorWriter targets lanes) state wire = state wire :=
  PaperCircuitUsesOnly.preservesOutside
    (borrowedXorWriter_usesOnly targets lanes) state hwire

private theorem selectedXorWriter_preservesOutside
    (targets : List Wire) (lanes : List BorrowedWriteLane)
    (state : BasisState) (wire : Wire) (hwire : wire ∉ targets) :
    run (selectedXorWriter targets lanes) state wire = state wire := by
  induction lanes generalizing state with
  | nil => rfl
  | cons lane lanes ih =>
      rw [selectedXorWriter, run_append, ih]
      exact controlledXorConstant_preservesOutside
        lane.selector targets lane.value state wire hwire

/-- Every borrowed wire is restored for arbitrary initial contents. -/
theorem borrowedXorWriter_restoresDirty
    (targets : List Wire) (lanes : List BorrowedWriteLane)
    (state : BasisState) (hlayout : BorrowedWriterLayout targets lanes)
    (lane : BorrowedWriteLane) (hlane : lane ∈ lanes) :
    run (borrowedXorWriter targets lanes) state lane.dirty = state lane.dirty := by
  rw [run_borrowedXorWriter targets lanes state hlayout]
  apply selectedXorWriter_preservesOutside
  intro hmem
  have hnd := hlayout lane hlane lane.dirty hmem
  simp at hnd

/-- Exact CNOT count of the per-lane normal form.  This is not yet the CNOT count of the grouped
production writer/zero-map sandwich from Figures 12--13. -/
theorem borrowedXorWriter_cnotCount
    (targets : List Wire) (lanes : List BorrowedWriteLane) :
    eeaCnotCount (borrowedXorWriter targets lanes) =
      4 * (lanes.map fun lane => lowBitCount targets.length lane.value).sum := by
  induction lanes with
  | nil => rfl
  | cons lane lanes ih =>
      rw [borrowedXorWriter, eeaCnotCount_append,
        borrowedXorConstant_cnotCount, ih]
      simp [Nat.mul_add]

theorem borrowedXorWriter_toffoliCount
    (targets : List Wire) (lanes : List BorrowedWriteLane) :
    eeaToffoliCount (borrowedXorWriter targets lanes) = 0 := by
  induction lanes with
  | nil => rfl
  | cons lane lanes ih =>
      simp [borrowedXorWriter, eeaToffoliCount_append,
        borrowedXorConstant_toffoliCount, ih]

theorem borrowedXorWriter_tCount
    (targets : List Wire) (lanes : List BorrowedWriteLane) :
    ShorECDLP.tCount (borrowedXorWriter targets lanes) = 0 := by
  induction lanes with
  | nil => rfl
  | cons lane lanes ih =>
      simp [borrowedXorWriter, tCount_append,
        borrowedXorConstant_tCount, ih]

/-! ## Exact telescoping values from the supplemental writers -/

/-- Adjacent telescoping delta `Enc(j) XOR Enc(j-1)` for `j > k` in the
highest-position writer. -/
def highestPositionAdjacentDelta (j : Nat) : Nat :=
  (j - 1) ^^^ (j - 2)

/-- Bottom-lane delta `Enc(k) XOR Enc(0)`, where the truth-minus-one zero encoding is the
all-ones `width`-bit word. -/
def highestPositionBaseDelta (width k : Nat) : Nat :=
  (k - 1) ^^^ (2 ^ width - 1)

/-- `Enc(n+4-j) XOR Enc(n+4-(j+1))` for the right-length writer. -/
def rightLengthDelta (n j : Nat) : Nat :=
  (n + 3 - j) ^^^ (n + 3 - (j + 1))

/-- Top-lane delta `Enc(length at K) XOR Enc(0)` for the right-length writer. -/
def rightLengthBaseDelta (n width K : Nat) : Nat :=
  (n + 3 - K) ^^^ (2 ^ width - 1)

/-- Encoded right length stored for a lowest nonzero one-based position. -/
def encodedRightLength (n position : Nat) : Nat :=
  n + 3 - position

end ShorECDLP.Paper2607_13816
