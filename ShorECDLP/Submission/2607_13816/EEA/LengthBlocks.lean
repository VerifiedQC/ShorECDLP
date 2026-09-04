import ShorECDLP.Submission.«2607_13816».EEA.ZeroMap
import ShorECDLP.Submission.«2607_13816».EEA.Endpoint

/-!
# Literal grouped length writers and complete unary length blocks

The supplement does not use the four-CNOT per-lane normal form from `LengthUpdate.lean` in the
production circuit.  It emits one dirty-controlled constant stream, toggles the dirty bank by a
two-pass zero map, repeats the same stream, and applies the same zero map again.  This file binds
that literal grouped order before composing the two complete `len_update_*` blocks.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-! ## Pure Boolean algebra of repeated constant writes -/

/-- XOR a low constant word only when the supplied Boolean selector is set. -/
def gatedXorConstantBits (enabled : Bool) (bits : List Bool) (value : Nat) : List Bool :=
  if enabled then xorConstantBits bits value else bits

@[simp]
theorem gatedXorConstantBits_false (bits : List Bool) (value : Nat) :
    gatedXorConstantBits false bits value = bits := rfl

@[simp]
theorem gatedXorConstantBits_true (bits : List Bool) (value : Nat) :
    gatedXorConstantBits true bits value = xorConstantBits bits value := rfl

theorem xorConstantBits_involutive (bits : List Bool) (value : Nat) :
    xorConstantBits (xorConstantBits bits value) value = bits := by
  induction bits generalizing value with
  | nil => rfl
  | cons bit bits ih =>
      by_cases hbit : value.testBit 0 <;>
        simp [xorConstantBits, hbit, ih]

theorem xorConstantBits_comm
    (bits : List Bool) (left right : Nat) :
    xorConstantBits (xorConstantBits bits left) right =
      xorConstantBits (xorConstantBits bits right) left := by
  induction bits generalizing left right with
  | nil => rfl
  | cons bit bits ih =>
      by_cases hleft : left.testBit 0 <;>
        by_cases hright : right.testBit 0 <;>
          simp [xorConstantBits, hleft, hright, ih]

theorem gatedXorConstantBits_comm
    (leftEnabled rightEnabled : Bool) (bits : List Bool)
    (leftValue rightValue : Nat) :
    gatedXorConstantBits rightEnabled
        (gatedXorConstantBits leftEnabled bits leftValue) rightValue =
      gatedXorConstantBits leftEnabled
        (gatedXorConstantBits rightEnabled bits rightValue) leftValue := by
  cases leftEnabled <;> cases rightEnabled <;>
    simp [gatedXorConstantBits, xorConstantBits_comm]

theorem gatedXorConstantBits_combine
    (left right : Bool) (bits : List Bool) (value : Nat) :
    gatedXorConstantBits right
        (gatedXorConstantBits left bits value) value =
      gatedXorConstantBits (Bool.xor left right) bits value := by
  cases left <;> cases right <;>
    simp [gatedXorConstantBits, xorConstantBits_involutive]

/-- Apply one source-ordered list of Boolean-controlled encoded constants. -/
def constantWriteWord
    (valueAt : Nat → Nat) : List Nat → List Bool → List Bool → List Bool
  | [], _, bits => bits
  | _, [], bits => bits
  | label :: labels, enabled :: selectors, bits =>
      constantWriteWord valueAt labels selectors
        (gatedXorConstantBits enabled bits (valueAt label))

private theorem constantWriteWord_gatedXor_comm
    (labels : List Nat) (selectors : List Bool) (valueAt : Nat → Nat)
    (enabled : Bool) (value : Nat) (bits : List Bool) :
    gatedXorConstantBits enabled
        (constantWriteWord valueAt labels selectors bits) value =
      constantWriteWord valueAt labels selectors
        (gatedXorConstantBits enabled bits value) := by
  induction labels generalizing selectors bits with
  | nil => rfl
  | cons label labels ih =>
      cases selectors with
      | nil => rfl
      | cons selector selectors =>
          rw [constantWriteWord, constantWriteWord, ih,
            gatedXorConstantBits_comm]

/-- Two identical constant streams whose selectors differ by an XOR collapse to the XOR
selector stream.  This is the algebra used by the write/map/write/map sandwich. -/
theorem constantWriteWord_pair
    (labels : List Nat) (left right : List Bool)
    (valueAt : Nat → Nat) (bits : List Bool)
    (hleft : left.length = labels.length)
    (hright : right.length = labels.length) :
    constantWriteWord valueAt labels right
        (constantWriteWord valueAt labels left bits) =
      constantWriteWord valueAt labels (xorWords left right) bits := by
  induction labels generalizing left right bits with
  | nil =>
      have hleftNil : left = [] := List.length_eq_zero_iff.mp hleft
      have hrightNil : right = [] := List.length_eq_zero_iff.mp hright
      subst left
      subst right
      rfl
  | cons label labels ih =>
      cases left with
      | nil => simp at hleft
      | cons left lefts =>
          cases right with
          | nil => simp at hright
          | cons right rights =>
              have hlefts : lefts.length = labels.length := by simpa using hleft
              have hrights : rights.length = labels.length := by simpa using hright
              change constantWriteWord valueAt labels rights
                  (gatedXorConstantBits right
                    (constantWriteWord valueAt labels lefts
                      (gatedXorConstantBits left bits (valueAt label)))
                    (valueAt label)) =
                constantWriteWord valueAt labels (xorWords lefts rights)
                  (gatedXorConstantBits (Bool.xor left right) bits (valueAt label))
              rw [
                constantWriteWord_gatedXor_comm labels lefts valueAt,
                ih lefts rights _ hlefts hrights,
                gatedXorConstantBits_combine]

theorem xorWords_reverse'
    (left right : List Bool) (hlength : left.length = right.length) :
    (xorWords left right).reverse = xorWords left.reverse right.reverse := by
  exact List.reverse_zipWith hlength

theorem xorWords_left_cancel
    (left right : List Bool) (hlength : left.length = right.length) :
    xorWords left (xorWords left right) = right := by
  induction left generalizing right with
  | nil =>
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail := ih rights (Nat.succ.inj hlength)
          change (Bool.xor left (Bool.xor left right)) ::
              xorWords lefts (xorWords lefts rights) = right :: rights
          rw [htail]
          cases left <;> cases right <;> rfl

theorem xorWords_right_cancel
    (left right : List Bool) (hlength : left.length = right.length) :
    xorWords (xorWords left right) right = left := by
  induction left generalizing right with
  | nil =>
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail := ih rights (Nat.succ.inj hlength)
          change (Bool.xor (Bool.xor left right) right) ::
              xorWords (xorWords lefts rights) rights = left :: lefts
          rw [htail]
          cases left <;> cases right <;> rfl

private theorem readWireWord_congr
    (labels : List Nat) (wireAt : Nat → Wire)
    (left right : BasisState)
    (hagree : ∀ label, label ∈ labels → left (wireAt label) = right (wireAt label)) :
    readWireWord labels wireAt left = readWireWord labels wireAt right := by
  unfold readWireWord
  apply List.map_congr_left
  exact hagree

private theorem readWireWord_eq_at
    (labels : List Nat) (wireAt : Nat → Wire)
    (left right : BasisState)
    (hvalues : readWireWord labels wireAt left = readWireWord labels wireAt right)
    (label : Nat) (hlabel : label ∈ labels) :
    left (wireAt label) = right (wireAt label) := by
  induction labels with
  | nil => simp at hlabel
  | cons head tail ih =>
      simp only [readWireWord, List.map_cons, List.cons.injEq] at hvalues
      rcases List.mem_cons.mp hlabel with rfl | hlabel
      · exact hvalues.1
      · exact ih hvalues.2 hlabel

private theorem wireValues_congr
    (wires : List Wire) (left right : BasisState)
    (hagree : ∀ wire, wire ∈ wires → left wire = right wire) :
    wireValues wires left = wireValues wires right := by
  unfold wireValues
  apply List.map_congr_left
  exact hagree

private theorem wireValues_eq_at_local
    (wires : List Wire) (left right : BasisState)
    (hvalues : wireValues wires left = wireValues wires right)
    (wire : Wire) (hwire : wire ∈ wires) :
    left wire = right wire := by
  induction wires with
  | nil => simp at hwire
  | cons head tail ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq] at hvalues
      rcases List.mem_cons.mp hwire with rfl | hwire
      · exact hvalues.1
      · exact ih hvalues.2 hwire

/-! ## Literal dirty-controlled constant streams -/

/-- One source-ordered dirty-controlled constant stream. -/
def dirtyConstantWrites
    (targets : List Wire) (dirtyAt : Nat → Wire)
    (valueAt : Nat → Nat) : List Nat → Circuit
  | [] => []
  | label :: labels =>
      controlledXorConstant (dirtyAt label) targets (valueAt label) ++
        dirtyConstantWrites targets dirtyAt valueAt labels

theorem xorConstantState_preservesOutside
    (enabled : Bool) (targets : List Wire) (value : Nat)
    (state : BasisState) (wire : Wire) (hwire : wire ∉ targets) :
    xorConstantState enabled targets value state wire = state wire := by
  induction targets generalizing value state with
  | nil => cases enabled <;> rfl
  | cons target targets ih =>
      simp only [List.mem_cons, not_or] at hwire
      rw [xorConstantState, ih (value / 2)]
      by_cases hbit : value.testBit 0
      · simp [hbit, upd, hwire.1]
      · simp [hbit]
      exact hwire.2

theorem wireValues_xorConstantState
    (enabled : Bool) (targets : List Wire) (value : Nat)
    (state : BasisState) (hnd : targets.Nodup) :
    wireValues targets (xorConstantState enabled targets value state) =
      gatedXorConstantBits enabled (wireValues targets state) value := by
  induction targets generalizing value state with
  | nil => simp [wireValues, xorConstantState, gatedXorConstantBits,
      xorConstantBits]
  | cons target targets ih =>
      have htarget := (List.nodup_cons.mp hnd).1
      have htail := (List.nodup_cons.mp hnd).2
      let next := if value.testBit 0 then
          state[target ↦ Bool.xor (state target) enabled]
        else state
      have htailValues : wireValues targets next = wireValues targets state := by
        unfold wireValues
        apply List.map_congr_left
        intro wire hwire
        simp only [next]
        by_cases hbit : value.testBit 0
        · rw [if_pos hbit, upd_other]
          intro equality
          subst wire
          exact htarget hwire
        · rw [if_neg hbit]
      have hhead :
          xorConstantState enabled targets (value / 2) next target = next target :=
        xorConstantState_preservesOutside enabled targets (value / 2) next target htarget
      rw [xorConstantState]
      change wireValues (target :: targets)
          (xorConstantState enabled targets (value / 2) next) = _
      have htailResult := ih (value / 2) next htail
      unfold wireValues at htailResult htailValues
      simp only [wireValues, List.map_cons]
      rw [hhead, htailResult, htailValues]
      cases enabled <;> by_cases hbit : value.testBit 0 <;>
        simp [gatedXorConstantBits, xorConstantBits, next, hbit]

/-- Direct target-word semantics of one dirty-controlled stream. -/
theorem run_dirtyConstantWrites_word
    (targets : List Wire) (dirtyAt : Nat → Wire)
    (valueAt : Nat → Nat) (labels : List Nat)
    (state : BasisState) (htargets : targets.Nodup)
    (hcontrols : ∀ label, label ∈ labels → dirtyAt label ∉ targets) :
    wireValues targets
        (Classical.run (dirtyConstantWrites targets dirtyAt valueAt labels) state) =
      constantWriteWord valueAt labels (readWireWord labels dirtyAt state)
        (wireValues targets state) := by
  induction labels generalizing state with
  | nil => rfl
  | cons label labels ih =>
      have hhead : dirtyAt label ∉ targets := hcontrols label (by simp)
      have htail : ∀ next, next ∈ labels → dirtyAt next ∉ targets := by
        intro next hnext
        exact hcontrols next (by simp [hnext])
      rw [dirtyConstantWrites, Classical.run_append,
        run_controlledXorConstant (dirtyAt label) targets (valueAt label) state
          (fun target htarget hEq ↦ hhead (hEq ▸ htarget)),
        ih _ htail]
      have hcontrolsPreserved : ∀ next, next ∈ labels →
          xorConstantState (state (dirtyAt label)) targets (valueAt label) state
              (dirtyAt next) = state (dirtyAt next) := by
        intro next hnext
        exact xorConstantState_preservesOutside _ _ _ _ _ (htail next hnext)
      have hselectorWord :
          readWireWord labels dirtyAt
              (xorConstantState (state (dirtyAt label)) targets (valueAt label) state) =
            readWireWord labels dirtyAt state := by
        unfold readWireWord
        apply List.map_congr_left
        exact hcontrolsPreserved
      change constantWriteWord valueAt labels
          (readWireWord labels dirtyAt
            (xorConstantState (state (dirtyAt label)) targets (valueAt label) state))
          (wireValues targets
            (xorConstantState (state (dirtyAt label)) targets (valueAt label) state)) =
        constantWriteWord valueAt labels (readWireWord labels dirtyAt state)
          (gatedXorConstantBits (state (dirtyAt label))
            (wireValues targets state) (valueAt label))
      rw [hselectorWord,
        wireValues_xorConstantState
          (state (dirtyAt label)) targets (valueAt label) state htargets]

/-- A dirty-controlled stream never changes any wire outside its target register. -/
theorem dirtyConstantWrites_preservesOutside
    (targets : List Wire) (dirtyAt : Nat → Wire)
    (valueAt : Nat → Nat) (labels : List Nat)
    (state : BasisState) (wire : Wire) (hwire : wire ∉ targets) :
    Classical.run (dirtyConstantWrites targets dirtyAt valueAt labels) state wire =
      state wire := by
  induction labels generalizing state with
  | nil => rfl
  | cons label labels ih =>
      rw [dirtyConstantWrites, Classical.run_append, ih]
      exact controlledXorConstant_preservesOutside
        (dirtyAt label) targets (valueAt label) state wire hwire

/-- Complete named footprint of one dirty-controlled constant stream. -/
def dirtyConstantWritesSupport
    (targets : List Wire) (dirtyAt : Nat → Wire) (labels : List Nat) : List Wire :=
  targets ++ labels.map dirtyAt

theorem dirtyConstantWrites_usesOnly
    (targets : List Wire) (dirtyAt : Nat → Wire)
    (valueAt : Nat → Nat) (labels : List Nat) :
    PaperCircuitUsesOnly (dirtyConstantWritesSupport targets dirtyAt labels)
      (dirtyConstantWrites targets dirtyAt valueAt labels) := by
  induction labels with
  | nil => simp [dirtyConstantWrites, PaperCircuitUsesOnly]
  | cons label labels ih =>
      rw [dirtyConstantWrites]
      apply PaperCircuitUsesOnly.append
      · apply (controlledXorConstant_usesOnly
          (dirtyAt label) targets (valueAt label)).mono
        intro wire hwire
        simp only [dirtyConstantWritesSupport, List.map_cons,
          List.mem_cons, List.mem_append] at hwire ⊢
        aesop
      · apply ih.mono
        intro wire hwire
        simp only [dirtyConstantWritesSupport, List.map_cons,
          List.mem_cons, List.mem_append] at hwire ⊢
        aesop

@[simp]
theorem dirtyConstantWrites_HPFree
    (targets : List Wire) (dirtyAt : Nat → Wire)
    (valueAt : Nat → Nat) (labels : List Nat) :
    HPFree (dirtyConstantWrites targets dirtyAt valueAt labels) := by
  induction labels with
  | nil => simp [dirtyConstantWrites]
  | cons label labels ih =>
      simp [dirtyConstantWrites, ih]

theorem dirtyConstantWrites_wellFormed
    (targets : List Wire) (dirtyAt : Nat → Wire)
    (valueAt : Nat → Nat) (labels : List Nat)
    (hcontrols : ∀ label, label ∈ labels → ∀ target, target ∈ targets →
      dirtyAt label ≠ target) :
    CircuitWellFormed (dirtyConstantWrites targets dirtyAt valueAt labels) := by
  induction labels with
  | nil => simp [dirtyConstantWrites, CircuitWellFormed]
  | cons label labels ih =>
      rw [dirtyConstantWrites, circuitWellFormed_append]
      constructor
      · exact controlledXorConstant_wellFormed
          (dirtyAt label) targets (valueAt label)
          (fun target htarget ↦ hcontrols label (by simp) target htarget)
      · exact ih (by
          intro next hnext target htarget
          exact hcontrols next (by simp [hnext]) target htarget)

/-- Exact CNOT count of one literal dirty-controlled stream. -/
theorem dirtyConstantWrites_cnotCount
    (targets : List Wire) (dirtyAt : Nat → Wire)
    (valueAt : Nat → Nat) (labels : List Nat) :
    eeaCnotCount (dirtyConstantWrites targets dirtyAt valueAt labels) =
      (labels.map fun label ↦ lowBitCount targets.length (valueAt label)).sum := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      rw [dirtyConstantWrites, eeaCnotCount_append,
        controlledXorConstant_cnotCount, ih]
      rfl

@[simp]
theorem dirtyConstantWrites_toffoliCount
    (targets : List Wire) (dirtyAt : Nat → Wire)
    (valueAt : Nat → Nat) (labels : List Nat) :
    eeaToffoliCount (dirtyConstantWrites targets dirtyAt valueAt labels) = 0 := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      simp [dirtyConstantWrites, eeaToffoliCount_append, ih]

@[simp]
theorem dirtyConstantWrites_tCount
    (targets : List Wire) (dirtyAt : Nat → Wire)
    (valueAt : Nat → Nat) (labels : List Nat) :
    ShorECDLP.tCount (dirtyConstantWrites targets dirtyAt valueAt labels) = 0 := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      simp [dirtyConstantWrites, tCount_append, ih]

/-! ## Source value streams and grouped writers -/

/-- Low-word truncation used by the supplement's `value & ((1 << width) - 1)`. -/
def truncateConstant (width value : Nat) : Nat :=
  value % 2 ^ width

/-- Source delta at one upper-writer dirty lane. -/
def highestPositionWriteValue (width k : Nat) (label : Nat) : Nat :=
  truncateConstant width
    (if label = k then highestPositionBaseDelta width k
      else highestPositionAdjacentDelta label)

/-- Source delta at one right-writer dirty lane. -/
def rightLengthWriteValue (n width K : Nat) (label : Nat) : Nat :=
  truncateConstant width
    (if label = K then rightLengthBaseDelta n width K
      else rightLengthDelta n label)

/-- Descending dirty-write stream emitted by `highest_position_xor_write`. -/
def highestPositionDirtyWrites
    (k K : Nat) (targets : List Wire) (dirtyAt : Nat → Wire) : Circuit :=
  dirtyConstantWrites targets dirtyAt
    (highestPositionWriteValue targets.length k) (zeroMapLabels k K).reverse

/-- Increasing dirty-write stream emitted by `right_length_xor_write`. -/
def rightLengthDirtyWrites
    (n k K : Nat) (targets : List Wire) (dirtyAt : Nat → Wire) : Circuit :=
  dirtyConstantWrites targets dirtyAt
    (rightLengthWriteValue n targets.length K) (zeroMapLabels k K)

/-- Literal `highest_position_xor_write`: controlled seed, paired dirty-write streams, and the
same upper zero map after each stream. -/
def highestPositionXorWrite
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) : Circuit :=
  controlledXorConstant control targets
      (truncateConstant targets.length (K - 1)) ++
    highestPositionDirtyWrites k K targets dirtyAt ++
    upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt ++
    highestPositionDirtyWrites k K targets dirtyAt ++
    upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt

/-- Literal `right_length_xor_write` mirror. -/
def rightLengthXorWrite
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) : Circuit :=
  controlledXorConstant control targets
      (truncateConstant targets.length (n + 3 - k)) ++
    rightLengthDirtyWrites n k K targets dirtyAt ++
    lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt ++
    rightLengthDirtyWrites n k K targets dirtyAt ++
    lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt

/-- Physical role separation for either grouped writer. -/
structure LengthWriterLayout
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) : Prop
    extends ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt where
  targetNodup : targets.Nodup
  targetDisjoint : List.Disjoint targets
    (zeroMapWires k K tree control rangeAccumulator temporary path bitAt dirtyAt)

theorem LengthWriterLayout.mapWire_not_target
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    {wire : Wire}
    (hwire : wire ∈ zeroMapWires k K tree control rangeAccumulator temporary path
      bitAt dirtyAt) :
    wire ∉ targets := by
  intro htarget
  exact List.disjoint_left.mp hlayout.targetDisjoint htarget hwire

theorem LengthWriterLayout.control_not_target
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets) :
    control ∉ targets :=
  hlayout.mapWire_not_target (by
    simp [zeroMapWires, zeroMapProtectedWires])

theorem LengthWriterLayout.dirty_not_target
    {k K label : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabel : label ∈ zeroMapLabels k K) :
    dirtyAt label ∉ targets :=
  hlayout.mapWire_not_target (by
    simp only [zeroMapWires, List.mem_append, List.mem_cons,
      List.mem_map]
    exact Or.inr ⟨label, hlabel, rfl⟩)

theorem LengthWriterLayout.target_ne_range
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    {target : Wire} (htarget : target ∈ targets) :
    target ≠ rangeAccumulator := by
  intro equality
  subst target
  exact hlayout.mapWire_not_target (by
    simp [zeroMapWires]) htarget

private theorem LengthWriterLayout.target_not_dirty
    {k K label : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabel : label ∈ zeroMapLabels k K)
    {target : Wire} (htarget : target ∈ targets) :
    target ≠ dirtyAt label := by
  intro equality
  subst target
  exact hlayout.dirty_not_target hlabel htarget

/-- A complete upper zero map does not touch the writer's target word. -/
theorem LengthWriterLayout.upperMap_preserves_targets
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hkK : k ≤ K) (state : BasisState)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false) :
    wireValues targets
        (run (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
          bitAt dirtyAt) state) =
      wireValues targets state := by
  apply wireValues_congr
  intro target htarget
  apply upperZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout.toZeroMapLayout hcleanPath hcleanTemporary target
      (hlayout.target_ne_range htarget)
  intro label hlabel
  exact hlayout.target_not_dirty hlabel htarget

/-- Lower-map mirror of `LengthWriterLayout.upperMap_preserves_targets`. -/
theorem LengthWriterLayout.lowerMap_preserves_targets
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hkK : k ≤ K) (state : BasisState)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false) :
    wireValues targets
        (run (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
          bitAt dirtyAt) state) =
      wireValues targets state := by
  apply wireValues_congr
  intro target htarget
  apply lowerZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout.toZeroMapLayout hcleanPath hcleanTemporary target
      (hlayout.target_ne_range htarget)
  intro label hlabel
  exact hlayout.target_not_dirty hlabel htarget

private theorem LengthWriterLayout.protected_ne_dirty
    {k K label : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    {wire : Wire} (hwire : wire ∈ zeroMapProtectedWires tree control path)
    (hlabel : label ∈ zeroMapLabels k K) :
    wire ≠ dirtyAt label := by
  intro equality
  subst wire
  have hshared := hlayout.toZeroMapLayout.shared_eq_control hwire (by
    simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map]
    right
    exact ⟨label, hlabel, rfl⟩)
  exact hlayout.toZeroMapLayout.control_ne_dirty hlabel hshared.symm

theorem LengthWriterLayout.upperMap_preserves_protected
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hkK : k ≤ K) (state : BasisState)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    {wire : Wire} (hwire : wire ∈ zeroMapProtectedWires tree control path) :
    run (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
      bitAt dirtyAt) state wire = state wire := by
  apply upperZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout.toZeroMapLayout hcleanPath hcleanTemporary wire
  · intro equality
    subst wire
    exact hlayout.toZeroMapLayout.range_not_protected hwire
  · intro label hlabel
    exact hlayout.protected_ne_dirty hwire hlabel

theorem LengthWriterLayout.lowerMap_preserves_protected
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hkK : k ≤ K) (state : BasisState)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    {wire : Wire} (hwire : wire ∈ zeroMapProtectedWires tree control path) :
    run (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
      bitAt dirtyAt) state wire = state wire := by
  apply lowerZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout.toZeroMapLayout hcleanPath hcleanTemporary wire
  · intro equality
    subst wire
    exact hlayout.toZeroMapLayout.range_not_protected hwire
  · intro label hlabel
    exact hlayout.protected_ne_dirty hwire hlabel

theorem LengthWriterLayout.upperMap_preserves_bit
    {k K label : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hkK : k ≤ K) (hlabel : label ∈ zeroMapLabels k K)
    (state : BasisState) (hcleanPath : Clean path state)
    (hcleanTemporary : state temporary = false) :
    run (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
      bitAt dirtyAt) state (bitAt label) = state (bitAt label) := by
  apply upperZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout.toZeroMapLayout hcleanPath hcleanTemporary
      (bitAt label) (Ne.symm (hlayout.toZeroMapLayout.range_ne_bit hlabel))
  intro dirtyLabel hdirtyLabel
  exact hlayout.toZeroMapLayout.bit_ne_dirty hlabel hdirtyLabel

theorem LengthWriterLayout.lowerMap_preserves_bit
    {k K label : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire} {targets : List Wire}
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hkK : k ≤ K) (hlabel : label ∈ zeroMapLabels k K)
    (state : BasisState) (hcleanPath : Clean path state)
    (hcleanTemporary : state temporary = false) :
    run (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
      bitAt dirtyAt) state (bitAt label) = state (bitAt label) := by
  apply lowerZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout.toZeroMapLayout hcleanPath hcleanTemporary
      (bitAt label) (Ne.symm (hlayout.toZeroMapLayout.range_ne_bit hlabel))
  intro dirtyLabel hdirtyLabel
  exact hlayout.toZeroMapLayout.bit_ne_dirty hlabel hdirtyLabel

/-! ## Direct semantics of the grouped writers -/

/-- Gate-independent action of one complete highest-position writer. -/
def highestPositionWordAction
    (width k K : Nat) (enabled : Bool) (rangeBits targetBits : List Bool) : List Bool :=
  constantWriteWord (highestPositionWriteValue width k)
    (zeroMapLabels k K).reverse
    (gateWord enabled (suffixZeroFlags rangeBits)).reverse
    (gatedXorConstantBits enabled targetBits
      (truncateConstant width (K - 1)))

/-- Gate-independent action of one complete right-length writer. -/
def rightLengthWordAction
    (n width k K : Nat) (enabled : Bool) (rangeBits targetBits : List Bool) : List Bool :=
  constantWriteWord (rightLengthWriteValue n width K)
    (zeroMapLabels k K)
    (gateWord enabled (prefixZeroFlags rangeBits))
    (gatedXorConstantBits enabled targetBits
      (truncateConstant width (n + 3 - k)))

/-- The literal upper writer has exactly the source seed followed by the suffix-zero-selected
telescoping constants.  This theorem is intentionally stated at the Boolean-word boundary; the
generic word-to-natural interpretation of the affine transforms lives in `WordNat`. -/
theorem highestPositionXorWrite_word
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    wireValues targets
        (run (highestPositionXorWrite k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) state) =
      constantWriteWord (highestPositionWriteValue targets.length k)
        (zeroMapLabels k K).reverse
        (gateWord (state control)
          (suffixZeroFlags
            (upperRangeBits (state control) boundary (zeroMapLabels k K) bitAt state))).reverse
        (gatedXorConstantBits (state control) (wireValues targets state)
          (truncateConstant targets.length (K - 1))) := by
  let labels := zeroMapLabels k K
  let seedValue := truncateConstant targets.length (K - 1)
  let valueAt := highestPositionWriteValue targets.length k
  let map := upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt
  let seed := controlledXorConstant control targets seedValue
  let writes := dirtyConstantWrites targets dirtyAt valueAt labels.reverse
  let seeded := run seed state
  let firstWritten := run writes seeded
  let firstMapped := run map firstWritten
  let secondWritten := run writes firstMapped
  let flags := gateWord (state control)
    (suffixZeroFlags
      (upperRangeBits (state control) boundary labels bitAt state))
  have hcontrolTargets : ∀ target ∈ targets, control ≠ target := by
    intro target htarget equality
    subst target
    exact hlayout.control_not_target htarget
  have hdirtyTargets : ∀ label, label ∈ labels.reverse → dirtyAt label ∉ targets := by
    intro label hlabel
    exact hlayout.dirty_not_target (by
      simpa only [labels, List.mem_reverse] using hlabel)
  have hseedOutside : ∀ wire, wire ∉ targets → seeded wire = state wire := by
    intro wire hwire
    exact controlledXorConstant_preservesOutside control targets seedValue state wire hwire
  have hfirstOutside : ∀ wire, wire ∉ targets → firstWritten wire = state wire := by
    intro wire hwire
    calc
      firstWritten wire = seeded wire := by
        exact dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels.reverse
          seeded wire hwire
      _ = state wire := hseedOutside wire hwire
  have hfirstCleanPath : Clean path firstWritten := by
    intro wire hwire
    rw [hfirstOutside wire]
    · exact hcleanPath wire hwire
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hwire])
  have hfirstRange : firstWritten rangeAccumulator = false := by
    rw [hfirstOutside rangeAccumulator]
    · exact hcleanRange
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstTemporary : firstWritten temporary = false := by
    rw [hfirstOutside temporary]
    · exact hcleanTemporary
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstRoute : tree.routeLabel firstWritten = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstOutside wire (hlayout.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hwire]))
  have hfirstControl : firstWritten control = state control := by
    exact hfirstOutside control hlayout.control_not_target
  have hfirstBits :
      upperRangeBits (firstWritten control) boundary labels bitAt firstWritten =
        upperRangeBits (state control) boundary labels bitAt state := by
    unfold upperRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hfirstControl]
    have hlabel' : label ∈ zeroMapLabels k K := by
      simpa only [labels] using hlabel
    have hbitNotTarget : bitAt label ∉ targets :=
      hlayout.mapWire_not_target (by
        simp only [zeroMapWires, List.mem_append, List.mem_cons, List.mem_map]
        aesop)
    rw [hfirstOutside (bitAt label) hbitNotTarget]
  have hseedWord :
      wireValues targets seeded =
        gatedXorConstantBits (state control) (wireValues targets state) seedValue := by
    rw [show seeded = xorConstantState (state control) targets seedValue state by
      exact run_controlledXorConstant control targets seedValue state hcontrolTargets]
    exact wireValues_xorConstantState (state control) targets seedValue state
      hlayout.targetNodup
  have hseedDirty : readWireWord labels.reverse dirtyAt seeded =
      readWireWord labels.reverse dirtyAt state := by
    apply readWireWord_congr
    intro label hlabel
    exact hseedOutside (dirtyAt label) (hdirtyTargets label hlabel)
  have hfirstTarget :
      wireValues targets firstWritten =
        constantWriteWord valueAt labels.reverse
          (readWireWord labels.reverse dirtyAt state)
          (gatedXorConstantBits (state control) (wireValues targets state) seedValue) := by
    rw [show wireValues targets firstWritten =
        constantWriteWord valueAt labels.reverse
          (readWireWord labels.reverse dirtyAt seeded) (wireValues targets seeded) by
      exact run_dirtyConstantWrites_word targets dirtyAt valueAt labels.reverse seeded
        hlayout.targetNodup hdirtyTargets,
      hseedDirty, hseedWord]
  have hfirstDirty : readWireWord labels dirtyAt firstWritten =
      readWireWord labels dirtyAt state := by
    apply readWireWord_congr
    intro label hlabel
    exact hfirstOutside (dirtyAt label)
      (hlayout.dirty_not_target (by simpa only [labels] using hlabel))
  have hmapDirty : readWireWord labels dirtyAt firstMapped =
      xorWords (readWireWord labels dirtyAt state) flags := by
    rw [show readWireWord labels dirtyAt firstMapped =
        xorWords (readWireWord labels dirtyAt firstWritten)
          (gateWord (firstWritten control)
            (suffixZeroFlags
              (upperRangeBits (firstWritten control) boundary labels bitAt firstWritten))) by
      exact upperZeroMapUnitary_correct k K boundary hkK hboundary tree control
        rangeAccumulator temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout
        (by simpa only [labels] using hlabels) hfirstRoute hfirstCleanPath hfirstRange
        hfirstTemporary,
      hfirstDirty, hfirstBits, hfirstControl]
  have hmapTarget : wireValues targets firstMapped = wireValues targets firstWritten := by
    exact hlayout.upperMap_preserves_targets hkK firstWritten hfirstCleanPath hfirstTemporary
  have hmapClean : Clean (path ++ [rangeAccumulator, temporary]) firstMapped := by
    exact upperZeroMapUnitary_clean k K boundary hkK hboundary tree control rangeAccumulator
      temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout
      (by simpa only [labels] using hlabels) hfirstRoute hfirstCleanPath hfirstRange
      hfirstTemporary
  have hflagsLength : flags.length = labels.length := by
    simp [flags, gateWord]
  have hdirtyFlagsLength :
      (readWireWord labels.reverse dirtyAt state).length = flags.reverse.length := by
    simp [readWireWord, hflagsLength]
  have hsecondSelectors : readWireWord labels.reverse dirtyAt firstMapped =
      xorWords (readWireWord labels.reverse dirtyAt state) flags.reverse := by
    calc
      readWireWord labels.reverse dirtyAt firstMapped =
          (readWireWord labels dirtyAt firstMapped).reverse := by
            rw [readWireWord_reverse]
      _ = (xorWords (readWireWord labels dirtyAt state) flags).reverse := by
            rw [hmapDirty]
      _ = xorWords (readWireWord labels dirtyAt state).reverse flags.reverse := by
            apply xorWords_reverse'
            simp [readWireWord, hflagsLength]
      _ = xorWords (readWireWord labels.reverse dirtyAt state) flags.reverse := by
            rw [readWireWord_reverse]
  have hsecondTarget : wireValues targets secondWritten =
      constantWriteWord valueAt labels.reverse flags.reverse
        (gatedXorConstantBits (state control) (wireValues targets state) seedValue) := by
    rw [show wireValues targets secondWritten =
        constantWriteWord valueAt labels.reverse
          (readWireWord labels.reverse dirtyAt firstMapped)
          (wireValues targets firstMapped) by
      exact run_dirtyConstantWrites_word targets dirtyAt valueAt labels.reverse firstMapped
        hlayout.targetNodup hdirtyTargets,
      hsecondSelectors, hmapTarget, hfirstTarget,
      constantWriteWord_pair labels.reverse
        (readWireWord labels.reverse dirtyAt state)
        (xorWords (readWireWord labels.reverse dirtyAt state) flags.reverse)
        valueAt
        (gatedXorConstantBits (state control) (wireValues targets state) seedValue)]
    · rw [xorWords_left_cancel _ _ hdirtyFlagsLength]
    · simp [readWireWord]
    · calc
        (xorWords (readWireWord labels.reverse dirtyAt state) flags.reverse).length =
            (readWireWord labels.reverse dirtyAt state).length :=
          xorWords_length _ _ hdirtyFlagsLength
        _ = labels.reverse.length := by simp [readWireWord]
  have hsecondCleanPath : Clean path secondWritten := by
    intro wire hwire
    change run (dirtyConstantWrites targets dirtyAt valueAt labels.reverse)
      firstMapped wire = false
    rw [dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels.reverse
      firstMapped wire]
    · exact hmapClean wire (by simp [hwire])
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hwire])
  have hsecondTemporary : secondWritten temporary = false := by
    change run (dirtyConstantWrites targets dirtyAt valueAt labels.reverse)
      firstMapped temporary = false
    rw [dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels.reverse
      firstMapped temporary]
    · exact hmapClean temporary (by simp)
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  rw [highestPositionXorWrite]
  simp only [Classical.run_append]
  change wireValues targets (run map secondWritten) = _
  rw [hlayout.upperMap_preserves_targets hkK secondWritten hsecondCleanPath
    hsecondTemporary, hsecondTarget]

theorem highestPositionXorWrite_wordAction
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    wireValues targets
        (run (highestPositionXorWrite k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) state) =
      highestPositionWordAction targets.length k K (state control)
        (upperRangeBits (state control) boundary (zeroMapLabels k K) bitAt state)
        (wireValues targets state) := by
  exact highestPositionXorWrite_word k K boundary hkK hboundary tree control
    rangeAccumulator temporary path bitAt dirtyAt targets state hlayout hlabels hroute
    hcleanPath hcleanRange hcleanTemporary

/-- Both upper zero-map applications restore the arbitrary dirty word, and the final application
leaves all decoder and recurrence scratch clean. -/
theorem highestPositionXorWrite_restores
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    let after := run
      (highestPositionXorWrite k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) state
    readWireWord (zeroMapLabels k K) dirtyAt after =
        readWireWord (zeroMapLabels k K) dirtyAt state ∧
      Clean (path ++ [rangeAccumulator, temporary]) after := by
  let labels := zeroMapLabels k K
  let seedValue := truncateConstant targets.length (K - 1)
  let valueAt := highestPositionWriteValue targets.length k
  let map := upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt
  let seed := controlledXorConstant control targets seedValue
  let writes := dirtyConstantWrites targets dirtyAt valueAt labels.reverse
  let seeded := run seed state
  let firstWritten := run writes seeded
  let firstMapped := run map firstWritten
  let secondWritten := run writes firstMapped
  let after := run map secondWritten
  let flags := gateWord (state control)
    (suffixZeroFlags
      (upperRangeBits (state control) boundary labels bitAt state))
  have hdirtyTargets : ∀ label, label ∈ labels.reverse → dirtyAt label ∉ targets := by
    intro label hlabel
    exact hlayout.dirty_not_target (by
      simpa only [labels, List.mem_reverse] using hlabel)
  have hseedOutside : ∀ wire, wire ∉ targets → seeded wire = state wire := by
    intro wire hwire
    exact controlledXorConstant_preservesOutside control targets seedValue state wire hwire
  have hfirstOutside : ∀ wire, wire ∉ targets → firstWritten wire = state wire := by
    intro wire hwire
    calc
      firstWritten wire = seeded wire :=
        dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels.reverse
          seeded wire hwire
      _ = state wire := hseedOutside wire hwire
  have hfirstCleanPath : Clean path firstWritten := by
    intro wire hwire
    rw [hfirstOutside wire]
    · exact hcleanPath wire hwire
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hwire])
  have hfirstRange : firstWritten rangeAccumulator = false := by
    rw [hfirstOutside rangeAccumulator]
    · exact hcleanRange
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstTemporary : firstWritten temporary = false := by
    rw [hfirstOutside temporary]
    · exact hcleanTemporary
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstRoute : tree.routeLabel firstWritten = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstOutside wire (hlayout.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hwire]))
  have hfirstControl : firstWritten control = state control :=
    hfirstOutside control hlayout.control_not_target
  have hfirstBits :
      upperRangeBits (firstWritten control) boundary labels bitAt firstWritten =
        upperRangeBits (state control) boundary labels bitAt state := by
    unfold upperRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hfirstControl]
    have hlabel' : label ∈ zeroMapLabels k K := by
      simpa only [labels] using hlabel
    rw [hfirstOutside (bitAt label) (hlayout.mapWire_not_target (by
      simp only [zeroMapWires, List.mem_append, List.mem_cons, List.mem_map]
      aesop))]
  have hfirstDirty : readWireWord labels dirtyAt firstWritten =
      readWireWord labels dirtyAt state := by
    apply readWireWord_congr
    intro label hlabel
    exact hfirstOutside (dirtyAt label)
      (hlayout.dirty_not_target (by simpa only [labels] using hlabel))
  have hmapDirty : readWireWord labels dirtyAt firstMapped =
      xorWords (readWireWord labels dirtyAt state) flags := by
    rw [show readWireWord labels dirtyAt firstMapped =
        xorWords (readWireWord labels dirtyAt firstWritten)
          (gateWord (firstWritten control)
            (suffixZeroFlags
              (upperRangeBits (firstWritten control) boundary labels bitAt firstWritten))) by
      exact upperZeroMapUnitary_correct k K boundary hkK hboundary tree control
        rangeAccumulator temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout
        (by simpa only [labels] using hlabels) hfirstRoute hfirstCleanPath hfirstRange
        hfirstTemporary,
      hfirstDirty, hfirstBits, hfirstControl]
  have hmapClean : Clean (path ++ [rangeAccumulator, temporary]) firstMapped :=
    upperZeroMapUnitary_clean k K boundary hkK hboundary tree control rangeAccumulator
      temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout
      (by simpa only [labels] using hlabels) hfirstRoute hfirstCleanPath hfirstRange
      hfirstTemporary
  have hmapRoute : tree.routeLabel firstMapped = boundary := by
    rw [← hfirstRoute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hlayout.upperMap_preserves_protected hkK firstWritten hfirstCleanPath
      hfirstTemporary (by simp [zeroMapProtectedWires, hwire])
  have hmapControl : firstMapped control = state control := by
    calc
      firstMapped control = firstWritten control := by
        change run
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
            firstWritten control = firstWritten control
        exact hlayout.upperMap_preserves_protected (wire := control) hkK firstWritten
          hfirstCleanPath hfirstTemporary (by simp [zeroMapProtectedWires])
      _ = state control := hfirstControl
  have hsecondOutside : ∀ wire, wire ∉ targets → secondWritten wire = firstMapped wire := by
    intro wire hwire
    exact dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels.reverse
      firstMapped wire hwire
  have hsecondCleanPath : Clean path secondWritten := by
    intro wire hwire
    rw [hsecondOutside wire]
    · exact hmapClean wire (by simp [hwire])
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hwire])
  have hsecondRange : secondWritten rangeAccumulator = false := by
    rw [hsecondOutside rangeAccumulator]
    · exact hmapClean rangeAccumulator (by simp)
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hsecondTemporary : secondWritten temporary = false := by
    rw [hsecondOutside temporary]
    · exact hmapClean temporary (by simp)
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hsecondRoute : tree.routeLabel secondWritten = boundary := by
    rw [← hmapRoute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hsecondOutside wire (hlayout.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hwire]))
  have hsecondControl : secondWritten control = state control := by
    rw [hsecondOutside control hlayout.control_not_target, hmapControl]
  have hsecondBits :
      upperRangeBits (secondWritten control) boundary labels bitAt secondWritten =
        upperRangeBits (state control) boundary labels bitAt state := by
    unfold upperRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hsecondControl]
    have hlabel' : label ∈ zeroMapLabels k K := by
      simpa only [labels] using hlabel
    have hbitNotTarget : bitAt label ∉ targets :=
      hlayout.mapWire_not_target (by
        simp only [zeroMapWires, List.mem_append, List.mem_cons, List.mem_map]
        aesop)
    have hmapBit : firstMapped (bitAt label) = firstWritten (bitAt label) := by
      change run
        (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
          firstWritten (bitAt label) = firstWritten (bitAt label)
      exact hlayout.upperMap_preserves_bit hkK hlabel' firstWritten hfirstCleanPath
        hfirstTemporary
    rw [hsecondOutside (bitAt label) hbitNotTarget, hmapBit,
      hfirstOutside (bitAt label) hbitNotTarget]
  have hsecondDirty : readWireWord labels dirtyAt secondWritten =
      xorWords (readWireWord labels dirtyAt state) flags := by
    rw [show readWireWord labels dirtyAt secondWritten =
        readWireWord labels dirtyAt firstMapped by
      apply readWireWord_congr
      intro label hlabel
      exact hsecondOutside (dirtyAt label)
        (hlayout.dirty_not_target (by simpa only [labels] using hlabel)),
      hmapDirty]
  have hflagsLength : (readWireWord labels dirtyAt state).length = flags.length := by
    simp [readWireWord, flags, gateWord]
  have hfinalDirty : readWireWord labels dirtyAt after =
      readWireWord labels dirtyAt state := by
    rw [show readWireWord labels dirtyAt after =
        xorWords (readWireWord labels dirtyAt secondWritten)
          (gateWord (secondWritten control)
            (suffixZeroFlags
              (upperRangeBits (secondWritten control) boundary labels bitAt secondWritten))) by
      exact upperZeroMapUnitary_correct k K boundary hkK hboundary tree control
        rangeAccumulator temporary path bitAt dirtyAt secondWritten hlayout.toZeroMapLayout
        (by simpa only [labels] using hlabels) hsecondRoute hsecondCleanPath hsecondRange
        hsecondTemporary,
      hsecondDirty, hsecondBits, hsecondControl,
      xorWords_right_cancel _ _ hflagsLength]
  have hfinalClean : Clean (path ++ [rangeAccumulator, temporary]) after :=
    upperZeroMapUnitary_clean k K boundary hkK hboundary tree control rangeAccumulator
      temporary path bitAt dirtyAt secondWritten hlayout.toZeroMapLayout
      (by simpa only [labels] using hlabels) hsecondRoute hsecondCleanPath hsecondRange
      hsecondTemporary
  change readWireWord labels dirtyAt
      (run (highestPositionXorWrite k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) state) = readWireWord labels dirtyAt state ∧
    Clean (path ++ [rangeAccumulator, temporary])
      (run (highestPositionXorWrite k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) state)
  rw [highestPositionXorWrite]
  simp only [Classical.run_append]
  exact ⟨hfinalDirty, hfinalClean⟩

/-- The literal lower writer has the source seed followed by the prefix-zero-selected
right-length telescoping constants. -/
theorem rightLengthXorWrite_word
    (n k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    wireValues targets
        (run (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) state) =
      constantWriteWord (rightLengthWriteValue n targets.length K)
        (zeroMapLabels k K)
        (gateWord (state control)
          (prefixZeroFlags
            (lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt state)))
        (gatedXorConstantBits (state control) (wireValues targets state)
          (truncateConstant targets.length (n + 3 - k))) := by
  let labels := zeroMapLabels k K
  let seedValue := truncateConstant targets.length (n + 3 - k)
  let valueAt := rightLengthWriteValue n targets.length K
  let map := lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt
  let seed := controlledXorConstant control targets seedValue
  let writes := dirtyConstantWrites targets dirtyAt valueAt labels
  let seeded := run seed state
  let firstWritten := run writes seeded
  let firstMapped := run map firstWritten
  let secondWritten := run writes firstMapped
  let flags := gateWord (state control)
    (prefixZeroFlags
      (lowerRangeBits (state control) boundary labels bitAt state))
  have hcontrolTargets : ∀ target ∈ targets, control ≠ target := by
    intro target htarget equality
    subst target
    exact hlayout.control_not_target htarget
  have hdirtyTargets : ∀ label, label ∈ labels → dirtyAt label ∉ targets := by
    intro label hlabel
    exact hlayout.dirty_not_target (by simpa only [labels] using hlabel)
  have hseedOutside : ∀ wire, wire ∉ targets → seeded wire = state wire := by
    intro wire hwire
    exact controlledXorConstant_preservesOutside control targets seedValue state wire hwire
  have hfirstOutside : ∀ wire, wire ∉ targets → firstWritten wire = state wire := by
    intro wire hwire
    calc
      firstWritten wire = seeded wire := by
        exact dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels
          seeded wire hwire
      _ = state wire := hseedOutside wire hwire
  have hfirstCleanPath : Clean path firstWritten := by
    intro wire hwire
    rw [hfirstOutside wire]
    · exact hcleanPath wire hwire
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hwire])
  have hfirstRange : firstWritten rangeAccumulator = false := by
    rw [hfirstOutside rangeAccumulator]
    · exact hcleanRange
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstTemporary : firstWritten temporary = false := by
    rw [hfirstOutside temporary]
    · exact hcleanTemporary
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstRoute : tree.routeLabel firstWritten = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstOutside wire (hlayout.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hwire]))
  have hfirstControl : firstWritten control = state control := by
    exact hfirstOutside control hlayout.control_not_target
  have hfirstBits :
      lowerRangeBits (firstWritten control) boundary labels bitAt firstWritten =
        lowerRangeBits (state control) boundary labels bitAt state := by
    unfold lowerRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hfirstControl]
    have hlabel' : label ∈ zeroMapLabels k K := by
      simpa only [labels] using hlabel
    have hbitNotTarget : bitAt label ∉ targets :=
      hlayout.mapWire_not_target (by
        simp only [zeroMapWires, List.mem_append, List.mem_cons, List.mem_map]
        aesop)
    rw [hfirstOutside (bitAt label) hbitNotTarget]
  have hseedWord :
      wireValues targets seeded =
        gatedXorConstantBits (state control) (wireValues targets state) seedValue := by
    rw [show seeded = xorConstantState (state control) targets seedValue state by
      exact run_controlledXorConstant control targets seedValue state hcontrolTargets]
    exact wireValues_xorConstantState (state control) targets seedValue state
      hlayout.targetNodup
  have hseedDirty : readWireWord labels dirtyAt seeded =
      readWireWord labels dirtyAt state := by
    apply readWireWord_congr
    intro label hlabel
    exact hseedOutside (dirtyAt label) (hdirtyTargets label hlabel)
  have hfirstTarget :
      wireValues targets firstWritten =
        constantWriteWord valueAt labels
          (readWireWord labels dirtyAt state)
          (gatedXorConstantBits (state control) (wireValues targets state) seedValue) := by
    rw [show wireValues targets firstWritten =
        constantWriteWord valueAt labels
          (readWireWord labels dirtyAt seeded) (wireValues targets seeded) by
      exact run_dirtyConstantWrites_word targets dirtyAt valueAt labels seeded
        hlayout.targetNodup hdirtyTargets,
      hseedDirty, hseedWord]
  have hfirstDirty : readWireWord labels dirtyAt firstWritten =
      readWireWord labels dirtyAt state := by
    apply readWireWord_congr
    intro label hlabel
    exact hfirstOutside (dirtyAt label) (hdirtyTargets label hlabel)
  have hmapDirty : readWireWord labels dirtyAt firstMapped =
      xorWords (readWireWord labels dirtyAt state) flags := by
    rw [show readWireWord labels dirtyAt firstMapped =
        xorWords (readWireWord labels dirtyAt firstWritten)
          (gateWord (firstWritten control)
            (prefixZeroFlags
              (lowerRangeBits (firstWritten control) boundary labels bitAt firstWritten))) by
      exact lowerZeroMapUnitary_correct k K boundary hkK hboundary tree control
        rangeAccumulator temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout
        (by simpa only [labels] using hlabels) hfirstRoute hfirstCleanPath hfirstRange
        hfirstTemporary,
      hfirstDirty, hfirstBits, hfirstControl]
  have hmapTarget : wireValues targets firstMapped = wireValues targets firstWritten := by
    exact hlayout.lowerMap_preserves_targets hkK firstWritten hfirstCleanPath hfirstTemporary
  have hmapClean : Clean (path ++ [rangeAccumulator, temporary]) firstMapped := by
    exact lowerZeroMapUnitary_clean k K boundary hkK hboundary tree control rangeAccumulator
      temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout
      (by simpa only [labels] using hlabels) hfirstRoute hfirstCleanPath hfirstRange
      hfirstTemporary
  have hflagsLength : (readWireWord labels dirtyAt state).length = flags.length := by
    simp [readWireWord, flags, gateWord]
  have hsecondTarget : wireValues targets secondWritten =
      constantWriteWord valueAt labels flags
        (gatedXorConstantBits (state control) (wireValues targets state) seedValue) := by
    rw [show wireValues targets secondWritten =
        constantWriteWord valueAt labels
          (readWireWord labels dirtyAt firstMapped)
          (wireValues targets firstMapped) by
      exact run_dirtyConstantWrites_word targets dirtyAt valueAt labels firstMapped
        hlayout.targetNodup hdirtyTargets,
      hmapDirty, hmapTarget, hfirstTarget,
      constantWriteWord_pair labels
        (readWireWord labels dirtyAt state)
        (xorWords (readWireWord labels dirtyAt state) flags)
        valueAt
        (gatedXorConstantBits (state control) (wireValues targets state) seedValue)]
    · rw [xorWords_left_cancel _ _ hflagsLength]
    · simp [readWireWord]
    · calc
        (xorWords (readWireWord labels dirtyAt state) flags).length =
            (readWireWord labels dirtyAt state).length :=
          xorWords_length _ _ hflagsLength
        _ = labels.length := by simp [readWireWord]
  have hsecondCleanPath : Clean path secondWritten := by
    intro wire hwire
    change run (dirtyConstantWrites targets dirtyAt valueAt labels)
      firstMapped wire = false
    rw [dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels
      firstMapped wire]
    · exact hmapClean wire (by simp [hwire])
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hwire])
  have hsecondTemporary : secondWritten temporary = false := by
    change run (dirtyConstantWrites targets dirtyAt valueAt labels)
      firstMapped temporary = false
    rw [dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels
      firstMapped temporary]
    · exact hmapClean temporary (by simp)
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  rw [rightLengthXorWrite]
  simp only [Classical.run_append]
  change wireValues targets (run map secondWritten) = _
  rw [hlayout.lowerMap_preserves_targets hkK secondWritten hsecondCleanPath
    hsecondTemporary, hsecondTarget]

theorem rightLengthXorWrite_wordAction
    (n k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    wireValues targets
        (run (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) state) =
      rightLengthWordAction n targets.length k K (state control)
        (lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt state)
        (wireValues targets state) := by
  exact rightLengthXorWrite_word n k K boundary hkK hboundary tree control
    rangeAccumulator temporary path bitAt dirtyAt targets state hlayout hlabels hroute
    hcleanPath hcleanRange hcleanTemporary

/-- Lower-writer restoration of the arbitrary dirty bank and all decoder/recurrence scratch. -/
theorem rightLengthXorWrite_restores
    (n k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    let after := run
      (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) state
    readWireWord (zeroMapLabels k K) dirtyAt after =
        readWireWord (zeroMapLabels k K) dirtyAt state ∧
      Clean (path ++ [rangeAccumulator, temporary]) after := by
  let labels := zeroMapLabels k K
  let seedValue := truncateConstant targets.length (n + 3 - k)
  let valueAt := rightLengthWriteValue n targets.length K
  let map := lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt
  let seed := controlledXorConstant control targets seedValue
  let writes := dirtyConstantWrites targets dirtyAt valueAt labels
  let seeded := run seed state
  let firstWritten := run writes seeded
  let firstMapped := run map firstWritten
  let secondWritten := run writes firstMapped
  let after := run map secondWritten
  let flags := gateWord (state control)
    (prefixZeroFlags
      (lowerRangeBits (state control) boundary labels bitAt state))
  have hdirtyTargets : ∀ label, label ∈ labels → dirtyAt label ∉ targets := by
    intro label hlabel
    exact hlayout.dirty_not_target (by simpa only [labels] using hlabel)
  have hseedOutside : ∀ wire, wire ∉ targets → seeded wire = state wire := by
    intro wire hwire
    exact controlledXorConstant_preservesOutside control targets seedValue state wire hwire
  have hfirstOutside : ∀ wire, wire ∉ targets → firstWritten wire = state wire := by
    intro wire hwire
    calc
      firstWritten wire = seeded wire :=
        dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels seeded wire hwire
      _ = state wire := hseedOutside wire hwire
  have hfirstCleanPath : Clean path firstWritten := by
    intro wire hwire
    rw [hfirstOutside wire]
    · exact hcleanPath wire hwire
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hwire])
  have hfirstRange : firstWritten rangeAccumulator = false := by
    rw [hfirstOutside rangeAccumulator]
    · exact hcleanRange
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstTemporary : firstWritten temporary = false := by
    rw [hfirstOutside temporary]
    · exact hcleanTemporary
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstRoute : tree.routeLabel firstWritten = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstOutside wire (hlayout.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hwire]))
  have hfirstControl : firstWritten control = state control :=
    hfirstOutside control hlayout.control_not_target
  have hfirstBits :
      lowerRangeBits (firstWritten control) boundary labels bitAt firstWritten =
        lowerRangeBits (state control) boundary labels bitAt state := by
    unfold lowerRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hfirstControl]
    have hlabel' : label ∈ zeroMapLabels k K := by
      simpa only [labels] using hlabel
    rw [hfirstOutside (bitAt label) (hlayout.mapWire_not_target (by
      simp only [zeroMapWires, List.mem_append, List.mem_cons, List.mem_map]
      aesop))]
  have hfirstDirty : readWireWord labels dirtyAt firstWritten =
      readWireWord labels dirtyAt state := by
    apply readWireWord_congr
    intro label hlabel
    exact hfirstOutside (dirtyAt label) (hdirtyTargets label hlabel)
  have hmapDirty : readWireWord labels dirtyAt firstMapped =
      xorWords (readWireWord labels dirtyAt state) flags := by
    rw [show readWireWord labels dirtyAt firstMapped =
        xorWords (readWireWord labels dirtyAt firstWritten)
          (gateWord (firstWritten control)
            (prefixZeroFlags
              (lowerRangeBits (firstWritten control) boundary labels bitAt firstWritten))) by
      exact lowerZeroMapUnitary_correct k K boundary hkK hboundary tree control
        rangeAccumulator temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout
        (by simpa only [labels] using hlabels) hfirstRoute hfirstCleanPath hfirstRange
        hfirstTemporary,
      hfirstDirty, hfirstBits, hfirstControl]
  have hmapClean : Clean (path ++ [rangeAccumulator, temporary]) firstMapped :=
    lowerZeroMapUnitary_clean k K boundary hkK hboundary tree control rangeAccumulator
      temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout
      (by simpa only [labels] using hlabels) hfirstRoute hfirstCleanPath hfirstRange
      hfirstTemporary
  have hmapRoute : tree.routeLabel firstMapped = boundary := by
    rw [← hfirstRoute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hlayout.lowerMap_preserves_protected hkK firstWritten hfirstCleanPath
      hfirstTemporary (by simp [zeroMapProtectedWires, hwire])
  have hmapControl : firstMapped control = state control := by
    calc
      firstMapped control = firstWritten control := by
        change run
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
            firstWritten control = firstWritten control
        exact hlayout.lowerMap_preserves_protected (wire := control) hkK firstWritten
          hfirstCleanPath hfirstTemporary (by simp [zeroMapProtectedWires])
      _ = state control := hfirstControl
  have hsecondOutside : ∀ wire, wire ∉ targets → secondWritten wire = firstMapped wire := by
    intro wire hwire
    exact dirtyConstantWrites_preservesOutside targets dirtyAt valueAt labels
      firstMapped wire hwire
  have hsecondCleanPath : Clean path secondWritten := by
    intro wire hwire
    rw [hsecondOutside wire]
    · exact hmapClean wire (by simp [hwire])
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hwire])
  have hsecondRange : secondWritten rangeAccumulator = false := by
    rw [hsecondOutside rangeAccumulator]
    · exact hmapClean rangeAccumulator (by simp)
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hsecondTemporary : secondWritten temporary = false := by
    rw [hsecondOutside temporary]
    · exact hmapClean temporary (by simp)
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hsecondRoute : tree.routeLabel secondWritten = boundary := by
    rw [← hmapRoute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hsecondOutside wire (hlayout.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hwire]))
  have hsecondControl : secondWritten control = state control := by
    rw [hsecondOutside control hlayout.control_not_target, hmapControl]
  have hsecondBits :
      lowerRangeBits (secondWritten control) boundary labels bitAt secondWritten =
        lowerRangeBits (state control) boundary labels bitAt state := by
    unfold lowerRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hsecondControl]
    have hlabel' : label ∈ zeroMapLabels k K := by
      simpa only [labels] using hlabel
    have hbitNotTarget : bitAt label ∉ targets :=
      hlayout.mapWire_not_target (by
        simp only [zeroMapWires, List.mem_append, List.mem_cons, List.mem_map]
        aesop)
    have hmapBit : firstMapped (bitAt label) = firstWritten (bitAt label) := by
      change run
        (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
          firstWritten (bitAt label) = firstWritten (bitAt label)
      exact hlayout.lowerMap_preserves_bit hkK hlabel' firstWritten hfirstCleanPath
        hfirstTemporary
    rw [hsecondOutside (bitAt label) hbitNotTarget, hmapBit,
      hfirstOutside (bitAt label) hbitNotTarget]
  have hsecondDirty : readWireWord labels dirtyAt secondWritten =
      xorWords (readWireWord labels dirtyAt state) flags := by
    rw [show readWireWord labels dirtyAt secondWritten =
        readWireWord labels dirtyAt firstMapped by
      apply readWireWord_congr
      intro label hlabel
      exact hsecondOutside (dirtyAt label) (hdirtyTargets label hlabel),
      hmapDirty]
  have hflagsLength : (readWireWord labels dirtyAt state).length = flags.length := by
    simp [readWireWord, flags, gateWord]
  have hfinalDirty : readWireWord labels dirtyAt after =
      readWireWord labels dirtyAt state := by
    rw [show readWireWord labels dirtyAt after =
        xorWords (readWireWord labels dirtyAt secondWritten)
          (gateWord (secondWritten control)
            (prefixZeroFlags
              (lowerRangeBits (secondWritten control) boundary labels bitAt secondWritten))) by
      exact lowerZeroMapUnitary_correct k K boundary hkK hboundary tree control
        rangeAccumulator temporary path bitAt dirtyAt secondWritten hlayout.toZeroMapLayout
        (by simpa only [labels] using hlabels) hsecondRoute hsecondCleanPath hsecondRange
        hsecondTemporary,
      hsecondDirty, hsecondBits, hsecondControl,
      xorWords_right_cancel _ _ hflagsLength]
  have hfinalClean : Clean (path ++ [rangeAccumulator, temporary]) after :=
    lowerZeroMapUnitary_clean k K boundary hkK hboundary tree control rangeAccumulator
      temporary path bitAt dirtyAt secondWritten hlayout.toZeroMapLayout
      (by simpa only [labels] using hlabels) hsecondRoute hsecondCleanPath hsecondRange
      hsecondTemporary
  change readWireWord labels dirtyAt
      (run (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) state) = readWireWord labels dirtyAt state ∧
    Clean (path ++ [rangeAccumulator, temporary])
      (run (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) state)
  rw [rightLengthXorWrite]
  simp only [Classical.run_append]
  exact ⟨hfinalDirty, hfinalClean⟩

/-- Every role outside the target and borrowed dirty bank is preserved by the upper writer.
The range accumulator is named separately because it is restored by the clean-scratch theorem. -/
theorem highestPositionXorWrite_preserves
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireTarget : wire ∉ targets)
    (hwireRange : wire ≠ rangeAccumulator)
    (hwireDirty : ∀ label ∈ zeroMapLabels k K, wire ≠ dirtyAt label) :
    run (highestPositionXorWrite k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets) state wire = state wire := by
  let map := upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt
  let seed := controlledXorConstant control targets
    (truncateConstant targets.length (K - 1))
  let writes := highestPositionDirtyWrites k K targets dirtyAt
  let seeded := run seed state
  let firstWritten := run writes seeded
  let firstMapped := run map firstWritten
  let secondWritten := run writes firstMapped
  have hseedWire : seeded wire = state wire :=
    controlledXorConstant_preservesOutside control targets _ state wire hwireTarget
  have hfirstWire : firstWritten wire = state wire := by
    calc
      firstWritten wire = seeded wire := by
        exact dirtyConstantWrites_preservesOutside targets dirtyAt _
          (zeroMapLabels k K).reverse seeded wire hwireTarget
      _ = state wire := hseedWire
  have hfirstOutside : ∀ next, next ∉ targets → firstWritten next = state next := by
    intro next hnext
    calc
      firstWritten next = seeded next := by
        exact dirtyConstantWrites_preservesOutside targets dirtyAt _
          (zeroMapLabels k K).reverse seeded next hnext
      _ = state next := controlledXorConstant_preservesOutside control targets _
        state next hnext
  have hfirstCleanPath : Clean path firstWritten := by
    intro next hnext
    rw [hfirstOutside next]
    · exact hcleanPath next hnext
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hnext])
  have hfirstRange : firstWritten rangeAccumulator = false := by
    rw [hfirstOutside rangeAccumulator]
    · exact hcleanRange
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstTemporary : firstWritten temporary = false := by
    rw [hfirstOutside temporary]
    · exact hcleanTemporary
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstRoute : tree.routeLabel firstWritten = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro next hnext
    exact hfirstOutside next (hlayout.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hnext]))
  have hmapWire : firstMapped wire = state wire := by
    calc
      firstMapped wire = firstWritten wire := by
        change run
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
            firstWritten wire = firstWritten wire
        exact upperZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
          path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout hfirstCleanPath
          hfirstTemporary wire hwireRange hwireDirty
      _ = state wire := hfirstWire
  have hmapClean : Clean (path ++ [rangeAccumulator, temporary]) firstMapped :=
    upperZeroMapUnitary_clean k K boundary hkK hboundary tree control rangeAccumulator
      temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout hlabels hfirstRoute
      hfirstCleanPath hfirstRange hfirstTemporary
  have hsecondWire : secondWritten wire = state wire := by
    calc
      secondWritten wire = firstMapped wire := by
        exact dirtyConstantWrites_preservesOutside targets dirtyAt _
          (zeroMapLabels k K).reverse firstMapped wire hwireTarget
      _ = state wire := hmapWire
  have hsecondCleanPath : Clean path secondWritten := by
    intro next hnext
    change run (dirtyConstantWrites targets dirtyAt _ (zeroMapLabels k K).reverse)
      firstMapped next = false
    rw [dirtyConstantWrites_preservesOutside targets dirtyAt _
      (zeroMapLabels k K).reverse firstMapped next]
    · exact hmapClean next (by simp [hnext])
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hnext])
  have hsecondTemporary : secondWritten temporary = false := by
    change run (dirtyConstantWrites targets dirtyAt _ (zeroMapLabels k K).reverse)
      firstMapped temporary = false
    rw [dirtyConstantWrites_preservesOutside targets dirtyAt _
      (zeroMapLabels k K).reverse firstMapped temporary]
    · exact hmapClean temporary (by simp)
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  rw [highestPositionXorWrite]
  simp only [Classical.run_append]
  change run map secondWritten wire = state wire
  rw [show run map secondWritten wire = secondWritten wire by
    change run
      (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
        secondWritten wire = secondWritten wire
    exact upperZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt secondWritten hlayout.toZeroMapLayout hsecondCleanPath
      hsecondTemporary wire hwireRange hwireDirty,
    hsecondWire]

/-- Lower-writer mirror of `highestPositionXorWrite_preserves`. -/
theorem rightLengthXorWrite_preserves
    (n k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireTarget : wire ∉ targets)
    (hwireRange : wire ≠ rangeAccumulator)
    (hwireDirty : ∀ label ∈ zeroMapLabels k K, wire ≠ dirtyAt label) :
    run (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets) state wire = state wire := by
  let map := lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt
  let seed := controlledXorConstant control targets
    (truncateConstant targets.length (n + 3 - k))
  let writes := rightLengthDirtyWrites n k K targets dirtyAt
  let seeded := run seed state
  let firstWritten := run writes seeded
  let firstMapped := run map firstWritten
  let secondWritten := run writes firstMapped
  have hseedWire : seeded wire = state wire :=
    controlledXorConstant_preservesOutside control targets _ state wire hwireTarget
  have hfirstWire : firstWritten wire = state wire := by
    calc
      firstWritten wire = seeded wire := by
        exact dirtyConstantWrites_preservesOutside targets dirtyAt _
          (zeroMapLabels k K) seeded wire hwireTarget
      _ = state wire := hseedWire
  have hfirstOutside : ∀ next, next ∉ targets → firstWritten next = state next := by
    intro next hnext
    calc
      firstWritten next = seeded next := by
        exact dirtyConstantWrites_preservesOutside targets dirtyAt _
          (zeroMapLabels k K) seeded next hnext
      _ = state next := controlledXorConstant_preservesOutside control targets _
        state next hnext
  have hfirstCleanPath : Clean path firstWritten := by
    intro next hnext
    rw [hfirstOutside next]
    · exact hcleanPath next hnext
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hnext])
  have hfirstRange : firstWritten rangeAccumulator = false := by
    rw [hfirstOutside rangeAccumulator]
    · exact hcleanRange
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstTemporary : firstWritten temporary = false := by
    rw [hfirstOutside temporary]
    · exact hcleanTemporary
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  have hfirstRoute : tree.routeLabel firstWritten = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro next hnext
    exact hfirstOutside next (hlayout.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hnext]))
  have hmapWire : firstMapped wire = state wire := by
    calc
      firstMapped wire = firstWritten wire := by
        change run
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
            firstWritten wire = firstWritten wire
        exact lowerZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
          path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout hfirstCleanPath
          hfirstTemporary wire hwireRange hwireDirty
      _ = state wire := hfirstWire
  have hmapClean : Clean (path ++ [rangeAccumulator, temporary]) firstMapped :=
    lowerZeroMapUnitary_clean k K boundary hkK hboundary tree control rangeAccumulator
      temporary path bitAt dirtyAt firstWritten hlayout.toZeroMapLayout hlabels hfirstRoute
      hfirstCleanPath hfirstRange hfirstTemporary
  have hsecondWire : secondWritten wire = state wire := by
    calc
      secondWritten wire = firstMapped wire := by
        exact dirtyConstantWrites_preservesOutside targets dirtyAt _
          (zeroMapLabels k K) firstMapped wire hwireTarget
      _ = state wire := hmapWire
  have hsecondCleanPath : Clean path secondWritten := by
    intro next hnext
    change run (dirtyConstantWrites targets dirtyAt _ (zeroMapLabels k K))
      firstMapped next = false
    rw [dirtyConstantWrites_preservesOutside targets dirtyAt _
      (zeroMapLabels k K) firstMapped next]
    · exact hmapClean next (by simp [hnext])
    · exact hlayout.mapWire_not_target (by
        simp [zeroMapWires, zeroMapProtectedWires, hnext])
  have hsecondTemporary : secondWritten temporary = false := by
    change run (dirtyConstantWrites targets dirtyAt _ (zeroMapLabels k K))
      firstMapped temporary = false
    rw [dirtyConstantWrites_preservesOutside targets dirtyAt _
      (zeroMapLabels k K) firstMapped temporary]
    · exact hmapClean temporary (by simp)
    · exact hlayout.mapWire_not_target (by simp [zeroMapWires])
  rw [rightLengthXorWrite]
  simp only [Classical.run_append]
  change run map secondWritten wire = state wire
  rw [show run map secondWritten wire = secondWritten wire by
    change run
      (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
        secondWritten wire = secondWritten wire
    exact lowerZeroMapUnitary_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt secondWritten hlayout.toZeroMapLayout hsecondCleanPath
      hsecondTemporary wire hwireRange hwireDirty,
    hsecondWire]

/-- The complete upper writer restores every basis wire outside its target word, including its
borrowed dirty bank and clean range accumulator. -/
theorem highestPositionXorWrite_preservesOutsideTarget
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireTarget : wire ∉ targets) :
    run (highestPositionXorWrite k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets) state wire = state wire := by
  have hrestores := highestPositionXorWrite_restores k K boundary hkK hboundary
    tree control rangeAccumulator temporary path bitAt dirtyAt targets state hlayout
    hlabels hroute hcleanPath hcleanRange hcleanTemporary
  by_cases hwireRange : wire = rangeAccumulator
  · subst wire
    rw [hrestores.2 rangeAccumulator (by simp), hcleanRange]
  · by_cases hwireDirty : ∃ label ∈ zeroMapLabels k K, wire = dirtyAt label
    · obtain ⟨label, hlabel, rfl⟩ := hwireDirty
      exact readWireWord_eq_at (zeroMapLabels k K) dirtyAt _ _ hrestores.1
        label hlabel
    · exact highestPositionXorWrite_preserves k K boundary hkK hboundary tree
        control rangeAccumulator temporary path bitAt dirtyAt targets state hlayout
        hlabels hroute hcleanPath hcleanRange hcleanTemporary wire hwireTarget
        hwireRange (by
          intro label hlabel equality
          exact hwireDirty ⟨label, hlabel, equality⟩)

/-- The complete lower writer likewise restores every basis wire outside its target word. -/
theorem rightLengthXorWrite_preservesOutsideTarget
    (n k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (state : BasisState)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireTarget : wire ∉ targets) :
    run (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets) state wire = state wire := by
  have hrestores := rightLengthXorWrite_restores n k K boundary hkK hboundary
    tree control rangeAccumulator temporary path bitAt dirtyAt targets state hlayout
    hlabels hroute hcleanPath hcleanRange hcleanTemporary
  by_cases hwireRange : wire = rangeAccumulator
  · subst wire
    rw [hrestores.2 rangeAccumulator (by simp), hcleanRange]
  · by_cases hwireDirty : ∃ label ∈ zeroMapLabels k K, wire = dirtyAt label
    · obtain ⟨label, hlabel, rfl⟩ := hwireDirty
      exact readWireWord_eq_at (zeroMapLabels k K) dirtyAt _ _ hrestores.1
        label hlabel
    · exact rightLengthXorWrite_preserves n k K boundary hkK hboundary tree
        control rangeAccumulator temporary path bitAt dirtyAt targets state hlayout
        hlabels hroute hcleanPath hcleanRange hcleanTemporary wire hwireTarget
        hwireRange (by
          intro label hlabel equality
          exact hwireDirty ⟨label, hlabel, equality⟩)

/-! ## Grouped-writer structural and resource contracts -/

/-- Both grouped writers use one target word and one complete zero-map footprint. -/
def lengthWriterSupport
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) : List Wire :=
  targets ++ zeroMapWires k K tree control rangeAccumulator temporary path bitAt dirtyAt

theorem highestPositionXorWrite_usesOnly
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    PaperCircuitUsesOnly
      (lengthWriterSupport k K tree control rangeAccumulator temporary path bitAt dirtyAt targets)
      (highestPositionXorWrite k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) := by
  have hseed : PaperCircuitUsesOnly
      (lengthWriterSupport k K tree control rangeAccumulator temporary path bitAt dirtyAt targets)
      (controlledXorConstant control targets
        (truncateConstant targets.length (K - 1))) := by
    apply (controlledXorConstant_usesOnly control targets _).mono
    intro wire hwire
    simp only [lengthWriterSupport, List.mem_cons, List.mem_append] at hwire ⊢
    rcases hwire with rfl | hwire
    · right
      simp [zeroMapWires, zeroMapProtectedWires]
    · exact Or.inl hwire
  have hwrites : PaperCircuitUsesOnly
      (lengthWriterSupport k K tree control rangeAccumulator temporary path bitAt dirtyAt targets)
      (highestPositionDirtyWrites k K targets dirtyAt) := by
    unfold highestPositionDirtyWrites
    apply (dirtyConstantWrites_usesOnly targets dirtyAt _
      (zeroMapLabels k K).reverse).mono
    intro wire hwire
    simp only [dirtyConstantWritesSupport, lengthWriterSupport,
      List.mem_append, List.mem_map, List.mem_reverse] at hwire ⊢
    rcases hwire with hwire | ⟨label, hlabel, rfl⟩
    · exact Or.inl hwire
    · right
      simp only [zeroMapWires, List.mem_append, List.mem_cons, List.mem_map]
      aesop
  have hmap : PaperCircuitUsesOnly
      (lengthWriterSupport k K tree control rangeAccumulator temporary path bitAt dirtyAt targets)
      (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
    apply (upperZeroMapUnitary_usesOnly k K hkK tree control rangeAccumulator temporary path
      bitAt dirtyAt).mono
    exact fun wire hwire ↦ List.mem_append_right targets hwire
  rw [highestPositionXorWrite]
  exact PaperCircuitUsesOnly.append
    (PaperCircuitUsesOnly.append
      (PaperCircuitUsesOnly.append
        (PaperCircuitUsesOnly.append hseed hwrites) hmap) hwrites) hmap

theorem rightLengthXorWrite_usesOnly
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    PaperCircuitUsesOnly
      (lengthWriterSupport k K tree control rangeAccumulator temporary path bitAt dirtyAt targets)
      (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) := by
  have hseed : PaperCircuitUsesOnly
      (lengthWriterSupport k K tree control rangeAccumulator temporary path bitAt dirtyAt targets)
      (controlledXorConstant control targets
        (truncateConstant targets.length (n + 3 - k))) := by
    apply (controlledXorConstant_usesOnly control targets _).mono
    intro wire hwire
    simp only [lengthWriterSupport, List.mem_cons, List.mem_append] at hwire ⊢
    rcases hwire with rfl | hwire
    · right
      simp [zeroMapWires, zeroMapProtectedWires]
    · exact Or.inl hwire
  have hwrites : PaperCircuitUsesOnly
      (lengthWriterSupport k K tree control rangeAccumulator temporary path bitAt dirtyAt targets)
      (rightLengthDirtyWrites n k K targets dirtyAt) := by
    unfold rightLengthDirtyWrites
    apply (dirtyConstantWrites_usesOnly targets dirtyAt _ (zeroMapLabels k K)).mono
    intro wire hwire
    simp only [dirtyConstantWritesSupport, lengthWriterSupport,
      List.mem_append, List.mem_map] at hwire ⊢
    rcases hwire with hwire | ⟨label, hlabel, rfl⟩
    · exact Or.inl hwire
    · right
      simp only [zeroMapWires, List.mem_append, List.mem_cons, List.mem_map]
      aesop
  have hmap : PaperCircuitUsesOnly
      (lengthWriterSupport k K tree control rangeAccumulator temporary path bitAt dirtyAt targets)
      (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
    apply (lowerZeroMapUnitary_usesOnly k K hkK tree control rangeAccumulator temporary path
      bitAt dirtyAt).mono
    exact fun wire hwire ↦ List.mem_append_right targets hwire
  rw [rightLengthXorWrite]
  exact PaperCircuitUsesOnly.append
    (PaperCircuitUsesOnly.append
      (PaperCircuitUsesOnly.append
        (PaperCircuitUsesOnly.append hseed hwrites) hmap) hwrites) hmap

@[simp]
theorem highestPositionXorWrite_HPFree
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    HPFree (highestPositionXorWrite k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets) := by
  simp [highestPositionXorWrite, highestPositionDirtyWrites]

@[simp]
theorem rightLengthXorWrite_HPFree
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    HPFree (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets) := by
  simp [rightLengthXorWrite, rightLengthDirtyWrites]

theorem highestPositionXorWrite_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets) :
    CircuitWellFormed
      (highestPositionXorWrite k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) := by
  have hseed := controlledXorConstant_wellFormed control targets
    (truncateConstant targets.length (K - 1)) (by
      intro target htarget equality
      subst target
      exact hlayout.control_not_target htarget)
  have hwrites : CircuitWellFormed (highestPositionDirtyWrites k K targets dirtyAt) := by
    unfold highestPositionDirtyWrites
    apply dirtyConstantWrites_wellFormed
    intro label hlabel target htarget equality
    subst target
    exact hlayout.dirty_not_target (by simpa using hlabel) htarget
  have hmap := upperZeroMapUnitary_wellFormed k K hkK tree control rangeAccumulator
    temporary path bitAt dirtyAt hlayout.toZeroMapLayout
  simp only [highestPositionXorWrite, circuitWellFormed_append]
  exact ⟨⟨⟨⟨hseed, hwrites⟩, hmap⟩, hwrites⟩, hmap⟩

theorem rightLengthXorWrite_wellFormed
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire)
    (hlayout : LengthWriterLayout k K tree control rangeAccumulator temporary path
      bitAt dirtyAt targets) :
    CircuitWellFormed
      (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
        bitAt dirtyAt targets) := by
  have hseed := controlledXorConstant_wellFormed control targets
    (truncateConstant targets.length (n + 3 - k)) (by
      intro target htarget equality
      subst target
      exact hlayout.control_not_target htarget)
  have hwrites : CircuitWellFormed (rightLengthDirtyWrites n k K targets dirtyAt) := by
    unfold rightLengthDirtyWrites
    apply dirtyConstantWrites_wellFormed
    intro label hlabel target htarget equality
    subst target
    exact hlayout.dirty_not_target hlabel htarget
  have hmap := lowerZeroMapUnitary_wellFormed k K hkK tree control rangeAccumulator
    temporary path bitAt dirtyAt hlayout.toZeroMapLayout
  simp only [rightLengthXorWrite, circuitWellFormed_append]
  exact ⟨⟨⟨⟨hseed, hwrites⟩, hmap⟩, hwrites⟩, hmap⟩

theorem highestPositionXorWrite_toffoliCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    eeaToffoliCount
        (highestPositionXorWrite k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) =
      2 * eeaToffoliCount
        (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  simp [highestPositionXorWrite, highestPositionDirtyWrites,
    eeaToffoliCount_append]
  omega

theorem highestPositionXorWrite_cnotCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    eeaCnotCount
        (highestPositionXorWrite k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) =
      lowBitCount targets.length (truncateConstant targets.length (K - 1)) +
        2 * ((zeroMapLabels k K).reverse.map fun label ↦
          lowBitCount targets.length (highestPositionWriteValue targets.length k label)).sum +
        2 * eeaCnotCount
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  simp only [highestPositionXorWrite, eeaCnotCount_append,
    controlledXorConstant_cnotCount, highestPositionDirtyWrites,
    dirtyConstantWrites_cnotCount]
  omega

theorem highestPositionXorWrite_tCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    ShorECDLP.tCount
        (highestPositionXorWrite k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) =
      2 * ShorECDLP.tCount
        (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  simp [highestPositionXorWrite, highestPositionDirtyWrites, tCount_append]
  omega

theorem rightLengthXorWrite_toffoliCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    eeaToffoliCount
        (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) =
      2 * eeaToffoliCount
        (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  simp [rightLengthXorWrite, rightLengthDirtyWrites, eeaToffoliCount_append]
  omega

theorem rightLengthXorWrite_cnotCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    eeaCnotCount
        (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) =
      lowBitCount targets.length (truncateConstant targets.length (n + 3 - k)) +
        2 * ((zeroMapLabels k K).map fun label ↦
          lowBitCount targets.length (rightLengthWriteValue n targets.length K label)).sum +
        2 * eeaCnotCount
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  simp only [rightLengthXorWrite, eeaCnotCount_append,
    controlledXorConstant_cnotCount, rightLengthDirtyWrites,
    dirtyConstantWrites_cnotCount]
  omega

theorem rightLengthXorWrite_tCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    ShorECDLP.tCount
        (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) =
      2 * ShorECDLP.tCount
        (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  simp [rightLengthXorWrite, rightLengthDirtyWrites, tCount_append]
  omega

/-! ## Complete source length-update blocks -/

/-- Common physical footprint of the two grouped writers.  Swapping `work1At` and `work2At`
only swaps the order of the two bank lists and does not change this named support. -/
def lengthBlockWriterSupport
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire) (target : List Wire) : List Wire :=
  target ++ zeroMapProtectedWires tree control path ++
    rangeAccumulator :: temporary ::
      (zeroMapLabels k K).map work1At ++ (zeroMapLabels k K).map work2At

/-- Shared physical allocation certificate for either complete length block. -/
structure LengthBlockLayout
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (affineRegister target constants : List Wire) : Prop where
  affine : ConstantLayout affineRegister constants carry
  work1Bits : LengthWriterLayout k K tree control rangeAccumulator temporary path
    work1At work2At target
  work2Bits : LengthWriterLayout k K tree control rangeAccumulator temporary path
    work2At work1At target
  affineDisjoint : List.Disjoint (constants ++ affineRegister ++ [carry])
    (lengthBlockWriterSupport k K tree control rangeAccumulator temporary path
      work1At work2At target)

private theorem LengthBlockLayout.writer_not_affineRegister
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary carry : Wire} {path : List Wire}
    {work1At work2At : Nat → Wire} {affineRegister target constants : List Wire}
    (hlayout : LengthBlockLayout k K tree control rangeAccumulator temporary carry path
      work1At work2At affineRegister target constants)
    {wire : Wire}
    (hwire : wire ∈ lengthBlockWriterSupport k K tree control rangeAccumulator
      temporary path work1At work2At target) :
    wire ∉ affineRegister := by
  intro haffine
  have hleft : wire ∈ constants ++ affineRegister ++ [carry] := by
    simp [haffine]
  exact List.disjoint_left.mp hlayout.affineDisjoint hleft hwire

private theorem LengthBlockLayout.affine_not_target
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary carry : Wire} {path : List Wire}
    {work1At work2At : Nat → Wire} {affineRegister target constants : List Wire}
    (hlayout : LengthBlockLayout k K tree control rangeAccumulator temporary carry path
      work1At work2At affineRegister target constants)
    {wire : Wire} (hwire : wire ∈ affineRegister) :
    wire ∉ target := by
  intro htarget
  have hleft : wire ∈ constants ++ affineRegister ++ [carry] := by
    simp [hwire]
  have hright : wire ∈ lengthBlockWriterSupport k K tree control rangeAccumulator
      temporary path work1At work2At target := by
    simp only [lengthBlockWriterSupport, List.mem_append]
    exact Or.inl (Or.inl (Or.inl htarget))
  exact List.disjoint_left.mp hlayout.affineDisjoint hleft hright

private theorem LengthBlockLayout.constantCarry_not_target
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary carry : Wire} {path : List Wire}
    {work1At work2At : Nat → Wire} {affineRegister target constants : List Wire}
    (hlayout : LengthBlockLayout k K tree control rangeAccumulator temporary carry path
      work1At work2At affineRegister target constants)
    {wire : Wire} (hwire : wire ∈ constants ++ [carry]) :
    wire ∉ target := by
  intro htarget
  have haffine : wire ∈ constants ++ affineRegister ++ [carry] := by
    simp only [List.mem_append, List.mem_singleton] at hwire ⊢
    rcases hwire with hconstant | hcarry
    · exact Or.inl (Or.inl hconstant)
    · exact Or.inr hcarry
  have hright : wire ∈ lengthBlockWriterSupport k K tree control rangeAccumulator
      temporary path work1At work2At target := by
    simp only [lengthBlockWriterSupport, List.mem_append]
    exact Or.inl (Or.inl (Or.inl htarget))
  exact List.disjoint_left.mp hlayout.affineDisjoint haffine hright

/-- Literal `len_update_lt_unary_gate`: reflect the right boundary, apply the two upper writers
with exchanged work banks, and reflect the boundary back. -/
def lenUpdateLtUnary
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) : Circuit :=
  constMinus lengthRP constants carry (n + 2) ++
    highestPositionXorWrite k K tree control rangeAccumulator temporary path
      work2At work1At lengthT ++
    highestPositionXorWrite k K tree control rangeAccumulator temporary path
      work1At work2At lengthT ++
    constMinus lengthRP constants carry (n + 2)

/-- Literal `len_update_lrp_unary_gate`: shift the left boundary, apply the two lower writers
with exchanged work banks, and undo the shift. -/
def lenUpdateLrpUnary
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) : Circuit :=
  addConstant lengthT constants carry 3 ++
    rightLengthXorWrite n k K tree control rangeAccumulator temporary path
      work1At work2At lengthRP ++
    rightLengthXorWrite n k K tree control rangeAccumulator temporary path
      work2At work1At lengthRP ++
    subConstant lengthT constants carry 3

/-- Direct whole-state semantics of the literal upper length block.  The target length receives
the two source writers in their emitted order; the reflected boundary, both borrowed banks, and
all scratch are restored. -/
theorem lenUpdateLtUnary_correct
    (n k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) (state : BasisState)
    (hpositive : 0 < lengthRP.length)
    (hlength : constants.length = lengthRP.length)
    (hlayout : LengthBlockLayout k K tree control rangeAccumulator temporary carry path
      work1At work2At lengthRP lengthT constants)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel
      (run (constMinus lengthRP constants carry (n + 2)) state) = boundary)
    (hcleanConstants : Clean (constants ++ [carry]) state)
    (hcleanPath : Clean path state)
    (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    let after := run
      (lenUpdateLtUnary n k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants) state
    wireValues lengthT after =
        highestPositionWordAction lengthT.length k K (state control)
          (upperRangeBits (state control) boundary (zeroMapLabels k K) work1At state)
          (highestPositionWordAction lengthT.length k K (state control)
            (upperRangeBits (state control) boundary (zeroMapLabels k K) work2At state)
            (wireValues lengthT state)) ∧
      wireValues lengthRP after = wireValues lengthRP state ∧
      Clean (constants ++ [carry]) after ∧
      Clean (path ++ [rangeAccumulator, temporary]) after ∧
      ∀ wire, wire ∉ lengthT → after wire = state wire := by
  let reflected := run (constMinus lengthRP constants carry (n + 2)) state
  have hreflect := constMinus_correct lengthRP constants carry (n + 2) state
    hpositive hlength hlayout.affine hcleanConstants
  let first := run
    (highestPositionXorWrite k K tree control rangeAccumulator temporary path
      work2At work1At lengthT) reflected
  let second := run
    (highestPositionXorWrite k K tree control rangeAccumulator temporary path
      work1At work2At lengthT) first
  let after := run (constMinus lengthRP constants carry (n + 2)) second
  have hreflectedSupport : ∀ wire,
      wire ∈ lengthBlockWriterSupport k K tree control rangeAccumulator temporary path
        work1At work2At lengthT → reflected wire = state wire := by
    intro wire hwire
    exact hreflect.2.2 wire (hlayout.writer_not_affineRegister hwire)
  have hreflectedPath : Clean path reflected := by
    intro wire hwire
    rw [hreflectedSupport wire (by
      simp [lengthBlockWriterSupport, zeroMapProtectedWires, hwire])]
    exact hcleanPath wire hwire
  have hreflectedRange : reflected rangeAccumulator = false := by
    rw [hreflectedSupport rangeAccumulator (by
      simp [lengthBlockWriterSupport]), hcleanRange]
  have hreflectedTemporary : reflected temporary = false := by
    rw [hreflectedSupport temporary (by
      simp [lengthBlockWriterSupport]), hcleanTemporary]
  have hfirstWord := highestPositionXorWrite_wordAction k K boundary hkK hboundary
    tree control rangeAccumulator temporary path work2At work1At lengthT reflected
    hlayout.work2Bits hlabels hroute hreflectedPath hreflectedRange hreflectedTemporary
  have hfirstRestores := highestPositionXorWrite_restores k K boundary hkK hboundary
    tree control rangeAccumulator temporary path work2At work1At lengthT reflected
    hlayout.work2Bits hlabels hroute hreflectedPath hreflectedRange hreflectedTemporary
  have hfirstOutside : ∀ wire, wire ∉ lengthT → first wire = reflected wire := by
    intro wire hwire
    exact highestPositionXorWrite_preservesOutsideTarget k K boundary hkK hboundary
      tree control rangeAccumulator temporary path work2At work1At lengthT reflected
      hlayout.work2Bits hlabels hroute hreflectedPath hreflectedRange hreflectedTemporary
      wire hwire
  have hfirstRoute : tree.routeLabel first = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstOutside wire (hlayout.work2Bits.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hwire]))
  have hfirstPath : Clean path first := by
    intro wire hwire
    exact hfirstRestores.2 wire (by simp [hwire])
  have hfirstRange : first rangeAccumulator = false :=
    hfirstRestores.2 rangeAccumulator (by simp)
  have hfirstTemporary : first temporary = false :=
    hfirstRestores.2 temporary (by simp)
  have hsecondWord := highestPositionXorWrite_wordAction k K boundary hkK hboundary
    tree control rangeAccumulator temporary path work1At work2At lengthT first
    hlayout.work1Bits hlabels hfirstRoute hfirstPath hfirstRange hfirstTemporary
  have hsecondRestores := highestPositionXorWrite_restores k K boundary hkK hboundary
    tree control rangeAccumulator temporary path work1At work2At lengthT first
    hlayout.work1Bits hlabels hfirstRoute hfirstPath hfirstRange hfirstTemporary
  have hsecondOutside : ∀ wire, wire ∉ lengthT → second wire = first wire := by
    intro wire hwire
    exact highestPositionXorWrite_preservesOutsideTarget k K boundary hkK hboundary
      tree control rangeAccumulator temporary path work1At work2At lengthT first
      hlayout.work1Bits hlabels hfirstRoute hfirstPath hfirstRange hfirstTemporary
      wire hwire
  have hconstantsFirst : Clean (constants ++ [carry]) first := by
    intro wire hwire
    rw [hfirstOutside wire (hlayout.constantCarry_not_target hwire)]
    exact hreflect.2.1 wire hwire
  have hconstantsSecond : Clean (constants ++ [carry]) second := by
    intro wire hwire
    rw [hsecondOutside wire (hlayout.constantCarry_not_target hwire)]
    exact hconstantsFirst wire hwire
  have hfinal := constMinus_correct lengthRP constants carry (n + 2) second
    hpositive hlength hlayout.affine hconstantsSecond
  have hreflectedControl : reflected control = state control :=
    hreflectedSupport control (by
      simp [lengthBlockWriterSupport, zeroMapProtectedWires])
  have hreflectedTarget : wireValues lengthT reflected = wireValues lengthT state := by
    apply wireValues_congr
    intro wire hwire
    exact hreflectedSupport wire (by
      simp [lengthBlockWriterSupport, hwire])
  have hreflectedWork2 :
      upperRangeBits (reflected control) boundary (zeroMapLabels k K) work2At reflected =
        upperRangeBits (state control) boundary (zeroMapLabels k K) work2At state := by
    unfold upperRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hreflectedControl]
    rw [hreflectedSupport (work2At label) (by
      simp only [lengthBlockWriterSupport, List.mem_append, List.mem_cons,
        List.mem_map]
      exact Or.inr ⟨label, hlabel, rfl⟩)]
  have hfirstControl : first control = state control := by
    rw [hfirstOutside control hlayout.work2Bits.control_not_target,
      hreflectedControl]
  have hfirstWork1 :
      upperRangeBits (first control) boundary (zeroMapLabels k K) work1At first =
        upperRangeBits (state control) boundary (zeroMapLabels k K) work1At state := by
    unfold upperRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hfirstControl]
    rw [hfirstOutside (work1At label)
      (hlayout.work2Bits.dirty_not_target hlabel)]
    rw [hreflectedSupport (work1At label) (by
      simp only [lengthBlockWriterSupport, List.mem_append, List.mem_cons,
        List.mem_map]
      exact Or.inl (Or.inr (Or.inr
        (Or.inr ⟨label, hlabel, rfl⟩))))]
  have hfirstTarget :
      wireValues lengthT first =
        highestPositionWordAction lengthT.length k K (state control)
          (upperRangeBits (state control) boundary (zeroMapLabels k K) work2At state)
          (wireValues lengthT state) := by
    rw [hfirstWord, hreflectedWork2, hreflectedControl, hreflectedTarget]
  have htargetSecond :
      wireValues lengthT second =
        highestPositionWordAction lengthT.length k K (state control)
          (upperRangeBits (state control) boundary (zeroMapLabels k K) work1At state)
          (highestPositionWordAction lengthT.length k K (state control)
            (upperRangeBits (state control) boundary (zeroMapLabels k K) work2At state)
            (wireValues lengthT state)) := by
    rw [hsecondWord, hfirstWork1, hfirstControl, hfirstTarget]
  have htargetAfter : wireValues lengthT after = wireValues lengthT second := by
    apply wireValues_congr
    intro wire hwire
    exact hfinal.2.2 wire (hlayout.writer_not_affineRegister (by
      simp only [lengthBlockWriterSupport, List.mem_append, List.mem_cons,
        List.mem_map]
      exact Or.inl (Or.inl (Or.inl hwire))))
  have hboundarySecond : wireValues lengthRP second = wireValues lengthRP reflected := by
    apply wireValues_congr
    intro wire hwire
    have hnotTarget := hlayout.affine_not_target hwire
    rw [hsecondOutside wire hnotTarget, hfirstOutside wire hnotTarget]
  have hboundaryAfter : wireValues lengthRP after = wireValues lengthRP state := by
    rw [hfinal.1, hboundarySecond, hreflect.1, constMinusBits_involutive]
  have hmapCleanAfter : Clean (path ++ [rangeAccumulator, temporary]) after := by
    intro wire hwire
    change run (constMinus lengthRP constants carry (n + 2)) second wire = false
    rw [hfinal.2.2 wire (hlayout.writer_not_affineRegister (by
      simp [lengthBlockWriterSupport, zeroMapProtectedWires] at hwire ⊢
      aesop))]
    exact hsecondRestores.2 wire hwire
  rw [lenUpdateLtUnary, Classical.run_append, Classical.run_append,
    Classical.run_append]
  change wireValues lengthT after = _ ∧ wireValues lengthRP after = _ ∧
    Clean (constants ++ [carry]) after ∧
    Clean (path ++ [rangeAccumulator, temporary]) after ∧
    ∀ wire, wire ∉ lengthT → after wire = state wire
  refine ⟨htargetAfter.trans htargetSecond, hboundaryAfter, hfinal.2.1,
    hmapCleanAfter, ?_⟩
  intro wire hwireTarget
  by_cases hwireAffine : wire ∈ lengthRP
  · exact wireValues_eq_at_local lengthRP after state hboundaryAfter wire hwireAffine
  · calc
      after wire = second wire := hfinal.2.2 wire hwireAffine
      _ = first wire := hsecondOutside wire hwireTarget
      _ = reflected wire := hfirstOutside wire hwireTarget
      _ = state wire := hreflect.2.2 wire hwireAffine

/-- Direct whole-state semantics of the literal lower length block.  The target length receives
the two source writers in their emitted order; the shifted boundary, both borrowed banks, and
all scratch are restored. -/
theorem lenUpdateLrpUnary_correct
    (n k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) (state : BasisState)
    (hlength : constants.length = lengthT.length)
    (hlayout : LengthBlockLayout k K tree control rangeAccumulator temporary carry path
      work1At work2At lengthT lengthRP constants)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel
      (run (addConstant lengthT constants carry 3) state) = boundary)
    (hcleanConstants : Clean (constants ++ [carry]) state)
    (hcleanPath : Clean path state)
    (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    let after := run
      (lenUpdateLrpUnary n k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants) state
    wireValues lengthRP after =
        rightLengthWordAction n lengthRP.length k K (state control)
          (lowerRangeBits (state control) boundary (zeroMapLabels k K) work2At state)
          (rightLengthWordAction n lengthRP.length k K (state control)
            (lowerRangeBits (state control) boundary (zeroMapLabels k K) work1At state)
            (wireValues lengthRP state)) ∧
      wireValues lengthT after = wireValues lengthT state ∧
      Clean (constants ++ [carry]) after ∧
      Clean (path ++ [rangeAccumulator, temporary]) after ∧
      ∀ wire, wire ∉ lengthRP → after wire = state wire := by
  let shifted := run (addConstant lengthT constants carry 3) state
  have hshift := addConstant_correct lengthT constants carry 3 state
    hlength hlayout.affine hcleanConstants
  let first := run
    (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
      work1At work2At lengthRP) shifted
  let second := run
    (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
      work2At work1At lengthRP) first
  let after := run (subConstant lengthT constants carry 3) second
  have hshiftedSupport : ∀ wire,
      wire ∈ lengthBlockWriterSupport k K tree control rangeAccumulator temporary path
        work1At work2At lengthRP → shifted wire = state wire := by
    intro wire hwire
    exact hshift.2.2 wire (hlayout.writer_not_affineRegister hwire)
  have hshiftedPath : Clean path shifted := by
    intro wire hwire
    rw [hshiftedSupport wire (by
      simp [lengthBlockWriterSupport, zeroMapProtectedWires, hwire])]
    exact hcleanPath wire hwire
  have hshiftedRange : shifted rangeAccumulator = false := by
    rw [hshiftedSupport rangeAccumulator (by
      simp [lengthBlockWriterSupport]), hcleanRange]
  have hshiftedTemporary : shifted temporary = false := by
    rw [hshiftedSupport temporary (by
      simp [lengthBlockWriterSupport]), hcleanTemporary]
  have hfirstWord := rightLengthXorWrite_wordAction n k K boundary hkK hboundary
    tree control rangeAccumulator temporary path work1At work2At lengthRP shifted
    hlayout.work1Bits hlabels hroute hshiftedPath hshiftedRange hshiftedTemporary
  have hfirstRestores := rightLengthXorWrite_restores n k K boundary hkK hboundary
    tree control rangeAccumulator temporary path work1At work2At lengthRP shifted
    hlayout.work1Bits hlabels hroute hshiftedPath hshiftedRange hshiftedTemporary
  have hfirstOutside : ∀ wire, wire ∉ lengthRP → first wire = shifted wire := by
    intro wire hwire
    exact rightLengthXorWrite_preservesOutsideTarget n k K boundary hkK hboundary
      tree control rangeAccumulator temporary path work1At work2At lengthRP shifted
      hlayout.work1Bits hlabels hroute hshiftedPath hshiftedRange hshiftedTemporary
      wire hwire
  have hfirstRoute : tree.routeLabel first = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstOutside wire (hlayout.work1Bits.mapWire_not_target (by
      simp [zeroMapWires, zeroMapProtectedWires, hwire]))
  have hfirstPath : Clean path first := by
    intro wire hwire
    exact hfirstRestores.2 wire (by simp [hwire])
  have hfirstRange : first rangeAccumulator = false :=
    hfirstRestores.2 rangeAccumulator (by simp)
  have hfirstTemporary : first temporary = false :=
    hfirstRestores.2 temporary (by simp)
  have hsecondWord := rightLengthXorWrite_wordAction n k K boundary hkK hboundary
    tree control rangeAccumulator temporary path work2At work1At lengthRP first
    hlayout.work2Bits hlabels hfirstRoute hfirstPath hfirstRange hfirstTemporary
  have hsecondRestores := rightLengthXorWrite_restores n k K boundary hkK hboundary
    tree control rangeAccumulator temporary path work2At work1At lengthRP first
    hlayout.work2Bits hlabels hfirstRoute hfirstPath hfirstRange hfirstTemporary
  have hsecondOutside : ∀ wire, wire ∉ lengthRP → second wire = first wire := by
    intro wire hwire
    exact rightLengthXorWrite_preservesOutsideTarget n k K boundary hkK hboundary
      tree control rangeAccumulator temporary path work2At work1At lengthRP first
      hlayout.work2Bits hlabels hfirstRoute hfirstPath hfirstRange hfirstTemporary
      wire hwire
  have hconstantsFirst : Clean (constants ++ [carry]) first := by
    intro wire hwire
    rw [hfirstOutside wire (hlayout.constantCarry_not_target hwire)]
    exact hshift.2.1 wire hwire
  have hconstantsSecond : Clean (constants ++ [carry]) second := by
    intro wire hwire
    rw [hsecondOutside wire (hlayout.constantCarry_not_target hwire)]
    exact hconstantsFirst wire hwire
  have hfinal := subConstant_correct lengthT constants carry 3 second
    hlength hlayout.affine hconstantsSecond
  have hshiftedControl : shifted control = state control :=
    hshiftedSupport control (by
      simp [lengthBlockWriterSupport, zeroMapProtectedWires])
  have hshiftedTarget : wireValues lengthRP shifted = wireValues lengthRP state := by
    apply wireValues_congr
    intro wire hwire
    exact hshiftedSupport wire (by
      simp [lengthBlockWriterSupport, hwire])
  have hshiftedWork1 :
      lowerRangeBits (shifted control) boundary (zeroMapLabels k K) work1At shifted =
        lowerRangeBits (state control) boundary (zeroMapLabels k K) work1At state := by
    unfold lowerRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hshiftedControl]
    rw [hshiftedSupport (work1At label) (by
      simp only [lengthBlockWriterSupport, List.mem_append, List.mem_cons,
        List.mem_map]
      exact Or.inl (Or.inr (Or.inr
        (Or.inr ⟨label, hlabel, rfl⟩))))]
  have hfirstControl : first control = state control := by
    rw [hfirstOutside control hlayout.work1Bits.control_not_target,
      hshiftedControl]
  have hfirstWork2 :
      lowerRangeBits (first control) boundary (zeroMapLabels k K) work2At first =
        lowerRangeBits (state control) boundary (zeroMapLabels k K) work2At state := by
    unfold lowerRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hfirstControl]
    rw [hfirstOutside (work2At label)
      (hlayout.work1Bits.dirty_not_target hlabel)]
    rw [hshiftedSupport (work2At label) (by
      simp only [lengthBlockWriterSupport, List.mem_append, List.mem_cons,
        List.mem_map]
      exact Or.inr ⟨label, hlabel, rfl⟩)]
  have hfirstTarget :
      wireValues lengthRP first =
        rightLengthWordAction n lengthRP.length k K (state control)
          (lowerRangeBits (state control) boundary (zeroMapLabels k K) work1At state)
          (wireValues lengthRP state) := by
    rw [hfirstWord, hshiftedWork1, hshiftedControl, hshiftedTarget]
  have htargetSecond :
      wireValues lengthRP second =
        rightLengthWordAction n lengthRP.length k K (state control)
          (lowerRangeBits (state control) boundary (zeroMapLabels k K) work2At state)
          (rightLengthWordAction n lengthRP.length k K (state control)
            (lowerRangeBits (state control) boundary (zeroMapLabels k K) work1At state)
            (wireValues lengthRP state)) := by
    rw [hsecondWord, hfirstWork2, hfirstControl, hfirstTarget]
  have htargetAfter : wireValues lengthRP after = wireValues lengthRP second := by
    apply wireValues_congr
    intro wire hwire
    exact hfinal.2.2 wire (hlayout.writer_not_affineRegister (by
      simp only [lengthBlockWriterSupport, List.mem_append, List.mem_cons,
        List.mem_map]
      exact Or.inl (Or.inl (Or.inl hwire))))
  have hboundarySecond : wireValues lengthT second = wireValues lengthT shifted := by
    apply wireValues_congr
    intro wire hwire
    have hnotTarget := hlayout.affine_not_target hwire
    rw [hsecondOutside wire hnotTarget, hfirstOutside wire hnotTarget]
  have hboundaryAfter : wireValues lengthT after = wireValues lengthT state := by
    rw [hfinal.1, hboundarySecond, hshift.1]
    apply cuccaroSubBits_addBits
    simpa [wireValues] using hlength
  have hmapCleanAfter : Clean (path ++ [rangeAccumulator, temporary]) after := by
    intro wire hwire
    change run (subConstant lengthT constants carry 3) second wire = false
    rw [hfinal.2.2 wire (hlayout.writer_not_affineRegister (by
      simp [lengthBlockWriterSupport, zeroMapProtectedWires] at hwire ⊢
      aesop))]
    exact hsecondRestores.2 wire hwire
  rw [lenUpdateLrpUnary, Classical.run_append, Classical.run_append,
    Classical.run_append]
  change wireValues lengthRP after = _ ∧ wireValues lengthT after = _ ∧
    Clean (constants ++ [carry]) after ∧
    Clean (path ++ [rangeAccumulator, temporary]) after ∧
    ∀ wire, wire ∉ lengthRP → after wire = state wire
  refine ⟨htargetAfter.trans htargetSecond, hboundaryAfter, hfinal.2.1,
    hmapCleanAfter, ?_⟩
  intro wire hwireTarget
  by_cases hwireAffine : wire ∈ lengthT
  · exact wireValues_eq_at_local lengthT after state hboundaryAfter wire hwireAffine
  · calc
      after wire = second wire := hfinal.2.2 wire hwireAffine
      _ = first wire := hsecondOutside wire hwireTarget
      _ = shifted wire := hfirstOutside wire hwireTarget
      _ = state wire := hshift.2.2 wire hwireAffine

/-! ## Complete-block structural and resource contracts -/

/-- Complete named footprint of either length block: the affine boundary word and its clean
constant scratch, followed by the common two-writer footprint. -/
def lengthBlockSupport
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (affineRegister target constants : List Wire) : List Wire :=
  (constants ++ affineRegister ++ [carry]) ++
    lengthBlockWriterSupport k K tree control rangeAccumulator temporary path
      work1At work2At target

theorem lenUpdateLtUnary_usesOnly
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    PaperCircuitUsesOnly
      (lengthBlockSupport k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthRP lengthT constants)
      (lenUpdateLtUnary n k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants) := by
  have haffine : PaperCircuitUsesOnly
      (lengthBlockSupport k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthRP lengthT constants)
      (constMinus lengthRP constants carry (n + 2)) := by
    apply (constMinus_usesOnly lengthRP constants carry (n + 2)).mono
    intro wire hwire
    exact List.mem_append_left _ hwire
  have hwork2 : PaperCircuitUsesOnly
      (lengthBlockSupport k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthRP lengthT constants)
      (highestPositionXorWrite k K tree control rangeAccumulator temporary path
        work2At work1At lengthT) := by
    apply (highestPositionXorWrite_usesOnly k K hkK tree control rangeAccumulator
      temporary path work2At work1At lengthT).mono
    intro wire hwire
    apply List.mem_append_right (constants ++ lengthRP ++ [carry])
    simp only [lengthWriterSupport, zeroMapWires,
      lengthBlockWriterSupport, List.mem_append, List.mem_cons,
      List.mem_map] at hwire ⊢
    aesop
  have hwork1 : PaperCircuitUsesOnly
      (lengthBlockSupport k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthRP lengthT constants)
      (highestPositionXorWrite k K tree control rangeAccumulator temporary path
        work1At work2At lengthT) := by
    apply (highestPositionXorWrite_usesOnly k K hkK tree control rangeAccumulator
      temporary path work1At work2At lengthT).mono
    intro wire hwire
    apply List.mem_append_right (constants ++ lengthRP ++ [carry])
    simp only [lengthWriterSupport, zeroMapWires,
      lengthBlockWriterSupport, List.mem_append, List.mem_cons,
      List.mem_map] at hwire ⊢
    aesop
  rw [lenUpdateLtUnary]
  exact PaperCircuitUsesOnly.append
    (PaperCircuitUsesOnly.append
      (PaperCircuitUsesOnly.append haffine hwork2) hwork1) haffine

theorem lenUpdateLrpUnary_usesOnly
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    PaperCircuitUsesOnly
      (lengthBlockSupport k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants)
      (lenUpdateLrpUnary n k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants) := by
  have hadd : PaperCircuitUsesOnly
      (lengthBlockSupport k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants)
      (addConstant lengthT constants carry 3) := by
    apply (addConstant_usesOnly lengthT constants carry 3).mono
    intro wire hwire
    exact List.mem_append_left _ hwire
  have hsub : PaperCircuitUsesOnly
      (lengthBlockSupport k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants)
      (subConstant lengthT constants carry 3) := by
    apply (subConstant_usesOnly lengthT constants carry 3).mono
    intro wire hwire
    exact List.mem_append_left _ hwire
  have hwork1 : PaperCircuitUsesOnly
      (lengthBlockSupport k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants)
      (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
        work1At work2At lengthRP) := by
    apply (rightLengthXorWrite_usesOnly n k K hkK tree control rangeAccumulator
      temporary path work1At work2At lengthRP).mono
    intro wire hwire
    apply List.mem_append_right (constants ++ lengthT ++ [carry])
    simp only [lengthWriterSupport, zeroMapWires,
      lengthBlockWriterSupport, List.mem_append, List.mem_cons,
      List.mem_map] at hwire ⊢
    aesop
  have hwork2 : PaperCircuitUsesOnly
      (lengthBlockSupport k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants)
      (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
        work2At work1At lengthRP) := by
    apply (rightLengthXorWrite_usesOnly n k K hkK tree control rangeAccumulator
      temporary path work2At work1At lengthRP).mono
    intro wire hwire
    apply List.mem_append_right (constants ++ lengthT ++ [carry])
    simp only [lengthWriterSupport, zeroMapWires,
      lengthBlockWriterSupport, List.mem_append, List.mem_cons,
      List.mem_map] at hwire ⊢
    aesop
  rw [lenUpdateLrpUnary]
  exact PaperCircuitUsesOnly.append
    (PaperCircuitUsesOnly.append
      (PaperCircuitUsesOnly.append hadd hwork1) hwork2) hsub

@[simp]
theorem lenUpdateLtUnary_HPFree
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    HPFree
      (lenUpdateLtUnary n k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants) := by
  simp [lenUpdateLtUnary]

@[simp]
theorem lenUpdateLrpUnary_HPFree
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    HPFree
      (lenUpdateLrpUnary n k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants) := by
  simp [lenUpdateLrpUnary]

theorem lenUpdateLtUnary_wellFormed
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hlength : constants.length = lengthRP.length)
    (hlayout : LengthBlockLayout k K tree control rangeAccumulator temporary carry path
      work1At work2At lengthRP lengthT constants) :
    CircuitWellFormed
      (lenUpdateLtUnary n k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants) := by
  simp only [lenUpdateLtUnary, circuitWellFormed_append]
  exact ⟨⟨⟨
    constMinus_wellFormed lengthRP constants carry (n + 2) hlength hlayout.affine,
    highestPositionXorWrite_wellFormed k K hkK tree control rangeAccumulator
      temporary path work2At work1At lengthT hlayout.work2Bits⟩,
    highestPositionXorWrite_wellFormed k K hkK tree control rangeAccumulator
      temporary path work1At work2At lengthT hlayout.work1Bits⟩,
    constMinus_wellFormed lengthRP constants carry (n + 2) hlength hlayout.affine⟩

theorem lenUpdateLrpUnary_wellFormed
    (n k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hlength : constants.length = lengthT.length)
    (hlayout : LengthBlockLayout k K tree control rangeAccumulator temporary carry path
      work1At work2At lengthT lengthRP constants) :
    CircuitWellFormed
      (lenUpdateLrpUnary n k K tree control rangeAccumulator temporary carry path
        work1At work2At lengthT lengthRP constants) := by
  simp only [lenUpdateLrpUnary, circuitWellFormed_append]
  exact ⟨⟨⟨
    addConstant_wellFormed lengthT constants carry 3 hlength hlayout.affine,
    rightLengthXorWrite_wellFormed n k K hkK tree control rangeAccumulator
      temporary path work1At work2At lengthRP hlayout.work1Bits⟩,
    rightLengthXorWrite_wellFormed n k K hkK tree control rangeAccumulator
      temporary path work2At work1At lengthRP hlayout.work2Bits⟩,
    subConstant_wellFormed lengthT constants carry 3 hlength hlayout.affine⟩

/-- Exact coherent Toffoli count of the complete upper length block. -/
theorem lenUpdateLtUnary_toffoliCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hpositive : 0 < lengthRP.length)
    (hlength : constants.length = lengthRP.length) :
    eeaToffoliCount
        (lenUpdateLtUnary n k K tree control rangeAccumulator temporary carry path
          work1At work2At lengthT lengthRP constants) =
      2 * (2 * (lengthRP.length - 2) + 2 * lengthRP.length) +
        2 * eeaToffoliCount
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
            work2At work1At) +
        2 * eeaToffoliCount
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
            work1At work2At) := by
  have haffine := constMinus_toffoliCount lengthRP constants carry (n + 2)
    hpositive hlength
  have hwork2 := highestPositionXorWrite_toffoliCount k K tree control
    rangeAccumulator temporary path work2At work1At lengthT
  have hwork1 := highestPositionXorWrite_toffoliCount k K tree control
    rangeAccumulator temporary path work1At work2At lengthT
  simp only [lenUpdateLtUnary, eeaToffoliCount_append]
  rw [haffine, hwork2, hwork1]
  omega

/-- Exact coherent CNOT count of the complete upper length block. -/
theorem lenUpdateLtUnary_cnotCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hwidth : 2 ≤ lengthRP.length)
    (hlength : constants.length = lengthRP.length) :
    eeaCnotCount
        (lenUpdateLtUnary n k K tree control rangeAccumulator temporary carry path
          work1At work2At lengthT lengthRP constants) =
      2 * (lengthRP.length + 1 + 4 * lengthRP.length) +
        2 * lowBitCount lengthT.length
          (truncateConstant lengthT.length (K - 1)) +
        4 * ((zeroMapLabels k K).reverse.map fun label ↦
          lowBitCount lengthT.length
            (highestPositionWriteValue lengthT.length k label)).sum +
        2 * eeaCnotCount
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
            work2At work1At) +
        2 * eeaCnotCount
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
            work1At work2At) := by
  cases lengthRP with
  | nil => simp at hwidth
  | cons low tail =>
      cases tail with
      | nil => simp at hwidth
      | cons next rest =>
          have haffine := constMinus_cnotCount low next rest constants carry (n + 2)
            hlength
          have hwork2 := highestPositionXorWrite_cnotCount k K tree control
            rangeAccumulator temporary path work2At work1At lengthT
          have hwork1 := highestPositionXorWrite_cnotCount k K tree control
            rangeAccumulator temporary path work1At work2At lengthT
          simp only [lenUpdateLtUnary, eeaCnotCount_append]
          rw [haffine, hwork2, hwork1]
          omega

/-- Exact coherent T count of the complete upper length block. -/
theorem lenUpdateLtUnary_tCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hpositive : 0 < lengthRP.length)
    (hlength : constants.length = lengthRP.length) :
    ShorECDLP.tCount
        (lenUpdateLtUnary n k K tree control rangeAccumulator temporary carry path
          work1At work2At lengthT lengthRP constants) =
      2 * (14 * (lengthRP.length - 2) + 14 * lengthRP.length) +
        2 * ShorECDLP.tCount
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
            work2At work1At) +
        2 * ShorECDLP.tCount
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
            work1At work2At) := by
  have haffine := constMinus_tCount lengthRP constants carry (n + 2)
    hpositive hlength
  have hwork2 := highestPositionXorWrite_tCount k K tree control
    rangeAccumulator temporary path work2At work1At lengthT
  have hwork1 := highestPositionXorWrite_tCount k K tree control
    rangeAccumulator temporary path work1At work2At lengthT
  simp only [lenUpdateLtUnary, tCount_append]
  rw [haffine, hwork2, hwork1]
  omega

/-- Exact coherent Toffoli count of the complete lower length block. -/
theorem lenUpdateLrpUnary_toffoliCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hlength : constants.length = lengthT.length) :
    eeaToffoliCount
        (lenUpdateLrpUnary n k K tree control rangeAccumulator temporary carry path
          work1At work2At lengthT lengthRP constants) =
      4 * lengthT.length +
        2 * eeaToffoliCount
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
            work1At work2At) +
        2 * eeaToffoliCount
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
            work2At work1At) := by
  have hadd := addConstant_toffoliCount lengthT constants carry 3 hlength
  have hsub := subConstant_toffoliCount lengthT constants carry 3 hlength
  have hwork1 := rightLengthXorWrite_toffoliCount n k K tree control
    rangeAccumulator temporary path work1At work2At lengthRP
  have hwork2 := rightLengthXorWrite_toffoliCount n k K tree control
    rangeAccumulator temporary path work2At work1At lengthRP
  simp only [lenUpdateLrpUnary, eeaToffoliCount_append]
  rw [hadd, hsub, hwork1, hwork2]
  omega

/-- Exact coherent CNOT count of the complete lower length block. -/
theorem lenUpdateLrpUnary_cnotCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hlength : constants.length = lengthT.length) :
    eeaCnotCount
        (lenUpdateLrpUnary n k K tree control rangeAccumulator temporary carry path
          work1At work2At lengthT lengthRP constants) =
      8 * lengthT.length +
        2 * lowBitCount lengthRP.length
          (truncateConstant lengthRP.length (n + 3 - k)) +
        4 * ((zeroMapLabels k K).map fun label ↦
          lowBitCount lengthRP.length
            (rightLengthWriteValue n lengthRP.length K label)).sum +
        2 * eeaCnotCount
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
            work1At work2At) +
        2 * eeaCnotCount
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
            work2At work1At) := by
  have hadd := addConstant_cnotCount lengthT constants carry 3 hlength
  have hsub := subConstant_cnotCount lengthT constants carry 3 hlength
  have hwork1 := rightLengthXorWrite_cnotCount n k K tree control
    rangeAccumulator temporary path work1At work2At lengthRP
  have hwork2 := rightLengthXorWrite_cnotCount n k K tree control
    rangeAccumulator temporary path work2At work1At lengthRP
  simp only [lenUpdateLrpUnary, eeaCnotCount_append]
  rw [hadd, hsub, hwork1, hwork2]
  omega

/-- Exact coherent T count of the complete lower length block. -/
theorem lenUpdateLrpUnary_tCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hlength : constants.length = lengthT.length) :
    ShorECDLP.tCount
        (lenUpdateLrpUnary n k K tree control rangeAccumulator temporary carry path
          work1At work2At lengthT lengthRP constants) =
      28 * lengthT.length +
        2 * ShorECDLP.tCount
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
            work1At work2At) +
        2 * ShorECDLP.tCount
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
            work2At work1At) := by
  have hadd := addConstant_tCount lengthT constants carry 3 hlength
  have hsub := subConstant_tCount lengthT constants carry 3 hlength
  have hwork1 := rightLengthXorWrite_tCount n k K tree control
    rangeAccumulator temporary path work1At work2At lengthRP
  have hwork2 := rightLengthXorWrite_tCount n k K tree control
    rangeAccumulator temporary path work2At work1At lengthRP
  simp only [lenUpdateLrpUnary, tCount_append]
  rw [hadd, hsub, hwork1, hwork2]
  omega

end

end ShorECDLP.Paper2607_13816
