import ShorECDLP.Submission.«2607_13816».EEA.UnaryAction
import ShorECDLP.Submission.«2607_13816».EEA.LengthUpdate

/-!
# Source zero maps for borrowed-work length updates

Figures 12--13 of the pinned supplement compute suffix/prefix zero flags in arbitrary dirty
storage.  The implementation is deliberately two-pass: the first pass introduces a dependence
on the original neighbouring dirty bit, and the reverse pass cancels that dependence while
retaining the desired cumulative zero flag.

This module first proves that Boolean dirty-storage identity, then binds it to the literal
range-scan leaf cells.  The grouped highest-position and right-length writers later in this file
use these maps between two identical borrowed-work write streams, exactly as emitted by the
supplement.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-! ## Pure two-pass dirty recurrence -/

/-- Conjunction saying that every bit in a Boolean word is zero. -/
def allFalse : List Bool → Bool
  | [] => true
  | bit :: bits => !bit && allFalse bits

/-- Suffix-zero flags, ordered like the input word. -/
def suffixZeroFlags : List Bool → List Bool
  | [] => []
  | bit :: bits => (!bit && allFalse bits) :: suffixZeroFlags bits

/-- Pointwise Boolean XOR.  Source-facing theorems require equal word lengths. -/
def xorWords (left right : List Bool) : List Bool :=
  List.zipWith Bool.xor left right

/-- First, low-to-high pass of `_upper_zero_map`. -/
def upperDirtyForward : List Bool → List Bool → List Bool
  | [], _ => []
  | [bit], dirty => [Bool.xor (dirty.headD false) (!bit)]
  | bit :: nextBit :: bits, dirty =>
      Bool.xor (dirty.headD false) (!bit && dirty.tail.headD false) ::
        upperDirtyForward (nextBit :: bits) dirty.tail

/-- Second, high-to-low pass of `_upper_zero_map`; the last (base) lane is skipped. -/
def upperDirtyReverse : List Bool → List Bool → List Bool
  | [], _ => []
  | [_], dirty => [dirty.headD false]
  | bit :: nextBit :: bits, dirty =>
      let tail := upperDirtyReverse (nextBit :: bits) dirty.tail
      Bool.xor (dirty.headD false) (!bit && tail.headD false) :: tail

/-- Complete upper two-pass dirty map. -/
def upperDirtyMap (bits dirty : List Bool) : List Bool :=
  upperDirtyReverse bits (upperDirtyForward bits dirty)

/-- Generalized first pass with an explicit root seed.  The source circuit uses the external
block control as this seed; `upperDirtyForward` is the always-enabled specialization. -/
def upperDirtyForwardSeed (seed : Bool) : List Bool → List Bool → List Bool
  | [], _ => []
  | [bit], dirty => [Bool.xor (dirty.headD false) (!bit && seed)]
  | bit :: nextBit :: bits, dirty =>
      Bool.xor (dirty.headD false) (!bit && dirty.tail.headD false) ::
        upperDirtyForwardSeed seed (nextBit :: bits) dirty.tail

/-- Generalized two-pass map with an explicit root seed. -/
def upperDirtyMapSeed (seed : Bool) (bits dirty : List Bool) : List Bool :=
  upperDirtyReverse bits (upperDirtyForwardSeed seed bits dirty)

/-- Pointwise gate of a Boolean flag word. -/
def gateWord (enabled : Bool) (word : List Bool) : List Bool :=
  word.map fun bit => enabled && bit

@[simp]
theorem xorWords_length
    (left right : List Bool) (hlength : left.length = right.length) :
    (xorWords left right).length = left.length := by
  simp [xorWords, hlength]

@[simp]
theorem suffixZeroFlags_length (bits : List Bool) :
    (suffixZeroFlags bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [suffixZeroFlags, ih]

@[simp]
theorem upperDirtyForward_length
    (bits dirty : List Bool) :
    (upperDirtyForward bits dirty).length = bits.length := by
  induction bits generalizing dirty with
  | nil => rfl
  | cons bit bits ih =>
      cases bits with
      | nil => rfl
      | cons nextBit bits =>
          simp [upperDirtyForward, ih]

@[simp]
theorem upperDirtyReverse_length
    (bits dirty : List Bool) :
    (upperDirtyReverse bits dirty).length = bits.length := by
  induction bits generalizing dirty with
  | nil => rfl
  | cons bit bits ih =>
      cases bits with
      | nil => rfl
      | cons nextBit bits =>
          simp [upperDirtyReverse, ih]

/-- The paired dirty passes cancel every dependence on the initial neighbouring dirty value.
Exactly the suffix-zero flag remains in each lane. -/
theorem upperDirtyMap_eq_xor_suffixZeroFlags
    (bits dirty : List Bool) (hlength : bits.length = dirty.length) :
    upperDirtyMap bits dirty = xorWords dirty (suffixZeroFlags bits) := by
  induction bits generalizing dirty with
  | nil =>
      have : dirty = [] := List.length_eq_zero_iff.mp hlength.symm
      subst dirty
      rfl
  | cons bit bits ih =>
      cases bits with
      | nil =>
          cases dirty with
          | nil => simp at hlength
          | cons dirty dirtys =>
              have : dirtys = [] := List.length_eq_zero_iff.mp (by
                simpa using Nat.succ.inj hlength.symm)
              subst dirtys
              cases bit <;> cases dirty <;> rfl
      | cons nextBit bits =>
          cases dirty with
          | nil => simp at hlength
          | cons dirty dirtys =>
              cases dirtys with
              | nil => simp at hlength
              | cons nextDirty dirtys =>
                  have htail : (nextBit :: bits).length =
                      (nextDirty :: dirtys).length := by
                    simpa using Nat.succ.inj hlength
                  have hih := ih (nextDirty :: dirtys) htail
                  simp only [upperDirtyMap, upperDirtyForward,
                    List.headD_cons, List.tail_cons]
                  rw [upperDirtyReverse]
                  simp only [List.headD_cons, List.tail_cons]
                  change
                    (Bool.xor (Bool.xor dirty (!bit && nextDirty))
                        (!bit &&
                          (upperDirtyMap (nextBit :: bits)
                            (nextDirty :: dirtys)).headD false) ::
                      upperDirtyMap (nextBit :: bits) (nextDirty :: dirtys)) =
                    (Bool.xor dirty (!bit && allFalse (nextBit :: bits)) ::
                      xorWords (nextDirty :: dirtys)
                        (suffixZeroFlags (nextBit :: bits)))
                  rw [hih]
                  simp only [suffixZeroFlags, allFalse, xorWords,
                    List.zipWith, List.headD_cons]
                  cases bit <;> cases dirty <;> cases nextDirty <;>
                    cases nextBit <;> cases allFalse bits <;> rfl

@[simp]
theorem upperDirtyForwardSeed_true (bits dirty : List Bool) :
    upperDirtyForwardSeed true bits dirty = upperDirtyForward bits dirty := by
  induction bits generalizing dirty with
  | nil => rfl
  | cons bit bits ih =>
      cases bits with
      | nil => simp [upperDirtyForwardSeed, upperDirtyForward]
      | cons nextBit bits =>
          simp [upperDirtyForwardSeed, upperDirtyForward, ih]

@[simp]
theorem upperDirtyMapSeed_true (bits dirty : List Bool) :
    upperDirtyMapSeed true bits dirty = upperDirtyMap bits dirty := by
  unfold upperDirtyMapSeed upperDirtyMap
  rw [upperDirtyForwardSeed_true]

private theorem upperDirtyMapSeed_false
    (bits dirty : List Bool) (hlength : bits.length = dirty.length) :
    upperDirtyMapSeed false bits dirty = dirty := by
  induction bits generalizing dirty with
  | nil =>
      have : dirty = [] := List.length_eq_zero_iff.mp hlength.symm
      subst dirty
      rfl
  | cons bit bits ih =>
      cases bits with
      | nil =>
          cases dirty with
          | nil => simp at hlength
          | cons dirty dirtys =>
              have : dirtys = [] := List.length_eq_zero_iff.mp (by
                simpa using Nat.succ.inj hlength.symm)
              subst dirtys
              cases bit <;> cases dirty <;> rfl
      | cons nextBit bits =>
          cases dirty with
          | nil => simp at hlength
          | cons dirty dirtys =>
              cases dirtys with
              | nil => simp at hlength
              | cons nextDirty dirtys =>
                  have htail : (nextBit :: bits).length =
                      (nextDirty :: dirtys).length := by
                    simpa using Nat.succ.inj hlength
                  have hih := ih (nextDirty :: dirtys) htail
                  simp only [upperDirtyMapSeed, upperDirtyForwardSeed,
                    List.headD_cons, List.tail_cons]
                  rw [upperDirtyReverse]
                  simp only [List.headD_cons, List.tail_cons]
                  change
                    (Bool.xor (Bool.xor dirty (!bit && nextDirty))
                        (!bit &&
                          (upperDirtyMapSeed false (nextBit :: bits)
                            (nextDirty :: dirtys)).headD false) ::
                      upperDirtyMapSeed false (nextBit :: bits)
                        (nextDirty :: dirtys)) =
                    dirty :: nextDirty :: dirtys
                  rw [hih]
                  cases bit <;> cases dirty <;> cases nextDirty <;> rfl

/-- Seeded form of the dirty-map identity used by the externally controlled source block. -/
theorem upperDirtyMapSeed_eq_xor_suffixZeroFlags
    (seed : Bool) (bits dirty : List Bool)
    (hlength : bits.length = dirty.length) :
    upperDirtyMapSeed seed bits dirty =
      xorWords dirty (gateWord seed (suffixZeroFlags bits)) := by
  cases seed with
  | false =>
      rw [upperDirtyMapSeed_false bits dirty hlength]
      induction dirty generalizing bits with
      | nil =>
          have : bits = [] := List.length_eq_zero_iff.mp hlength
          subst bits
          rfl
      | cons dirty dirtys ih =>
          cases bits with
          | nil => simp at hlength
          | cons bit bits =>
              have htail : bits.length = dirtys.length := Nat.succ.inj hlength
              simp only [suffixZeroFlags, gateWord, List.map_cons,
                Bool.false_and, xorWords, List.zipWith]
              simpa only [Bool.xor_false, xorWords, gateWord,
                Bool.false_and] using
                congrArg (List.cons dirty) (ih bits htail)
  | true =>
      simpa [gateWord] using upperDirtyMap_eq_xor_suffixZeroFlags bits dirty hlength

/-! ## State-level recurrence corresponding to the dirty-word identity -/

/-- Read a labelled wire bank in label order. -/
def readWireWord (labels : List Nat) (wireAt : Nat → Wire)
    (state : BasisState) : List Bool :=
  labels.map fun label => state (wireAt label)

@[simp]
theorem readWireWord_reverse
    (labels : List Nat) (wireAt : Nat → Wire) (state : BasisState) :
    readWireWord labels.reverse wireAt state =
      (readWireWord labels wireAt state).reverse := by
  simp [readWireWord]

theorem readWireWord_upd_not_mem
    (labels : List Nat) (wireAt : Nat → Wire) (state : BasisState)
    (wire : Wire) (value : Bool) (hwire : wire ∉ labels.map wireAt) :
    readWireWord labels wireAt state[wire ↦ value] =
      readWireWord labels wireAt state := by
  unfold readWireWord
  apply List.map_congr_left
  intro label hlabel
  rw [upd_other]
  intro equality
  apply hwire
  exact List.mem_map.mpr ⟨label, hlabel, equality⟩

/-- State-level first upper pass.  `bits` already includes the dynamic range mask. -/
def upperForwardStateSeed (seed : Bool) (bits : List Bool)
    (dirtyAt : Nat → Wire) : List Nat → BasisState → BasisState
  | [], state => state
  | [label], state =>
      state[dirtyAt label ↦ Bool.xor (state (dirtyAt label))
        (!bits.headD false && seed)]
  | label :: next :: labels, state =>
      upperForwardStateSeed seed bits.tail dirtyAt (next :: labels)
        (state[dirtyAt label ↦ Bool.xor (state (dirtyAt label))
          (!bits.headD false && state (dirtyAt next))])

/-- State-level second upper pass, performed in reverse source order. -/
def upperReverseState (bits : List Bool)
    (dirtyAt : Nat → Wire) : List Nat → BasisState → BasisState
  | [], state => state
  | [_], state => state
  | label :: next :: labels, state =>
      let tail := upperReverseState bits.tail dirtyAt (next :: labels) state
      tail[dirtyAt label ↦ Bool.xor (tail (dirtyAt label))
        (!bits.headD false && tail (dirtyAt next))]

def upperMapStateSeed (seed : Bool) (bits : List Bool)
    (labels : List Nat) (dirtyAt : Nat → Wire) (state : BasisState) : BasisState :=
  upperReverseState bits dirtyAt labels
    (upperForwardStateSeed seed bits dirtyAt labels state)

theorem upperForwardStateSeed_preservesOutside
    (seed : Bool) (bits : List Bool) (labels : List Nat)
    (dirtyAt : Nat → Wire) (state : BasisState) (wire : Wire)
    (hwire : wire ∉ labels.map dirtyAt) :
    upperForwardStateSeed seed bits dirtyAt labels state wire = state wire := by
  induction labels generalizing bits state with
  | nil => rfl
  | cons label labels ih =>
      cases labels with
      | nil =>
          simp only [upperForwardStateSeed, List.map_cons, List.map_nil,
            List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
          rw [upd_other state (dirtyAt label) _ hwire]
      | cons next labels =>
          have hwire' : wire ≠ dirtyAt label ∧
              wire ∉ (next :: labels).map dirtyAt := by
            simpa only [List.map_cons, List.mem_cons, not_or] using hwire
          simp only [upperForwardStateSeed]
          rw [ih]
          · rw [upd_other state (dirtyAt label) _ hwire'.1]
          · exact hwire'.2

theorem upperReverseState_preservesOutside
    (bits : List Bool) (labels : List Nat)
    (dirtyAt : Nat → Wire) (state : BasisState) (wire : Wire)
    (hwire : wire ∉ labels.map dirtyAt) :
    upperReverseState bits dirtyAt labels state wire = state wire := by
  induction labels generalizing bits state with
  | nil => rfl
  | cons label labels ih =>
      cases labels with
      | nil => rfl
      | cons next labels =>
          have hwire' : wire ≠ dirtyAt label ∧
              wire ∉ (next :: labels).map dirtyAt := by
            simpa only [List.map_cons, List.mem_cons, not_or] using hwire
          simp only [upperReverseState]
          rw [upd_other _ (dirtyAt label) _ hwire'.1]
          rw [ih]
          exact hwire'.2

theorem readWireWord_upperForwardStateSeed
    (seed : Bool) (bits : List Bool) (labels : List Nat)
    (dirtyAt : Nat → Wire) (state : BasisState)
    (hlength : bits.length = labels.length)
    (hnodup : (labels.map dirtyAt).Nodup) :
    readWireWord labels dirtyAt
        (upperForwardStateSeed seed bits dirtyAt labels state) =
      upperDirtyForwardSeed seed bits (readWireWord labels dirtyAt state) := by
  induction labels generalizing bits state with
  | nil =>
      have : bits = [] := List.length_eq_zero_iff.mp hlength
      subst bits
      rfl
  | cons label labels ih =>
      cases labels with
      | nil =>
          cases bits with
          | nil => simp at hlength
          | cons bit bits =>
              have : bits = [] := List.length_eq_zero_iff.mp (by
                simpa using Nat.succ.inj hlength)
              subst bits
              simp [readWireWord, upperForwardStateSeed,
                upperDirtyForwardSeed, upd]
      | cons next labels =>
          cases bits with
          | nil => simp at hlength
          | cons bit bits =>
              cases bits with
              | nil => simp at hlength
              | cons nextBit bits =>
                  have htailLength : (nextBit :: bits).length =
                      (next :: labels).length := by
                    simpa using Nat.succ.inj hlength
                  have hnodup' : dirtyAt label ∉ (next :: labels).map dirtyAt ∧
                      ((next :: labels).map dirtyAt).Nodup := by
                    simpa only [List.map_cons, List.nodup_cons] using hnodup
                  let first := state[dirtyAt label ↦
                    Bool.xor (state (dirtyAt label))
                      (!bit && state (dirtyAt next))]
                  have hhead := upperForwardStateSeed_preservesOutside seed
                    (nextBit :: bits) (next :: labels) dirtyAt first
                    (dirtyAt label) hnodup'.1
                  have htail := ih (nextBit :: bits) first htailLength hnodup'.2
                  have htailFirst :
                      readWireWord (next :: labels) dirtyAt first =
                        readWireWord (next :: labels) dirtyAt state := by
                    exact readWireWord_upd_not_mem (next :: labels) dirtyAt state
                      (dirtyAt label) _ hnodup'.1
                  simp only [upperForwardStateSeed, readWireWord, List.map_cons]
                  change
                    (upperForwardStateSeed seed (nextBit :: bits) dirtyAt
                        (next :: labels) first (dirtyAt label) ::
                      readWireWord (next :: labels) dirtyAt
                        (upperForwardStateSeed seed (nextBit :: bits) dirtyAt
                          (next :: labels) first)) = _
                  rw [hhead, htail]
                  rw [htailFirst]
                  simp [first, upperDirtyForwardSeed, readWireWord]

theorem readWireWord_upperReverseState
    (bits : List Bool) (labels : List Nat)
    (dirtyAt : Nat → Wire) (state : BasisState)
    (hlength : bits.length = labels.length)
    (hnodup : (labels.map dirtyAt).Nodup) :
    readWireWord labels dirtyAt (upperReverseState bits dirtyAt labels state) =
      upperDirtyReverse bits (readWireWord labels dirtyAt state) := by
  induction labels generalizing bits state with
  | nil =>
      have : bits = [] := List.length_eq_zero_iff.mp hlength
      subst bits
      rfl
  | cons label labels ih =>
      cases labels with
      | nil =>
          cases bits with
          | nil => simp at hlength
          | cons bit bits =>
              have : bits = [] := List.length_eq_zero_iff.mp (by
                simpa using Nat.succ.inj hlength)
              subst bits
              rfl
      | cons next labels =>
          cases bits with
          | nil => simp at hlength
          | cons bit bits =>
              cases bits with
              | nil => simp at hlength
              | cons nextBit bits =>
                  have htailLength : (nextBit :: bits).length =
                      (next :: labels).length := by
                    simpa using Nat.succ.inj hlength
                  have hnodup' : dirtyAt label ∉ (next :: labels).map dirtyAt ∧
                      ((next :: labels).map dirtyAt).Nodup := by
                    simpa only [List.map_cons, List.nodup_cons] using hnodup
                  let tail := upperReverseState (nextBit :: bits) dirtyAt
                    (next :: labels) state
                  have hhead := upperReverseState_preservesOutside
                    (nextBit :: bits) (next :: labels) dirtyAt state
                    (dirtyAt label) hnodup'.1
                  have htail := ih (nextBit :: bits) state htailLength hnodup'.2
                  have hnext : tail (dirtyAt next) =
                      (upperDirtyReverse (nextBit :: bits)
                        (readWireWord (next :: labels) dirtyAt state)).headD false := by
                    have := congrArg (fun word : List Bool => word.headD false) htail
                    simpa [tail, readWireWord] using this
                  have htailRead :
                      readWireWord (next :: labels) dirtyAt
                          tail[dirtyAt label ↦ Bool.xor (tail (dirtyAt label))
                            (!bit && tail (dirtyAt next))] =
                        readWireWord (next :: labels) dirtyAt tail := by
                    exact readWireWord_upd_not_mem (next :: labels) dirtyAt tail
                      (dirtyAt label) _ hnodup'.1
                  simp only [upperReverseState, readWireWord, List.map_cons]
                  change
                    ((tail[dirtyAt label ↦ Bool.xor (tail (dirtyAt label))
                        (!bit && tail (dirtyAt next))]) (dirtyAt label) ::
                      readWireWord (next :: labels) dirtyAt
                        tail[dirtyAt label ↦ Bool.xor (tail (dirtyAt label))
                          (!bit && tail (dirtyAt next))]) = _
                  rw [upd_same, htailRead, htail]
                  simp only [upperDirtyReverse, List.headD_cons, List.tail_cons]
                  rw [show tail (dirtyAt label) = state (dirtyAt label) by
                    exact hhead, hnext]
                  rfl

theorem readWireWord_upperMapStateSeed
    (seed : Bool) (bits : List Bool) (labels : List Nat)
    (dirtyAt : Nat → Wire) (state : BasisState)
    (hlength : bits.length = labels.length)
    (hnodup : (labels.map dirtyAt).Nodup) :
    readWireWord labels dirtyAt
        (upperMapStateSeed seed bits labels dirtyAt state) =
      upperDirtyMapSeed seed bits (readWireWord labels dirtyAt state) := by
  rw [upperMapStateSeed,
    readWireWord_upperReverseState bits labels dirtyAt _ hlength hnodup,
    readWireWord_upperForwardStateSeed seed bits labels dirtyAt state hlength hnodup]
  rfl

theorem readWireWord_upperMapStateSeed_flags
    (seed : Bool) (bits : List Bool) (labels : List Nat)
    (dirtyAt : Nat → Wire) (state : BasisState)
    (hlength : bits.length = labels.length)
    (hnodup : (labels.map dirtyAt).Nodup) :
    readWireWord labels dirtyAt
        (upperMapStateSeed seed bits labels dirtyAt state) =
      xorWords (readWireWord labels dirtyAt state)
        (gateWord seed (suffixZeroFlags bits)) := by
  rw [readWireWord_upperMapStateSeed seed bits labels dirtyAt state hlength hnodup,
    upperDirtyMapSeed_eq_xor_suffixZeroFlags]
  exact hlength.trans (by simp [readWireWord])

/-- Complete lower map, obtained by applying the same recurrence to the reversed banks. -/
def lowerDirtyMap (bits dirty : List Bool) : List Bool :=
  (upperDirtyMap bits.reverse dirty.reverse).reverse

/-- First lower pass, expressed as the upper first pass over the reversed banks. -/
def lowerDirtyForwardSeed (seed : Bool) (bits dirty : List Bool) : List Bool :=
  (upperDirtyForwardSeed seed bits.reverse dirty.reverse).reverse

/-- Second lower pass, likewise mirrored through the reversed banks. -/
def lowerDirtyReverse (bits dirty : List Bool) : List Bool :=
  (upperDirtyReverse bits.reverse dirty.reverse).reverse

/-- Complete externally seeded lower map. -/
def lowerDirtyMapSeed (seed : Bool) (bits dirty : List Bool) : List Bool :=
  lowerDirtyReverse bits (lowerDirtyForwardSeed seed bits dirty)

/-- Prefix-zero flags, ordered like the input word. -/
def prefixZeroFlags (bits : List Bool) : List Bool :=
  (suffixZeroFlags bits.reverse).reverse

@[simp]
theorem prefixZeroFlags_length (bits : List Bool) :
    (prefixZeroFlags bits).length = bits.length := by
  simp [prefixZeroFlags]

private theorem xorWords_reverse
    (left right : List Bool) (hlength : left.length = right.length) :
    (xorWords left right).reverse = xorWords left.reverse right.reverse := by
  exact List.reverse_zipWith hlength

/-- The mirror map XORs the prefix-zero flag into every dirty lane. -/
theorem lowerDirtyMap_eq_xor_prefixZeroFlags
    (bits dirty : List Bool) (hlength : bits.length = dirty.length) :
    lowerDirtyMap bits dirty = xorWords dirty (prefixZeroFlags bits) := by
  rw [lowerDirtyMap, upperDirtyMap_eq_xor_suffixZeroFlags]
  · rw [xorWords_reverse]
    · simp [prefixZeroFlags]
    · simpa using hlength.symm
  · simpa using hlength

/-- Seeded lower mirror: the external root gates the prefix-zero flags exactly. -/
theorem lowerDirtyMapSeed_eq_xor_prefixZeroFlags
    (seed : Bool) (bits dirty : List Bool)
    (hlength : bits.length = dirty.length) :
    lowerDirtyMapSeed seed bits dirty =
      xorWords dirty (gateWord seed (prefixZeroFlags bits)) := by
  have hreversed : bits.reverse.length = dirty.reverse.length := by
    simpa using hlength
  unfold lowerDirtyMapSeed lowerDirtyReverse lowerDirtyForwardSeed
  simp only [List.reverse_reverse]
  change (upperDirtyMapSeed seed bits.reverse dirty.reverse).reverse = _
  rw [upperDirtyMapSeed_eq_xor_suffixZeroFlags seed bits.reverse dirty.reverse hreversed]
  rw [xorWords_reverse]
  · simp [gateWord, prefixZeroFlags]
  · simpa [gateWord] using hlength.symm

/-! ## Literal zero-recurrence leaf cell -/

/-- One source recurrence cell.  `temporary` first receives `rangeControl AND bit`; the two X
gates make the middle Toffoli negatively controlled by that value, and the final Toffoli restores
the clean temporary.  `guard` is the neighbouring dirty lane, or the external root at the base. -/
def zeroRecurrenceCell
    (rangeControl bit guard target temporary : Wire) : Circuit :=
  [.CCX rangeControl bit temporary,
    .X temporary,
    .CCX temporary guard target,
    .X temporary,
    .CCX rangeControl bit temporary]

/-- Source-ordered base cell.  The supplement writes the external root control before the
temporary negative control in the middle Toffoli; non-base cells use `zeroRecurrenceCell` with
the temporary first and the neighbouring dirty lane second. -/
private def zeroRecurrenceBaseCell
    (rangeControl bit control target temporary : Wire) : Circuit :=
  [.CCX rangeControl bit temporary,
    .X temporary,
    .CCX control temporary target,
    .X temporary,
    .CCX rangeControl bit temporary]

/-- Direct Boolean state action of one recurrence cell. -/
def zeroRecurrenceCellState
    (rangeControl bit guard target : Wire) (state : BasisState) : BasisState :=
  state[target ↦ Bool.xor (state target)
    (!(state rangeControl && state bit) && state guard)]

theorem zeroRecurrenceCellState_preserves
    (rangeControl bit guard target wire : Wire) (state : BasisState)
    (hwire : wire ≠ target) :
    zeroRecurrenceCellState rangeControl bit guard target state wire = state wire := by
  simp [zeroRecurrenceCellState, upd, hwire]

/-- The literal five-gate cell restores its clean temporary and changes only the target lane. -/
theorem run_zeroRecurrenceCell
    (rangeControl bit guard target temporary : Wire) (state : BasisState)
    (hlayout : [rangeControl, bit, guard, target, temporary].Nodup)
    (hclean : state temporary = false) :
    Classical.run (zeroRecurrenceCell rangeControl bit guard target temporary) state =
      zeroRecurrenceCellState rangeControl bit guard target state := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hlayout
  funext wire
  by_cases hwireTarget : wire = target
  · subst wire
    cases hc : state rangeControl <;> cases hb : state bit <;>
      cases hg : state guard <;> cases ht : state target <;>
      simp_all [zeroRecurrenceCell, zeroRecurrenceCellState,
        Classical.run, Classical.applyGate, upd]
  · by_cases hwireTemporary : wire = temporary
    · subst wire
      cases hc : state rangeControl <;> cases hb : state bit <;>
        cases hg : state guard <;> cases ht : state target <;>
        simp_all [zeroRecurrenceCell, zeroRecurrenceCellState,
          Classical.run, Classical.applyGate, upd]
    · by_cases hwireControl : wire = rangeControl
      · subst wire
        simp_all [zeroRecurrenceCell, zeroRecurrenceCellState,
          Classical.run, Classical.applyGate, upd]
      · by_cases hwireBit : wire = bit
        · subst wire
          simp_all [zeroRecurrenceCell, zeroRecurrenceCellState,
            Classical.run, Classical.applyGate, upd]
        · by_cases hwireGuard : wire = guard
          · subst wire
            simp_all [zeroRecurrenceCell, zeroRecurrenceCellState,
              Classical.run, Classical.applyGate, upd]
          · simp [zeroRecurrenceCell, zeroRecurrenceCellState,
              Classical.run, Classical.applyGate, upd, hwireTarget, hwireTemporary]

private theorem run_zeroRecurrenceBaseCell
    (rangeControl bit control target temporary : Wire) (state : BasisState)
    (hlayout : [rangeControl, bit, control, target, temporary].Nodup)
    (hclean : state temporary = false) :
    Classical.run (zeroRecurrenceBaseCell rangeControl bit control target temporary) state =
      zeroRecurrenceCellState rangeControl bit control target state := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hlayout
  funext wire
  by_cases hwireTarget : wire = target
  · subst wire
    cases hc : state rangeControl <;> cases hb : state bit <;>
      cases hg : state control <;> cases ht : state target <;>
      simp_all [zeroRecurrenceBaseCell, zeroRecurrenceCellState,
        Classical.run, Classical.applyGate, upd]
  · by_cases hwireTemporary : wire = temporary
    · subst wire
      cases hc : state rangeControl <;> cases hb : state bit <;>
        cases hg : state control <;> cases ht : state target <;>
        simp_all [zeroRecurrenceBaseCell, zeroRecurrenceCellState,
          Classical.run, Classical.applyGate, upd]
    · by_cases hwireControl : wire = rangeControl
      · subst wire
        simp_all [zeroRecurrenceBaseCell, zeroRecurrenceCellState,
          Classical.run, Classical.applyGate, upd]
      · by_cases hwireBit : wire = bit
        · subst wire
          simp_all [zeroRecurrenceBaseCell, zeroRecurrenceCellState,
            Classical.run, Classical.applyGate, upd]
        · by_cases hwireGuard : wire = control
          · subst wire
            simp_all [zeroRecurrenceBaseCell, zeroRecurrenceCellState,
              Classical.run, Classical.applyGate, upd]
          · simp [zeroRecurrenceBaseCell, zeroRecurrenceCellState,
              Classical.run, Classical.applyGate, upd, hwireTarget, hwireTemporary]

theorem zeroRecurrenceCell_usesOnly
    (rangeControl bit guard target temporary : Wire) :
    PaperCircuitUsesOnly [rangeControl, bit, guard, target, temporary]
      (zeroRecurrenceCell rangeControl bit guard target temporary) := by
  simp [zeroRecurrenceCell, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

private theorem zeroRecurrenceBaseCell_usesOnly
    (rangeControl bit control target temporary : Wire) :
    PaperCircuitUsesOnly [rangeControl, bit, control, target, temporary]
      (zeroRecurrenceBaseCell rangeControl bit control target temporary) := by
  simp [zeroRecurrenceBaseCell, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

/-- A recurrence cell can only update its declared target and temporary wires. -/
theorem zeroRecurrenceCell_preserves
    (rangeControl bit guard target temporary wire : Wire)
    (hwireTarget : wire ≠ target) (hwireTemporary : wire ≠ temporary)
    (state : BasisState) :
    Classical.run (zeroRecurrenceCell rangeControl bit guard target temporary) state wire =
      state wire := by
  simp [zeroRecurrenceCell, Classical.run, Classical.applyGate, upd,
    hwireTarget, hwireTemporary]

private theorem zeroRecurrenceBaseCell_preserves
    (rangeControl bit control target temporary wire : Wire)
    (hwireTarget : wire ≠ target) (hwireTemporary : wire ≠ temporary)
    (state : BasisState) :
    Classical.run
      (zeroRecurrenceBaseCell rangeControl bit control target temporary) state wire =
      state wire := by
  simp [zeroRecurrenceBaseCell, Classical.run, Classical.applyGate, upd,
    hwireTarget, hwireTemporary]

@[simp]
theorem zeroRecurrenceCell_HPFree
    (rangeControl bit guard target temporary : Wire) :
    HPFree (zeroRecurrenceCell rangeControl bit guard target temporary) := by
  simp [zeroRecurrenceCell]

theorem zeroRecurrenceCell_wellFormed
    (rangeControl bit guard target temporary : Wire)
    (hlayout : [rangeControl, bit, guard, target, temporary].Nodup) :
    CircuitWellFormed
      (zeroRecurrenceCell rangeControl bit guard target temporary) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hlayout
  simp_all [zeroRecurrenceCell, CircuitWellFormed, Gate.WellFormed,
    Ne.symm]

private theorem zeroRecurrenceBaseCell_wellFormed
    (rangeControl bit control target temporary : Wire)
    (hlayout : [rangeControl, bit, control, target, temporary].Nodup) :
    CircuitWellFormed
      (zeroRecurrenceBaseCell rangeControl bit control target temporary) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hlayout
  simp_all [zeroRecurrenceBaseCell, CircuitWellFormed, Gate.WellFormed,
    Ne.symm]

@[simp]
theorem zeroRecurrenceCell_toffoliCount
    (rangeControl bit guard target temporary : Wire) :
    eeaToffoliCount
      (zeroRecurrenceCell rangeControl bit guard target temporary) = 3 := rfl

@[simp]
theorem zeroRecurrenceCell_cnotCount
    (rangeControl bit guard target temporary : Wire) :
    eeaCnotCount
      (zeroRecurrenceCell rangeControl bit guard target temporary) = 0 := rfl

@[simp]
theorem zeroRecurrenceCell_tCount
    (rangeControl bit guard target temporary : Wire) :
    ShorECDLP.tCount
      (zeroRecurrenceCell rangeControl bit guard target temporary) = 21 := rfl

/-! ## Source range-scan wrapper -/

/-- One wrapped leaf of `range_scan_leq` / `range_scan_geq`.  In the two source directions with
an initially seeded accumulator the equality pulse follows the arithmetic leaf; in the other two
directions it precedes it. -/
def rangeScanLeafAction
    (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leafAction : Nat → Wire → Circuit)
    (label : Nat) (equalityControl : Wire) : Circuit :=
  if toggleAfter then
    leafAction label rangeAccumulator ++ [.CX equalityControl rangeAccumulator]
  else
    [.CX equalityControl rangeAccumulator] ++ leafAction label rangeAccumulator

/-- Decoder-erased meaning of one wrapped range-scan leaf. -/
def rangeScanLogicalLeafState
    (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leafAction : Nat → Wire → Circuit)
    (label : Nat) (equalityPulse : Bool) (state : BasisState) : BasisState :=
  if toggleAfter then
    let after := Classical.run (leafAction label rangeAccumulator) state
    after[rangeAccumulator ↦ Bool.xor (after rangeAccumulator) equalityPulse]
  else
    Classical.run (leafAction label rangeAccumulator)
      (state[rangeAccumulator ↦ Bool.xor (state rangeAccumulator) equalityPulse])

/-- Same decoder-erased wrapper around a proved state transformer rather than a circuit. -/
def rangeScanDirectLeafState
    (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leafState : Nat → BasisState → BasisState)
    (label : Nat) (equalityPulse : Bool) (state : BasisState) : BasisState :=
  if toggleAfter then
    let after := leafState label state
    after[rangeAccumulator ↦ Bool.xor (after rangeAccumulator) equalityPulse]
  else
    leafState label
      (state[rangeAccumulator ↦ Bool.xor (state rangeAccumulator) equalityPulse])

private theorem foldl_rangeScanLogical_eq_direct
    (toggleAfter : Bool) (rangeAccumulator temporary : Wire)
    (leafAction : Nat → Wire → Circuit)
    (leafState : Nat → BasisState → BasisState)
    (pulses : List (Nat × Bool)) (state : BasisState)
    (hrangeTemporary : rangeAccumulator ≠ temporary)
    (hrun : ∀ label state', state' temporary = false →
      Classical.run (leafAction label rangeAccumulator) state' = leafState label state')
    (hpreserve : ∀ label state', leafState label state' temporary = state' temporary)
    (hclean : state temporary = false) :
    pulses.foldl
        (fun current pulse =>
          rangeScanLogicalLeafState toggleAfter rangeAccumulator leafAction
            pulse.1 pulse.2 current) state =
      pulses.foldl
        (fun current pulse =>
          rangeScanDirectLeafState toggleAfter rangeAccumulator leafState
            pulse.1 pulse.2 current) state := by
  induction pulses generalizing state with
  | nil => rfl
  | cons pulse pulses ih =>
      cases toggleAfter with
      | false =>
          let updated := state[rangeAccumulator ↦
            Bool.xor (state rangeAccumulator) pulse.2]
          have hcleanUpdated : updated temporary = false := by
            simp only [updated]
            rw [upd_other state rangeAccumulator _ (Ne.symm hrangeTemporary)]
            exact hclean
          have hstep :
              rangeScanLogicalLeafState false rangeAccumulator leafAction
                  pulse.1 pulse.2 state =
                rangeScanDirectLeafState false rangeAccumulator leafState
                  pulse.1 pulse.2 state := by
            simp [rangeScanLogicalLeafState, rangeScanDirectLeafState,
              updated, hrun pulse.1 updated hcleanUpdated]
          simp only [List.foldl_cons, hstep]
          apply ih
          change leafState pulse.1 updated temporary = false
          rw [hpreserve]
          exact hcleanUpdated
      | true =>
          have hstep :
              rangeScanLogicalLeafState true rangeAccumulator leafAction
                  pulse.1 pulse.2 state =
                rangeScanDirectLeafState true rangeAccumulator leafState
                  pulse.1 pulse.2 state := by
            simp [rangeScanLogicalLeafState, rangeScanDirectLeafState,
              hrun pulse.1 state hclean]
          simp only [List.foldl_cons, hstep]
          apply ih
          change
            (leafState pulse.1 state)[rangeAccumulator ↦
              Bool.xor (leafState pulse.1 state rangeAccumulator) pulse.2]
                temporary = false
          rw [upd_other _ rangeAccumulator _ (Ne.symm hrangeTemporary),
            hpreserve, hclean]

private theorem foldl_rangeScanDirect_preserves
    (toggleAfter : Bool) (rangeAccumulator wire : Wire)
    (leafState : Nat → BasisState → BasisState)
    (pulses : List (Nat × Bool)) (state : BasisState)
    (hwireRange : wire ≠ rangeAccumulator)
    (hleaf : ∀ label state', leafState label state' wire = state' wire) :
    pulses.foldl
        (fun current pulse =>
          rangeScanDirectLeafState toggleAfter rangeAccumulator leafState
            pulse.1 pulse.2 current) state wire =
      state wire := by
  induction pulses generalizing state with
  | nil => rfl
  | cons pulse pulses ih =>
      rw [List.foldl_cons, ih]
      cases toggleAfter <;>
        simp [rangeScanDirectLeafState, hleaf, upd, hwireRange]

private theorem foldl_rangeScanDirect_preserves_of_mem
    (toggleAfter : Bool) (rangeAccumulator wire : Wire)
    (leafState : Nat → BasisState → BasisState)
    (pulses : List (Nat × Bool)) (state : BasisState)
    (hwireRange : wire ≠ rangeAccumulator)
    (hleaf : ∀ label, label ∈ pulses.map Prod.fst → ∀ state',
      leafState label state' wire = state' wire) :
    pulses.foldl
        (fun current pulse =>
          rangeScanDirectLeafState toggleAfter rangeAccumulator leafState
            pulse.1 pulse.2 current) state wire =
      state wire := by
  induction pulses generalizing state with
  | nil => rfl
  | cons pulse pulses ih =>
      rw [List.foldl_cons, ih]
      · cases toggleAfter <;>
          simp [rangeScanDirectLeafState,
            hleaf pulse.1 (by simp), upd, hwireRange]
      · intro label hlabel state'
        exact hleaf label (by simp [hlabel]) state'

private theorem foldl_rangeScanDirect_range
    (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leafState : Nat → BasisState → BasisState)
    (pulses : List (Nat × Bool)) (state : BasisState)
    (hleaf : ∀ label state',
      leafState label state' rangeAccumulator = state' rangeAccumulator) :
    pulses.foldl
        (fun current pulse =>
          rangeScanDirectLeafState toggleAfter rangeAccumulator leafState
            pulse.1 pulse.2 current) state rangeAccumulator =
      pulses.foldl (fun current pulse => Bool.xor current pulse.2)
        (state rangeAccumulator) := by
  induction pulses generalizing state with
  | nil => rfl
  | cons pulse pulses ih =>
      rw [List.foldl_cons, ih, List.foldl_cons]
      cases toggleAfter <;>
        simp [rangeScanDirectLeafState, hleaf, upd]

/-- The common literal source skeleton.  `toggleAfter=true` is `leq/inc` or `geq/dec`: seed the
range accumulator, visit every leaf, and turn it off after the boundary.  `false` is the mirrored
turn-on-before-boundary traversal followed by accumulator cleanup. -/
def rangeScanUnitary
    (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire)
    (path : List Wire) (leafAction : Nat → Wire → Circuit) : Circuit :=
  if toggleAfter then
    [.CX control rangeAccumulator] ++
      unaryActionUnitary order
        (rangeScanLeafAction true rangeAccumulator leafAction) tree control path
  else
    unaryActionUnitary order
        (rangeScanLeafAction false rangeAccumulator leafAction) tree control path ++
      [.CX control rangeAccumulator]

private theorem unaryActionUnitary_usesOnly_of
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (path support : List Wire)
    (hcontrol : control ∈ support)
    (hindices : ∀ wire, wire ∈ tree.indexWires → wire ∈ support)
    (hpath : ∀ wire, wire ∈ path → wire ∈ support)
    (hleaf : ∀ label, label ∈ tree.labels → ∀ dynamic,
      dynamic ∈ support →
        PaperCircuitUsesOnly support (leafAction label dynamic)) :
    PaperCircuitUsesOnly support
      (unaryActionUnitary order leafAction tree control path) := by
  induction tree generalizing control path with
  | leaf label =>
      exact hleaf label (by simp [UnaryActionTree.labels]) control hcontrol
  | node indexBit zero one ihZero ihOne =>
      cases path with
      | nil => simp [unaryActionUnitary, PaperCircuitUsesOnly]
      | cons path rest =>
          have hindex : indexBit ∈ support :=
            hindices indexBit (by simp [UnaryActionTree.indexWires])
          have hpathHead : path ∈ support := hpath path (by simp)
          have hrest : ∀ wire, wire ∈ rest → wire ∈ support := by
            intro wire hwire
            exact hpath wire (by simp [hwire])
          have hzeroIndices : ∀ wire, wire ∈ zero.indexWires → wire ∈ support := by
            intro wire hwire
            exact hindices wire (by simp [UnaryActionTree.indexWires, hwire])
          have honeIndices : ∀ wire, wire ∈ one.indexWires → wire ∈ support := by
            intro wire hwire
            exact hindices wire (by simp [UnaryActionTree.indexWires, hwire])
          have hzeroLeaf : ∀ label, label ∈ zero.labels → ∀ dynamic,
              dynamic ∈ support →
                PaperCircuitUsesOnly support (leafAction label dynamic) := by
            intro label hlabel dynamic hdynamic
            exact hleaf label (by simp [UnaryActionTree.labels, hlabel]) dynamic hdynamic
          have honeLeaf : ∀ label, label ∈ one.labels → ∀ dynamic,
              dynamic ∈ support →
                PaperCircuitUsesOnly support (leafAction label dynamic) := by
            intro label hlabel dynamic hdynamic
            exact hleaf label (by simp [UnaryActionTree.labels, hlabel]) dynamic hdynamic
          have hzero := ihZero path rest hpathHead hzeroIndices hrest hzeroLeaf
          have hone := ihOne path rest hpathHead honeIndices hrest honeLeaf
          have hcompute : PaperCircuitUsesOnly support
              (computeZeroAnd control indexBit path) := by
            simp [computeZeroAnd, PaperCircuitUsesOnly, PaperGateUsesOnly,
              gateWires, hcontrol, hindex, hpathHead]
          have htoggle : PaperCircuitUsesOnly support
              ([.CX control path] : Circuit) := by
            simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires,
              hcontrol, hpathHead]
          cases order with
          | inc =>
              rw [unaryActionUnitary]
              have hempty : PaperCircuitUsesOnly support ([] : Circuit) := by
                simp [PaperCircuitUsesOnly]
              exact hcompute.append
                (((((hempty.append hzero).append htoggle).append hone).append
                  htoggle).append hcompute)
          | dec =>
              rw [unaryActionUnitary]
              have hempty : PaperCircuitUsesOnly support ([] : Circuit) := by
                simp [PaperCircuitUsesOnly]
              exact hcompute.append
                (((((hempty.append htoggle).append hone).append htoggle).append
                  hzero).append hcompute)

private theorem rangeScanUnitary_usesOnly_of
    (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire)
    (path support : List Wire) (leafAction : Nat → Wire → Circuit)
    (hcontrol : control ∈ support)
    (hrange : rangeAccumulator ∈ support)
    (hindices : ∀ wire, wire ∈ tree.indexWires → wire ∈ support)
    (hpath : ∀ wire, wire ∈ path → wire ∈ support)
    (hleaf : ∀ label,
      PaperCircuitUsesOnly support (leafAction label rangeAccumulator)) :
    PaperCircuitUsesOnly support
      (rangeScanUnitary toggleAfter order tree control rangeAccumulator path leafAction) := by
  have hwrapped : ∀ label, label ∈ tree.labels → ∀ dynamic,
      dynamic ∈ support →
        PaperCircuitUsesOnly support
          (rangeScanLeafAction toggleAfter rangeAccumulator leafAction label dynamic) := by
    intro label _ dynamic hdynamic
    have htoggle : PaperCircuitUsesOnly support
        ([.CX dynamic rangeAccumulator] : Circuit) := by
      simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires, hdynamic, hrange]
    cases toggleAfter <;>
      simp only [rangeScanLeafAction, Bool.false_eq_true, if_false,
        if_true] <;>
      first | exact htoggle.append (hleaf label) | exact (hleaf label).append htoggle
  have hunary := unaryActionUnitary_usesOnly_of order
    (rangeScanLeafAction toggleAfter rangeAccumulator leafAction)
    tree control path support hcontrol hindices hpath hwrapped
  have houter : PaperCircuitUsesOnly support
      ([.CX control rangeAccumulator] : Circuit) := by
    simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires, hcontrol, hrange]
  cases toggleAfter <;>
    simp only [rangeScanUnitary, Bool.false_eq_true, if_false, if_true] <;>
    first | exact hunary.append houter | exact houter.append hunary

private theorem rangeScanUnitary_HPFree_of
    (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire)
    (path : List Wire) (leafAction : Nat → Wire → Circuit)
    (hleaf : ∀ label, HPFree (leafAction label rangeAccumulator)) :
    HPFree
      (rangeScanUnitary toggleAfter order tree control rangeAccumulator path leafAction) := by
  have hwrapped : UnaryLeafHPFree
      (rangeScanLeafAction toggleAfter rangeAccumulator leafAction) := by
    intro label dynamic
    cases toggleAfter <;>
      simp [rangeScanLeafAction, hleaf]
  have hunary := unaryActionUnitary_HPFree order
    (rangeScanLeafAction toggleAfter rangeAccumulator leafAction)
    tree control path hwrapped
  cases toggleAfter <;>
    simp [rangeScanUnitary, hunary]

private theorem rangeScanUnitary_wellFormed_of
    (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire)
    (path : List Wire) (leafAction : Nat → Wire → Circuit)
    (hlayout : tree.Layout control path)
    (hrange : rangeAccumulator ∉ control :: tree.indexWires.dedup ++ path)
    (hleaf : ∀ label, label ∈ tree.labels →
      CircuitWellFormed (leafAction label rangeAccumulator)) :
    CircuitWellFormed
      (rangeScanUnitary toggleAfter order tree control rangeAccumulator path leafAction) := by
  have hwrapped : UnaryLeafWellFormed
      (rangeScanLeafAction toggleAfter rangeAccumulator leafAction)
      tree (control :: tree.indexWires.dedup ++ path) := by
    intro label hlabel dynamic hdynamic
    have hne : dynamic ≠ rangeAccumulator := by
      intro equality
      subst dynamic
      exact hrange hdynamic
    have htoggle : CircuitWellFormed
        ([.CX dynamic rangeAccumulator] : Circuit) := by
      simp [CircuitWellFormed, Gate.WellFormed, hne]
    cases toggleAfter <;>
      simp only [rangeScanLeafAction, Bool.false_eq_true, if_false,
        if_true, circuitWellFormed_append] <;>
      first | exact ⟨htoggle, hleaf label hlabel⟩ |
        exact ⟨hleaf label hlabel, htoggle⟩
  have hunary := unaryActionUnitary_wellFormed order
    (rangeScanLeafAction toggleAfter rangeAccumulator leafAction)
    tree control path hlayout hwrapped
  have hcontrolRange : control ≠ rangeAccumulator := by
    intro equality
    subst control
    exact hrange (by simp)
  have houter : CircuitWellFormed
      ([.CX control rangeAccumulator] : Circuit) := by
    simp [CircuitWellFormed, Gate.WellFormed, hcontrolRange]
  cases toggleAfter <;>
    simp only [rangeScanUnitary, Bool.false_eq_true, if_false, if_true,
      circuitWellFormed_append] <;>
    first | exact ⟨hunary, houter⟩ | exact ⟨houter, hunary⟩

@[simp]
theorem rangeScanLeafAction_toffoliCount
    (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leafAction : Nat → Wire → Circuit) (label : Nat) (dynamic : Wire) :
    eeaToffoliCount
        (rangeScanLeafAction toggleAfter rangeAccumulator leafAction label dynamic) =
      eeaToffoliCount (leafAction label rangeAccumulator) := by
  cases toggleAfter <;>
    simp [rangeScanLeafAction, eeaToffoliCount]

@[simp]
theorem rangeScanLeafAction_cnotCount
    (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leafAction : Nat → Wire → Circuit) (label : Nat) (dynamic : Wire) :
    eeaCnotCount
        (rangeScanLeafAction toggleAfter rangeAccumulator leafAction label dynamic) =
      eeaCnotCount (leafAction label rangeAccumulator) + 1 := by
  cases toggleAfter with
  | false =>
      simp [rangeScanLeafAction, eeaCnotCount]
      omega
  | true => simp [rangeScanLeafAction, eeaCnotCount]

@[simp]
theorem rangeScanLeafAction_tCount
    (toggleAfter : Bool) (rangeAccumulator : Wire)
    (leafAction : Nat → Wire → Circuit) (label : Nat) (dynamic : Wire) :
    ShorECDLP.tCount
        (rangeScanLeafAction toggleAfter rangeAccumulator leafAction label dynamic) =
      ShorECDLP.tCount (leafAction label rangeAccumulator) := by
  cases toggleAfter <;>
    simp [rangeScanLeafAction, ShorECDLP.tCount, tCost]

/-- Constructor-derived Toffoli count for either literal range scan. -/
theorem rangeScanUnitary_toffoliCount
    (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire)
    (path : List Wire) (leafAction : Nat → Wire → Circuit)
    (hlayout : tree.Layout control path) :
    eeaToffoliCount
        (rangeScanUnitary toggleAfter order tree control rangeAccumulator path leafAction) =
      tree.leafCostSum
          (fun label _ ↦ eeaToffoliCount (leafAction label rangeAccumulator))
          control path +
        2 * tree.internalNodes := by
  have houter : eeaToffoliCount
      ([.CX control rangeAccumulator] : Circuit) = 0 := rfl
  cases toggleAfter with
  | false =>
      change eeaToffoliCount
          (unaryActionUnitary order
              (rangeScanLeafAction false rangeAccumulator leafAction)
              tree control path ++ [.CX control rangeAccumulator]) = _
      rw [eeaToffoliCount_append,
        unaryActionUnitary_toffoliCount order
          (rangeScanLeafAction false rangeAccumulator leafAction)
          tree control path hlayout, houter]
      simp
  | true =>
      change eeaToffoliCount
          (([.CX control rangeAccumulator] : Circuit) ++
            unaryActionUnitary order
              (rangeScanLeafAction true rangeAccumulator leafAction)
              tree control path) = _
      rw [eeaToffoliCount_append, houter,
        unaryActionUnitary_toffoliCount order
          (rangeScanLeafAction true rangeAccumulator leafAction)
          tree control path hlayout]
      simp

/-- Constructor-derived CNOT count, including one range toggle at every leaf and one outer seed
or cleanup toggle. -/
theorem rangeScanUnitary_cnotCount
    (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire)
    (path : List Wire) (leafAction : Nat → Wire → Circuit)
    (hlayout : tree.Layout control path) :
    eeaCnotCount
        (rangeScanUnitary toggleAfter order tree control rangeAccumulator path leafAction) =
      1 + tree.leafCostSum
          (fun label _ ↦ eeaCnotCount (leafAction label rangeAccumulator) + 1)
          control path +
        2 * tree.internalNodes := by
  have houter : eeaCnotCount
      ([.CX control rangeAccumulator] : Circuit) = 1 := rfl
  cases toggleAfter with
  | false =>
      change eeaCnotCount
          (unaryActionUnitary order
              (rangeScanLeafAction false rangeAccumulator leafAction)
              tree control path ++ [.CX control rangeAccumulator]) = _
      rw [eeaCnotCount_append,
        unaryActionUnitary_cnotCount order
          (rangeScanLeafAction false rangeAccumulator leafAction)
          tree control path hlayout, houter]
      simp
      omega
  | true =>
      change eeaCnotCount
          (([.CX control rangeAccumulator] : Circuit) ++
            unaryActionUnitary order
              (rangeScanLeafAction true rangeAccumulator leafAction)
              tree control path) = _
      rw [eeaCnotCount_append, houter,
        unaryActionUnitary_cnotCount order
          (rangeScanLeafAction true rangeAccumulator leafAction)
          tree control path hlayout]
      simp
      omega

/-- Constructor-derived coherent T count for either literal range scan. -/
theorem rangeScanUnitary_tCount
    (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire)
    (path : List Wire) (leafAction : Nat → Wire → Circuit)
    (hlayout : tree.Layout control path) :
    ShorECDLP.tCount
        (rangeScanUnitary toggleAfter order tree control rangeAccumulator path leafAction) =
      tree.leafCostSum
          (fun label _ ↦ ShorECDLP.tCount (leafAction label rangeAccumulator))
          control path +
        14 * tree.internalNodes := by
  have houter : ShorECDLP.tCount
      ([.CX control rangeAccumulator] : Circuit) = 0 := rfl
  cases toggleAfter with
  | false =>
      change ShorECDLP.tCount
          (unaryActionUnitary order
              (rangeScanLeafAction false rangeAccumulator leafAction)
              tree control path ++ [.CX control rangeAccumulator]) = _
      rw [tCount_append,
        unaryActionUnitary_tCount order
          (rangeScanLeafAction false rangeAccumulator leafAction)
          tree control path hlayout, houter]
      simp
  | true =>
      change ShorECDLP.tCount
          (([.CX control rangeAccumulator] : Circuit) ++
            unaryActionUnitary order
              (rangeScanLeafAction true rangeAccumulator leafAction)
              tree control path) = _
      rw [tCount_append, houter,
        unaryActionUnitary_tCount order
          (rangeScanLeafAction true rangeAccumulator leafAction)
          tree control path hlayout]
      simp

private theorem run_agreesOutside_of_usesOnly
    (support protectedWires : List Wire) (circuit : Circuit)
    (stableRoot : Wire) (left right : BasisState)
    (huses : PaperCircuitUsesOnly support circuit)
    (hshared : ∀ wire, wire ∈ protectedWires → wire ∈ support →
      wire = stableRoot)
    (houtside : AgreesOutside protectedWires left right)
    (hstable : left stableRoot = right stableRoot) :
    AgreesOutside protectedWires
      (Classical.run circuit left) (Classical.run circuit right) := by
  intro wire hwire
  by_cases hsupport : wire ∈ support
  · exact huses.run_congrOn left right (by
      intro used hused
      by_cases hprotected : used ∈ protectedWires
      · rw [hshared used hprotected hused]
        exact hstable
      · exact houtside used hprotected) wire hsupport
  · rw [huses.preservesOutside left hsupport,
      huses.preservesOutside right hsupport]
    exact houtside wire hwire

private theorem updateBoth_agreesOutside
    (protectedWires : List Wire) (left right : BasisState)
    (target : Wire) (leftValue rightValue : Bool)
    (houtside : AgreesOutside protectedWires left right)
    (hvalue : leftValue = rightValue) :
    AgreesOutside protectedWires
      (left[target ↦ leftValue]) (right[target ↦ rightValue]) := by
  intro wire hwire
  by_cases hwt : wire = target
  · subst wire
    simpa [upd] using hvalue
  · simp [upd, hwt, houtside wire hwire]

/-- Direct ordered logical-trace semantics of the common range-scan skeleton.  The assumptions
say only that arithmetic leaves stay within a data footprint disjoint from the unary decoder. -/
theorem run_rangeScanUnitary
    (toggleAfter : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control rangeAccumulator : Wire)
    (path protectedWires dataWires : List Wire)
    (leafAction : Nat → Wire → Circuit) (state : BasisState)
    (hlayout : tree.Layout control path)
    (hroles : ∀ wire,
      wire ∈ control :: tree.indexWires.dedup ++ path →
        wire ∈ protectedWires)
    (hrangeProtected : rangeAccumulator ∉ protectedWires)
    (hshared : ∀ wire, wire ∈ protectedWires → wire ∈ dataWires →
      wire = control)
    (hleafUses : ∀ label,
      PaperCircuitUsesOnly dataWires (leafAction label rangeAccumulator))
    (hleafControl : ∀ label state',
      Classical.run (leafAction label rangeAccumulator) state' control = state' control)
    (hclean : Clean path state) :
    Classical.run
        (rangeScanUnitary toggleAfter order tree control rangeAccumulator path leafAction)
        state =
      if toggleAfter then
        let seeded := state[rangeAccumulator ↦
          Bool.xor (state rangeAccumulator) (state control)]
        tree.runLogicalTree order
          (rangeScanLogicalLeafState true rangeAccumulator leafAction)
          (state control) seeded seeded
      else
        let traced := tree.runLogicalTree order
          (rangeScanLogicalLeafState false rangeAccumulator leafAction)
          (state control) state state
        traced[rangeAccumulator ↦
          Bool.xor (traced rangeAccumulator) (traced control)] := by
  have hcontrolRange : control ≠ rangeAccumulator := by
    intro equality
    subst control
    exact hrangeProtected (hroles rangeAccumulator (by simp))
  have hleafDataProtected : ∀ label state' wire, wire ∈ protectedWires →
      Classical.run (leafAction label rangeAccumulator) state' wire = state' wire := by
    intro label state' wire hwire
    by_cases hwc : wire = control
    · subst wire
      exact hleafControl label state'
    · apply (hleafUses label).preservesOutside
      intro hdata
      exact hwc (hshared wire hwire hdata)
  have hleafPreserves :
      UnaryLeafPreserves
        (rangeScanLeafAction toggleAfter rangeAccumulator leafAction)
        protectedWires := by
    intro label equalityControl hequality state' wire hwire
    have heqRange : equalityControl ≠ rangeAccumulator := by
      intro equality
      subst equalityControl
      exact hrangeProtected hequality
    have hwireRange : wire ≠ rangeAccumulator := by
      intro equality
      subst wire
      exact hrangeProtected hwire
    have hleafOutside := hleafDataProtected label state' wire hwire
    cases toggleAfter with
    | false =>
        rw [rangeScanLeafAction, if_neg (by decide), Classical.run_append]
        rw [hleafDataProtected label _ wire hwire]
        simp [Classical.run, Classical.applyGate, upd, hwireRange]
    | true =>
        rw [rangeScanLeafAction, if_pos (by decide), Classical.run_append]
        change Classical.applyGate (.CX equalityControl rangeAccumulator)
          (Classical.run (leafAction label rangeAccumulator) state') wire = state' wire
        simp only [Classical.applyGate]
        rw [upd_other _ rangeAccumulator _ hwireRange]
        exact hleafOutside
  let physicalLeafState := fun label equalityControl state' =>
    Classical.run
      (rangeScanLeafAction toggleAfter rangeAccumulator leafAction
        label equalityControl) state'
  have hruns : UnaryLeafRunsAs
      (rangeScanLeafAction toggleAfter rangeAccumulator leafAction)
      physicalLeafState := by
    intro label equalityControl state'
    rfl
  have hlogical : UnaryLeafRunsLogically physicalLeafState
      (rangeScanLogicalLeafState toggleAfter rangeAccumulator leafAction)
      protectedWires := by
    intro label equalityControl hequality state'
    have heqRange : equalityControl ≠ rangeAccumulator := by
      intro equality
      subst equalityControl
      exact hrangeProtected hequality
    cases toggleAfter with
    | false =>
        simp only [physicalLeafState]
        rw [rangeScanLeafAction, if_neg (by decide), Classical.run_append,
          rangeScanLogicalLeafState, if_neg (by decide)]
        rfl
    | true =>
        simp only [physicalLeafState]
        rw [rangeScanLeafAction, if_pos (by decide),
          rangeScanLogicalLeafState, if_pos (by decide), Classical.run_append]
        have hequalityOutside :=
          hleafDataProtected label state' equalityControl hequality
        change Classical.applyGate (.CX equalityControl rangeAccumulator)
            (Classical.run (leafAction label rangeAccumulator) state') =
          (Classical.run (leafAction label rangeAccumulator) state')
            [rangeAccumulator ↦ Bool.xor
              (Classical.run (leafAction label rangeAccumulator) state' rangeAccumulator)
              (state' equalityControl)]
        simp only [Classical.applyGate]
        rw [hequalityOutside]
  have hlogicalPreserves : LogicalLeafPreserves
      (rangeScanLogicalLeafState toggleAfter rangeAccumulator leafAction)
      protectedWires := by
    intro label pulse state' wire hwire
    have hwireRange : wire ≠ rangeAccumulator := by
      intro equality
      subst wire
      exact hrangeProtected hwire
    have hleafOutside := hleafDataProtected label state' wire hwire
    cases toggleAfter with
    | false =>
        rw [rangeScanLogicalLeafState, if_neg (by decide),
          hleafDataProtected label _ wire hwire]
        simp [upd, hwireRange]
    | true =>
        rw [rangeScanLogicalLeafState, if_pos (by decide)]
        rw [upd_other _ rangeAccumulator _ (by
          intro equality
          subst wire
          exact hrangeProtected hwire)]
        exact hleafOutside
  have hlogicalOutside : LogicalLeafRespectsOutside
      (rangeScanLogicalLeafState toggleAfter rangeAccumulator leafAction)
      protectedWires control := by
    intro label pulse left right houtside hcontrolAgreement
    have hrunOutside := run_agreesOutside_of_usesOnly
      dataWires protectedWires (leafAction label rangeAccumulator)
      control left right (hleafUses label) hshared houtside hcontrolAgreement
    cases toggleAfter with
    | false =>
        rw [rangeScanLogicalLeafState, if_neg (by decide)]
        apply run_agreesOutside_of_usesOnly dataWires protectedWires
          (leafAction label rangeAccumulator) control _ _ (hleafUses label) hshared
        apply updateBoth_agreesOutside protectedWires left right
          rangeAccumulator _ _ houtside
        rw [houtside rangeAccumulator hrangeProtected]
        simpa [upd, hcontrolRange] using hcontrolAgreement
    | true =>
        rw [rangeScanLogicalLeafState, if_pos (by decide)]
        apply updateBoth_agreesOutside protectedWires _ _
          rangeAccumulator _ _ hrunOutside
        rw [hrunOutside rangeAccumulator hrangeProtected]
  cases toggleAfter with
  | false =>
      rw [rangeScanUnitary, if_neg (by decide), Classical.run_append]
      let traced := Classical.run
        (unaryActionUnitary order
          (rangeScanLeafAction false rangeAccumulator leafAction)
          tree control path) state
      have htrace := run_unaryActionUnitary_as_runLogicalTree order
        (rangeScanLeafAction false rangeAccumulator leafAction)
        physicalLeafState
        (rangeScanLogicalLeafState false rangeAccumulator leafAction)
        tree control path protectedWires state hlayout hruns hlogical
        hleafPreserves hlogicalPreserves hlogicalOutside hroles hclean
      rw [htrace]
      simp [Classical.run, Classical.applyGate]
  | true =>
      rw [rangeScanUnitary, if_pos (by decide), Classical.run_append]
      let seeded := Classical.run [.CX control rangeAccumulator] state
      have hseeded : seeded =
          state[rangeAccumulator ↦
            Bool.xor (state rangeAccumulator) (state control)] := rfl
      have hcleanSeeded : Clean path seeded := by
        intro wire hwire
        rw [hseeded, upd_other state rangeAccumulator _ (by
          intro equality
          subst wire
          exact hrangeProtected (hroles rangeAccumulator (by simp [hwire])))]
        exact hclean wire hwire
      have hcontrolSeeded : seeded control = state control := by
        rw [hseeded, upd_other state rangeAccumulator _ (by
          intro equality
          subst control
          exact hrangeProtected (hroles rangeAccumulator (by simp)))]
      have htrace := run_unaryActionUnitary_as_runLogicalTree order
        (rangeScanLeafAction true rangeAccumulator leafAction)
        physicalLeafState
        (rangeScanLogicalLeafState true rangeAccumulator leafAction)
        tree control path protectedWires seeded hlayout hruns hlogical
        hleafPreserves hlogicalPreserves hlogicalOutside hroles hcleanSeeded
      rw [hcontrolSeeded] at htrace
      simpa only [seeded, hseeded, if_true] using htrace

/-! ## Literal upper and lower zero maps -/

/-- Inclusive source labels `k, ..., K`. -/
def zeroMapLabels (k K : Nat) : List Nat :=
  (List.range (K + 1 - k)).map fun offset => k + offset

theorem zeroMapLabels_eq_range' (k K : Nat) :
    zeroMapLabels k K = List.range' k (K + 1 - k) := by
  simp only [zeroMapLabels, List.range'_eq_map_range]

@[simp]
theorem zeroMapLabels_self (k : Nat) :
    zeroMapLabels k k = [k] := by
  simp [zeroMapLabels_eq_range']

theorem zeroMapLabels_cons {k K : Nat} (hkK : k < K) :
    zeroMapLabels k K = k :: zeroMapLabels (k + 1) K := by
  rw [zeroMapLabels_eq_range', zeroMapLabels_eq_range']
  have hlength : K + 1 - k = (K + 1 - (k + 1)) + 1 := by omega
  rw [hlength, List.range'_succ]

theorem zeroMapLabels_snoc {k K : Nat} (hkK : k ≤ K) :
    zeroMapLabels k (K + 1) = zeroMapLabels k K ++ [K + 1] := by
  rw [zeroMapLabels_eq_range', zeroMapLabels_eq_range']
  have hlength : K + 1 + 1 - k = (K + 1 - k) + 1 := by omega
  rw [hlength, ← List.range'_append_1]
  rw [show k + (K + 1 - k) = K + 1 by omega]
  rfl

theorem zeroMapLabels_reverse_cons {k K : Nat} (hkK : k ≤ K) :
    ∃ rest, (zeroMapLabels k K).reverse = K :: rest := by
  by_cases heq : k = K
  · subst K
    exact ⟨[], by simp⟩
  · have hkPrev : k ≤ K - 1 := by omega
    have hsucc : K - 1 + 1 = K := by omega
    have hsnoc := zeroMapLabels_snoc (k := k) (K := K - 1) hkPrev
    rw [hsucc] at hsnoc
    rw [hsnoc, List.reverse_append]
    exact ⟨(zeroMapLabels k (K - 1)).reverse, by simp⟩

@[simp]
theorem zeroMapLabels_nodup (k K : Nat) :
    (zeroMapLabels k K).Nodup := by
  rw [zeroMapLabels_eq_range']
  exact List.nodup_range'

theorem mem_zeroMapLabels {k K label : Nat} (hkK : k ≤ K) :
    label ∈ zeroMapLabels k K ↔ k ≤ label ∧ label ≤ K := by
  constructor
  · intro hlabel
    simp only [zeroMapLabels, List.mem_map] at hlabel
    obtain ⟨offset, hoffset, rfl⟩ := hlabel
    have := List.mem_range.mp hoffset
    omega
  · rintro ⟨hkl, hlK⟩
    simp only [zeroMapLabels, List.mem_map]
    refine ⟨label - k, List.mem_range.mpr ?_, by omega⟩
    omega

/-- Source range mask for the upper map: only positions at or below the decoded boundary retain
their data bit. -/
def upperRangeBits
    (enabled : Bool) (boundary : Nat) (labels : List Nat)
    (bitAt : Nat → Wire) (state : BasisState) : List Bool :=
  labels.map fun label => enabled && decide (label ≤ boundary) && state (bitAt label)

/-- Source range mask for the lower map: only positions at or above the decoded boundary retain
their data bit. -/
def lowerRangeBits
    (enabled : Bool) (boundary : Nat) (labels : List Nat)
    (bitAt : Nat → Wire) (state : BasisState) : List Bool :=
  labels.map fun label => enabled && decide (boundary ≤ label) && state (bitAt label)

@[simp]
theorem upperRangeBits_length enabled boundary labels bitAt state :
    (upperRangeBits enabled boundary labels bitAt state).length = labels.length := by
  simp [upperRangeBits]

@[simp]
theorem lowerRangeBits_length enabled boundary labels bitAt state :
    (lowerRangeBits enabled boundary labels bitAt state).length = labels.length := by
  simp [lowerRangeBits]

theorem UnaryActionTree.visitPulses_zeroMap
    (order : UnaryOrder) (tree : UnaryActionTree)
    (active : Bool) (routeState : BasisState)
    (k K : Nat)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K) :
    tree.visitPulses order active routeState =
      (tree.visitLabels order).map fun label =>
        (label, active && decide (label = tree.routeLabel routeState)) := by
  apply tree.visitPulses_eq_route
  rw [← tree.visitLabels_inc, hlabels]
  exact zeroMapLabels_nodup k K

private theorem foldl_routePulses_not_mem
    (labels : List Nat) (enabled current : Bool) (route : Nat)
    (hroute : route ∉ labels) :
    (labels.map fun label => (label, enabled && decide (label = route))).foldl
        (fun value pulse => Bool.xor value pulse.2) current = current := by
  induction labels generalizing current with
  | nil => rfl
  | cons label labels ih =>
      simp only [List.mem_cons, not_or] at hroute
      simp [Ne.symm hroute.1, ih _ hroute.2]

private theorem foldl_routePulses_eq_xor
    (labels : List Nat) (enabled current : Bool) (route : Nat)
    (hroute : route ∈ labels) (hnodup : labels.Nodup) :
    (labels.map fun label => (label, enabled && decide (label = route))).foldl
        (fun value pulse => Bool.xor value pulse.2) current =
      Bool.xor current enabled := by
  induction labels generalizing current with
  | nil => simp at hroute
  | cons label labels ih =>
      simp only [List.mem_cons] at hroute
      simp only [List.nodup_cons] at hnodup
      by_cases heq : label = route
      · subst label
        simp only [List.map_cons, decide_true, Bool.and_true, List.foldl_cons]
        exact foldl_routePulses_not_mem labels enabled
          (Bool.xor current enabled) route hnodup.1
      · have htail : route ∈ labels := by
          rcases hroute with hroute | hroute
          · exact (heq hroute.symm).elim
          · exact hroute
        simpa [heq] using ih (Bool.xor current false) htail hnodup.2

private theorem foldl_falsePulses
    (labels : List Nat) (current : Bool) :
    (labels.map fun label => (label, false)).foldl
        (fun value pulse => Bool.xor value pulse.2) current = current := by
  induction labels generalizing current with
  | nil => rfl
  | cons label labels ih => simp [ih]

private theorem foldl_routePulses_eq_false
    (labels : List Nat) (enabled : Bool) (route : Nat)
    (hroute : route ∈ labels) (hnodup : labels.Nodup) :
    (labels.map fun label => (label, enabled && decide (label = route))).foldl
        (fun value pulse => Bool.xor value pulse.2) enabled = false := by
  cases enabled with
  | false => exact foldl_falsePulses labels false
  | true =>
      induction labels with
      | nil => simp at hroute
      | cons label labels ih =>
          simp only [List.nodup_cons] at hnodup
          simp only [List.mem_cons] at hroute
          by_cases heq : label = route
          · subst label
            simp only [List.map_cons, Bool.true_and, decide_true,
              List.foldl_cons, Bool.xor_true]
            exact foldl_routePulses_not_mem labels true false route hnodup.1
          · have htail : route ∈ labels := by
              rcases hroute with hroute | hroute
              · exact (heq hroute.symm).elim
              · exact hroute
            simpa [heq] using ih htail hnodup.2

private theorem xor_leq_routePulse
    (enabled : Bool) (label boundary : Nat) :
    Bool.xor (enabled && decide (label ≤ boundary))
        (enabled && decide (label = boundary)) =
      (enabled && decide (label + 1 ≤ boundary)) := by
  cases enabled with
  | false => rfl
  | true =>
      by_cases heq : label = boundary
      · subst boundary
        simp
      · by_cases hle : label ≤ boundary
        · have hnext : label + 1 ≤ boundary := by omega
          simp [heq, hle, hnext]
        · have hnext : ¬label + 1 ≤ boundary := by omega
          simp [heq, hle, hnext]

private theorem xor_geq_routePulse
    (enabled : Bool) (label boundary : Nat) :
    Bool.xor (enabled && decide (label + 1 ≤ boundary))
        (enabled && decide (label = boundary)) =
      (enabled && decide (label ≤ boundary)) := by
  cases enabled with
  | false => rfl
  | true =>
      by_cases heq : label = boundary
      · subst boundary
        simp
      · by_cases hle : label ≤ boundary
        · have hnext : label + 1 ≤ boundary := by omega
          simp [heq, hle, hnext]
        · have hnext : ¬label + 1 ≤ boundary := by omega
          simp [heq, hle, hnext]

private theorem xor_lowerForward_routePulse
    (enabled : Bool) (label boundary : Nat) :
    Bool.xor (enabled && decide (boundary ≤ label + 1))
        (enabled && decide (label + 1 = boundary)) =
      (enabled && decide (boundary ≤ label)) := by
  cases enabled with
  | false => rfl
  | true =>
      by_cases heq : label + 1 = boundary
      · subst boundary
        simp
      · by_cases hle : boundary ≤ label + 1
        · have hprev : boundary ≤ label := by omega
          simp [heq, hle, hprev]
        · have hprev : ¬boundary ≤ label := by omega
          simp [heq, hle, hprev]

private theorem xor_lowerReverse_routePulse
    (enabled : Bool) (label boundary : Nat) :
    Bool.xor (enabled && decide (boundary ≤ label))
        (enabled && decide (label + 1 = boundary)) =
      (enabled && decide (boundary ≤ label + 1)) := by
  cases enabled with
  | false => rfl
  | true =>
      by_cases heq : label + 1 = boundary
      · subst boundary
        simp
      · by_cases hle : boundary ≤ label
        · have hnext : boundary ≤ label + 1 := by omega
          simp [heq, hle, hnext]
        · have hnext : ¬boundary ≤ label + 1 := by omega
          simp [heq, hle, hnext]

/-- Finite data footprint for either zero map. -/
def zeroMapDataWires
    (k K : Nat) (control rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) : List Wire :=
  [control, rangeAccumulator, temporary] ++
    (zeroMapLabels k K).map bitAt ++
    (zeroMapLabels k K).map dirtyAt

/-- Decoder interface erased by the logical range-scan theorem. -/
def zeroMapProtectedWires
    (tree : UnaryActionTree) (control : Wire) (path : List Wire) : List Wire :=
  control :: tree.indexWires.dedup ++ path

/-- Complete physical footprint of either zero map: the read-only decoder interface followed by
the range accumulator, recurrence temporary, source bits, and borrowed dirty bank. -/
def zeroMapWires
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) : List Wire :=
  zeroMapProtectedWires tree control path ++
    rangeAccumulator :: temporary ::
      (zeroMapLabels k K).map bitAt ++
      (zeroMapLabels k K).map dirtyAt

/-- One physical allocation certificate for a zero map.  The external root control is the only
wire shared by the read-only decoder interface and the recurrence-cell footprint. -/
structure ZeroMapLayout
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) : Prop where
  decoder : tree.Layout control path
  wires :
    (zeroMapProtectedWires tree control path ++
      (rangeAccumulator :: temporary ::
        (zeroMapLabels k K).map bitAt ++
        (zeroMapLabels k K).map dirtyAt)).Nodup
  cell : ∀ label ∈ zeroMapLabels k K, ∀ guard,
    (guard = control ∨
      ∃ neighbour ∈ zeroMapLabels k K,
        neighbour ≠ label ∧ guard = dirtyAt neighbour) →
    [rangeAccumulator, bitAt label, guard, dirtyAt label, temporary].Nodup

private theorem ZeroMapLayout.tail_disjoint
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    List.Disjoint (zeroMapProtectedWires tree control path)
      (rangeAccumulator :: temporary ::
        (zeroMapLabels k K).map bitAt ++
        (zeroMapLabels k K).map dirtyAt) := by
  exact List.disjoint_of_nodup_append hlayout.wires

theorem ZeroMapLayout.range_not_protected
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    rangeAccumulator ∉ zeroMapProtectedWires tree control path := by
  intro hprotected
  exact (List.disjoint_left.mp hlayout.tail_disjoint hprotected (by simp))

theorem ZeroMapLayout.range_ne_temporary
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    rangeAccumulator ≠ temporary := by
  have htail := hlayout.wires.of_append_right
  have hrangeNot := (List.nodup_cons.mp htail).1
  intro equality
  apply hrangeNot
  simp [equality]

theorem ZeroMapLayout.control_ne_range
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    control ≠ rangeAccumulator := by
  intro equality
  subst control
  exact hlayout.range_not_protected (by simp [zeroMapProtectedWires])

private theorem ZeroMapLayout.range_not_bit_dirty
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    rangeAccumulator ∉
      (zeroMapLabels k K).map bitAt ++ (zeroMapLabels k K).map dirtyAt := by
  have htail := hlayout.wires.of_append_right
  exact (List.nodup_cons.mp htail).1 ∘ List.mem_cons_of_mem temporary

theorem ZeroMapLayout.range_ne_bit
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    {label : Nat} (hlabel : label ∈ zeroMapLabels k K) :
    rangeAccumulator ≠ bitAt label := by
  intro equality
  apply hlayout.range_not_bit_dirty
  exact List.mem_append_left _ (List.mem_map.mpr ⟨label, hlabel, equality.symm⟩)

theorem ZeroMapLayout.range_ne_dirty
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    {label : Nat} (hlabel : label ∈ zeroMapLabels k K) :
    rangeAccumulator ≠ dirtyAt label := by
  intro equality
  apply hlayout.range_not_bit_dirty
  exact List.mem_append_right _ (List.mem_map.mpr ⟨label, hlabel, equality.symm⟩)

private theorem ZeroMapLayout.bit_dirty_disjoint
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    List.Disjoint ((zeroMapLabels k K).map bitAt)
      ((zeroMapLabels k K).map dirtyAt) := by
  have htail := hlayout.wires.of_append_right
  have hrest := (List.nodup_cons.mp (List.nodup_cons.mp htail).2).2
  exact List.disjoint_of_nodup_append hrest

theorem ZeroMapLayout.bit_ne_dirty
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    {bitLabel dirtyLabel : Nat}
    (hbit : bitLabel ∈ zeroMapLabels k K)
    (hdirty : dirtyLabel ∈ zeroMapLabels k K) :
    bitAt bitLabel ≠ dirtyAt dirtyLabel := by
  intro equality
  apply hlayout.bit_dirty_disjoint
    (List.mem_map.mpr ⟨bitLabel, hbit, rfl⟩)
  rw [equality]
  exact List.mem_map.mpr ⟨dirtyLabel, hdirty, rfl⟩

theorem ZeroMapLayout.shared_eq_control
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    {wire : Wire}
    (hprotected : wire ∈ zeroMapProtectedWires tree control path)
    (hdata : wire ∈ zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt) :
    wire = control := by
  by_contra hne
  apply List.disjoint_left.mp hlayout.tail_disjoint hprotected
  simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hdata ⊢
  aesop

private theorem ZeroMapLayout.control_not_tail
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    control ∉
      (rangeAccumulator :: temporary ::
        (zeroMapLabels k K).map bitAt ++
        (zeroMapLabels k K).map dirtyAt) := by
  exact List.disjoint_left.mp hlayout.tail_disjoint (by
    simp [zeroMapProtectedWires])

theorem ZeroMapLayout.control_ne_temporary
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    control ≠ temporary := by
  intro equality
  subst temporary
  exact hlayout.control_not_tail (by simp)

theorem ZeroMapLayout.control_ne_dirty
    {k K label : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabel : label ∈ zeroMapLabels k K) :
    control ≠ dirtyAt label := by
  intro equality
  subst control
  exact hlayout.control_not_tail (by
    simp only [List.mem_append, List.mem_cons, List.mem_map]
    exact Or.inr ⟨label, hlabel, rfl⟩)

theorem ZeroMapLayout.dirty_nodup
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    ((zeroMapLabels k K).map dirtyAt).Nodup := by
  exact hlayout.wires.of_append_right.of_append_right

theorem ZeroMapLayout.dirty_injective
    {k K : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    {left right : Nat}
    (hleft : left ∈ zeroMapLabels k K)
    (hright : right ∈ zeroMapLabels k K)
    (hequality : dirtyAt left = dirtyAt right) :
    left = right := by
  exact List.inj_on_of_nodup_map hlayout.dirty_nodup hleft hright hequality

theorem ZeroMapLayout.temporary_ne_dirty
    {k K label : Nat} {tree : UnaryActionTree}
    {control rangeAccumulator temporary : Wire} {path : List Wire}
    {bitAt dirtyAt : Nat → Wire}
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabel : label ∈ zeroMapLabels k K) :
    temporary ≠ dirtyAt label := by
  intro equality
  have hnd := hlayout.cell label hlabel control (Or.inl rfl)
  subst temporary
  simp at hnd

/-- Increasing first pass of `_upper_zero_map`, including its externally gated base at `K`. -/
def upperZeroForwardLeaf
    (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (rangeAccumulator : Wire) : Circuit :=
  if k ≤ label ∧ label ≤ K then
    if label = K then
      zeroRecurrenceBaseCell rangeAccumulator (bitAt label) control
        (dirtyAt label) temporary
    else
      zeroRecurrenceCell rangeAccumulator (bitAt label) (dirtyAt (label + 1))
        (dirtyAt label) temporary
  else []

/-- Decreasing second pass of `_upper_zero_map`; the base leaf `K` is deliberately empty. -/
def upperZeroReverseLeaf
    (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (rangeAccumulator : Wire) : Circuit :=
  if k ≤ label ∧ label < K then
    zeroRecurrenceCell rangeAccumulator (bitAt label) (dirtyAt (label + 1))
      (dirtyAt label) temporary
  else []

/-- Decreasing first pass of `_lower_zero_map`, including its externally gated base at `k`. -/
def lowerZeroForwardLeaf
    (k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (rangeAccumulator : Wire) : Circuit :=
  if k ≤ label ∧ label ≤ K then
    if label = k then
      zeroRecurrenceBaseCell rangeAccumulator (bitAt label) control
        (dirtyAt label) temporary
    else
      zeroRecurrenceCell rangeAccumulator (bitAt label) (dirtyAt (label - 1))
        (dirtyAt label) temporary
  else []

/-- Increasing second pass of `_lower_zero_map`; the base leaf `k` is deliberately empty. -/
def lowerZeroReverseLeaf
    (k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (rangeAccumulator : Wire) : Circuit :=
  if k < label ∧ label ≤ K then
    zeroRecurrenceCell rangeAccumulator (bitAt label) (dirtyAt (label - 1))
      (dirtyAt label) temporary
  else []

def upperZeroForwardLeafState
    (k K : Nat) (control rangeAccumulator : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (state : BasisState) : BasisState :=
  if k ≤ label ∧ label ≤ K then
    if label = K then
      zeroRecurrenceCellState rangeAccumulator (bitAt label) control
        (dirtyAt label) state
    else
      zeroRecurrenceCellState rangeAccumulator (bitAt label) (dirtyAt (label + 1))
        (dirtyAt label) state
  else state

def upperZeroReverseLeafState
    (k K : Nat) (rangeAccumulator : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (state : BasisState) : BasisState :=
  if k ≤ label ∧ label < K then
    zeroRecurrenceCellState rangeAccumulator (bitAt label) (dirtyAt (label + 1))
      (dirtyAt label) state
  else state

def lowerZeroForwardLeafState
    (k K : Nat) (control rangeAccumulator : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (state : BasisState) : BasisState :=
  if k ≤ label ∧ label ≤ K then
    if label = k then
      zeroRecurrenceCellState rangeAccumulator (bitAt label) control
        (dirtyAt label) state
    else
      zeroRecurrenceCellState rangeAccumulator (bitAt label) (dirtyAt (label - 1))
        (dirtyAt label) state
  else state

def lowerZeroReverseLeafState
    (k K : Nat) (rangeAccumulator : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (state : BasisState) : BasisState :=
  if k < label ∧ label ≤ K then
    zeroRecurrenceCellState rangeAccumulator (bitAt label) (dirtyAt (label - 1))
      (dirtyAt label) state
  else state

theorem upperZeroForwardLeafState_preserves
    (k K : Nat) (control rangeAccumulator : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (state : BasisState) (wire : Wire) (hwire : wire ≠ dirtyAt label) :
    upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state wire =
      state wire := by
  simp only [upperZeroForwardLeafState]
  split
  · split <;> exact zeroRecurrenceCellState_preserves _ _ _ _ _ _ hwire
  · rfl

theorem upperZeroReverseLeafState_preserves
    (k K : Nat) (rangeAccumulator : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (state : BasisState) (wire : Wire) (hwire : wire ≠ dirtyAt label) :
    upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state wire =
      state wire := by
  simp only [upperZeroReverseLeafState]
  split
  · exact zeroRecurrenceCellState_preserves _ _ _ _ _ _ hwire
  · rfl

theorem lowerZeroForwardLeafState_preserves
    (k K : Nat) (control rangeAccumulator : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (state : BasisState) (wire : Wire) (hwire : wire ≠ dirtyAt label) :
    lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state wire =
      state wire := by
  simp only [lowerZeroForwardLeafState]
  split
  · split <;> exact zeroRecurrenceCellState_preserves _ _ _ _ _ _ hwire
  · rfl

theorem lowerZeroReverseLeafState_preserves
    (k K : Nat) (rangeAccumulator : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat)
    (state : BasisState) (wire : Wire) (hwire : wire ≠ dirtyAt label) :
    lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state wire =
      state wire := by
  simp only [lowerZeroReverseLeafState]
  split
  · exact zeroRecurrenceCellState_preserves _ _ _ _ _ _ hwire
  · rfl

theorem upperZeroForwardLeafState_preserves_range
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state
        rangeAccumulator = state rangeAccumulator := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · apply upperZeroForwardLeafState_preserves
    exact hlayout.range_ne_dirty ((mem_zeroMapLabels hkK).2 hwindow)
  · simp [upperZeroForwardLeafState, hwindow]

theorem upperZeroReverseLeafState_preserves_range
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state
        rangeAccumulator = state rangeAccumulator := by
  by_cases hwindow : k ≤ label ∧ label < K
  · apply upperZeroReverseLeafState_preserves
    exact hlayout.range_ne_dirty ((mem_zeroMapLabels hkK).2 (by omega))
  · simp [upperZeroReverseLeafState, hwindow]

theorem lowerZeroForwardLeafState_preserves_range
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state
        rangeAccumulator = state rangeAccumulator := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · apply lowerZeroForwardLeafState_preserves
    exact hlayout.range_ne_dirty ((mem_zeroMapLabels hkK).2 hwindow)
  · simp [lowerZeroForwardLeafState, hwindow]

theorem lowerZeroReverseLeafState_preserves_range
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state
        rangeAccumulator = state rangeAccumulator := by
  by_cases hwindow : k < label ∧ label ≤ K
  · apply lowerZeroReverseLeafState_preserves
    exact hlayout.range_ne_dirty ((mem_zeroMapLabels hkK).2 (by omega))
  · simp [lowerZeroReverseLeafState, hwindow]

/-- Exact coherent `MEASUREMENT_UNCOMPUTE=False` upper map from the pinned supplement. -/
def upperZeroMapUnitary
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) : Circuit :=
  rangeScanUnitary true .inc tree control rangeAccumulator path
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt) ++
    rangeScanUnitary false .dec tree control rangeAccumulator path
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt)

/-- Exact coherent `MEASUREMENT_UNCOMPUTE=False` lower-map mirror. -/
def lowerZeroMapUnitary
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) : Circuit :=
  rangeScanUnitary true .dec tree control rangeAccumulator path
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt) ++
    rangeScanUnitary false .inc tree control rangeAccumulator path
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)

private theorem zeroRecurrenceCell_usesOnly_zeroMapData
    (k K label : Nat)
    (control rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire)
    (guard : Wire) (hguard : guard = control ∨
      ∃ next ∈ zeroMapLabels k K, guard = dirtyAt next)
    (hlabel : label ∈ zeroMapLabels k K) :
    PaperCircuitUsesOnly
      (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
      (zeroRecurrenceCell rangeAccumulator (bitAt label) guard
        (dirtyAt label) temporary) := by
  apply (zeroRecurrenceCell_usesOnly rangeAccumulator (bitAt label) guard
    (dirtyAt label) temporary).mono
  intro wire hwire
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hwire | hwire | hwire | hwire | hwire
  · subst wire
    simp [zeroMapDataWires]
  · subst wire
    simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map]
    exact Or.inl (Or.inr ⟨label, hlabel, rfl⟩)
  · subst wire
    rcases hguard with rfl | ⟨next, hnext, rfl⟩
    · simp [zeroMapDataWires]
    · simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_map]
      exact Or.inr ⟨next, hnext, rfl⟩
  · subst wire
    simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map]
    exact Or.inr ⟨label, hlabel, rfl⟩
  · subst wire
    simp [zeroMapDataWires]

private theorem zeroRecurrenceBaseCell_usesOnly_zeroMapData
    (k K label : Nat)
    (control rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlabel : label ∈ zeroMapLabels k K) :
    PaperCircuitUsesOnly
      (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
      (zeroRecurrenceBaseCell rangeAccumulator (bitAt label) control
        (dirtyAt label) temporary) := by
  apply (zeroRecurrenceBaseCell_usesOnly rangeAccumulator (bitAt label) control
    (dirtyAt label) temporary).mono
  intro wire hwire
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hwire | hwire | hwire | hwire | hwire
  · subst wire
    simp [zeroMapDataWires]
  · subst wire
    simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map]
    exact Or.inl (Or.inr ⟨label, hlabel, rfl⟩)
  · subst wire
    simp [zeroMapDataWires]
  · subst wire
    simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map]
    exact Or.inr ⟨label, hlabel, rfl⟩
  · subst wire
    simp [zeroMapDataWires]

theorem upperZeroForwardLeaf_usesOnly
    (k K : Nat) (hkK : k ≤ K)
    (control rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) :
    PaperCircuitUsesOnly
      (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [upperZeroForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    by_cases hbase : label = K
    · rw [if_pos hbase]
      exact zeroRecurrenceBaseCell_usesOnly_zeroMapData k K label control
        rangeAccumulator temporary bitAt dirtyAt hlabel
    · rw [if_neg hbase]
      apply zeroRecurrenceCell_usesOnly_zeroMapData k K label control
        rangeAccumulator temporary bitAt dirtyAt (dirtyAt (label + 1))
        (Or.inr ⟨label + 1, ?_, rfl⟩) hlabel
      apply (mem_zeroMapLabels hkK).2
      omega
  · simp [upperZeroForwardLeaf, hwindow, PaperCircuitUsesOnly]

theorem upperZeroReverseLeaf_usesOnly
    (k K : Nat) (hkK : k ≤ K)
    (control rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) :
    PaperCircuitUsesOnly
      (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k ≤ label ∧ label < K
  · rw [upperZeroReverseLeaf, if_pos hwindow]
    apply zeroRecurrenceCell_usesOnly_zeroMapData k K label control
      rangeAccumulator temporary bitAt dirtyAt (dirtyAt (label + 1))
      (Or.inr ⟨label + 1, (mem_zeroMapLabels hkK).2 (by omega), rfl⟩)
      ((mem_zeroMapLabels hkK).2 (by omega))
  · simp [upperZeroReverseLeaf, hwindow, PaperCircuitUsesOnly]

theorem lowerZeroForwardLeaf_usesOnly
    (k K : Nat) (hkK : k ≤ K)
    (control rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) :
    PaperCircuitUsesOnly
      (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [lowerZeroForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    by_cases hbase : label = k
    · rw [if_pos hbase]
      exact zeroRecurrenceBaseCell_usesOnly_zeroMapData k K label control
        rangeAccumulator temporary bitAt dirtyAt hlabel
    · rw [if_neg hbase]
      apply zeroRecurrenceCell_usesOnly_zeroMapData k K label control
        rangeAccumulator temporary bitAt dirtyAt (dirtyAt (label - 1))
        (Or.inr ⟨label - 1, ?_, rfl⟩) hlabel
      apply (mem_zeroMapLabels hkK).2
      omega
  · simp [lowerZeroForwardLeaf, hwindow, PaperCircuitUsesOnly]

theorem lowerZeroReverseLeaf_usesOnly
    (k K : Nat) (hkK : k ≤ K)
    (control rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) :
    PaperCircuitUsesOnly
      (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k < label ∧ label ≤ K
  · rw [lowerZeroReverseLeaf, if_pos hwindow]
    apply zeroRecurrenceCell_usesOnly_zeroMapData k K label control
      rangeAccumulator temporary bitAt dirtyAt (dirtyAt (label - 1))
      (Or.inr ⟨label - 1, (mem_zeroMapLabels hkK).2 (by omega), rfl⟩)
      ((mem_zeroMapLabels hkK).2 (by omega))
  · simp [lowerZeroReverseLeaf, hwindow, PaperCircuitUsesOnly]

private theorem zeroMapDataWires_subset_zeroMapWires
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) :
    ∀ wire,
      wire ∈ zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt →
      wire ∈ zeroMapWires k K tree control rangeAccumulator temporary path bitAt dirtyAt := by
  intro wire hwire
  simp only [zeroMapDataWires, zeroMapWires, zeroMapProtectedWires,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
  aesop

/-- The complete coherent upper map stays inside its declared decoder/data footprint. -/
theorem upperZeroMapUnitary_usesOnly
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) :
    PaperCircuitUsesOnly
      (zeroMapWires k K tree control rangeAccumulator temporary path bitAt dirtyAt)
      (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  rw [upperZeroMapUnitary]
  apply PaperCircuitUsesOnly.append
  · apply rangeScanUnitary_usesOnly_of
    · simp [zeroMapWires, zeroMapProtectedWires]
    · simp [zeroMapWires]
    · intro wire hwire
      simp [zeroMapWires, zeroMapProtectedWires, hwire]
    · intro wire hwire
      simp [zeroMapWires, zeroMapProtectedWires, hwire]
    · intro label
      exact (upperZeroForwardLeaf_usesOnly k K hkK control rangeAccumulator
        temporary bitAt dirtyAt label).mono
        (zeroMapDataWires_subset_zeroMapWires k K tree control rangeAccumulator
          temporary path bitAt dirtyAt)
  · apply rangeScanUnitary_usesOnly_of
    · simp [zeroMapWires, zeroMapProtectedWires]
    · simp [zeroMapWires]
    · intro wire hwire
      simp [zeroMapWires, zeroMapProtectedWires, hwire]
    · intro wire hwire
      simp [zeroMapWires, zeroMapProtectedWires, hwire]
    · intro label
      exact (upperZeroReverseLeaf_usesOnly k K hkK control rangeAccumulator
        temporary bitAt dirtyAt label).mono
        (zeroMapDataWires_subset_zeroMapWires k K tree control rangeAccumulator
          temporary path bitAt dirtyAt)

/-- The complete coherent lower map stays inside the same declared footprint. -/
theorem lowerZeroMapUnitary_usesOnly
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) :
    PaperCircuitUsesOnly
      (zeroMapWires k K tree control rangeAccumulator temporary path bitAt dirtyAt)
      (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  rw [lowerZeroMapUnitary]
  apply PaperCircuitUsesOnly.append
  · apply rangeScanUnitary_usesOnly_of
    · simp [zeroMapWires, zeroMapProtectedWires]
    · simp [zeroMapWires]
    · intro wire hwire
      simp [zeroMapWires, zeroMapProtectedWires, hwire]
    · intro wire hwire
      simp [zeroMapWires, zeroMapProtectedWires, hwire]
    · intro label
      exact (lowerZeroForwardLeaf_usesOnly k K hkK control rangeAccumulator
        temporary bitAt dirtyAt label).mono
        (zeroMapDataWires_subset_zeroMapWires k K tree control rangeAccumulator
          temporary path bitAt dirtyAt)
  · apply rangeScanUnitary_usesOnly_of
    · simp [zeroMapWires, zeroMapProtectedWires]
    · simp [zeroMapWires]
    · intro wire hwire
      simp [zeroMapWires, zeroMapProtectedWires, hwire]
    · intro wire hwire
      simp [zeroMapWires, zeroMapProtectedWires, hwire]
    · intro label
      exact (lowerZeroReverseLeaf_usesOnly k K hkK control rangeAccumulator
        temporary bitAt dirtyAt label).mono
        (zeroMapDataWires_subset_zeroMapWires k K tree control rangeAccumulator
          temporary path bitAt dirtyAt)

@[simp]
theorem upperZeroForwardLeaf_HPFree
    (k K : Nat) (control rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) :
    HPFree
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [upperZeroForwardLeaf, if_pos hwindow]
    by_cases hbase : label = K <;>
      simp [hbase, zeroRecurrenceBaseCell, zeroRecurrenceCell, HPFree]
  · simp [upperZeroForwardLeaf, hwindow, HPFree]

@[simp]
theorem upperZeroReverseLeaf_HPFree
    (k K : Nat) (rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) :
    HPFree
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k ≤ label ∧ label < K
  · simp [upperZeroReverseLeaf, hwindow, zeroRecurrenceCell, HPFree]
  · simp [upperZeroReverseLeaf, hwindow, HPFree]

@[simp]
theorem lowerZeroForwardLeaf_HPFree
    (k K : Nat) (control rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) :
    HPFree
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [lowerZeroForwardLeaf, if_pos hwindow]
    by_cases hbase : label = k <;>
      simp [hbase, zeroRecurrenceBaseCell, zeroRecurrenceCell, HPFree]
  · simp [lowerZeroForwardLeaf, hwindow, HPFree]

@[simp]
theorem lowerZeroReverseLeaf_HPFree
    (k K : Nat) (rangeAccumulator temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) :
    HPFree
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k < label ∧ label ≤ K
  · simp [lowerZeroReverseLeaf, hwindow, zeroRecurrenceCell, HPFree]
  · simp [lowerZeroReverseLeaf, hwindow, HPFree]

@[simp]
theorem upperZeroMapUnitary_HPFree
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) :
    HPFree
      (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  rw [upperZeroMapUnitary]
  rw [hpFree_append]
  exact ⟨
    rangeScanUnitary_HPFree_of true .inc tree control rangeAccumulator path
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt) (by simp),
    rangeScanUnitary_HPFree_of false .dec tree control rangeAccumulator path
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt) (by simp)⟩

@[simp]
theorem lowerZeroMapUnitary_HPFree
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) :
    HPFree
      (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  rw [lowerZeroMapUnitary]
  rw [hpFree_append]
  exact ⟨
    rangeScanUnitary_HPFree_of true .dec tree control rangeAccumulator path
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt) (by simp),
    rangeScanUnitary_HPFree_of false .inc tree control rangeAccumulator path
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt) (by simp)⟩

theorem upperZeroForwardLeaf_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) :
    CircuitWellFormed
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [upperZeroForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    by_cases hbase : label = K
    · rw [if_pos hbase]
      exact zeroRecurrenceBaseCell_wellFormed rangeAccumulator (bitAt label)
        control (dirtyAt label) temporary
        (hlayout.cell label hlabel control (Or.inl rfl))
    · rw [if_neg hbase]
      have hnext : label + 1 ∈ zeroMapLabels k K :=
        (mem_zeroMapLabels hkK).2 (by omega)
      exact zeroRecurrenceCell_wellFormed rangeAccumulator (bitAt label)
        (dirtyAt (label + 1)) (dirtyAt label) temporary
        (hlayout.cell label hlabel (dirtyAt (label + 1))
          (Or.inr ⟨label + 1, hnext, by omega, rfl⟩))
  · simp [upperZeroForwardLeaf, hwindow, CircuitWellFormed]

theorem upperZeroReverseLeaf_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) :
    CircuitWellFormed
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k ≤ label ∧ label < K
  · rw [upperZeroReverseLeaf, if_pos hwindow]
    have hlabel : label ∈ zeroMapLabels k K :=
      (mem_zeroMapLabels hkK).2 (by omega)
    have hnext : label + 1 ∈ zeroMapLabels k K :=
      (mem_zeroMapLabels hkK).2 (by omega)
    exact zeroRecurrenceCell_wellFormed rangeAccumulator (bitAt label)
      (dirtyAt (label + 1)) (dirtyAt label) temporary
      (hlayout.cell label hlabel (dirtyAt (label + 1))
        (Or.inr ⟨label + 1, hnext, by omega, rfl⟩))
  · simp [upperZeroReverseLeaf, hwindow, CircuitWellFormed]

theorem lowerZeroForwardLeaf_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) :
    CircuitWellFormed
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [lowerZeroForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    by_cases hbase : label = k
    · rw [if_pos hbase]
      exact zeroRecurrenceBaseCell_wellFormed rangeAccumulator (bitAt label)
        control (dirtyAt label) temporary
        (hlayout.cell label hlabel control (Or.inl rfl))
    · rw [if_neg hbase]
      have hprev : label - 1 ∈ zeroMapLabels k K :=
        (mem_zeroMapLabels hkK).2 (by omega)
      exact zeroRecurrenceCell_wellFormed rangeAccumulator (bitAt label)
        (dirtyAt (label - 1)) (dirtyAt label) temporary
        (hlayout.cell label hlabel (dirtyAt (label - 1))
          (Or.inr ⟨label - 1, hprev, by omega, rfl⟩))
  · simp [lowerZeroForwardLeaf, hwindow, CircuitWellFormed]

theorem lowerZeroReverseLeaf_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) :
    CircuitWellFormed
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label
        rangeAccumulator) := by
  by_cases hwindow : k < label ∧ label ≤ K
  · rw [lowerZeroReverseLeaf, if_pos hwindow]
    have hlabel : label ∈ zeroMapLabels k K :=
      (mem_zeroMapLabels hkK).2 (by omega)
    have hprev : label - 1 ∈ zeroMapLabels k K :=
      (mem_zeroMapLabels hkK).2 (by omega)
    exact zeroRecurrenceCell_wellFormed rangeAccumulator (bitAt label)
      (dirtyAt (label - 1)) (dirtyAt label) temporary
      (hlayout.cell label hlabel (dirtyAt (label - 1))
        (Or.inr ⟨label - 1, hprev, by omega, rfl⟩))
  · simp [lowerZeroReverseLeaf, hwindow, CircuitWellFormed]

/-- Physical well-formedness of the literal two-pass upper zero map. -/
theorem upperZeroMapUnitary_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    CircuitWellFormed
      (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  rw [upperZeroMapUnitary, circuitWellFormed_append]
  constructor
  · apply rangeScanUnitary_wellFormed_of true .inc tree control rangeAccumulator path
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)
      hlayout.decoder hlayout.range_not_protected
    intro label _
    exact upperZeroForwardLeaf_wellFormed k K hkK tree control rangeAccumulator
      temporary path bitAt dirtyAt hlayout label
  · apply rangeScanUnitary_wellFormed_of false .dec tree control rangeAccumulator path
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt)
      hlayout.decoder hlayout.range_not_protected
    intro label _
    exact upperZeroReverseLeaf_wellFormed k K hkK tree control rangeAccumulator
      temporary path bitAt dirtyAt hlayout label

/-- Physical well-formedness of the literal two-pass lower zero map. -/
theorem lowerZeroMapUnitary_wellFormed
    (k K : Nat) (hkK : k ≤ K) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    CircuitWellFormed
      (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) := by
  rw [lowerZeroMapUnitary, circuitWellFormed_append]
  constructor
  · apply rangeScanUnitary_wellFormed_of true .dec tree control rangeAccumulator path
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)
      hlayout.decoder hlayout.range_not_protected
    intro label _
    exact lowerZeroForwardLeaf_wellFormed k K hkK tree control rangeAccumulator
      temporary path bitAt dirtyAt hlayout label
  · apply rangeScanUnitary_wellFormed_of false .inc tree control rangeAccumulator path
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)
      hlayout.decoder hlayout.range_not_protected
    intro label _
    exact lowerZeroReverseLeaf_wellFormed k K hkK tree control rangeAccumulator
      temporary path bitAt dirtyAt hlayout label

/-- Exact coherent Toffoli count of the upper map, derived from both literal scans. -/
theorem upperZeroMapUnitary_toffoliCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : tree.Layout control path) :
    eeaToffoliCount
        (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) =
      tree.leafCostSum
          (fun label _ ↦ eeaToffoliCount
            (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label
              rangeAccumulator)) control path +
        tree.leafCostSum
          (fun label _ ↦ eeaToffoliCount
            (upperZeroReverseLeaf k K temporary bitAt dirtyAt label
              rangeAccumulator)) control path +
        4 * tree.internalNodes := by
  rw [upperZeroMapUnitary, eeaToffoliCount_append,
    rangeScanUnitary_toffoliCount true .inc tree control rangeAccumulator path
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt) hlayout,
    rangeScanUnitary_toffoliCount false .dec tree control rangeAccumulator path
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt) hlayout]
  omega

/-- Exact coherent Toffoli count of the lower-map mirror. -/
theorem lowerZeroMapUnitary_toffoliCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : tree.Layout control path) :
    eeaToffoliCount
        (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) =
      tree.leafCostSum
          (fun label _ ↦ eeaToffoliCount
            (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label
              rangeAccumulator)) control path +
        tree.leafCostSum
          (fun label _ ↦ eeaToffoliCount
            (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label
              rangeAccumulator)) control path +
        4 * tree.internalNodes := by
  rw [lowerZeroMapUnitary, eeaToffoliCount_append,
    rangeScanUnitary_toffoliCount true .dec tree control rangeAccumulator path
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt) hlayout,
    rangeScanUnitary_toffoliCount false .inc tree control rangeAccumulator path
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt) hlayout]
  omega

/-- Exact coherent CNOT count of the upper map, including the four scan-control layers. -/
theorem upperZeroMapUnitary_cnotCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : tree.Layout control path) :
    eeaCnotCount
        (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) =
      2 + tree.leafCostSum
          (fun label _ ↦ eeaCnotCount
              (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label
                rangeAccumulator) + 1) control path +
        tree.leafCostSum
          (fun label _ ↦ eeaCnotCount
              (upperZeroReverseLeaf k K temporary bitAt dirtyAt label
                rangeAccumulator) + 1) control path +
        4 * tree.internalNodes := by
  rw [upperZeroMapUnitary, eeaCnotCount_append,
    rangeScanUnitary_cnotCount true .inc tree control rangeAccumulator path
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt) hlayout,
    rangeScanUnitary_cnotCount false .dec tree control rangeAccumulator path
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt) hlayout]
  omega

/-- Exact coherent CNOT count of the lower-map mirror. -/
theorem lowerZeroMapUnitary_cnotCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : tree.Layout control path) :
    eeaCnotCount
        (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) =
      2 + tree.leafCostSum
          (fun label _ ↦ eeaCnotCount
              (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label
                rangeAccumulator) + 1) control path +
        tree.leafCostSum
          (fun label _ ↦ eeaCnotCount
              (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label
                rangeAccumulator) + 1) control path +
        4 * tree.internalNodes := by
  rw [lowerZeroMapUnitary, eeaCnotCount_append,
    rangeScanUnitary_cnotCount true .dec tree control rangeAccumulator path
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt) hlayout,
    rangeScanUnitary_cnotCount false .inc tree control rangeAccumulator path
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt) hlayout]
  omega

/-- Exact coherent T count of the upper map. -/
theorem upperZeroMapUnitary_tCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : tree.Layout control path) :
    ShorECDLP.tCount
        (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) =
      tree.leafCostSum
          (fun label _ ↦ ShorECDLP.tCount
            (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label
              rangeAccumulator)) control path +
        tree.leafCostSum
          (fun label _ ↦ ShorECDLP.tCount
            (upperZeroReverseLeaf k K temporary bitAt dirtyAt label
              rangeAccumulator)) control path +
        28 * tree.internalNodes := by
  rw [upperZeroMapUnitary, tCount_append,
    rangeScanUnitary_tCount true .inc tree control rangeAccumulator path
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt) hlayout,
    rangeScanUnitary_tCount false .dec tree control rangeAccumulator path
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt) hlayout]
  omega

/-- Exact coherent T count of the lower-map mirror. -/
theorem lowerZeroMapUnitary_tCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire)
    (hlayout : tree.Layout control path) :
    ShorECDLP.tCount
        (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt) =
      tree.leafCostSum
          (fun label _ ↦ ShorECDLP.tCount
            (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label
              rangeAccumulator)) control path +
        tree.leafCostSum
          (fun label _ ↦ ShorECDLP.tCount
            (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label
              rangeAccumulator)) control path +
        28 * tree.internalNodes := by
  rw [lowerZeroMapUnitary, tCount_append,
    rangeScanUnitary_tCount true .dec tree control rangeAccumulator path
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt) hlayout,
    rangeScanUnitary_tCount false .inc tree control rangeAccumulator path
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt) hlayout]
  omega

theorem run_upperZeroForwardLeaf
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) (hclean : state temporary = false) :
    Classical.run
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator) state =
      upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [upperZeroForwardLeaf, upperZeroForwardLeafState, if_pos hwindow,
      if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    by_cases hbase : label = K
    · rw [if_pos hbase, if_pos hbase]
      exact run_zeroRecurrenceBaseCell rangeAccumulator (bitAt label) control
        (dirtyAt label) temporary state
        (hlayout.cell label hlabel control (Or.inl rfl)) hclean
    · rw [if_neg hbase, if_neg hbase]
      apply run_zeroRecurrenceCell
      · apply hlayout.cell label hlabel (dirtyAt (label + 1))
        exact Or.inr ⟨label + 1, (mem_zeroMapLabels hkK).2 (by omega),
          by omega, rfl⟩
      · exact hclean
  · simp [upperZeroForwardLeaf, upperZeroForwardLeafState, hwindow]

theorem run_upperZeroReverseLeaf
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) (hclean : state temporary = false) :
    Classical.run
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator) state =
      upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state := by
  by_cases hwindow : k ≤ label ∧ label < K
  · rw [upperZeroReverseLeaf, upperZeroReverseLeafState,
      if_pos hwindow, if_pos hwindow]
    apply run_zeroRecurrenceCell
    · apply hlayout.cell label ((mem_zeroMapLabels hkK).2 (by omega))
        (dirtyAt (label + 1))
      exact Or.inr ⟨label + 1, (mem_zeroMapLabels hkK).2 (by omega),
        by omega, rfl⟩
    · exact hclean
  · simp [upperZeroReverseLeaf, upperZeroReverseLeafState, hwindow]

theorem run_lowerZeroForwardLeaf
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) (hclean : state temporary = false) :
    Classical.run
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator) state =
      lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [lowerZeroForwardLeaf, lowerZeroForwardLeafState, if_pos hwindow,
      if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    by_cases hbase : label = k
    · rw [if_pos hbase, if_pos hbase]
      exact run_zeroRecurrenceBaseCell rangeAccumulator (bitAt label) control
        (dirtyAt label) temporary state
        (hlayout.cell label hlabel control (Or.inl rfl)) hclean
    · rw [if_neg hbase, if_neg hbase]
      apply run_zeroRecurrenceCell
      · apply hlayout.cell label hlabel (dirtyAt (label - 1))
        exact Or.inr ⟨label - 1, (mem_zeroMapLabels hkK).2 (by omega),
          by omega, rfl⟩
      · exact hclean
  · simp [lowerZeroForwardLeaf, lowerZeroForwardLeafState, hwindow]

theorem run_lowerZeroReverseLeaf
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) (hclean : state temporary = false) :
    Classical.run
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator) state =
      lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state := by
  by_cases hwindow : k < label ∧ label ≤ K
  · rw [lowerZeroReverseLeaf, lowerZeroReverseLeafState,
      if_pos hwindow, if_pos hwindow]
    apply run_zeroRecurrenceCell
    · apply hlayout.cell label ((mem_zeroMapLabels hkK).2 (by omega))
        (dirtyAt (label - 1))
      exact Or.inr ⟨label - 1, (mem_zeroMapLabels hkK).2 (by omega),
        by omega, rfl⟩
    · exact hclean
  · simp [lowerZeroReverseLeaf, lowerZeroReverseLeafState, hwindow]

theorem upperZeroForwardLeafState_preserves_temporary
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state temporary =
      state temporary := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    rw [upperZeroForwardLeafState, if_pos hwindow]
    split <;> apply zeroRecurrenceCellState_preserves
    <;> exact hlayout.temporary_ne_dirty hlabel
  · simp [upperZeroForwardLeafState, hwindow]

theorem upperZeroReverseLeafState_preserves_temporary
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state temporary =
      state temporary := by
  by_cases hwindow : k ≤ label ∧ label < K
  · have hlabel : label ∈ zeroMapLabels k K :=
      (mem_zeroMapLabels hkK).2 (by omega)
    rw [upperZeroReverseLeafState, if_pos hwindow]
    exact zeroRecurrenceCellState_preserves _ _ _ _ _ _
      (hlayout.temporary_ne_dirty hlabel)
  · simp [upperZeroReverseLeafState, hwindow]

theorem lowerZeroForwardLeafState_preserves_temporary
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state temporary =
      state temporary := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    rw [lowerZeroForwardLeafState, if_pos hwindow]
    split <;> apply zeroRecurrenceCellState_preserves
    <;> exact hlayout.temporary_ne_dirty hlabel
  · simp [lowerZeroForwardLeafState, hwindow]

theorem lowerZeroReverseLeafState_preserves_temporary
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state temporary =
      state temporary := by
  by_cases hwindow : k < label ∧ label ≤ K
  · have hlabel : label ∈ zeroMapLabels k K :=
      (mem_zeroMapLabels hkK).2 (by omega)
    rw [lowerZeroReverseLeafState, if_pos hwindow]
    exact zeroRecurrenceCellState_preserves _ _ _ _ _ _
      (hlayout.temporary_ne_dirty hlabel)
  · simp [lowerZeroReverseLeafState, hwindow]

theorem upperZeroForwardLeaf_preserves_control
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    Classical.run
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator)
      state control = state control := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [upperZeroForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    by_cases hbase : label = K
    · rw [if_pos hbase]
      apply zeroRecurrenceBaseCell_preserves
      · exact hlayout.control_ne_dirty hlabel
      · exact hlayout.control_ne_temporary
    · rw [if_neg hbase]
      apply zeroRecurrenceCell_preserves
      · exact hlayout.control_ne_dirty hlabel
      · exact hlayout.control_ne_temporary
  · simp [upperZeroForwardLeaf, hwindow]

theorem upperZeroReverseLeaf_preserves_control
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    Classical.run
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator)
      state control = state control := by
  by_cases hwindow : k ≤ label ∧ label < K
  · rw [upperZeroReverseLeaf, if_pos hwindow]
    apply zeroRecurrenceCell_preserves
    · exact hlayout.control_ne_dirty ((mem_zeroMapLabels hkK).2 (by omega))
    · exact hlayout.control_ne_temporary
  · simp [upperZeroReverseLeaf, hwindow]

theorem lowerZeroForwardLeaf_preserves_control
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    Classical.run
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt label rangeAccumulator)
      state control = state control := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · rw [lowerZeroForwardLeaf, if_pos hwindow]
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    by_cases hbase : label = k
    · rw [if_pos hbase]
      apply zeroRecurrenceBaseCell_preserves
      · exact hlayout.control_ne_dirty hlabel
      · exact hlayout.control_ne_temporary
    · rw [if_neg hbase]
      apply zeroRecurrenceCell_preserves
      · exact hlayout.control_ne_dirty hlabel
      · exact hlayout.control_ne_temporary
  · simp [lowerZeroForwardLeaf, hwindow]

theorem lowerZeroReverseLeaf_preserves_control
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) :
    Classical.run
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt label rangeAccumulator)
      state control = state control := by
  by_cases hwindow : k < label ∧ label ≤ K
  · rw [lowerZeroReverseLeaf, if_pos hwindow]
    apply zeroRecurrenceCell_preserves
    · exact hlayout.control_ne_dirty ((mem_zeroMapLabels hkK).2 (by omega))
    · exact hlayout.control_ne_temporary
  · simp [lowerZeroReverseLeaf, hwindow]

/-! ### Decoder-erased exact traces of the four source scans -/

theorem run_upperZeroForwardScan
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hclean : Clean path state) :
    Classical.run
      (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state =
      let seeded := state[rangeAccumulator ↦
        Bool.xor (state rangeAccumulator) (state control)]
      tree.runLogicalTree .inc
        (rangeScanLogicalLeafState true rangeAccumulator
          (upperZeroForwardLeaf k K control temporary bitAt dirtyAt))
        (state control) seeded seeded := by
  apply run_rangeScanUnitary true .inc tree control rangeAccumulator path
    (zeroMapProtectedWires tree control path)
    (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
    (upperZeroForwardLeaf k K control temporary bitAt dirtyAt) state
  · exact hlayout.decoder
  · intro wire hwire
    exact hwire
  · exact hlayout.range_not_protected
  · exact fun wire hprotected hdata => hlayout.shared_eq_control hprotected hdata
  · exact upperZeroForwardLeaf_usesOnly k K hkK control rangeAccumulator temporary bitAt dirtyAt
  · exact upperZeroForwardLeaf_preserves_control k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout
  · exact hclean

theorem run_upperZeroReverseScan
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hclean : Clean path state) :
    Classical.run
      (rangeScanUnitary false .dec tree control rangeAccumulator path
        (upperZeroReverseLeaf k K temporary bitAt dirtyAt)) state =
      let traced := tree.runLogicalTree .dec
        (rangeScanLogicalLeafState false rangeAccumulator
          (upperZeroReverseLeaf k K temporary bitAt dirtyAt))
        (state control) state state
      traced[rangeAccumulator ↦
        Bool.xor (traced rangeAccumulator) (traced control)] := by
  apply run_rangeScanUnitary false .dec tree control rangeAccumulator path
    (zeroMapProtectedWires tree control path)
    (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
    (upperZeroReverseLeaf k K temporary bitAt dirtyAt) state
  · exact hlayout.decoder
  · intro wire hwire
    exact hwire
  · exact hlayout.range_not_protected
  · exact fun wire hprotected hdata => hlayout.shared_eq_control hprotected hdata
  · exact upperZeroReverseLeaf_usesOnly k K hkK control rangeAccumulator temporary bitAt dirtyAt
  · exact upperZeroReverseLeaf_preserves_control k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout
  · exact hclean

theorem run_lowerZeroForwardScan
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hclean : Clean path state) :
    Classical.run
      (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state =
      let seeded := state[rangeAccumulator ↦
        Bool.xor (state rangeAccumulator) (state control)]
      tree.runLogicalTree .dec
        (rangeScanLogicalLeafState true rangeAccumulator
          (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt))
        (state control) seeded seeded := by
  apply run_rangeScanUnitary true .dec tree control rangeAccumulator path
    (zeroMapProtectedWires tree control path)
    (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
    (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt) state
  · exact hlayout.decoder
  · intro wire hwire
    exact hwire
  · exact hlayout.range_not_protected
  · exact fun wire hprotected hdata => hlayout.shared_eq_control hprotected hdata
  · exact lowerZeroForwardLeaf_usesOnly k K hkK control rangeAccumulator temporary bitAt dirtyAt
  · exact lowerZeroForwardLeaf_preserves_control k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout
  · exact hclean

theorem run_lowerZeroReverseScan
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hclean : Clean path state) :
    Classical.run
      (rangeScanUnitary false .inc tree control rangeAccumulator path
        (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)) state =
      let traced := tree.runLogicalTree .inc
        (rangeScanLogicalLeafState false rangeAccumulator
          (lowerZeroReverseLeaf k K temporary bitAt dirtyAt))
        (state control) state state
      traced[rangeAccumulator ↦
        Bool.xor (traced rangeAccumulator) (traced control)] := by
  apply run_rangeScanUnitary false .inc tree control rangeAccumulator path
    (zeroMapProtectedWires tree control path)
    (zeroMapDataWires k K control rangeAccumulator temporary bitAt dirtyAt)
    (lowerZeroReverseLeaf k K temporary bitAt dirtyAt) state
  · exact hlayout.decoder
  · intro wire hwire
    exact hwire
  · exact hlayout.range_not_protected
  · exact fun wire hprotected hdata => hlayout.shared_eq_control hprotected hdata
  · exact lowerZeroReverseLeaf_usesOnly k K hkK control rangeAccumulator temporary bitAt dirtyAt
  · exact lowerZeroReverseLeaf_preserves_control k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout
  · exact hclean

/-! ### Exact direct-state traces -/

/-- The decoder-erased upper-forward trace is the corresponding fold of the proved recurrence
state transformer.  This is the bridge used below to discharge the source-order Boolean
recurrence without exposing decoder path values. -/
theorem run_upperZeroForwardScan_direct
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false) :
    Classical.run
      (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state =
      let seeded := state[rangeAccumulator ↦
        Bool.xor (state rangeAccumulator) (state control)]
      (tree.visitPulses .inc (state control) seeded).foldl
        (fun current pulse =>
          rangeScanDirectLeafState true rangeAccumulator
            (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
            pulse.1 pulse.2 current) seeded := by
  rw [run_upperZeroForwardScan k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath]
  let seeded := state[rangeAccumulator ↦
    Bool.xor (state rangeAccumulator) (state control)]
  rw [UnaryActionTree.runLogicalTree_eq_foldl]
  apply foldl_rangeScanLogical_eq_direct true rangeAccumulator temporary
    (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)
    (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
  · exact hlayout.range_ne_temporary
  · intro label state' hclean
    exact run_upperZeroForwardLeaf k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt hlayout label state' hclean
  · intro label state'
    exact upperZeroForwardLeafState_preserves_temporary k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state'
  · rw [upd_other state rangeAccumulator _ (Ne.symm hlayout.range_ne_temporary)]
    exact hcleanTemporary

theorem run_upperZeroReverseScan_direct
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false) :
    Classical.run
      (rangeScanUnitary false .dec tree control rangeAccumulator path
        (upperZeroReverseLeaf k K temporary bitAt dirtyAt)) state =
      let traced :=
        (tree.visitPulses .dec (state control) state).foldl
          (fun current pulse =>
            rangeScanDirectLeafState false rangeAccumulator
              (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
              pulse.1 pulse.2 current) state
      traced[rangeAccumulator ↦
        Bool.xor (traced rangeAccumulator) (traced control)] := by
  rw [run_upperZeroReverseScan k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath,
    UnaryActionTree.runLogicalTree_eq_foldl]
  rw [foldl_rangeScanLogical_eq_direct false rangeAccumulator temporary
    (upperZeroReverseLeaf k K temporary bitAt dirtyAt)
    (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)]
  · exact hlayout.range_ne_temporary
  · intro label state' hclean
    exact run_upperZeroReverseLeaf k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt hlayout label state' hclean
  · intro label state'
    exact upperZeroReverseLeafState_preserves_temporary k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state'
  · exact hcleanTemporary

theorem run_lowerZeroForwardScan_direct
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false) :
    Classical.run
      (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state =
      let seeded := state[rangeAccumulator ↦
        Bool.xor (state rangeAccumulator) (state control)]
      (tree.visitPulses .dec (state control) seeded).foldl
        (fun current pulse =>
          rangeScanDirectLeafState true rangeAccumulator
            (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
            pulse.1 pulse.2 current) seeded := by
  rw [run_lowerZeroForwardScan k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath]
  let seeded := state[rangeAccumulator ↦
    Bool.xor (state rangeAccumulator) (state control)]
  rw [UnaryActionTree.runLogicalTree_eq_foldl]
  apply foldl_rangeScanLogical_eq_direct true rangeAccumulator temporary
    (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)
    (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
  · exact hlayout.range_ne_temporary
  · intro label state' hclean
    exact run_lowerZeroForwardLeaf k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt hlayout label state' hclean
  · intro label state'
    exact lowerZeroForwardLeafState_preserves_temporary k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state'
  · rw [upd_other state rangeAccumulator _ (Ne.symm hlayout.range_ne_temporary)]
    exact hcleanTemporary

theorem run_lowerZeroReverseScan_direct
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false) :
    Classical.run
      (rangeScanUnitary false .inc tree control rangeAccumulator path
        (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)) state =
      let traced :=
        (tree.visitPulses .inc (state control) state).foldl
          (fun current pulse =>
            rangeScanDirectLeafState false rangeAccumulator
              (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
              pulse.1 pulse.2 current) state
      traced[rangeAccumulator ↦
        Bool.xor (traced rangeAccumulator) (traced control)] := by
  rw [run_lowerZeroReverseScan k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath,
    UnaryActionTree.runLogicalTree_eq_foldl]
  rw [foldl_rangeScanLogical_eq_direct false rangeAccumulator temporary
    (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)
    (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)]
  · exact hlayout.range_ne_temporary
  · intro label state' hclean
    exact run_lowerZeroReverseLeaf k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt hlayout label state' hclean
  · intro label state'
    exact lowerZeroReverseLeafState_preserves_temporary k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state'
  · exact hcleanTemporary

/-! ### Scratch cleanup of the ordered source scans -/

theorem run_upperZeroForwardScan_range_false
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    Classical.run
      (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state
        rangeAccumulator = false := by
  rw [run_upperZeroForwardScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let seeded := state[rangeAccumulator ↦
    Bool.xor (state rangeAccumulator) (state control)]
  rw [foldl_rangeScanDirect_range true rangeAccumulator
    (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)]
  · rw [tree.visitPulses_zeroMap .inc (state control) seeded k K hlabels,
      hlabels]
    have hseeded : seeded rangeAccumulator = state control := by
      simp [seeded, hcleanRange]
    change
      ((zeroMapLabels k K).map fun label =>
        (label, state control && decide (label = tree.routeLabel seeded))).foldl
          (fun current pulse => Bool.xor current pulse.2)
          (seeded rangeAccumulator) = false
    rw [hseeded]
    apply foldl_routePulses_eq_false
    · rw [← hlabels, UnaryActionTree.visitLabels_inc]
      exact tree.routeLabel_mem_labels seeded
    · exact zeroMapLabels_nodup k K
  · intro label state'
    exact upperZeroForwardLeafState_preserves_range k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state'

theorem run_lowerZeroForwardScan_range_false
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    Classical.run
      (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state
        rangeAccumulator = false := by
  rw [run_lowerZeroForwardScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let seeded := state[rangeAccumulator ↦
    Bool.xor (state rangeAccumulator) (state control)]
  rw [foldl_rangeScanDirect_range true rangeAccumulator
    (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)]
  · rw [tree.visitPulses_zeroMap .dec (state control) seeded k K hlabels,
      UnaryActionTree.visitLabels_dec]
    have htreeLabels : tree.labels = zeroMapLabels k K := by
      simpa using hlabels
    rw [htreeLabels]
    have hseeded : seeded rangeAccumulator = state control := by
      simp [seeded, hcleanRange]
    change
      ((zeroMapLabels k K).reverse.map fun label =>
        (label, state control && decide (label = tree.routeLabel seeded))).foldl
          (fun current pulse => Bool.xor current pulse.2)
          (seeded rangeAccumulator) = false
    rw [hseeded]
    apply foldl_routePulses_eq_false
    · rw [List.mem_reverse, ← hlabels, UnaryActionTree.visitLabels_inc]
      exact tree.routeLabel_mem_labels seeded
    · exact List.nodup_reverse.mpr (zeroMapLabels_nodup k K)
  · intro label state'
    exact lowerZeroForwardLeafState_preserves_range k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state'

/-! ### Dirty-word meaning of the upper source scan -/

private theorem foldl_upperZeroForward_read_self
    (k K boundary : Nat) (hkK : k ≤ K) (hboundary : boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcontrol : state control = enabled)
    (hrange : state rangeAccumulator = (enabled && decide (K ≤ boundary))) :
    let pulses := (zeroMapLabels K K).map fun label =>
      (label, enabled && decide (label = boundary))
    let result := pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState true rangeAccumulator
          (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state
    readWireWord (zeroMapLabels K K) dirtyAt result =
      upperDirtyForwardSeed enabled
        (upperRangeBits enabled boundary (zeroMapLabels K K) bitAt state)
        (readWireWord (zeroMapLabels K K) dirtyAt state) := by
  have hlabel : K ∈ zeroMapLabels k K := (mem_zeroMapLabels hkK).2 ⟨hkK, le_rfl⟩
  have hrangeDirty := hlayout.range_ne_dirty hlabel
  have hdirtyRange : dirtyAt K ≠ rangeAccumulator := Ne.symm hrangeDirty
  have hcontrolDirty := hlayout.control_ne_dirty hlabel
  by_cases hbeq : boundary = K
  · subst boundary
    cases enabled <;> cases hb : state (bitAt K) <;>
      cases hd : state (dirtyAt K) <;>
      simp_all [zeroMapLabels_self, rangeScanDirectLeafState,
        upperZeroForwardLeafState, zeroRecurrenceCellState,
        readWireWord, upperRangeBits, upperDirtyForwardSeed,
        upperDirtyForward, upd]
  · have hlt : boundary < K := lt_of_le_of_ne hboundary hbeq
    have hnotle : ¬K ≤ boundary := by omega
    have hKbeq : K ≠ boundary := Ne.symm hbeq
    cases enabled <;> cases hb : state (bitAt K) <;>
      cases hd : state (dirtyAt K) <;>
      simp_all [zeroMapLabels_self, rangeScanDirectLeafState,
        upperZeroForwardLeafState, zeroRecurrenceCellState,
        readWireWord, upperRangeBits, upperDirtyForwardSeed,
        upperDirtyForward, upd]

private theorem foldl_upperZeroForward_read
    (k j K boundary : Nat) (hkj : k ≤ j) (hjK : j ≤ K)
    (hboundary : boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcontrol : state control = enabled)
    (hrange : state rangeAccumulator = (enabled && decide (j ≤ boundary))) :
    let pulses := (zeroMapLabels j K).map fun label =>
      (label, enabled && decide (label = boundary))
    let result := pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState true rangeAccumulator
          (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state
    readWireWord (zeroMapLabels j K) dirtyAt result =
      upperDirtyForwardSeed enabled
        (upperRangeBits enabled boundary (zeroMapLabels j K) bitAt state)
        (readWireWord (zeroMapLabels j K) dirtyAt state) := by
  induction hjK using Nat.decreasingInduction generalizing state with
  | self =>
      exact foldl_upperZeroForward_read_self k K boundary hkj hboundary tree
        control rangeAccumulator temporary path bitAt dirtyAt enabled state
        hlayout hcontrol hrange
  | of_succ j hjK ih =>
      rw [zeroMapLabels_cons hjK]
      simp only [List.map_cons, List.foldl_cons, readWireWord, upperRangeBits]
      let tailLabels := zeroMapLabels (j + 1) K
      let tailPulses := tailLabels.map fun label =>
        (label, enabled && decide (label = boundary))
      let first := rangeScanDirectLeafState true rangeAccumulator
        (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
        j (enabled && decide (j = boundary)) state
      let result := tailPulses.foldl
        (fun current pulse =>
          rangeScanDirectLeafState true rangeAccumulator
            (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
            pulse.1 pulse.2 current) first
      change
        result (dirtyAt j) :: readWireWord tailLabels dirtyAt result =
          upperDirtyForwardSeed enabled
            ((enabled && decide (j ≤ boundary) && state (bitAt j)) ::
              upperRangeBits enabled boundary tailLabels bitAt state)
            (state (dirtyAt j) :: readWireWord tailLabels dirtyAt state)
      have hjmem : j ∈ zeroMapLabels k K :=
        (mem_zeroMapLabels (hkj.trans hjK.le)).2 ⟨hkj, hjK.le⟩
      have hnextMem : j + 1 ∈ zeroMapLabels k K :=
        (mem_zeroMapLabels (hkj.trans hjK.le)).2 ⟨by omega, hjK⟩
      have htailMem : ∀ label, label ∈ tailLabels →
          label ∈ zeroMapLabels k K := by
        intro label hlabel
        apply (mem_zeroMapLabels (hkj.trans hjK.le)).2
        have := (mem_zeroMapLabels hjK).1 hlabel
        omega
      have hfirstControl : first control = enabled := by
        simp only [first, rangeScanDirectLeafState, if_pos]
        rw [upd_other _ rangeAccumulator _ hlayout.control_ne_range]
        rw [upperZeroForwardLeafState_preserves]
        · exact hcontrol
        · exact hlayout.control_ne_dirty hjmem
      have hfirstRange : first rangeAccumulator =
          (enabled && decide (j + 1 ≤ boundary)) := by
        simp only [first, rangeScanDirectLeafState, if_pos, upd_same]
        rw [upperZeroForwardLeafState_preserves_range k K
          (hkj.trans hjK.le) tree control rangeAccumulator temporary path
          bitAt dirtyAt hlayout j state, hrange,
          xor_leq_routePulse]
      have hfirstBit : ∀ label, label ∈ tailLabels →
          first (bitAt label) = state (bitAt label) := by
        intro label hlabel
        have hoverall := htailMem label hlabel
        simp only [first, rangeScanDirectLeafState, if_pos]
        rw [upd_other _ rangeAccumulator _
          (Ne.symm (hlayout.range_ne_bit hoverall))]
        apply upperZeroForwardLeafState_preserves
        exact hlayout.bit_ne_dirty hoverall hjmem
      have hfirstDirty : ∀ label, label ∈ tailLabels →
          first (dirtyAt label) = state (dirtyAt label) := by
        intro label hlabel
        have hoverall := htailMem label hlabel
        have hlabelBounds := (mem_zeroMapLabels hjK).1 hlabel
        have hne : dirtyAt label ≠ dirtyAt j := by
          intro equality
          have := hlayout.dirty_injective hoverall hjmem equality
          omega
        simp only [first, rangeScanDirectLeafState, if_pos]
        rw [upd_other _ rangeAccumulator _
          (Ne.symm (hlayout.range_ne_dirty hoverall))]
        exact upperZeroForwardLeafState_preserves k K control rangeAccumulator
          bitAt dirtyAt j state (dirtyAt label) hne
      have hfirstBits : upperRangeBits enabled boundary tailLabels bitAt first =
          upperRangeBits enabled boundary tailLabels bitAt state := by
        unfold upperRangeBits
        apply List.map_congr_left
        intro label hlabel
        rw [hfirstBit label hlabel]
      have hfirstDirtyWord : readWireWord tailLabels dirtyAt first =
          readWireWord tailLabels dirtyAt state := by
        unfold readWireWord
        apply List.map_congr_left
        intro label hlabel
        rw [hfirstDirty label hlabel]
      have htail := ih (by omega) first hfirstControl hfirstRange
      change readWireWord tailLabels dirtyAt result =
        upperDirtyForwardSeed enabled
          (upperRangeBits enabled boundary tailLabels bitAt first)
          (readWireWord tailLabels dirtyAt first) at htail
      rw [hfirstBits, hfirstDirtyWord] at htail
      have hhead : result (dirtyAt j) = first (dirtyAt j) := by
        apply foldl_rangeScanDirect_preserves_of_mem true rangeAccumulator
          (dirtyAt j)
          (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
          tailPulses first
        · exact Ne.symm (hlayout.range_ne_dirty hjmem)
        · intro label hlabel state'
          have hlabelTail : label ∈ tailLabels := by
            simpa [tailPulses] using hlabel
          have hoverall := htailMem label hlabelTail
          apply upperZeroForwardLeafState_preserves
          intro equality
          have := hlayout.dirty_injective hjmem hoverall equality
          have hlabelBounds := (mem_zeroMapLabels hjK).1 hlabelTail
          omega
      have hfirstHead : first (dirtyAt j) =
          Bool.xor (state (dirtyAt j))
            (!(enabled && decide (j ≤ boundary) && state (bitAt j)) &&
              state (dirtyAt (j + 1))) := by
        have hdirtyRange : dirtyAt j ≠ rangeAccumulator :=
          Ne.symm (hlayout.range_ne_dirty hjmem)
        simp [first, rangeScanDirectLeafState, upperZeroForwardLeafState,
          zeroRecurrenceCellState, hkj, hjK.le, hjK.ne, hrange,
          upd, hdirtyRange]
      rw [hhead, hfirstHead, htail]
      obtain ⟨rest, htailCons⟩ : ∃ rest,
          tailLabels = (j + 1) :: rest := by
        by_cases heq : j + 1 = K
        · subst K
          exact ⟨[], by simp [tailLabels]⟩
        · exact ⟨zeroMapLabels (j + 2) K, by
            simpa [tailLabels] using
              (zeroMapLabels_cons (k := j + 1) (K := K) (by omega))⟩
      rw [htailCons]
      simp [upperRangeBits, readWireWord, upperDirtyForwardSeed]

/-- The literal increasing `range_scan_leq` pass computes the first dirty suffix recurrence over
the boundary-masked source bits. -/
theorem readWireWord_run_upperZeroForwardScan
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    readWireWord (zeroMapLabels k K) dirtyAt
      (Classical.run
        (rangeScanUnitary true .inc tree control rangeAccumulator path
          (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state) =
      upperDirtyForwardSeed (state control)
        (upperRangeBits (state control) boundary (zeroMapLabels k K) bitAt state)
        (readWireWord (zeroMapLabels k K) dirtyAt state) := by
  rw [run_upperZeroForwardScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let seeded := state[rangeAccumulator ↦
    Bool.xor (state rangeAccumulator) (state control)]
  have hrouteSeeded : tree.routeLabel seeded = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    simp only [seeded]
    rw [upd_other]
    intro equality
    subst wire
    exact hlayout.range_not_protected (by
      simp [zeroMapProtectedWires, hwire])
  change readWireWord (zeroMapLabels k K) dirtyAt
      ((tree.visitPulses .inc (state control) seeded).foldl
        (fun current pulse =>
          rangeScanDirectLeafState true rangeAccumulator
            (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
            pulse.1 pulse.2 current) seeded) = _
  rw [tree.visitPulses_zeroMap .inc (state control) seeded k K hlabels,
    hlabels, hrouteSeeded]
  have hseededControl : seeded control = state control := by
    simp only [seeded]
    rw [upd_other]
    exact hlayout.control_ne_range
  have hseededRange : seeded rangeAccumulator =
      ((state control) && decide (k ≤ boundary)) := by
    simp [seeded, hcleanRange, hboundary.1]
  have hfold := foldl_upperZeroForward_read k k K boundary le_rfl hkK
    hboundary.2 tree control rangeAccumulator temporary path bitAt dirtyAt
    (state control) seeded hlayout hseededControl hseededRange
  have hseededBits :
      upperRangeBits (state control) boundary (zeroMapLabels k K) bitAt seeded =
        upperRangeBits (state control) boundary (zeroMapLabels k K) bitAt state := by
    unfold upperRangeBits
    apply List.map_congr_left
    intro label hlabel
    simp only [seeded]
    rw [upd_other]
    exact Ne.symm (hlayout.range_ne_bit hlabel)
  have hseededDirty :
      readWireWord (zeroMapLabels k K) dirtyAt seeded =
        readWireWord (zeroMapLabels k K) dirtyAt state := by
    unfold readWireWord
    apply List.map_congr_left
    intro label hlabel
    simp only [seeded]
    rw [upd_other]
    exact Ne.symm (hlayout.range_ne_dirty hlabel)
  rw [hseededBits, hseededDirty] at hfold
  exact hfold

private theorem foldl_upperZeroReverse_range
    (k j K boundary : Nat) (hkj : k ≤ j) (hjK : j ≤ K)
    (hboundary : boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanRange : state rangeAccumulator = false) :
    let pulses := (zeroMapLabels j K).reverse.map fun label =>
      (label, enabled && decide (label = boundary))
    pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState false rangeAccumulator
          (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state rangeAccumulator =
      (enabled && decide (j ≤ boundary)) := by
  dsimp only
  rw [foldl_rangeScanDirect_range false rangeAccumulator
    (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)]
  · rw [hcleanRange]
    by_cases hle : j ≤ boundary
    · have hmem : boundary ∈ (zeroMapLabels j K).reverse := by
        rw [List.mem_reverse]
        exact (mem_zeroMapLabels hjK).2 ⟨hle, hboundary⟩
      rw [foldl_routePulses_eq_xor _ enabled false boundary hmem
        (List.nodup_reverse.mpr (zeroMapLabels_nodup j K))]
      simp [hle]
    · have hnotmem : boundary ∉ (zeroMapLabels j K).reverse := by
        rw [List.mem_reverse]
        intro hmem
        exact hle ((mem_zeroMapLabels hjK).1 hmem).1
      rw [foldl_routePulses_not_mem _ enabled false boundary hnotmem]
      simp [hle]
  · intro label state'
    exact upperZeroReverseLeafState_preserves_range k K (hkj.trans hjK)
      tree control rangeAccumulator temporary path bitAt dirtyAt hlayout label state'

private theorem foldl_upperZeroReverse_read_self
    (k K boundary : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    let pulses := (zeroMapLabels K K).reverse.map fun label =>
      (label, enabled && decide (label = boundary))
    let result := pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState false rangeAccumulator
          (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state
    readWireWord (zeroMapLabels K K) dirtyAt result =
      upperDirtyReverse
        (upperRangeBits enabled boundary (zeroMapLabels K K) bitAt state)
        (readWireWord (zeroMapLabels K K) dirtyAt state) := by
  have hlabel : K ∈ zeroMapLabels k K := (mem_zeroMapLabels hkK).2 ⟨hkK, le_rfl⟩
  have hdirtyRange : dirtyAt K ≠ rangeAccumulator :=
    Ne.symm (hlayout.range_ne_dirty hlabel)
  simp [zeroMapLabels_self, rangeScanDirectLeafState,
    upperZeroReverseLeafState, upperDirtyReverse, upperRangeBits,
    readWireWord, upd, hdirtyRange]

private theorem foldl_upperZeroReverse_read
    (k j K boundary : Nat) (hkj : k ≤ j) (hjK : j ≤ K)
    (hboundary : boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanRange : state rangeAccumulator = false) :
    let pulses := (zeroMapLabels j K).reverse.map fun label =>
      (label, enabled && decide (label = boundary))
    let result := pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState false rangeAccumulator
          (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state
    readWireWord (zeroMapLabels j K) dirtyAt result =
      upperDirtyReverse
        (upperRangeBits enabled boundary (zeroMapLabels j K) bitAt state)
        (readWireWord (zeroMapLabels j K) dirtyAt state) := by
  induction hjK using Nat.decreasingInduction generalizing state with
  | self =>
      exact foldl_upperZeroReverse_read_self k K boundary hkj tree control
        rangeAccumulator temporary path bitAt dirtyAt enabled state hlayout
  | of_succ j hjK ih =>
      rw [zeroMapLabels_cons hjK]
      dsimp only
      rw [List.reverse_cons, List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      let tailLabels := zeroMapLabels (j + 1) K
      let tailPulses := tailLabels.reverse.map fun label =>
        (label, enabled && decide (label = boundary))
      let afterTail := tailPulses.foldl
        (fun current pulse =>
          rangeScanDirectLeafState false rangeAccumulator
            (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
            pulse.1 pulse.2 current) state
      let result := rangeScanDirectLeafState false rangeAccumulator
        (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
        j (enabled && decide (j = boundary)) afterTail
      change readWireWord (j :: tailLabels) dirtyAt result =
        upperDirtyReverse
          (upperRangeBits enabled boundary (j :: tailLabels) bitAt state)
          (readWireWord (j :: tailLabels) dirtyAt state)
      have hjmem : j ∈ zeroMapLabels k K :=
        (mem_zeroMapLabels (hkj.trans hjK.le)).2 ⟨hkj, hjK.le⟩
      have htailMem : ∀ label, label ∈ tailLabels →
          label ∈ zeroMapLabels k K := by
        intro label hlabel
        apply (mem_zeroMapLabels (hkj.trans hjK.le)).2
        have := (mem_zeroMapLabels hjK).1 hlabel
        omega
      have htail := ih (by omega) state hcleanRange
      change readWireWord tailLabels dirtyAt afterTail =
        upperDirtyReverse
          (upperRangeBits enabled boundary tailLabels bitAt state)
          (readWireWord tailLabels dirtyAt state) at htail
      have hafterRange : afterTail rangeAccumulator =
          (enabled && decide (j + 1 ≤ boundary)) := by
        exact foldl_upperZeroReverse_range k (j + 1) K boundary (by omega)
          hjK hboundary tree control rangeAccumulator temporary path bitAt dirtyAt
          enabled state hlayout hcleanRange
      have hafterBit : afterTail (bitAt j) = state (bitAt j) := by
        apply foldl_rangeScanDirect_preserves_of_mem false rangeAccumulator
          (bitAt j)
          (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          tailPulses state
        · exact Ne.symm (hlayout.range_ne_bit hjmem)
        · intro label hlabel state'
          have hlabelTail : label ∈ tailLabels := by
            simpa [tailPulses] using hlabel
          apply upperZeroReverseLeafState_preserves
          exact hlayout.bit_ne_dirty hjmem (htailMem label hlabelTail)
      have hafterDirty : afterTail (dirtyAt j) = state (dirtyAt j) := by
        apply foldl_rangeScanDirect_preserves_of_mem false rangeAccumulator
          (dirtyAt j)
          (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          tailPulses state
        · exact Ne.symm (hlayout.range_ne_dirty hjmem)
        · intro label hlabel state'
          have hlabelTail : label ∈ tailLabels := by
            simpa [tailPulses] using hlabel
          have hoverall := htailMem label hlabelTail
          apply upperZeroReverseLeafState_preserves
          intro equality
          have := hlayout.dirty_injective hjmem hoverall equality
          have hlabelBounds := (mem_zeroMapLabels hjK).1 hlabelTail
          omega
      obtain ⟨rest, htailCons⟩ : ∃ rest,
          tailLabels = (j + 1) :: rest := by
        by_cases heq : j + 1 = K
        · subst K
          exact ⟨[], by simp [tailLabels]⟩
        · exact ⟨zeroMapLabels (j + 2) K, by
            simpa [tailLabels] using
              (zeroMapLabels_cons (k := j + 1) (K := K) (by omega))⟩
      let tailWord := upperDirtyReverse
        (upperRangeBits enabled boundary tailLabels bitAt state)
        (readWireWord tailLabels dirtyAt state)
      have hnext : afterTail (dirtyAt (j + 1)) = tailWord.headD false := by
        have := congrArg (fun word : List Bool => word.headD false) htail
        simpa [tailWord, htailCons, readWireWord] using this
      have hresultTail : readWireWord tailLabels dirtyAt result =
          readWireWord tailLabels dirtyAt afterTail := by
        unfold readWireWord
        apply List.map_congr_left
        intro label hlabel
        have hoverall := htailMem label hlabel
        have hne : dirtyAt label ≠ dirtyAt j := by
          intro equality
          have := hlayout.dirty_injective hoverall hjmem equality
          have hlabelBounds := (mem_zeroMapLabels hjK).1 hlabel
          omega
        rw [show result = upperZeroReverseLeafState k K rangeAccumulator
            bitAt dirtyAt j
            afterTail[rangeAccumulator ↦ Bool.xor (afterTail rangeAccumulator)
              (enabled && decide (j = boundary))] by
          simp [result, rangeScanDirectLeafState]]
        rw [upperZeroReverseLeafState_preserves _ _ _ _ _ _ _ _ hne]
        rw [upd_other]
        exact Ne.symm (hlayout.range_ne_dirty hoverall)
      have hresultHead : result (dirtyAt j) =
          Bool.xor (state (dirtyAt j))
            (!(enabled && decide (j ≤ boundary) && state (bitAt j)) &&
              tailWord.headD false) := by
        let switched := afterTail[rangeAccumulator ↦
          Bool.xor (afterTail rangeAccumulator)
            (enabled && decide (j = boundary))]
        have hresultEq : result = upperZeroReverseLeafState k K rangeAccumulator
            bitAt dirtyAt j switched := by
          simp [result, switched, rangeScanDirectLeafState]
        have hswitchRange : switched rangeAccumulator =
            (enabled && decide (j ≤ boundary)) := by
          simp only [switched, upd_same]
          rw [hafterRange, xor_geq_routePulse]
        have hswitchBit : switched (bitAt j) = state (bitAt j) := by
          simp only [switched]
          rw [upd_other _ rangeAccumulator _
            (Ne.symm (hlayout.range_ne_bit hjmem)), hafterBit]
        have hswitchDirty : switched (dirtyAt j) = state (dirtyAt j) := by
          simp only [switched]
          rw [upd_other _ rangeAccumulator _
            (Ne.symm (hlayout.range_ne_dirty hjmem)), hafterDirty]
        have hnextMem : j + 1 ∈ zeroMapLabels k K :=
          (mem_zeroMapLabels (hkj.trans hjK.le)).2 ⟨by omega, hjK⟩
        have hswitchNext : switched (dirtyAt (j + 1)) = tailWord.headD false := by
          simp only [switched]
          rw [upd_other _ rangeAccumulator _
            (Ne.symm (hlayout.range_ne_dirty hnextMem)), hnext]
        rw [hresultEq]
        simp [upperZeroReverseLeafState, hkj, hjK,
          zeroRecurrenceCellState, hswitchRange, hswitchBit,
          hswitchDirty, hswitchNext]
      change result (dirtyAt j) :: readWireWord tailLabels dirtyAt result = _
      rw [hresultHead, hresultTail, htail]
      change
        (Bool.xor (state (dirtyAt j))
          (!(enabled && decide (j ≤ boundary) && state (bitAt j)) &&
            (upperDirtyReverse
              (upperRangeBits enabled boundary tailLabels bitAt state)
              (readWireWord tailLabels dirtyAt state)).headD false)) ::
            upperDirtyReverse
              (upperRangeBits enabled boundary tailLabels bitAt state)
              (readWireWord tailLabels dirtyAt state) = _
      rw [htailCons]
      simp [upperRangeBits, readWireWord, upperDirtyReverse]

/-- The literal decreasing `range_scan_leq` pass performs the cancelling reverse recurrence on
the same boundary-masked source bits. -/
theorem readWireWord_run_upperZeroReverseScan
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    readWireWord (zeroMapLabels k K) dirtyAt
      (Classical.run
        (rangeScanUnitary false .dec tree control rangeAccumulator path
          (upperZeroReverseLeaf k K temporary bitAt dirtyAt)) state) =
      upperDirtyReverse
        (upperRangeBits (state control) boundary (zeroMapLabels k K) bitAt state)
        (readWireWord (zeroMapLabels k K) dirtyAt state) := by
  rw [run_upperZeroReverseScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let pulses := tree.visitPulses .dec (state control) state
  let traced := pulses.foldl
    (fun current pulse =>
      rangeScanDirectLeafState false rangeAccumulator
        (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
        pulse.1 pulse.2 current) state
  change readWireWord (zeroMapLabels k K) dirtyAt
    traced[rangeAccumulator ↦ Bool.xor (traced rangeAccumulator) (traced control)] = _
  rw [readWireWord_upd_not_mem]
  · have htreeLabels : tree.labels = zeroMapLabels k K := by
      simpa using hlabels
    have hpulses : pulses =
        (zeroMapLabels k K).reverse.map fun label =>
          (label, state control && decide (label = boundary)) := by
      simp only [pulses]
      rw [tree.visitPulses_zeroMap .dec (state control) state k K hlabels,
        UnaryActionTree.visitLabels_dec, htreeLabels, hroute]
    simp only [traced]
    rw [hpulses]
    exact foldl_upperZeroReverse_read k k K boundary le_rfl hkK hboundary.2
      tree control rangeAccumulator temporary path bitAt dirtyAt (state control)
      state hlayout hcleanRange
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨label, hlabel, equality⟩ := hmem
    exact hlayout.range_ne_dirty hlabel equality.symm

/-! ### Complete upper zero map -/

private theorem upperZeroForwardLeafState_preserves_protected
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) (wire : Wire)
    (hwire : wire ∈ zeroMapProtectedWires tree control path) :
    upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state wire =
      state wire := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · apply upperZeroForwardLeafState_preserves
    intro equality
    subst wire
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    have hshared := hlayout.shared_eq_control hwire (by
      simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_map]
      right
      exact ⟨label, hlabel, rfl⟩)
    exact hlayout.control_ne_dirty hlabel hshared.symm
  · simp [upperZeroForwardLeafState, hwindow]

private theorem upperZeroForwardLeafState_preserves_bit
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (bitLabel : Nat) (hbitLabel : bitLabel ∈ zeroMapLabels k K)
    (label : Nat) (state : BasisState) :
    upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state
        (bitAt bitLabel) = state (bitAt bitLabel) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · apply upperZeroForwardLeafState_preserves
    exact hlayout.bit_ne_dirty hbitLabel ((mem_zeroMapLabels hkK).2 hwindow)
  · simp [upperZeroForwardLeafState, hwindow]

private theorem run_upperZeroForwardScan_preserves
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireRange : wire ≠ rangeAccumulator)
    (hleaf : ∀ label state',
      upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state' wire =
        state' wire) :
    Classical.run
      (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state wire =
      state wire := by
  rw [run_upperZeroForwardScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let seeded := state[rangeAccumulator ↦
    Bool.xor (state rangeAccumulator) (state control)]
  change
    ((tree.visitPulses .inc (state control) seeded).foldl
      (fun current pulse =>
        rangeScanDirectLeafState true rangeAccumulator
          (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) seeded) wire = state wire
  calc
    _ = seeded wire := foldl_rangeScanDirect_preserves true rangeAccumulator wire
      (upperZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
      (tree.visitPulses .inc (state control) seeded) seeded hwireRange hleaf
    _ = state wire := by
      simp only [seeded]
      rw [upd_other]
      exact hwireRange

private theorem run_upperZeroForwardScan_preserves_protected
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwire : wire ∈ zeroMapProtectedWires tree control path) :
    Classical.run
      (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state wire =
      state wire := by
  apply run_upperZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary wire
  · intro equality
    subst wire
    exact hlayout.range_not_protected hwire
  · intro label state'
    exact upperZeroForwardLeafState_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state' wire hwire

private theorem run_upperZeroForwardScan_preserves_bit
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (label : Nat) (hlabel : label ∈ zeroMapLabels k K) :
    Classical.run
      (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state (bitAt label) =
      state (bitAt label) := by
  apply run_upperZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary (bitAt label)
  · exact Ne.symm (hlayout.range_ne_bit hlabel)
  · exact upperZeroForwardLeafState_preserves_bit k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label hlabel

/-- The complete literal two-scan upper block XORs the boundary-masked suffix-zero flags into
the borrowed dirty bank. -/
theorem upperZeroMapUnitary_correct
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    readWireWord (zeroMapLabels k K) dirtyAt
      (Classical.run
        (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
        state) =
      xorWords (readWireWord (zeroMapLabels k K) dirtyAt state)
        (gateWord (state control)
          (suffixZeroFlags
            (upperRangeBits (state control) boundary (zeroMapLabels k K) bitAt state))) := by
  let first := Classical.run
    (rangeScanUnitary true .inc tree control rangeAccumulator path
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state
  have hfirstProtected : ∀ wire,
      wire ∈ zeroMapProtectedWires tree control path → first wire = state wire := by
    intro wire hwire
    exact run_upperZeroForwardScan_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt state hlayout hcleanPath
      hcleanTemporary wire hwire
  have hfirstControl : first control = state control :=
    hfirstProtected control (by simp [zeroMapProtectedWires])
  have hfirstCleanPath : Clean path first := by
    intro wire hwire
    rw [hfirstProtected wire (by simp [zeroMapProtectedWires, hwire])]
    exact hcleanPath wire hwire
  have hfirstTemporary : first temporary = false := by
    change Classical.run
      (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state temporary = false
    exact (run_upperZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary temporary
      (Ne.symm hlayout.range_ne_temporary)
      (upperZeroForwardLeafState_preserves_temporary k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout)).trans hcleanTemporary
  have hfirstRange : first rangeAccumulator = false :=
    run_upperZeroForwardScan_range_false k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hlabels hcleanPath hcleanRange hcleanTemporary
  have hfirstRoute : tree.routeLabel first = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstProtected wire (by simp [zeroMapProtectedWires, hwire])
  have hfirstBits :
      upperRangeBits (first control) boundary (zeroMapLabels k K) bitAt first =
        upperRangeBits (state control) boundary (zeroMapLabels k K) bitAt state := by
    unfold upperRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hfirstControl]
    have hbit : first (bitAt label) = state (bitAt label) :=
      run_upperZeroForwardScan_preserves_bit k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary label hlabel
    rw [hbit]
  have hfirstDirty := readWireWord_run_upperZeroForwardScan k K boundary hkK hboundary
    tree control rangeAccumulator temporary path bitAt dirtyAt state hlayout hlabels hroute
    hcleanPath hcleanRange hcleanTemporary
  rw [upperZeroMapUnitary, Classical.run_append]
  change readWireWord (zeroMapLabels k K) dirtyAt
    (Classical.run
      (rangeScanUnitary false .dec tree control rangeAccumulator path
        (upperZeroReverseLeaf k K temporary bitAt dirtyAt)) first) = _
  rw [readWireWord_run_upperZeroReverseScan k K boundary hkK hboundary tree control
    rangeAccumulator temporary path bitAt dirtyAt first hlayout hlabels hfirstRoute
    hfirstCleanPath hfirstRange hfirstTemporary,
    hfirstBits, hfirstDirty]
  exact upperDirtyMapSeed_eq_xor_suffixZeroFlags (state control)
    (upperRangeBits (state control) boundary (zeroMapLabels k K) bitAt state)
    (readWireWord (zeroMapLabels k K) dirtyAt state) (by simp [readWireWord])

/-! ### Dirty-word meaning of the lower source scan -/

private theorem foldl_lowerZeroForward_read_self
    (k K boundary : Nat) (hkK : k ≤ K) (hboundary : k ≤ boundary)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcontrol : state control = enabled)
    (hrange : state rangeAccumulator = (enabled && decide (boundary ≤ k))) :
    let labels := zeroMapLabels k k
    let pulses := labels.reverse.map fun label =>
      (label, enabled && decide (label = boundary))
    let result := pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState true rangeAccumulator
          (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state
    readWireWord labels.reverse dirtyAt result =
      upperDirtyForwardSeed enabled
        (lowerRangeBits enabled boundary labels bitAt state).reverse
        (readWireWord labels dirtyAt state).reverse := by
  have hlabel : k ∈ zeroMapLabels k K := (mem_zeroMapLabels hkK).2 ⟨le_rfl, hkK⟩
  have hdirtyRange := hlayout.range_ne_dirty hlabel
  have hdirtyRange' : dirtyAt k ≠ rangeAccumulator := Ne.symm hdirtyRange
  have hdirtyControl := Ne.symm (hlayout.control_ne_dirty hlabel)
  by_cases hbeq : boundary = k
  · subst boundary
    cases enabled <;> cases hb : state (bitAt k) <;>
      cases hd : state (dirtyAt k) <;>
      simp_all [zeroMapLabels_self, rangeScanDirectLeafState,
        lowerZeroForwardLeafState, zeroRecurrenceCellState,
        lowerRangeBits, readWireWord, upperDirtyForwardSeed,
        upperDirtyForward, upd]
  · have hnotle : ¬boundary ≤ k := by omega
    have hkbeq : k ≠ boundary := Ne.symm hbeq
    cases enabled <;> cases hb : state (bitAt k) <;>
      cases hd : state (dirtyAt k) <;>
      simp_all [zeroMapLabels_self, rangeScanDirectLeafState,
        lowerZeroForwardLeafState, zeroRecurrenceCellState,
        lowerRangeBits, readWireWord, upperDirtyForwardSeed,
        upperDirtyForward, upd]

private theorem foldl_lowerZeroForward_read
    (k j K boundary : Nat) (hkj : k ≤ j) (hjK : j ≤ K)
    (hboundary : k ≤ boundary)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcontrol : state control = enabled)
    (hrange : state rangeAccumulator = (enabled && decide (boundary ≤ j))) :
    let labels := zeroMapLabels k j
    let pulses := labels.reverse.map fun label =>
      (label, enabled && decide (label = boundary))
    let result := pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState true rangeAccumulator
          (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state
    readWireWord labels.reverse dirtyAt result =
      upperDirtyForwardSeed enabled
        (lowerRangeBits enabled boundary labels bitAt state).reverse
        (readWireWord labels dirtyAt state).reverse := by
  induction j, hkj using Nat.le_induction generalizing state with
  | base =>
      exact foldl_lowerZeroForward_read_self k K boundary hjK hboundary tree
        control rangeAccumulator temporary path bitAt dirtyAt enabled state
        hlayout hcontrol hrange
  | succ j hkj ih =>
      rw [zeroMapLabels_snoc hkj]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.map_append, List.map_cons, List.map_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        readWireWord, lowerRangeBits]
      let oldLabels := zeroMapLabels k j
      let oldPulses := oldLabels.reverse.map fun label =>
        (label, enabled && decide (label = boundary))
      let first := rangeScanDirectLeafState true rangeAccumulator
        (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
        (j + 1) (enabled && decide (j + 1 = boundary)) state
      let result := oldPulses.foldl
        (fun current pulse =>
          rangeScanDirectLeafState true rangeAccumulator
            (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
            pulse.1 pulse.2 current) first
      change
        result (dirtyAt (j + 1)) :: readWireWord oldLabels.reverse dirtyAt result =
          upperDirtyForwardSeed enabled
            ((enabled && decide (boundary ≤ j + 1) && state (bitAt (j + 1))) ::
              (lowerRangeBits enabled boundary oldLabels bitAt state).reverse)
            (state (dirtyAt (j + 1)) ::
              (readWireWord oldLabels dirtyAt state).reverse)
      have htopMem : j + 1 ∈ zeroMapLabels k K :=
        (mem_zeroMapLabels (hkj.trans (by omega))).2 ⟨by omega, by omega⟩
      have holdMem : ∀ label, label ∈ oldLabels →
          label ∈ zeroMapLabels k K := by
        intro label hlabel
        apply (mem_zeroMapLabels (hkj.trans (by omega))).2
        have := (mem_zeroMapLabels hkj).1 hlabel
        omega
      have hfirstControl : first control = enabled := by
        simp only [first, rangeScanDirectLeafState, if_pos]
        rw [upd_other _ rangeAccumulator _ hlayout.control_ne_range]
        rw [lowerZeroForwardLeafState_preserves]
        · exact hcontrol
        · exact hlayout.control_ne_dirty htopMem
      have hfirstRange : first rangeAccumulator =
          (enabled && decide (boundary ≤ j)) := by
        simp only [first, rangeScanDirectLeafState, if_pos, upd_same]
        rw [lowerZeroForwardLeafState_preserves_range k K
          (hkj.trans (by omega)) tree control rangeAccumulator temporary path
          bitAt dirtyAt hlayout (j + 1) state, hrange,
          xor_lowerForward_routePulse]
      have hfirstBit : ∀ label, label ∈ oldLabels →
          first (bitAt label) = state (bitAt label) := by
        intro label hlabel
        have hoverall := holdMem label hlabel
        simp only [first, rangeScanDirectLeafState, if_pos]
        rw [upd_other _ rangeAccumulator _
          (Ne.symm (hlayout.range_ne_bit hoverall))]
        apply lowerZeroForwardLeafState_preserves
        exact hlayout.bit_ne_dirty hoverall htopMem
      have hfirstDirty : ∀ label, label ∈ oldLabels →
          first (dirtyAt label) = state (dirtyAt label) := by
        intro label hlabel
        have hoverall := holdMem label hlabel
        have hlabelBounds := (mem_zeroMapLabels hkj).1 hlabel
        have hne : dirtyAt label ≠ dirtyAt (j + 1) := by
          intro equality
          have := hlayout.dirty_injective hoverall htopMem equality
          omega
        simp only [first, rangeScanDirectLeafState, if_pos]
        rw [upd_other _ rangeAccumulator _
          (Ne.symm (hlayout.range_ne_dirty hoverall))]
        exact lowerZeroForwardLeafState_preserves k K control rangeAccumulator
          bitAt dirtyAt (j + 1) state (dirtyAt label) hne
      have hfirstBits :
          lowerRangeBits enabled boundary oldLabels bitAt first =
            lowerRangeBits enabled boundary oldLabels bitAt state := by
        unfold lowerRangeBits
        apply List.map_congr_left
        intro label hlabel
        rw [hfirstBit label hlabel]
      have hfirstDirtyWord : readWireWord oldLabels dirtyAt first =
          readWireWord oldLabels dirtyAt state := by
        unfold readWireWord
        apply List.map_congr_left
        intro label hlabel
        rw [hfirstDirty label hlabel]
      have htail := ih (by omega) first hfirstControl hfirstRange
      change readWireWord oldLabels.reverse dirtyAt result =
        upperDirtyForwardSeed enabled
          (lowerRangeBits enabled boundary oldLabels bitAt first).reverse
          (readWireWord oldLabels dirtyAt first).reverse at htail
      rw [hfirstBits, hfirstDirtyWord] at htail
      have hhead : result (dirtyAt (j + 1)) = first (dirtyAt (j + 1)) := by
        apply foldl_rangeScanDirect_preserves_of_mem true rangeAccumulator
          (dirtyAt (j + 1))
          (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
          oldPulses first
        · exact Ne.symm (hlayout.range_ne_dirty htopMem)
        · intro label hlabel state'
          have hlabelOld : label ∈ oldLabels := by
            simpa [oldPulses] using hlabel
          have hoverall := holdMem label hlabelOld
          apply lowerZeroForwardLeafState_preserves
          intro equality
          have := hlayout.dirty_injective htopMem hoverall equality
          have hlabelBounds := (mem_zeroMapLabels hkj).1 hlabelOld
          omega
      have hfirstHead : first (dirtyAt (j + 1)) =
          Bool.xor (state (dirtyAt (j + 1)))
            (!(enabled && decide (boundary ≤ j + 1) && state (bitAt (j + 1))) &&
              state (dirtyAt j)) := by
        have hdirtyRange : dirtyAt (j + 1) ≠ rangeAccumulator :=
          Ne.symm (hlayout.range_ne_dirty htopMem)
        have hkTop : k ≤ j + 1 := by omega
        have htopNe : j + 1 ≠ k := by omega
        simp [first, rangeScanDirectLeafState, lowerZeroForwardLeafState,
          hkTop, hjK, htopNe, hrange, zeroRecurrenceCellState, upd, hdirtyRange]
      rw [hhead, hfirstHead, htail]
      obtain ⟨rest, holdCons⟩ := zeroMapLabels_reverse_cons hkj
      have holdCons' : oldLabels.reverse = j :: rest := by
        simpa [oldLabels] using holdCons
      have hbitsRev :
          (lowerRangeBits enabled boundary oldLabels bitAt state).reverse =
            (enabled && decide (boundary ≤ j) && state (bitAt j)) ::
              rest.map fun label =>
                enabled && decide (boundary ≤ label) && state (bitAt label) := by
        unfold lowerRangeBits
        rw [← List.map_reverse, holdCons']
        rfl
      have hdirtyRev :
          (readWireWord oldLabels dirtyAt state).reverse =
            state (dirtyAt j) :: rest.map fun label => state (dirtyAt label) := by
        unfold readWireWord
        rw [← List.map_reverse, holdCons']
        rfl
      rw [hbitsRev, hdirtyRev]
      simp [upperDirtyForwardSeed]

/-- The literal decreasing `range_scan_geq` pass computes the first dirty prefix recurrence over
the boundary-masked source bits. -/
theorem readWireWord_run_lowerZeroForwardScan
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    readWireWord (zeroMapLabels k K) dirtyAt
      (Classical.run
        (rangeScanUnitary true .dec tree control rangeAccumulator path
          (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state) =
      lowerDirtyForwardSeed (state control)
        (lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt state)
        (readWireWord (zeroMapLabels k K) dirtyAt state) := by
  rw [run_lowerZeroForwardScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let seeded := state[rangeAccumulator ↦
    Bool.xor (state rangeAccumulator) (state control)]
  have hrouteSeeded : tree.routeLabel seeded = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    simp only [seeded]
    rw [upd_other]
    intro equality
    subst wire
    exact hlayout.range_not_protected (by
      simp [zeroMapProtectedWires, hwire])
  change readWireWord (zeroMapLabels k K) dirtyAt
      ((tree.visitPulses .dec (state control) seeded).foldl
        (fun current pulse =>
          rangeScanDirectLeafState true rangeAccumulator
            (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
            pulse.1 pulse.2 current) seeded) = _
  rw [tree.visitPulses_zeroMap .dec (state control) seeded k K hlabels,
    UnaryActionTree.visitLabels_dec]
  have htreeLabels : tree.labels = zeroMapLabels k K := by
    simpa using hlabels
  rw [htreeLabels, hrouteSeeded]
  have hseededControl : seeded control = state control := by
    simp only [seeded]
    rw [upd_other]
    exact hlayout.control_ne_range
  have hseededRange : seeded rangeAccumulator =
      ((state control) && decide (boundary ≤ K)) := by
    simp [seeded, hcleanRange, hboundary.2]
  have hfold := foldl_lowerZeroForward_read k K K boundary hkK le_rfl
    hboundary.1 tree control rangeAccumulator temporary path bitAt dirtyAt
    (state control) seeded hlayout hseededControl hseededRange
  have hseededBits :
      lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt seeded =
        lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt state := by
    unfold lowerRangeBits
    apply List.map_congr_left
    intro label hlabel
    simp only [seeded]
    rw [upd_other]
    exact Ne.symm (hlayout.range_ne_bit hlabel)
  have hseededDirty :
      readWireWord (zeroMapLabels k K) dirtyAt seeded =
        readWireWord (zeroMapLabels k K) dirtyAt state := by
    unfold readWireWord
    apply List.map_congr_left
    intro label hlabel
    simp only [seeded]
    rw [upd_other]
    exact Ne.symm (hlayout.range_ne_dirty hlabel)
  change readWireWord (zeroMapLabels k K).reverse dirtyAt
      (((zeroMapLabels k K).reverse.map fun label =>
        (label, state control && decide (label = boundary))).foldl
        (fun current pulse =>
          rangeScanDirectLeafState true rangeAccumulator
            (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
            pulse.1 pulse.2 current) seeded) =
    upperDirtyForwardSeed (state control)
      (lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt seeded).reverse
      (readWireWord (zeroMapLabels k K) dirtyAt seeded).reverse at hfold
  rw [hseededBits, hseededDirty] at hfold
  have hreverse := congrArg List.reverse hfold
  simpa [lowerDirtyForwardSeed] using hreverse

private theorem foldl_lowerZeroReverse_range
    (k j K boundary : Nat) (hkj : k ≤ j) (hjK : j ≤ K)
    (hboundary : k ≤ boundary)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanRange : state rangeAccumulator = false) :
    let pulses := (zeroMapLabels k j).map fun label =>
      (label, enabled && decide (label = boundary))
    pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState false rangeAccumulator
          (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state rangeAccumulator =
      (enabled && decide (boundary ≤ j)) := by
  dsimp only
  rw [foldl_rangeScanDirect_range false rangeAccumulator
    (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)]
  · rw [hcleanRange]
    by_cases hle : boundary ≤ j
    · have hmem : boundary ∈ zeroMapLabels k j :=
        (mem_zeroMapLabels hkj).2 ⟨hboundary, hle⟩
      rw [foldl_routePulses_eq_xor _ enabled false boundary hmem
        (zeroMapLabels_nodup k j)]
      simp [hle]
    · have hnotmem : boundary ∉ zeroMapLabels k j := by
        intro hmem
        exact hle ((mem_zeroMapLabels hkj).1 hmem).2
      rw [foldl_routePulses_not_mem _ enabled false boundary hnotmem]
      simp [hle]
  · intro label state'
    exact lowerZeroReverseLeafState_preserves_range k K (hkj.trans hjK)
      tree control rangeAccumulator temporary path bitAt dirtyAt hlayout label state'

private theorem foldl_lowerZeroReverse_read_self
    (k K boundary : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt) :
    let labels := zeroMapLabels k k
    let pulses := labels.map fun label =>
      (label, enabled && decide (label = boundary))
    let result := pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState false rangeAccumulator
          (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state
    readWireWord labels.reverse dirtyAt result =
      upperDirtyReverse
        (lowerRangeBits enabled boundary labels bitAt state).reverse
        (readWireWord labels dirtyAt state).reverse := by
  have hlabel : k ∈ zeroMapLabels k K := (mem_zeroMapLabels hkK).2 ⟨le_rfl, hkK⟩
  have hdirtyRange : dirtyAt k ≠ rangeAccumulator :=
    Ne.symm (hlayout.range_ne_dirty hlabel)
  simp [zeroMapLabels_self, rangeScanDirectLeafState,
    lowerZeroReverseLeafState, upperDirtyReverse, lowerRangeBits,
    readWireWord, upd, hdirtyRange]

private theorem foldl_lowerZeroReverse_read
    (k j K boundary : Nat) (hkj : k ≤ j) (hjK : j ≤ K)
    (hboundary : k ≤ boundary)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (enabled : Bool) (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanRange : state rangeAccumulator = false) :
    let labels := zeroMapLabels k j
    let pulses := labels.map fun label =>
      (label, enabled && decide (label = boundary))
    let result := pulses.foldl
      (fun current pulse =>
        rangeScanDirectLeafState false rangeAccumulator
          (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) state
    readWireWord labels.reverse dirtyAt result =
      upperDirtyReverse
        (lowerRangeBits enabled boundary labels bitAt state).reverse
        (readWireWord labels dirtyAt state).reverse := by
  induction j, hkj using Nat.le_induction generalizing state with
  | base =>
      exact foldl_lowerZeroReverse_read_self k K boundary hjK tree control
        rangeAccumulator temporary path bitAt dirtyAt enabled state hlayout
  | succ j hkj ih =>
      rw [zeroMapLabels_snoc hkj]
      dsimp only
      rw [List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, readWireWord, lowerRangeBits, List.map_append,
        List.map_cons, List.map_nil]
      let oldLabels := zeroMapLabels k j
      let oldPulses := oldLabels.map fun label =>
        (label, enabled && decide (label = boundary))
      let afterTail := oldPulses.foldl
        (fun current pulse =>
          rangeScanDirectLeafState false rangeAccumulator
            (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
            pulse.1 pulse.2 current) state
      let result := rangeScanDirectLeafState false rangeAccumulator
        (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
        (j + 1) (enabled && decide (j + 1 = boundary)) afterTail
      change
        result (dirtyAt (j + 1)) :: readWireWord oldLabels.reverse dirtyAt result =
          upperDirtyReverse
            ((enabled && decide (boundary ≤ j + 1) && state (bitAt (j + 1))) ::
              (lowerRangeBits enabled boundary oldLabels bitAt state).reverse)
            (state (dirtyAt (j + 1)) ::
              (readWireWord oldLabels dirtyAt state).reverse)
      have htopMem : j + 1 ∈ zeroMapLabels k K :=
        (mem_zeroMapLabels (hkj.trans (by omega))).2 ⟨by omega, by omega⟩
      have holdMem : ∀ label, label ∈ oldLabels →
          label ∈ zeroMapLabels k K := by
        intro label hlabel
        apply (mem_zeroMapLabels (hkj.trans (by omega))).2
        have := (mem_zeroMapLabels hkj).1 hlabel
        omega
      have htail := ih (by omega) state hcleanRange
      change readWireWord oldLabels.reverse dirtyAt afterTail =
        upperDirtyReverse
          (lowerRangeBits enabled boundary oldLabels bitAt state).reverse
          (readWireWord oldLabels dirtyAt state).reverse at htail
      let tailWord := upperDirtyReverse
        (lowerRangeBits enabled boundary oldLabels bitAt state).reverse
        (readWireWord oldLabels dirtyAt state).reverse
      have hafterRange : afterTail rangeAccumulator =
          (enabled && decide (boundary ≤ j)) := by
        exact foldl_lowerZeroReverse_range k j K boundary hkj (by omega)
          hboundary tree control rangeAccumulator temporary path bitAt dirtyAt
          enabled state hlayout hcleanRange
      have hafterBit : afterTail (bitAt (j + 1)) = state (bitAt (j + 1)) := by
        apply foldl_rangeScanDirect_preserves_of_mem false rangeAccumulator
          (bitAt (j + 1))
          (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          oldPulses state
        · exact Ne.symm (hlayout.range_ne_bit htopMem)
        · intro label hlabel state'
          have hlabelOld : label ∈ oldLabels := by
            simpa [oldPulses] using hlabel
          exact lowerZeroReverseLeafState_preserves _ _ _ _ _ _ _ _
            (hlayout.bit_ne_dirty htopMem (holdMem label hlabelOld))
      have hafterDirty : afterTail (dirtyAt (j + 1)) = state (dirtyAt (j + 1)) := by
        apply foldl_rangeScanDirect_preserves_of_mem false rangeAccumulator
          (dirtyAt (j + 1))
          (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
          oldPulses state
        · exact Ne.symm (hlayout.range_ne_dirty htopMem)
        · intro label hlabel state'
          have hlabelOld : label ∈ oldLabels := by
            simpa [oldPulses] using hlabel
          have hoverall := holdMem label hlabelOld
          apply lowerZeroReverseLeafState_preserves
          intro equality
          have := hlayout.dirty_injective htopMem hoverall equality
          have hlabelBounds := (mem_zeroMapLabels hkj).1 hlabelOld
          omega
      obtain ⟨rest, holdCons⟩ := zeroMapLabels_reverse_cons hkj
      have holdCons' : oldLabels.reverse = j :: rest := by
        simpa [oldLabels] using holdCons
      have hbitsRev :
          (lowerRangeBits enabled boundary oldLabels bitAt state).reverse =
            (enabled && decide (boundary ≤ j) && state (bitAt j)) ::
              rest.map fun label =>
                enabled && decide (boundary ≤ label) && state (bitAt label) := by
        unfold lowerRangeBits
        rw [← List.map_reverse, holdCons']
        rfl
      have hdirtyRev :
          (readWireWord oldLabels dirtyAt state).reverse =
            state (dirtyAt j) :: rest.map fun label => state (dirtyAt label) := by
        unfold readWireWord
        rw [← List.map_reverse, holdCons']
        rfl
      have hnext : afterTail (dirtyAt j) = tailWord.headD false := by
        have hhead := congrArg (fun word : List Bool => word.headD false) htail
        change (readWireWord oldLabels.reverse dirtyAt afterTail).headD false =
          tailWord.headD false at hhead
        have hleft : (readWireWord oldLabels.reverse dirtyAt afterTail).headD false =
            afterTail (dirtyAt j) := by
          rw [holdCons']
          rfl
        rw [hleft] at hhead
        exact hhead
      have hresultTail : readWireWord oldLabels.reverse dirtyAt result =
          readWireWord oldLabels.reverse dirtyAt afterTail := by
        unfold readWireWord
        apply List.map_congr_left
        intro label hlabel
        have hlabelOld : label ∈ oldLabels := by
          simpa using hlabel
        have hoverall := holdMem label hlabelOld
        have hne : dirtyAt label ≠ dirtyAt (j + 1) := by
          intro equality
          have := hlayout.dirty_injective hoverall htopMem equality
          have hlabelBounds := (mem_zeroMapLabels hkj).1 hlabelOld
          omega
        rw [show result = lowerZeroReverseLeafState k K rangeAccumulator
            bitAt dirtyAt (j + 1)
            afterTail[rangeAccumulator ↦ Bool.xor (afterTail rangeAccumulator)
              (enabled && decide (j + 1 = boundary))] by
          simp [result, rangeScanDirectLeafState]]
        rw [lowerZeroReverseLeafState_preserves _ _ _ _ _ _ _ _ hne]
        rw [upd_other]
        exact Ne.symm (hlayout.range_ne_dirty hoverall)
      have hresultHead : result (dirtyAt (j + 1)) =
          Bool.xor (state (dirtyAt (j + 1)))
            (!(enabled && decide (boundary ≤ j + 1) && state (bitAt (j + 1))) &&
              tailWord.headD false) := by
        let switched := afterTail[rangeAccumulator ↦
          Bool.xor (afterTail rangeAccumulator)
            (enabled && decide (j + 1 = boundary))]
        have hresultEq : result = lowerZeroReverseLeafState k K rangeAccumulator
            bitAt dirtyAt (j + 1) switched := by
          simp [result, switched, rangeScanDirectLeafState]
        have hswitchRange : switched rangeAccumulator =
            (enabled && decide (boundary ≤ j + 1)) := by
          simp only [switched, upd_same]
          rw [hafterRange, xor_lowerReverse_routePulse]
        have hswitchBit : switched (bitAt (j + 1)) = state (bitAt (j + 1)) := by
          simp only [switched]
          rw [upd_other _ rangeAccumulator _
            (Ne.symm (hlayout.range_ne_bit htopMem)), hafterBit]
        have hswitchDirty : switched (dirtyAt (j + 1)) =
            state (dirtyAt (j + 1)) := by
          simp only [switched]
          rw [upd_other _ rangeAccumulator _
            (Ne.symm (hlayout.range_ne_dirty htopMem)), hafterDirty]
        have hjMem : j ∈ zeroMapLabels k K :=
          (mem_zeroMapLabels (hkj.trans (by omega))).2 ⟨hkj, by omega⟩
        have hswitchNext : switched (dirtyAt j) = tailWord.headD false := by
          simp only [switched]
          rw [upd_other _ rangeAccumulator _
            (Ne.symm (hlayout.range_ne_dirty hjMem)), hnext]
        rw [hresultEq]
        simp [lowerZeroReverseLeafState, hkj, hjK,
          zeroRecurrenceCellState, hswitchRange, hswitchBit,
          hswitchDirty, hswitchNext]
      change result (dirtyAt (j + 1)) ::
        readWireWord oldLabels.reverse dirtyAt result = _
      rw [hresultHead, hresultTail, htail, hbitsRev, hdirtyRev]
      simp only [tailWord, hbitsRev, hdirtyRev]
      simp [upperDirtyReverse]

/-- The literal increasing `range_scan_geq` pass performs the cancelling reverse recurrence on
the same boundary-masked source bits. -/
theorem readWireWord_run_lowerZeroReverseScan
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    readWireWord (zeroMapLabels k K) dirtyAt
      (Classical.run
        (rangeScanUnitary false .inc tree control rangeAccumulator path
          (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)) state) =
      lowerDirtyReverse
        (lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt state)
        (readWireWord (zeroMapLabels k K) dirtyAt state) := by
  rw [run_lowerZeroReverseScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let pulses := tree.visitPulses .inc (state control) state
  let traced := pulses.foldl
    (fun current pulse =>
      rangeScanDirectLeafState false rangeAccumulator
        (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
        pulse.1 pulse.2 current) state
  change readWireWord (zeroMapLabels k K) dirtyAt
    traced[rangeAccumulator ↦ Bool.xor (traced rangeAccumulator) (traced control)] = _
  rw [readWireWord_upd_not_mem]
  · have hpulses : pulses =
        (zeroMapLabels k K).map fun label =>
          (label, state control && decide (label = boundary)) := by
      simp only [pulses]
      rw [tree.visitPulses_zeroMap .inc (state control) state k K hlabels,
        hlabels, hroute]
    simp only [traced]
    rw [hpulses]
    have hfold := foldl_lowerZeroReverse_read k K K boundary hkK le_rfl
      hboundary.1 tree control rangeAccumulator temporary path bitAt dirtyAt
      (state control) state hlayout hcleanRange
    change readWireWord (zeroMapLabels k K).reverse dirtyAt
        (((zeroMapLabels k K).map fun label =>
          (label, state control && decide (label = boundary))).foldl
          (fun current pulse =>
            rangeScanDirectLeafState false rangeAccumulator
              (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
              pulse.1 pulse.2 current) state) =
      upperDirtyReverse
        (lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt state).reverse
        (readWireWord (zeroMapLabels k K) dirtyAt state).reverse at hfold
    have hreverse := congrArg List.reverse hfold
    simpa [lowerDirtyReverse] using hreverse
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨label, hlabel, equality⟩ := hmem
    exact hlayout.range_ne_dirty hlabel equality.symm

/-! ### Complete lower zero map -/

private theorem lowerZeroForwardLeafState_preserves_protected
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) (wire : Wire)
    (hwire : wire ∈ zeroMapProtectedWires tree control path) :
    lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state wire =
      state wire := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · apply lowerZeroForwardLeafState_preserves
    intro equality
    subst wire
    have hlabel := (mem_zeroMapLabels hkK).2 hwindow
    have hshared := hlayout.shared_eq_control hwire (by
      simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_map]
      right
      exact ⟨label, hlabel, rfl⟩)
    exact hlayout.control_ne_dirty hlabel hshared.symm
  · simp [lowerZeroForwardLeafState, hwindow]

private theorem lowerZeroForwardLeafState_preserves_bit
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (bitLabel : Nat) (hbitLabel : bitLabel ∈ zeroMapLabels k K)
    (label : Nat) (state : BasisState) :
    lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state
        (bitAt bitLabel) = state (bitAt bitLabel) := by
  by_cases hwindow : k ≤ label ∧ label ≤ K
  · apply lowerZeroForwardLeafState_preserves
    exact hlayout.bit_ne_dirty hbitLabel ((mem_zeroMapLabels hkK).2 hwindow)
  · simp [lowerZeroForwardLeafState, hwindow]

private theorem run_lowerZeroForwardScan_preserves
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireRange : wire ≠ rangeAccumulator)
    (hleaf : ∀ label state',
      lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt label state' wire =
        state' wire) :
    Classical.run
      (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state wire =
      state wire := by
  rw [run_lowerZeroForwardScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let seeded := state[rangeAccumulator ↦
    Bool.xor (state rangeAccumulator) (state control)]
  change
    ((tree.visitPulses .dec (state control) seeded).foldl
      (fun current pulse =>
        rangeScanDirectLeafState true rangeAccumulator
          (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
          pulse.1 pulse.2 current) seeded) wire = state wire
  calc
    _ = seeded wire := foldl_rangeScanDirect_preserves true rangeAccumulator wire
      (lowerZeroForwardLeafState k K control rangeAccumulator bitAt dirtyAt)
      (tree.visitPulses .dec (state control) seeded) seeded hwireRange hleaf
    _ = state wire := by
      simp only [seeded]
      rw [upd_other]
      exact hwireRange

private theorem run_lowerZeroForwardScan_preserves_protected
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwire : wire ∈ zeroMapProtectedWires tree control path) :
    Classical.run
      (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state wire =
      state wire := by
  apply run_lowerZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary wire
  · intro equality
    subst wire
    exact hlayout.range_not_protected hwire
  · intro label state'
    exact lowerZeroForwardLeafState_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state' wire hwire

private theorem run_lowerZeroForwardScan_preserves_bit
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (label : Nat) (hlabel : label ∈ zeroMapLabels k K) :
    Classical.run
      (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state (bitAt label) =
      state (bitAt label) := by
  apply run_lowerZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary (bitAt label)
  · exact Ne.symm (hlayout.range_ne_bit hlabel)
  · exact lowerZeroForwardLeafState_preserves_bit k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label hlabel

/-- The complete literal two-scan lower block XORs the boundary-masked prefix-zero flags into
the borrowed dirty bank. -/
theorem lowerZeroMapUnitary_correct
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    readWireWord (zeroMapLabels k K) dirtyAt
      (Classical.run
        (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
        state) =
      xorWords (readWireWord (zeroMapLabels k K) dirtyAt state)
        (gateWord (state control)
          (prefixZeroFlags
            (lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt state))) := by
  let first := Classical.run
    (rangeScanUnitary true .dec tree control rangeAccumulator path
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state
  have hfirstProtected : ∀ wire,
      wire ∈ zeroMapProtectedWires tree control path → first wire = state wire := by
    intro wire hwire
    exact run_lowerZeroForwardScan_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt state hlayout hcleanPath
      hcleanTemporary wire hwire
  have hfirstControl : first control = state control :=
    hfirstProtected control (by simp [zeroMapProtectedWires])
  have hfirstCleanPath : Clean path first := by
    intro wire hwire
    rw [hfirstProtected wire (by simp [zeroMapProtectedWires, hwire])]
    exact hcleanPath wire hwire
  have hfirstTemporary : first temporary = false := by
    change Classical.run
      (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state temporary = false
    exact (run_lowerZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary temporary
      (Ne.symm hlayout.range_ne_temporary)
      (lowerZeroForwardLeafState_preserves_temporary k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout)).trans hcleanTemporary
  have hfirstRange : first rangeAccumulator = false :=
    run_lowerZeroForwardScan_range_false k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hlabels hcleanPath hcleanRange hcleanTemporary
  have hfirstRoute : tree.routeLabel first = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstProtected wire (by simp [zeroMapProtectedWires, hwire])
  have hfirstBits :
      lowerRangeBits (first control) boundary (zeroMapLabels k K) bitAt first =
        lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt state := by
    unfold lowerRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hfirstControl]
    have hbit : first (bitAt label) = state (bitAt label) :=
      run_lowerZeroForwardScan_preserves_bit k K hkK tree control rangeAccumulator temporary
        path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary label hlabel
    rw [hbit]
  have hfirstDirty := readWireWord_run_lowerZeroForwardScan k K boundary hkK hboundary
    tree control rangeAccumulator temporary path bitAt dirtyAt state hlayout hlabels hroute
    hcleanPath hcleanRange hcleanTemporary
  rw [lowerZeroMapUnitary, Classical.run_append]
  change readWireWord (zeroMapLabels k K) dirtyAt
    (Classical.run
      (rangeScanUnitary false .inc tree control rangeAccumulator path
        (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)) first) = _
  rw [readWireWord_run_lowerZeroReverseScan k K boundary hkK hboundary tree control
    rangeAccumulator temporary path bitAt dirtyAt first hlayout hlabels hfirstRoute
    hfirstCleanPath hfirstRange hfirstTemporary,
    hfirstBits, hfirstDirty]
  exact lowerDirtyMapSeed_eq_xor_prefixZeroFlags (state control)
    (lowerRangeBits (state control) boundary (zeroMapLabels k K) bitAt state)
    (readWireWord (zeroMapLabels k K) dirtyAt state) (by simp [readWireWord])

/-! ### Restored scratch of the complete maps -/

private theorem upperZeroReverseLeafState_preserves_protected
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) (wire : Wire)
    (hwire : wire ∈ zeroMapProtectedWires tree control path) :
    upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state wire =
      state wire := by
  by_cases hwindow : k ≤ label ∧ label < K
  · apply upperZeroReverseLeafState_preserves
    intro equality
    subst wire
    have hlabel : label ∈ zeroMapLabels k K :=
      (mem_zeroMapLabels hkK).2 (by omega)
    have hshared := hlayout.shared_eq_control hwire (by
      simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_map]
      right
      exact ⟨label, hlabel, rfl⟩)
    exact hlayout.control_ne_dirty hlabel hshared.symm
  · simp [upperZeroReverseLeafState, hwindow]

private theorem lowerZeroReverseLeafState_preserves_protected
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (label : Nat) (state : BasisState) (wire : Wire)
    (hwire : wire ∈ zeroMapProtectedWires tree control path) :
    lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state wire =
      state wire := by
  by_cases hwindow : k < label ∧ label ≤ K
  · apply lowerZeroReverseLeafState_preserves
    intro equality
    subst wire
    have hlabel : label ∈ zeroMapLabels k K :=
      (mem_zeroMapLabels hkK).2 (by omega)
    have hshared := hlayout.shared_eq_control hwire (by
      simp only [zeroMapDataWires, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_map]
      right
      exact ⟨label, hlabel, rfl⟩)
    exact hlayout.control_ne_dirty hlabel hshared.symm
  · simp [lowerZeroReverseLeafState, hwindow]

private theorem run_upperZeroReverseScan_preserves
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireRange : wire ≠ rangeAccumulator)
    (hleaf : ∀ label state',
      upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state' wire =
        state' wire) :
    Classical.run
      (rangeScanUnitary false .dec tree control rangeAccumulator path
        (upperZeroReverseLeaf k K temporary bitAt dirtyAt)) state wire =
      state wire := by
  rw [run_upperZeroReverseScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let traced := (tree.visitPulses .dec (state control) state).foldl
    (fun current pulse =>
      rangeScanDirectLeafState false rangeAccumulator
        (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
        pulse.1 pulse.2 current) state
  change traced[rangeAccumulator ↦
    Bool.xor (traced rangeAccumulator) (traced control)] wire = state wire
  rw [upd_other _ rangeAccumulator _ hwireRange]
  exact foldl_rangeScanDirect_preserves false rangeAccumulator wire
    (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
    (tree.visitPulses .dec (state control) state) state hwireRange hleaf

private theorem run_lowerZeroReverseScan_preserves
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireRange : wire ≠ rangeAccumulator)
    (hleaf : ∀ label state',
      lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt label state' wire =
        state' wire) :
    Classical.run
      (rangeScanUnitary false .inc tree control rangeAccumulator path
        (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)) state wire =
      state wire := by
  rw [run_lowerZeroReverseScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let traced := (tree.visitPulses .inc (state control) state).foldl
    (fun current pulse =>
      rangeScanDirectLeafState false rangeAccumulator
        (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
        pulse.1 pulse.2 current) state
  change traced[rangeAccumulator ↦
    Bool.xor (traced rangeAccumulator) (traced control)] wire = state wire
  rw [upd_other _ rangeAccumulator _ hwireRange]
  exact foldl_rangeScanDirect_preserves false rangeAccumulator wire
    (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
    (tree.visitPulses .inc (state control) state) state hwireRange hleaf

theorem run_upperZeroReverseScan_range_false
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    Classical.run
      (rangeScanUnitary false .dec tree control rangeAccumulator path
        (upperZeroReverseLeaf k K temporary bitAt dirtyAt)) state rangeAccumulator = false := by
  rw [run_upperZeroReverseScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let traced := (tree.visitPulses .dec (state control) state).foldl
    (fun current pulse =>
      rangeScanDirectLeafState false rangeAccumulator
        (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
        pulse.1 pulse.2 current) state
  change traced[rangeAccumulator ↦
    Bool.xor (traced rangeAccumulator) (traced control)] rangeAccumulator = false
  rw [upd_same]
  have htreeLabels : tree.labels = zeroMapLabels k K := by
    simpa using hlabels
  have hpulses : tree.visitPulses .dec (state control) state =
      (zeroMapLabels k K).reverse.map fun label =>
        (label, state control && decide (label = boundary)) := by
    rw [tree.visitPulses_zeroMap .dec (state control) state k K hlabels,
      UnaryActionTree.visitLabels_dec, htreeLabels, hroute]
  have hrangeTrace : traced rangeAccumulator = state control := by
    simp only [traced, hpulses]
    rw [foldl_upperZeroReverse_range k k K boundary le_rfl hkK hboundary.2
      tree control rangeAccumulator temporary path bitAt dirtyAt (state control)
      state hlayout hcleanRange]
    simp [hboundary.1]
  have hcontrolTrace : traced control = state control := by
    simp only [traced]
    apply foldl_rangeScanDirect_preserves false rangeAccumulator control
      (upperZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
      (tree.visitPulses .dec (state control) state) state hlayout.control_ne_range
    intro label state'
    exact upperZeroReverseLeafState_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state' control
      (by simp [zeroMapProtectedWires])
  rw [hrangeTrace, hcontrolTrace]
  cases state control <;> rfl

theorem run_lowerZeroReverseScan_range_false
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    Classical.run
      (rangeScanUnitary false .inc tree control rangeAccumulator path
        (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)) state rangeAccumulator = false := by
  rw [run_lowerZeroReverseScan_direct k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary]
  let traced := (tree.visitPulses .inc (state control) state).foldl
    (fun current pulse =>
      rangeScanDirectLeafState false rangeAccumulator
        (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
        pulse.1 pulse.2 current) state
  change traced[rangeAccumulator ↦
    Bool.xor (traced rangeAccumulator) (traced control)] rangeAccumulator = false
  rw [upd_same]
  have hpulses : tree.visitPulses .inc (state control) state =
      (zeroMapLabels k K).map fun label =>
        (label, state control && decide (label = boundary)) := by
    rw [tree.visitPulses_zeroMap .inc (state control) state k K hlabels,
      hlabels, hroute]
  have hrangeTrace : traced rangeAccumulator = state control := by
    simp only [traced, hpulses]
    rw [foldl_lowerZeroReverse_range k K K boundary hkK le_rfl hboundary.1
      tree control rangeAccumulator temporary path bitAt dirtyAt (state control)
      state hlayout hcleanRange]
    simp [hboundary.2]
  have hcontrolTrace : traced control = state control := by
    simp only [traced]
    apply foldl_rangeScanDirect_preserves false rangeAccumulator control
      (lowerZeroReverseLeafState k K rangeAccumulator bitAt dirtyAt)
      (tree.visitPulses .inc (state control) state) state hlayout.control_ne_range
    intro label state'
    exact lowerZeroReverseLeafState_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt hlayout label state' control
      (by simp [zeroMapProtectedWires])
  rw [hrangeTrace, hcontrolTrace]
  cases state control <;> rfl

/-! ### Complete-map preservation outside the borrowed dirty bank -/

/-- Apart from the borrowed dirty word, the complete upper map is observationally the
identity.  The range accumulator is excluded separately because it is a transient scan
accumulator; its restored-clean contract is stated below. -/
theorem upperZeroMapUnitary_preserves
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireRange : wire ≠ rangeAccumulator)
    (hwireDirty : ∀ label ∈ zeroMapLabels k K, wire ≠ dirtyAt label) :
    Classical.run
      (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
      state wire = state wire := by
  let first := Classical.run
    (rangeScanUnitary true .inc tree control rangeAccumulator path
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state
  have hfirstWire : first wire = state wire := by
    apply run_upperZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary wire hwireRange
    intro label state'
    by_cases hwindow : k ≤ label ∧ label ≤ K
    · exact upperZeroForwardLeafState_preserves k K control rangeAccumulator bitAt dirtyAt
        label state' wire (hwireDirty label ((mem_zeroMapLabels hkK).2 hwindow))
    · simp [upperZeroForwardLeafState, hwindow]
  have hfirstProtected : ∀ protectedWire,
      protectedWire ∈ zeroMapProtectedWires tree control path →
        first protectedWire = state protectedWire := by
    intro protectedWire hprotected
    exact run_upperZeroForwardScan_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt state hlayout hcleanPath
      hcleanTemporary protectedWire hprotected
  have hfirstCleanPath : Clean path first := by
    intro protectedWire hprotected
    rw [hfirstProtected protectedWire (by simp [zeroMapProtectedWires, hprotected])]
    exact hcleanPath protectedWire hprotected
  have hfirstTemporary : first temporary = false := by
    change Classical.run
      (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state temporary = false
    exact (run_upperZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary temporary
      (Ne.symm hlayout.range_ne_temporary)
      (upperZeroForwardLeafState_preserves_temporary k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout)).trans hcleanTemporary
  rw [upperZeroMapUnitary, Classical.run_append]
  change Classical.run
    (rangeScanUnitary false .dec tree control rangeAccumulator path
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt)) first wire = state wire
  rw [run_upperZeroReverseScan_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt first hlayout hfirstCleanPath hfirstTemporary wire hwireRange]
  · exact hfirstWire
  · intro label state'
    by_cases hwindow : k ≤ label ∧ label < K
    · exact upperZeroReverseLeafState_preserves k K rangeAccumulator bitAt dirtyAt
        label state' wire (hwireDirty label ((mem_zeroMapLabels hkK).2 (by omega)))
    · simp [upperZeroReverseLeafState, hwindow]

/-- Lower-map mirror of `upperZeroMapUnitary_preserves`. -/
theorem lowerZeroMapUnitary_preserves
    (k K : Nat) (hkK : k ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hcleanPath : Clean path state) (hcleanTemporary : state temporary = false)
    (wire : Wire) (hwireRange : wire ≠ rangeAccumulator)
    (hwireDirty : ∀ label ∈ zeroMapLabels k K, wire ≠ dirtyAt label) :
    Classical.run
      (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
      state wire = state wire := by
  let first := Classical.run
    (rangeScanUnitary true .dec tree control rangeAccumulator path
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state
  have hfirstWire : first wire = state wire := by
    apply run_lowerZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary wire hwireRange
    intro label state'
    by_cases hwindow : k ≤ label ∧ label ≤ K
    · exact lowerZeroForwardLeafState_preserves k K control rangeAccumulator bitAt dirtyAt
        label state' wire (hwireDirty label ((mem_zeroMapLabels hkK).2 hwindow))
    · simp [lowerZeroForwardLeafState, hwindow]
  have hfirstProtected : ∀ protectedWire,
      protectedWire ∈ zeroMapProtectedWires tree control path →
        first protectedWire = state protectedWire := by
    intro protectedWire hprotected
    exact run_lowerZeroForwardScan_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt state hlayout hcleanPath
      hcleanTemporary protectedWire hprotected
  have hfirstCleanPath : Clean path first := by
    intro protectedWire hprotected
    rw [hfirstProtected protectedWire (by simp [zeroMapProtectedWires, hprotected])]
    exact hcleanPath protectedWire hprotected
  have hfirstTemporary : first temporary = false := by
    change Classical.run
      (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state temporary = false
    exact (run_lowerZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary temporary
      (Ne.symm hlayout.range_ne_temporary)
      (lowerZeroForwardLeafState_preserves_temporary k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout)).trans hcleanTemporary
  rw [lowerZeroMapUnitary, Classical.run_append]
  change Classical.run
    (rangeScanUnitary false .inc tree control rangeAccumulator path
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)) first wire = state wire
  rw [run_lowerZeroReverseScan_preserves k K hkK tree control rangeAccumulator temporary
    path bitAt dirtyAt first hlayout hfirstCleanPath hfirstTemporary wire hwireRange]
  · exact hfirstWire
  · intro label state'
    by_cases hwindow : k < label ∧ label ≤ K
    · exact lowerZeroReverseLeafState_preserves k K rangeAccumulator bitAt dirtyAt
        label state' wire (hwireDirty label ((mem_zeroMapLabels hkK).2 (by omega)))
    · simp [lowerZeroReverseLeafState, hwindow]

/-- Both upper passes restore the decoder path, range accumulator, and recurrence temporary. -/
theorem upperZeroMapUnitary_clean
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    Clean (path ++ [rangeAccumulator, temporary])
      (Classical.run
        (upperZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
        state) := by
  let first := Classical.run
    (rangeScanUnitary true .inc tree control rangeAccumulator path
      (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state
  have hfirstProtected : ∀ wire,
      wire ∈ zeroMapProtectedWires tree control path → first wire = state wire := by
    intro wire hwire
    exact run_upperZeroForwardScan_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt state hlayout hcleanPath
      hcleanTemporary wire hwire
  have hfirstCleanPath : Clean path first := by
    intro wire hwire
    rw [hfirstProtected wire (by simp [zeroMapProtectedWires, hwire])]
    exact hcleanPath wire hwire
  have hfirstTemporary : first temporary = false := by
    change Classical.run
      (rangeScanUnitary true .inc tree control rangeAccumulator path
        (upperZeroForwardLeaf k K control temporary bitAt dirtyAt)) state temporary = false
    exact (run_upperZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary temporary
      (Ne.symm hlayout.range_ne_temporary)
      (upperZeroForwardLeafState_preserves_temporary k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout)).trans hcleanTemporary
  have hfirstRange : first rangeAccumulator = false :=
    run_upperZeroForwardScan_range_false k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hlabels hcleanPath hcleanRange hcleanTemporary
  have hfirstRoute : tree.routeLabel first = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstProtected wire (by simp [zeroMapProtectedWires, hwire])
  have hsecondRange : Classical.run
      (rangeScanUnitary false .dec tree control rangeAccumulator path
        (upperZeroReverseLeaf k K temporary bitAt dirtyAt)) first rangeAccumulator = false :=
    run_upperZeroReverseScan_range_false k K boundary hkK hboundary tree control
      rangeAccumulator temporary path bitAt dirtyAt first hlayout hlabels hfirstRoute
      hfirstCleanPath hfirstRange hfirstTemporary
  intro wire hwire
  rw [upperZeroMapUnitary, Classical.run_append]
  change Classical.run
    (rangeScanUnitary false .dec tree control rangeAccumulator path
      (upperZeroReverseLeaf k K temporary bitAt dirtyAt)) first wire = false
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hpath | hwire
  · rw [run_upperZeroReverseScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt first hlayout hfirstCleanPath hfirstTemporary wire]
    · exact hfirstCleanPath wire hpath
    · intro equality
      subst wire
      exact hlayout.range_not_protected (by simp [zeroMapProtectedWires, hpath])
    · intro label state'
      exact upperZeroReverseLeafState_preserves_protected k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout label state' wire
        (by simp [zeroMapProtectedWires, hpath])
  · rcases hwire with hRange | hTemporary
    · subst wire
      exact hsecondRange
    · subst wire
      rw [run_upperZeroReverseScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt first hlayout hfirstCleanPath hfirstTemporary temporary
      (Ne.symm hlayout.range_ne_temporary)
      (upperZeroReverseLeafState_preserves_temporary k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout)]
      exact hfirstTemporary

/-- Both lower passes restore the decoder path, range accumulator, and recurrence temporary. -/
theorem lowerZeroMapUnitary_clean
    (k K boundary : Nat) (hkK : k ≤ K)
    (hboundary : k ≤ boundary ∧ boundary ≤ K)
    (tree : UnaryActionTree) (control rangeAccumulator temporary : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire)
    (state : BasisState)
    (hlayout : ZeroMapLayout k K tree control rangeAccumulator temporary path bitAt dirtyAt)
    (hlabels : tree.visitLabels .inc = zeroMapLabels k K)
    (hroute : tree.routeLabel state = boundary)
    (hcleanPath : Clean path state) (hcleanRange : state rangeAccumulator = false)
    (hcleanTemporary : state temporary = false) :
    Clean (path ++ [rangeAccumulator, temporary])
      (Classical.run
        (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path bitAt dirtyAt)
        state) := by
  let first := Classical.run
    (rangeScanUnitary true .dec tree control rangeAccumulator path
      (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state
  have hfirstProtected : ∀ wire,
      wire ∈ zeroMapProtectedWires tree control path → first wire = state wire := by
    intro wire hwire
    exact run_lowerZeroForwardScan_preserves_protected k K hkK tree control
      rangeAccumulator temporary path bitAt dirtyAt state hlayout hcleanPath
      hcleanTemporary wire hwire
  have hfirstCleanPath : Clean path first := by
    intro wire hwire
    rw [hfirstProtected wire (by simp [zeroMapProtectedWires, hwire])]
    exact hcleanPath wire hwire
  have hfirstTemporary : first temporary = false := by
    change Classical.run
      (rangeScanUnitary true .dec tree control rangeAccumulator path
        (lowerZeroForwardLeaf k K control temporary bitAt dirtyAt)) state temporary = false
    exact (run_lowerZeroForwardScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hcleanPath hcleanTemporary temporary
      (Ne.symm hlayout.range_ne_temporary)
      (lowerZeroForwardLeafState_preserves_temporary k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout)).trans hcleanTemporary
  have hfirstRange : first rangeAccumulator = false :=
    run_lowerZeroForwardScan_range_false k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt state hlayout hlabels hcleanPath hcleanRange hcleanTemporary
  have hfirstRoute : tree.routeLabel first = boundary := by
    rw [← hroute]
    apply tree.routeLabel_congr
    intro wire hwire
    exact hfirstProtected wire (by simp [zeroMapProtectedWires, hwire])
  have hsecondRange : Classical.run
      (rangeScanUnitary false .inc tree control rangeAccumulator path
        (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)) first rangeAccumulator = false :=
    run_lowerZeroReverseScan_range_false k K boundary hkK hboundary tree control
      rangeAccumulator temporary path bitAt dirtyAt first hlayout hlabels hfirstRoute
      hfirstCleanPath hfirstRange hfirstTemporary
  intro wire hwire
  rw [lowerZeroMapUnitary, Classical.run_append]
  change Classical.run
    (rangeScanUnitary false .inc tree control rangeAccumulator path
      (lowerZeroReverseLeaf k K temporary bitAt dirtyAt)) first wire = false
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hpath | hwire
  · rw [run_lowerZeroReverseScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt first hlayout hfirstCleanPath hfirstTemporary wire]
    · exact hfirstCleanPath wire hpath
    · intro equality
      subst wire
      exact hlayout.range_not_protected (by simp [zeroMapProtectedWires, hpath])
    · intro label state'
      exact lowerZeroReverseLeafState_preserves_protected k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout label state' wire
        (by simp [zeroMapProtectedWires, hpath])
  · rcases hwire with hRange | hTemporary
    · subst wire
      exact hsecondRange
    · subst wire
      rw [run_lowerZeroReverseScan_preserves k K hkK tree control rangeAccumulator temporary
      path bitAt dirtyAt first hlayout hfirstCleanPath hfirstTemporary temporary
      (Ne.symm hlayout.range_ne_temporary)
      (lowerZeroReverseLeafState_preserves_temporary k K hkK tree control
        rangeAccumulator temporary path bitAt dirtyAt hlayout)]
      exact hfirstTemporary

end

end ShorECDLP.Paper2607_13816
