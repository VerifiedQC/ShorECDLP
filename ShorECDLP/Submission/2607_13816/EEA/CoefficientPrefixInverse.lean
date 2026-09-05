import ShorECDLP.Submission.«2607_13816».EEA.Interval
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefix

/-!
# Explicit inverse of prepared-boundary coefficient-prefix arithmetic

The pinned supplement's `lc_prefix_addsub_prepared_boundary_gate(..., inverse=True)` branch
reverses the two unary traversals and replaces every Figure-11 ripple cell by its literal inverse.
For these cells, that source construction is exactly the forward prepared-boundary block at the
opposite `RippleMode`: inverse second-pass cells become opposite-mode first-pass cells, and inverse
first-pass cells become opposite-mode second-pass cells.

This module keeps that explicit source specialization separate from an opaque call to `adjoint`,
then proves that the resulting circuit is the ordinary adjoint.  It exposes direct circuit-free
whole-state semantics, scratch restoration, both source round trips, adaptive coherent refinement,
and constructor-derived resource equations.  Phase-dependent boundary preparation/restoration is
the caller-owned layer proved in `TBoundary.lean`.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-! ## Literal inverse source term -/

/-- Coherent source inverse.  This is the literal `inverse=True` specialization: the same unary
tree and block order, with every ripple cell changed to the opposite arithmetic mode. -/
def coefficientPrefixInverseUnitary
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) : Circuit :=
  coefficientPrefixUnitary registers k K mode.inverse signUpdate target

/-- Measurement-uncomputed realization of the same inverse source specialization. -/
def coefficientPrefixInverseAdaptive
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    AdaptiveCircuit :=
  coefficientPrefixAdaptive registers k K mode.inverse signUpdate target

/-- Gate-independent reverse recurrence corresponding to the literal inverse source term. -/
def coefficientPrefixInverseState
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) : BasisState :=
  coefficientPrefixState registers k K mode.inverse signUpdate target state

@[simp]
private theorem coefficientPrefix_computeZeroAnd_adjoint
    (control indexBit target : Wire) :
    (computeZeroAnd control indexBit target).adjoint =
      computeZeroAnd control indexBit target := by
  simp [computeZeroAnd, Circuit.adjoint]

/-- Reversing the source traversal order while adjointing each leaf gives the adjoint traversal. -/
private theorem coefficientPrefix_unaryActionUnitary_reverse_eq_adjoint
    (order : UnaryOrder)
    (leafAction inverseLeafAction : Nat → Wire → Circuit)
    (hleaf : ∀ label control,
      inverseLeafAction label control = (leafAction label control).adjoint)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire) :
    unaryActionUnitary order.reverse inverseLeafAction tree control ancillas =
      (unaryActionUnitary order leafAction tree control ancillas).adjoint := by
  induction tree generalizing control ancillas with
  | leaf label => exact hleaf label control
  | node indexBit zero one ihZero ihOne =>
      cases ancillas with
      | nil => simp [unaryActionUnitary]
      | cons path rest =>
          cases order <;>
            simp only [UnaryOrder.reverse] at ihZero ihOne ⊢ <;>
            simp [unaryActionUnitary, circuit_adjoint_append, ihZero, ihOne]

private theorem coefficientPrefixFirstLeaf_inverse_eq_adjoint_second
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (control : Wire) :
  coefficientPrefixFirstLeaf registers k K mode.inverse target label control =
      (coefficientPrefixSecondLeaf registers k K mode target label control).adjoint := by
  simp [coefficientPrefixFirstLeaf, coefficientPrefixSecondLeaf,
    rippleFirstCell_inverse_eq]

private theorem coefficientPrefixSecondLeaf_inverse_eq_adjoint_first
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget)
    (label : Nat) (control : Wire) :
    coefficientPrefixSecondLeaf registers k K mode.inverse target label control =
      (coefficientPrefixFirstLeaf registers k K mode target label control).adjoint := by
  simp [coefficientPrefixFirstLeaf, coefficientPrefixSecondLeaf,
    circuit_adjoint_append, rippleSecondCell_inverse_eq]

/-- The explicit pinned inverse stream is exactly the adjoint of the forward stream. -/
theorem coefficientPrefixInverseUnitary_eq_adjoint
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    coefficientPrefixInverseUnitary registers k K mode signUpdate target =
      (coefficientPrefixUnitary registers k K mode signUpdate target).adjoint := by
  rw [coefficientPrefixInverseUnitary, coefficientPrefixUnitary]
  have hfirst := coefficientPrefix_unaryActionUnitary_reverse_eq_adjoint .dec
    (coefficientPrefixSecondLeaf registers k K mode target)
    (coefficientPrefixFirstLeaf registers k K mode.inverse target)
    (coefficientPrefixFirstLeaf_inverse_eq_adjoint_second registers k K mode target)
    (coefficientPrefixTree registers k K) registers.control (registers.path k K)
  have hsecond := coefficientPrefix_unaryActionUnitary_reverse_eq_adjoint .inc
    (coefficientPrefixFirstLeaf registers k K mode target)
    (coefficientPrefixSecondLeaf registers k K mode.inverse target)
    (coefficientPrefixSecondLeaf_inverse_eq_adjoint_first registers k K mode target)
    (coefficientPrefixTree registers k K) registers.control (registers.path k K)
  simp only [UnaryOrder.reverse] at hfirst hsecond
  rw [hfirst, hsecond]
  simp [coefficientPrefixUnitary, Circuit.adjoint]
  cases signUpdate <;> rfl

/-! ## Direct semantics and structural contracts -/

/-- Direct whole-state execution of the pinned inverse source term. -/
theorem run_coefficientPrefixInverseUnitary_state
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hready : CoefficientPrefixReady registers state) :
    Classical.run
        (coefficientPrefixInverseUnitary registers k K mode signUpdate target) state =
      coefficientPrefixInverseState registers k K mode signUpdate target state := by
  exact run_coefficientPrefixUnitary_state registers mode.inverse signUpdate target
    state hlayout hready

/-- The explicit inverse restores the complete shared scratch bank. -/
theorem coefficientPrefixInverseUnitary_ready
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hready : CoefficientPrefixReady registers state) :
    CoefficientPrefixReady registers
      (Classical.run
        (coefficientPrefixInverseUnitary registers k K mode signUpdate target) state) := by
  exact coefficientPrefixUnitary_clean registers mode.inverse signUpdate target
    state hlayout hready

@[simp]
theorem coefficientPrefixInverseUnitary_HPFree
    (registers : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    HPFree (coefficientPrefixInverseUnitary registers k K mode signUpdate target) := by
  simp [coefficientPrefixInverseUnitary]

theorem coefficientPrefixInverseUnitary_usesOnly
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    PaperCircuitUsesOnly registers.allWires
      (coefficientPrefixInverseUnitary registers k K mode signUpdate target) := by
  exact coefficientPrefixUnitary_usesOnly registers mode.inverse signUpdate target hlayout

theorem coefficientPrefixInverseUnitary_preservesOutside
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    {wire : Wire} (hwire : wire ∉ registers.allWires) :
    Classical.run
        (coefficientPrefixInverseUnitary registers k K mode signUpdate target) state wire =
      state wire := by
  exact (coefficientPrefixInverseUnitary_usesOnly registers mode signUpdate target hlayout)
    |>.preservesOutside state hwire

theorem coefficientPrefixInverseUnitary_wellFormed
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CircuitWellFormed
      (coefficientPrefixInverseUnitary registers k K mode signUpdate target) := by
  exact coefficientPrefixUnitary_wellFormed registers mode.inverse signUpdate target hlayout

theorem coefficientPrefixInverseAdaptive_wellFormed
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    (coefficientPrefixInverseAdaptive registers k K mode signUpdate target).WellFormed := by
  exact coefficientPrefixAdaptive_wellFormed registers mode.inverse signUpdate target hlayout

/-- The measurement-uncomputed inverse is coefficient-aligned with the explicit coherent source
term on every clean shared-scratch input. -/
theorem coefficientPrefixInverseAdaptive_coherent
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    CoherentlyImplementsOn
      (coefficientPrefixInverseAdaptive registers k K mode signUpdate target)
      (Quantum.run
        (coefficientPrefixInverseUnitary registers k K mode signUpdate target))
      (CoefficientPrefixReady registers) := by
  exact coefficientPrefixAdaptive_coherent registers mode.inverse signUpdate target hlayout

/-! ## Two-sided whole-state cancellation -/

/-- The explicit inverse cancels the forward source term on every basis state. -/
theorem run_coefficientPrefixInverseUnitary_after_forward
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K) :
    Classical.run
        (coefficientPrefixInverseUnitary registers k K mode signUpdate target)
        (Classical.run
          (coefficientPrefixUnitary registers k K mode signUpdate target) state) =
      state := by
  rw [coefficientPrefixInverseUnitary_eq_adjoint]
  exact coefficientPrefixUnitary_adjoint_roundtrip registers mode signUpdate target
    state hlayout

/-- Symmetrically, the forward source term cancels the explicit inverse. -/
theorem run_coefficientPrefixUnitary_after_inverse
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K) :
    Classical.run
        (coefficientPrefixUnitary registers k K mode signUpdate target)
        (Classical.run
          (coefficientPrefixInverseUnitary registers k K mode signUpdate target) state) =
      state := by
  simpa [coefficientPrefixInverseUnitary] using
    (run_coefficientPrefixInverseUnitary_after_forward registers mode.inverse
      signUpdate target state hlayout)

/-- The gate-independent reverse recurrence cancels the forward recurrence on a clean source
boundary. -/
theorem coefficientPrefixInverseState_after_forward
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hready : CoefficientPrefixReady registers state) :
    coefficientPrefixInverseState registers k K mode signUpdate target
        (coefficientPrefixState registers k K mode signUpdate target state) = state := by
  have hforward := run_coefficientPrefixUnitary_state registers mode signUpdate target
    state hlayout hready
  have hreadyForward := coefficientPrefixUnitary_clean registers mode signUpdate target
    state hlayout hready
  have hinverse := run_coefficientPrefixInverseUnitary_state registers mode signUpdate target
    (Classical.run (coefficientPrefixUnitary registers k K mode signUpdate target) state)
    hlayout hreadyForward
  calc
    coefficientPrefixInverseState registers k K mode signUpdate target
        (coefficientPrefixState registers k K mode signUpdate target state) =
        coefficientPrefixInverseState registers k K mode signUpdate target
          (Classical.run
            (coefficientPrefixUnitary registers k K mode signUpdate target) state) := by
              rw [hforward]
    _ = Classical.run
        (coefficientPrefixInverseUnitary registers k K mode signUpdate target)
        (Classical.run
          (coefficientPrefixUnitary registers k K mode signUpdate target) state) :=
      hinverse.symm
    _ = state := run_coefficientPrefixInverseUnitary_after_forward registers mode
      signUpdate target state hlayout

/-- Symmetrically, the forward recurrence cancels the gate-independent inverse recurrence. -/
theorem coefficientPrefixState_after_inverse
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (state : BasisState) (hlayout : CoefficientPrefixLayout registers k K)
    (hready : CoefficientPrefixReady registers state) :
    coefficientPrefixState registers k K mode signUpdate target
        (coefficientPrefixInverseState registers k K mode signUpdate target state) = state := by
  have hinverse := run_coefficientPrefixInverseUnitary_state registers mode signUpdate target
    state hlayout hready
  have hreadyInverse := coefficientPrefixInverseUnitary_ready registers mode signUpdate target
    state hlayout hready
  have hforward := run_coefficientPrefixUnitary_state registers mode signUpdate target
    (Classical.run (coefficientPrefixInverseUnitary registers k K mode signUpdate target) state)
    hlayout hreadyInverse
  calc
    coefficientPrefixState registers k K mode signUpdate target
        (coefficientPrefixInverseState registers k K mode signUpdate target state) =
        coefficientPrefixState registers k K mode signUpdate target
          (Classical.run
            (coefficientPrefixInverseUnitary registers k K mode signUpdate target) state) := by
              rw [hinverse]
    _ = Classical.run
        (coefficientPrefixUnitary registers k K mode signUpdate target)
        (Classical.run
          (coefficientPrefixInverseUnitary registers k K mode signUpdate target) state) :=
      hforward.symm
    _ = state := run_coefficientPrefixUnitary_after_inverse registers mode signUpdate target
      state hlayout

/-! ## Constructor-derived resources -/

theorem coefficientPrefixInverseUnitary_toffoliCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    eeaToffoliCount
        (coefficientPrefixInverseUnitary registers k K mode signUpdate target) =
      7 * (coefficientPrefixTree registers k K).leaves +
        4 * (coefficientPrefixTree registers k K).internalNodes := by
  exact coefficientPrefixUnitary_toffoliCount registers mode.inverse signUpdate target hlayout

theorem coefficientPrefixInverseUnitary_cnotCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    eeaCnotCount
        (coefficientPrefixInverseUnitary registers k K mode signUpdate target) =
      2 + (if signUpdate then 1 else 0) +
        6 * (coefficientPrefixTree registers k K).leaves +
        4 * (coefficientPrefixTree registers k K).internalNodes := by
  exact coefficientPrefixUnitary_cnotCount registers mode.inverse signUpdate target hlayout

theorem coefficientPrefixInverseUnitary_tCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    ShorECDLP.tCount
        (coefficientPrefixInverseUnitary registers k K mode signUpdate target) =
      49 * (coefficientPrefixTree registers k K).leaves +
        28 * (coefficientPrefixTree registers k K).internalNodes := by
  exact coefficientPrefixUnitary_tCount registers mode.inverse signUpdate target hlayout

theorem coefficientPrefixInverseAdaptive_measurementCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    (coefficientPrefixInverseAdaptive registers k K mode signUpdate target).measurementCount =
      2 * (coefficientPrefixTree registers k K).leaves +
        2 * (coefficientPrefixTree registers k K).internalNodes := by
  exact coefficientPrefixAdaptive_measurementCount registers mode.inverse signUpdate target hlayout

theorem coefficientPrefixInverseAdaptive_tCount
    (registers : CoefficientPrefixRegisters) {k K : Nat}
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers k K) :
    (coefficientPrefixInverseAdaptive registers k K mode signUpdate target).tCount =
      35 * (coefficientPrefixTree registers k K).leaves +
        14 * (coefficientPrefixTree registers k K).internalNodes := by
  exact coefficientPrefixAdaptive_tCount registers mode.inverse signUpdate target hlayout

/-! ## Pinned-source regressions -/

private def coefficientPrefixInverseNarrowRegisters : CoefficientPrefixRegisters where
  control := 0
  sign := 1
  work1 := [2, 3]
  work2 := [4, 5]
  boundary := [6, 7, 8, 9, 10, 11, 12, 13, 14]
  scratch := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

private theorem coefficientPrefixInverseNarrow_tree :
    coefficientPrefixTree coefficientPrefixInverseNarrowRegisters 1 2 =
      .node 7 (.leaf 1) (.leaf 2) := by
  decide

private theorem coefficientPrefixInverseNarrow_layout :
    CoefficientPrefixLayout coefficientPrefixInverseNarrowRegisters 1 2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  change (coefficientPrefixTree coefficientPrefixInverseNarrowRegisters 1 2).Layout
    0 ([15] : List Wire)
  rw [coefficientPrefixInverseNarrow_tree]
  exact .node 7 0 15 _ _ ([] : List Wire) (by decide)
    (.leaf 1 15 ([] : List Wire) (by decide))
    (.leaf 2 15 ([] : List Wire) (by decide))

/-- Flattened literal comparison for the pinned inverse of the first narrow production subtract
call.  The inverse emits opposite-mode MAJ/UMA cells in exactly the source's order. -/
theorem coefficientPrefixInverseNarrow_source_regressions :
    let registers : CoefficientPrefixRegisters := {
      control := 0
      sign := 1
      work1 := [2, 3]
      work2 := [4, 5]
      boundary := [6, 7, 8, 9, 10, 11, 12, 13, 14]
      scratch := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
    }
    coefficientPrefixInverseUnitary registers 1 2 .sub false .work2 =
      [.CX 0 25] ++
      computeZeroAnd 0 7 15 ++
      controlledMaj 25 4 2 24 26 ++ [.CX 15 25] ++
      [.CX 0 15] ++
      controlledMaj 25 5 3 24 26 ++ [.CX 15 25] ++
      [.CX 0 15] ++ computeZeroAnd 0 7 15 ++
      computeZeroAnd 0 7 15 ++ [.CX 0 15] ++
      [.CX 15 25] ++ controlledUma 25 5 3 24 26 ++
      [.CX 0 15] ++ [.CX 15 25] ++
      controlledUma 25 4 2 24 26 ++
      computeZeroAnd 0 7 15 ++ [.CX 0 25] ∧
    coefficientPrefixInverseUnitary registers 1 2 .add true .work2 =
      [.CX 0 25] ++
      computeZeroAnd 0 7 15 ++
      controlledUmaInv 25 4 2 24 26 ++ [.CX 15 25] ++
      [.CX 0 15] ++
      controlledUmaInv 25 5 3 24 26 ++ [.CX 15 25] ++
      [.CX 0 15] ++ computeZeroAnd 0 7 15 ++
      [.CX 24 1] ++
      computeZeroAnd 0 7 15 ++ [.CX 0 15] ++
      [.CX 15 25] ++ controlledMajInv 25 5 3 24 26 ++
      [.CX 0 15] ++ [.CX 15 25] ++
      controlledMajInv 25 4 2 24 26 ++
      computeZeroAnd 0 7 15 ++ [.CX 0 25] := by
  decide

set_option maxRecDepth 10000 in
/-- The narrow inverse has the same exact resources and physical surface as its forward partner. -/
theorem coefficientPrefixInverseNarrow_resources :
    let registers : CoefficientPrefixRegisters := {
      control := 0
      sign := 1
      work1 := [2, 3]
      work2 := [4, 5]
      boundary := [6, 7, 8, 9, 10, 11, 12, 13, 14]
      scratch := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
    }
    eeaToffoliCount
        (coefficientPrefixInverseUnitary registers 1 2 .sub false .work2) = 18 ∧
      eeaCnotCount
        (coefficientPrefixInverseUnitary registers 1 2 .sub false .work2) = 18 ∧
      ShorECDLP.tCount
        (coefficientPrefixInverseUnitary registers 1 2 .sub false .work2) = 126 ∧
      (coefficientPrefixInverseAdaptive registers 1 2
        .sub false .work2).measurementCount = 6 ∧
      (coefficientPrefixInverseAdaptive registers 1 2
        .sub false .work2).tCount = 84 ∧
      eeaXCount
        (coefficientPrefixInverseUnitary registers 1 2 .sub false .work2) = 8 ∧
      qubitCount
        (coefficientPrefixInverseUnitary registers 1 2 .sub false .work2) = 10 := by
  change
    eeaToffoliCount
        (coefficientPrefixInverseUnitary coefficientPrefixInverseNarrowRegisters 1 2
          .sub false .work2) = 18 ∧
      eeaCnotCount
        (coefficientPrefixInverseUnitary coefficientPrefixInverseNarrowRegisters 1 2
          .sub false .work2) = 18 ∧
      ShorECDLP.tCount
        (coefficientPrefixInverseUnitary coefficientPrefixInverseNarrowRegisters 1 2
          .sub false .work2) = 126 ∧
      (coefficientPrefixInverseAdaptive coefficientPrefixInverseNarrowRegisters 1 2
          .sub false .work2).measurementCount = 6 ∧
      (coefficientPrefixInverseAdaptive coefficientPrefixInverseNarrowRegisters 1 2
          .sub false .work2).tCount = 84 ∧
      eeaXCount
        (coefficientPrefixInverseUnitary coefficientPrefixInverseNarrowRegisters 1 2
          .sub false .work2) = 8 ∧
      qubitCount
        (coefficientPrefixInverseUnitary coefficientPrefixInverseNarrowRegisters 1 2
          .sub false .work2) = 10
  rw [coefficientPrefixInverseUnitary_toffoliCount coefficientPrefixInverseNarrowRegisters
      .sub false .work2 coefficientPrefixInverseNarrow_layout,
    coefficientPrefixInverseUnitary_cnotCount coefficientPrefixInverseNarrowRegisters
      .sub false .work2 coefficientPrefixInverseNarrow_layout,
    coefficientPrefixInverseUnitary_tCount coefficientPrefixInverseNarrowRegisters
      .sub false .work2 coefficientPrefixInverseNarrow_layout,
    coefficientPrefixInverseAdaptive_measurementCount coefficientPrefixInverseNarrowRegisters
      .sub false .work2 coefficientPrefixInverseNarrow_layout,
    coefficientPrefixInverseAdaptive_tCount coefficientPrefixInverseNarrowRegisters
      .sub false .work2 coefficientPrefixInverseNarrow_layout,
    coefficientPrefixInverseNarrow_tree]
  decide

set_option maxRecDepth 10000 in
/-- Production-width resources of the explicit inverse source calls. -/
theorem coefficientPrefixInverseProduction_resources
    (registers : CoefficientPrefixRegisters)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hlayout : CoefficientPrefixLayout registers 1 257)
    (hboundary : registers.boundary.length = 9) :
    eeaToffoliCount
        (coefficientPrefixInverseUnitary registers 1 257 mode signUpdate target) = 2823 ∧
      eeaCnotCount
        (coefficientPrefixInverseUnitary registers 1 257 mode signUpdate target) =
          2568 + (if signUpdate then 1 else 0) ∧
      ShorECDLP.tCount
        (coefficientPrefixInverseUnitary registers 1 257 mode signUpdate target) = 19761 ∧
      (coefficientPrefixInverseAdaptive registers 1 257 mode signUpdate target).measurementCount =
        1026 ∧
      (coefficientPrefixInverseAdaptive registers 1 257 mode signUpdate target).tCount = 12579 := by
  exact coefficientPrefixProduction_resources registers mode.inverse signUpdate target
    hlayout hboundary

end

end ShorECDLP.Paper2607_13816
