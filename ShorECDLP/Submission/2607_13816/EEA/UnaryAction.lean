import ShorECDLP.Submission.«2607_13816».EEA.UnaryIteration

/-!
# Measured unary traversal with generic leaf actions

`UnaryIteration.lean` proves the marker-leaf instance used to validate the measured path
decoder.  The EEA arithmetic blocks need the same pruned traversal with a circuit-valued action
at each leaf.  This module isolates that generic control-flow theorem.  Its hypotheses say exactly
what the later arithmetic cells must establish: every leaf circuit is H/P-free, physically
well-formed, and preserves the decoder's control, index, and path wires.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-- Leaf visitation order, matching the supplement's `order="inc"` / `order="dec"` switch. -/
inductive UnaryOrder where
  | inc
  | dec
deriving DecidableEq, Repr

/-- A pruned decision tree whose leaves carry source labels but no dedicated marker wires. -/
inductive UnaryActionTree where
  | leaf (label : Nat)
  | node (indexBit : Wire) (zero one : UnaryActionTree)
deriving DecidableEq, Repr

namespace UnaryActionTree

def indexWires : UnaryActionTree → List Wire
  | .leaf _ => []
  | .node indexBit zero one =>
      indexBit :: (zero.indexWires ++ one.indexWires)

def internalNodes : UnaryActionTree → Nat
  | .leaf _ => 0
  | .node _ zero one => 1 + zero.internalNodes + one.internalNodes

def leaves : UnaryActionTree → Nat
  | .leaf _ => 1
  | .node _ zero one => zero.leaves + one.leaves

def labels : UnaryActionTree → List Nat
  | .leaf label => [label]
  | .node _ zero one => zero.labels ++ one.labels

/-- Sum a leaf-local resource function over the concrete dynamic controls used by a traversal. -/
def leafCostSum
    (leafCost : Nat → Wire → Nat) :
    UnaryActionTree → Wire → List Wire → Nat
  | .leaf label, control, _ => leafCost label control
  | .node _ zero one, _, path :: rest =>
      zero.leafCostSum leafCost path rest +
        one.leafCostSum leafCost path rest
  | .node _ _ _, _, [] => 0

/-- Label reached by the stored index-bit decisions. -/
def routeLabel : UnaryActionTree → BasisState → Nat
  | .leaf label, _ => label
  | .node indexBit zero one, state =>
      if state indexBit then one.routeLabel state
      else zero.routeLabel state

theorem routeLabel_mem_labels (tree : UnaryActionTree) (state : BasisState) :
    tree.routeLabel state ∈ tree.labels := by
  induction tree with
  | leaf label => simp [routeLabel, labels]
  | node indexBit zero one ihZero ihOne =>
      cases hbit : state indexBit <;>
        simp [routeLabel, labels, hbit, ihZero, ihOne]

theorem routeLabel_congr
    (tree : UnaryActionTree) (left right : BasisState)
    (h : ∀ wire ∈ tree.indexWires, left wire = right wire) :
    tree.routeLabel left = tree.routeLabel right := by
  induction tree with
  | leaf label => rfl
  | node indexBit zero one ihZero ihOne =>
      have hbit : left indexBit = right indexBit :=
        h indexBit (by simp [indexWires])
      have hzero : ∀ wire ∈ zero.indexWires,
          left wire = right wire := by
        intro wire hwire
        exact h wire (by simp [indexWires, hwire])
      have hone : ∀ wire ∈ one.indexWires,
          left wire = right wire := by
        intro wire hwire
        exact h wire (by simp [indexWires, hwire])
      simp only [routeLabel, hbit]
      split
      · exact ihOne hone
      · exact ihZero hzero

/-- Decoder layout.  All index roles and the reusable path stack are distinct from the current
control.  Index wires may occur at several tree nodes, hence the deduplication. -/
inductive Layout : UnaryActionTree → Wire → List Wire → Prop where
  | leaf
      (label : Nat) (control : Wire) (ancillas : List Wire)
      (hlocal : (control :: ancillas).Nodup) :
      Layout (.leaf label) control ancillas
  | node
      (indexBit control path : Wire)
      (zero one : UnaryActionTree) (rest : List Wire)
      (hlocal :
        (control ::
          ((UnaryActionTree.node indexBit zero one).indexWires.dedup ++
            (path :: rest))).Nodup)
      (hzero : Layout zero path rest)
      (hone : Layout one path rest) :
      Layout (.node indexBit zero one) control (path :: rest)

end UnaryActionTree

/-- Coherent reference: every path AND is reversed with its ordinary Toffoli circuit. -/
def unaryActionUnitary
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit) :
    UnaryActionTree → Wire → List Wire → Circuit
  | .leaf label, control, _ => leafAction label control
  | .node indexBit zero one, control, path :: rest =>
      match order with
      | .inc =>
          computeZeroAnd control indexBit path ++
            unaryActionUnitary order leafAction zero path rest ++
            [.CX control path] ++
            unaryActionUnitary order leafAction one path rest ++
            [.CX control path] ++
            computeZeroAnd control indexBit path
      | .dec =>
          computeZeroAnd control indexBit path ++
            [.CX control path] ++
            unaryActionUnitary order leafAction one path rest ++
            [.CX control path] ++
            unaryActionUnitary order leafAction zero path rest ++
            computeZeroAnd control indexBit path
  | .node _ _ _, _, [] => []

/-- Adaptive source traversal: the final path AND at every internal node is erased by
X-measure/reset and the feed-forward Clifford correction. -/
def unaryAction
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit) :
    UnaryActionTree → Wire → List Wire → AdaptiveCircuit
  | .leaf label, control, _ =>
      .unitary (leafAction label control) .done
  | .node indexBit zero one, control, path :: rest =>
      match order with
      | .inc =>
          .unitary (computeZeroAnd control indexBit path)
            ((unaryAction order leafAction zero path rest).seq
              (.unitary [.CX control path]
                ((unaryAction order leafAction one path rest).seq
                  (.unitary [.CX control path]
                    (eraseZeroAnd control indexBit path)))))
      | .dec =>
          .unitary (computeZeroAnd control indexBit path)
            (.unitary [.CX control path]
              ((unaryAction order leafAction one path rest).seq
                (.unitary [.CX control path]
                  ((unaryAction order leafAction zero path rest).seq
                    (eraseZeroAnd control indexBit path)))))
  | .node _ _ _, _, [] => .done

/-- A leaf action preserves a declared set of decoder wires, including its dynamic path
control. -/
def UnaryLeafPreserves
    (leafAction : Nat → Wire → Circuit) (protectedWires : List Wire) : Prop :=
  ∀ label control, control ∈ protectedWires → ∀ state wire,
    wire ∈ protectedWires →
      run (leafAction label control) state wire = state wire

/-- Every leaf action is entirely classical. -/
def UnaryLeafHPFree (leafAction : Nat → Wire → Circuit) : Prop :=
  ∀ label control, HPFree (leafAction label control)

/-- Every leaf action reached by this tree is physically well formed. -/
def UnaryLeafWellFormed
    (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (protectedWires : List Wire) : Prop :=
  ∀ label ∈ tree.labels, ∀ control ∈ protectedWires,
    CircuitWellFormed (leafAction label control)

private theorem unaryActionNode_parts
    (indexBit control path : Wire) (zero one : UnaryActionTree)
    (rest : List Wire)
    (hlocal :
      (control ::
        ((UnaryActionTree.node indexBit zero one).indexWires.dedup ++
          (path :: rest))).Nodup) :
    control ≠ indexBit ∧ control ≠ path ∧ indexBit ≠ path ∧
      path ∉ rest := by
  have htail :
      ((UnaryActionTree.node indexBit zero one).indexWires.dedup ++
        (path :: rest)).Nodup :=
    (List.nodup_cons.mp hlocal).2
  obtain ⟨hindices, hancillas, hcross⟩ := List.nodup_append.mp htail
  have hcontrolAll := (List.nodup_cons.mp hlocal).1
  have hindexMem : indexBit ∈
      (UnaryActionTree.node indexBit zero one).indexWires.dedup := by
    simp [UnaryActionTree.indexWires]
  have hci : control ≠ indexBit := by
    intro equality
    apply hcontrolAll
    rw [equality]
    exact List.mem_append_left _ hindexMem
  have hcp : control ≠ path := by
    intro equality
    apply hcontrolAll
    rw [equality]
    exact List.mem_append_right _ (by simp)
  have hip : indexBit ≠ path :=
    hcross indexBit hindexMem path (by simp)
  exact ⟨hci, hcp, hip, (List.nodup_cons.mp hancillas).1⟩

private theorem actionTree_indices_subset_node
    (indexBit : Wire) (zero one : UnaryActionTree) :
    ∀ wire, wire ∈ zero.indexWires →
      wire ∈ (UnaryActionTree.node indexBit zero one).indexWires := by
  intro wire hwire
  simp [UnaryActionTree.indexWires, hwire]

private theorem actionTree_one_indices_subset_node
    (indexBit : Wire) (zero one : UnaryActionTree) :
    ∀ wire, wire ∈ one.indexWires →
      wire ∈ (UnaryActionTree.node indexBit zero one).indexWires := by
  intro wire hwire
  simp [UnaryActionTree.indexWires, hwire]

private theorem actionTree_zero_decoder_subset
    (indexBit control path : Wire) (zero one : UnaryActionTree)
    (rest : List Wire) :
    ∀ wire, wire ∈ path :: zero.indexWires.dedup ++ rest →
      wire ∈ control ::
        (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
          (path :: rest) := by
  intro wire hwire
  rcases List.mem_cons.mp hwire with rfl | hwire
  · simp
  rcases List.mem_append.mp hwire with hwire | hwire
  · have hn : wire ∈
        (UnaryActionTree.node indexBit zero one).indexWires.dedup :=
      List.mem_dedup.mpr
        (actionTree_indices_subset_node indexBit zero one wire
          (List.mem_dedup.mp hwire))
    simp [hn]
  · simp [hwire]

private theorem actionTree_one_decoder_subset
    (indexBit control path : Wire) (zero one : UnaryActionTree)
    (rest : List Wire) :
    ∀ wire, wire ∈ path :: one.indexWires.dedup ++ rest →
      wire ∈ control ::
        (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
          (path :: rest) := by
  intro wire hwire
  rcases List.mem_cons.mp hwire with rfl | hwire
  · simp
  rcases List.mem_append.mp hwire with hwire | hwire
  · have hn : wire ∈
        (UnaryActionTree.node indexBit zero one).indexWires.dedup :=
      List.mem_dedup.mpr
        (actionTree_one_indices_subset_node indexBit zero one wire
          (List.mem_dedup.mp hwire))
    simp [hn]
  · simp [hwire]

private theorem unaryActionUnitary_preservesProtected
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire)
    (ancillas protectedWires : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout control ancillas)
    (hleaf : UnaryLeafPreserves leafAction protectedWires)
    (hroles : ∀ wire,
      wire ∈ control :: tree.indexWires.dedup ++ ancillas →
        wire ∈ protectedWires)
    (hclean : Clean ancillas state) :
    ∀ wire, wire ∈ protectedWires →
      run (unaryActionUnitary order leafAction tree control ancillas) state wire =
        state wire := by
  induction hlayout generalizing state with
  | leaf label control ancillas hlocal =>
      intro wire hwire
      exact hleaf label control (hroles control (by simp)) state wire hwire
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip, hpathRest⟩ :=
        unaryActionNode_parts indexBit control path zero one rest hlocal
      have hpathFalse : state path = false := hclean path (by simp)
      have hrestClean : Clean rest state := by
        intro wire hwire
        exact hclean wire (by simp [hwire])
      let first := run (computeZeroAnd control indexBit path) state
      have hfirst : first =
          state[path ↦ state control && !state indexBit] := by
        simpa only [first] using run_computeZeroAnd control indexBit path state
          hci hcp hip hpathFalse
      have hrestCleanFirst : Clean rest first := by
        rw [hfirst]
        intro wire hwire
        rw [upd_other state path _ (by
          intro equality
          subst wire
          exact hpathRest hwire)]
        exact hrestClean wire hwire
      have hzeroRoles : ∀ wire,
          wire ∈ path :: zero.indexWires.dedup ++ rest →
            wire ∈ protectedWires := by
        intro wire hwire
        exact hroles wire
          (actionTree_zero_decoder_subset indexBit control path zero one rest
            wire hwire)
      have honeRoles : ∀ wire,
          wire ∈ path :: one.indexWires.dedup ++ rest →
            wire ∈ protectedWires := by
        intro wire hwire
        exact hroles wire
          (actionTree_one_decoder_subset indexBit control path zero one rest
            wire hwire)
      cases order with
      | inc =>
          let afterZero :=
            run (unaryActionUnitary .inc leafAction zero path rest) first
          have hzeroPreserves : ∀ wire, wire ∈ protectedWires →
              afterZero wire = first wire := by
            intro wire hwire
            exact ihZero first hzeroRoles hrestCleanFirst wire hwire
          have hrestCleanAfterZero : Clean rest afterZero := by
            intro wire hwire
            rw [hzeroPreserves wire (hzeroRoles wire (by simp [hwire]))]
            exact hrestCleanFirst wire hwire
          let switched := applyGate (.CX control path) afterZero
          have hrestCleanSwitched : Clean rest switched := by
            intro wire hwire
            have hwp : wire ≠ path := by
              intro equality
              subst wire
              exact hpathRest hwire
            change afterZero[path ↦ Bool.xor (afterZero path) (afterZero control)] wire = false
            rw [upd_other afterZero path _ hwp]
            exact hrestCleanAfterZero wire hwire
          let afterOne :=
            run (unaryActionUnitary .inc leafAction one path rest) switched
          have honePreserves : ∀ wire, wire ∈ protectedWires →
              afterOne wire = switched wire := by
            intro wire hwire
            exact ihOne switched honeRoles hrestCleanSwitched wire hwire
          let switchedBack := applyGate (.CX control path) afterOne
          have hready : ZeroAndComputed control indexBit path switchedBack := by
            unfold ZeroAndComputed
            have hcMem : control ∈ protectedWires := hroles control (by simp)
            have hiMem : indexBit ∈ protectedWires := hroles indexBit (by
              simp [UnaryActionTree.indexWires])
            have hpMem : path ∈ protectedWires := hroles path (by simp)
            simp only [switchedBack, Classical.applyGate]
            simp only [upd_same, upd_other afterOne path _ hcp,
              upd_other afterOne path _ hip]
            rw [honePreserves control hcMem, honePreserves indexBit hiMem,
              honePreserves path hpMem]
            simp only [switched, Classical.applyGate]
            simp only [upd_same, upd_other afterZero path _ hcp,
              upd_other afterZero path _ hip]
            rw [hzeroPreserves control hcMem, hzeroPreserves indexBit hiMem,
              hzeroPreserves path hpMem]
            simp [hfirst, upd, hcp, hip]
          have hcleanup := run_computeZeroAnd_of_computed
            control indexBit path switchedBack hci hcp hip hready
          intro wire hwire
          rw [unaryActionUnitary, Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append, Classical.run_append]
          change run (computeZeroAnd control indexBit path) switchedBack wire = _
          rw [hcleanup]
          by_cases hwp : wire = path
          · subst wire
            simp [hpathFalse]
          · rw [upd_other switchedBack path false hwp]
            change Classical.applyGate (.CX control path) afterOne wire = state wire
            simp only [Classical.applyGate]
            rw [upd_other afterOne path _ hwp]
            rw [honePreserves wire hwire]
            change Classical.applyGate (.CX control path) afterZero wire = state wire
            simp only [Classical.applyGate]
            rw [upd_other afterZero path _ hwp]
            rw [hzeroPreserves wire hwire, hfirst,
              upd_other state path _ hwp]
      | dec =>
          let switched := applyGate (.CX control path) first
          have hrestCleanSwitched : Clean rest switched := by
            intro wire hwire
            have hwp : wire ≠ path := by
              intro equality
              subst wire
              exact hpathRest hwire
            change first[path ↦ Bool.xor (first path) (first control)] wire = false
            rw [upd_other first path _ hwp]
            exact hrestCleanFirst wire hwire
          let afterOne :=
            run (unaryActionUnitary .dec leafAction one path rest) switched
          have honePreserves : ∀ wire, wire ∈ protectedWires →
              afterOne wire = switched wire := by
            intro wire hwire
            exact ihOne switched honeRoles hrestCleanSwitched wire hwire
          have hrestCleanAfterOne : Clean rest afterOne := by
            intro wire hwire
            rw [honePreserves wire (honeRoles wire (by simp [hwire]))]
            exact hrestCleanSwitched wire hwire
          let switchedBack := applyGate (.CX control path) afterOne
          have hrestCleanSwitchedBack : Clean rest switchedBack := by
            intro wire hwire
            have hwp : wire ≠ path := by
              intro equality
              subst wire
              exact hpathRest hwire
            change afterOne[path ↦ Bool.xor (afterOne path) (afterOne control)] wire = false
            rw [upd_other afterOne path _ hwp]
            exact hrestCleanAfterOne wire hwire
          let afterZero :=
            run (unaryActionUnitary .dec leafAction zero path rest) switchedBack
          have hzeroPreserves : ∀ wire, wire ∈ protectedWires →
              afterZero wire = switchedBack wire := by
            intro wire hwire
            exact ihZero switchedBack hzeroRoles hrestCleanSwitchedBack wire hwire
          have hready : ZeroAndComputed control indexBit path afterZero := by
            unfold ZeroAndComputed
            have hcMem : control ∈ protectedWires := hroles control (by simp)
            have hiMem : indexBit ∈ protectedWires := hroles indexBit (by
              simp [UnaryActionTree.indexWires])
            have hpMem : path ∈ protectedWires := hroles path (by simp)
            rw [hzeroPreserves control hcMem, hzeroPreserves indexBit hiMem,
              hzeroPreserves path hpMem]
            simp only [switchedBack, Classical.applyGate]
            simp only [upd_same, upd_other afterOne path _ hcp,
              upd_other afterOne path _ hip]
            rw [honePreserves control hcMem, honePreserves indexBit hiMem,
              honePreserves path hpMem]
            simp only [switched, Classical.applyGate]
            simp [hfirst, upd, hcp, hip]
          have hcleanup := run_computeZeroAnd_of_computed
            control indexBit path afterZero hci hcp hip hready
          intro wire hwire
          rw [unaryActionUnitary, Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append, Classical.run_append]
          change run (computeZeroAnd control indexBit path) afterZero wire = _
          rw [hcleanup]
          by_cases hwp : wire = path
          · subst wire
            simp [hpathFalse]
          · rw [upd_other afterZero path false hwp]
            rw [hzeroPreserves wire hwire]
            change Classical.applyGate (.CX control path) afterOne wire = state wire
            simp only [Classical.applyGate]
            rw [upd_other afterOne path _ hwp]
            rw [honePreserves wire hwire]
            change Classical.applyGate (.CX control path) first wire = state wire
            simp only [Classical.applyGate]
            rw [upd_other first path _ hwp, hfirst,
              upd_other state path _ hwp]

/-- The coherent traversal preserves its complete decoder interface whenever every leaf action
does.  In particular, leaf actions may modify arithmetic data wires, but cannot corrupt the path
decoder that selects them. -/
theorem unaryActionUnitary_preservesDecoder
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout control ancillas)
    (hleaf : UnaryLeafPreserves leafAction
      (control :: tree.indexWires.dedup ++ ancillas))
    (hclean : Clean ancillas state) :
    ∀ wire, wire ∈ control :: tree.indexWires.dedup ++ ancillas →
      run (unaryActionUnitary order leafAction tree control ancillas) state wire =
        state wire := by
  exact unaryActionUnitary_preservesProtected order leafAction tree control ancillas
    (control :: tree.indexWires.dedup ++ ancillas) state hlayout hleaf
    (fun wire hwire => hwire) hclean

/-- Every reverse path-AND in the coherent reference restores the clean path bank. -/
theorem unaryActionUnitary_clean
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout control ancillas)
    (hleaf : UnaryLeafPreserves leafAction
      (control :: tree.indexWires.dedup ++ ancillas))
    (hclean : Clean ancillas state) :
    Clean ancillas
      (run (unaryActionUnitary order leafAction tree control ancillas) state) := by
  intro wire hwire
  rw [unaryActionUnitary_preservesDecoder order leafAction tree control ancillas state
    hlayout hleaf hclean wire (by simp [hwire])]
  exact hclean wire hwire

/-- The coherent reference is entirely classical when every leaf action is. -/
theorem unaryActionUnitary_HPFree
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hleaf : UnaryLeafHPFree leafAction) :
    HPFree (unaryActionUnitary order leafAction tree control ancillas) := by
  induction tree generalizing control ancillas with
  | leaf label => simpa [unaryActionUnitary] using hleaf label control
  | node indexBit zero one ihZero ihOne =>
      cases ancillas with
      | nil => simp [unaryActionUnitary]
      | cons path rest =>
          cases order <;> simp [unaryActionUnitary, ihZero, ihOne]

/-- Physical well-formedness of the coherent reference follows compositionally from the decoder
layout and the well-formedness of every reachable leaf action. -/
theorem unaryActionUnitary_wellFormed
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas)
    (hleaf : UnaryLeafWellFormed leafAction tree
      (control :: tree.indexWires.dedup ++ ancillas)) :
    CircuitWellFormed
      (unaryActionUnitary order leafAction tree control ancillas) := by
  induction hlayout with
  | leaf label control ancillas hlocal =>
      exact hleaf label (by simp [UnaryActionTree.labels]) control (by simp)
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip, hpathRest⟩ :=
        unaryActionNode_parts indexBit control path zero one rest hlocal
      have hzeroLeaf : UnaryLeafWellFormed leafAction zero
          (path :: zero.indexWires.dedup ++ rest) := by
        intro label hlabel childControl hchildControl
        exact hleaf label (by
          simp [UnaryActionTree.labels, hlabel]) childControl
          (actionTree_zero_decoder_subset indexBit control path zero one rest
            childControl hchildControl)
      have honeLeaf : UnaryLeafWellFormed leafAction one
          (path :: one.indexWires.dedup ++ rest) := by
        intro label hlabel childControl hchildControl
        exact hleaf label (by
          simp [UnaryActionTree.labels, hlabel]) childControl
          (actionTree_one_decoder_subset indexBit control path zero one rest
            childControl hchildControl)
      have hcompute :=
        computeZeroAnd_wellFormed control indexBit path hci hcp hip
      have htoggle : CircuitWellFormed [.CX control path] := by
        simp [CircuitWellFormed, Gate.WellFormed, hcp]
      cases order with
      | inc =>
          rw [unaryActionUnitary]
          simp only [circuitWellFormed_append]
          exact ⟨⟨⟨⟨⟨hcompute, ihZero hzeroLeaf⟩, htoggle⟩,
            ihOne honeLeaf⟩, htoggle⟩, hcompute⟩
      | dec =>
          rw [unaryActionUnitary]
          simp only [circuitWellFormed_append]
          exact ⟨⟨⟨⟨⟨hcompute, htoggle⟩, ihOne honeLeaf⟩,
            htoggle⟩, ihZero hzeroLeaf⟩, hcompute⟩

/-- Constructor-derived coherent Toffoli count: leaf work plus compute and reverse-uncompute at
every internal node. -/
theorem unaryActionUnitary_toffoliCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    eeaToffoliCount (unaryActionUnitary order leafAction tree control ancillas) =
      tree.leafCostSum (fun label wire ↦
        eeaToffoliCount (leafAction label wire)) control ancillas +
        2 * tree.internalNodes := by
  induction hlayout with
  | leaf label control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [unaryActionUnitary] <;>
        simp only [eeaToffoliCount_append] <;>
        rw [ihZero, ihOne] <;>
        simp only [computeZeroAnd_toffoliCount] <;>
        simp [eeaToffoliCount, UnaryActionTree.leafCostSum,
          UnaryActionTree.internalNodes] <;>
        omega

/-- Constructor-derived coherent CNOT count: leaf work plus two path switches per internal node. -/
theorem unaryActionUnitary_cnotCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    eeaCnotCount (unaryActionUnitary order leafAction tree control ancillas) =
      tree.leafCostSum (fun label wire ↦
        eeaCnotCount (leafAction label wire)) control ancillas +
        2 * tree.internalNodes := by
  induction hlayout with
  | leaf label control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [unaryActionUnitary] <;>
        simp only [eeaCnotCount_append] <;>
        rw [ihZero, ihOne] <;>
        simp only [computeZeroAnd_cnotCount] <;>
        simp [eeaCnotCount, UnaryActionTree.leafCostSum,
          UnaryActionTree.internalNodes] <;>
        omega

/-- Constructor-derived coherent T count. -/
theorem unaryActionUnitary_tCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    ShorECDLP.tCount (unaryActionUnitary order leafAction tree control ancillas) =
      tree.leafCostSum (fun label wire ↦
        ShorECDLP.tCount (leafAction label wire)) control ancillas +
        14 * tree.internalNodes := by
  induction hlayout with
  | leaf label control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [unaryActionUnitary] <;>
        simp only [tCount_append] <;>
        rw [ihZero, ihOne] <;>
        simp [computeZeroAnd, ShorECDLP.tCount, tCost,
          UnaryActionTree.leafCostSum, UnaryActionTree.internalNodes] <;>
        omega

private def ActionZeroPathReady
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState) : Prop :=
  Clean rest state ∧ ZeroAndComputed control indexBit path state

private def ActionOnePathReady
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState) : Prop :=
  Clean rest state ∧
    state path = (state control && state indexBit)

private theorem actionZeroPathReady_after_compute
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState)
    (hci : control ≠ indexBit) (hcp : control ≠ path)
    (hip : indexBit ≠ path) (hpathRest : path ∉ rest)
    (hclean : Clean (path :: rest) state) :
    ActionZeroPathReady control indexBit path rest
      (run (computeZeroAnd control indexBit path) state) := by
  have hpath : state path = false := hclean path (by simp)
  have hrun := run_computeZeroAnd control indexBit path state
    hci hcp hip hpath
  rw [hrun]
  constructor
  · intro wire hwire
    have hwp : wire ≠ path := by
      intro equality
      subst wire
      exact hpathRest hwire
    rw [upd_other state path _ hwp]
    exact hclean wire (by simp [hwire])
  · unfold ZeroAndComputed
    simp [upd, hcp, hip]

private theorem actionOnePathReady_after_zero_toggle
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState)
    (hcp : control ≠ path) (hip : indexBit ≠ path)
    (hpathRest : path ∉ rest)
    (hready : ActionZeroPathReady control indexBit path rest state) :
    ActionOnePathReady control indexBit path rest
      (Classical.applyGate (.CX control path) state) := by
  constructor
  · intro wire hwire
    have hwp : wire ≠ path := by
      intro equality
      subst wire
      exact hpathRest hwire
    change state[path ↦ Bool.xor (state path) (state control)] wire = false
    rw [upd_other state path _ hwp]
    exact hready.1 wire hwire
  · unfold ActionZeroPathReady at hready
    unfold ZeroAndComputed at hready
    simp only [Classical.applyGate]
    cases hc : state control <;> cases hi : state indexBit <;>
      simp [upd, hcp, hip, hready.2, hc, hi]

private theorem actionZeroPathReady_after_one_toggle
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState)
    (hcp : control ≠ path) (hip : indexBit ≠ path)
    (hpathRest : path ∉ rest)
    (hready : ActionOnePathReady control indexBit path rest state) :
    ActionZeroPathReady control indexBit path rest
      (Classical.applyGate (.CX control path) state) := by
  constructor
  · intro wire hwire
    have hwp : wire ≠ path := by
      intro equality
      subst wire
      exact hpathRest hwire
    change state[path ↦ Bool.xor (state path) (state control)] wire = false
    rw [upd_other state path _ hwp]
    exact hready.1 wire hwire
  · unfold ActionOnePathReady at hready
    unfold ZeroAndComputed
    simp only [Classical.applyGate]
    cases hc : state control <;> cases hi : state indexBit <;>
      simp [upd, hcp, hip, hready.2, hc, hi]

private theorem unaryAction_coherent_mono
    {program : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid Stronger : BasisState → Prop}
    (hrefines : CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ state, Stronger state → Valid state) :
    CoherentlyImplementsOn program ideal Stronger := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch state hstate ↦
    hbranch state (hsub state hstate)

private theorem unaryAction_coherent_seq_circuits
    {first second : AdaptiveCircuit}
    {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : CoherentlyImplementsOn first
      (Quantum.run firstCircuit) FirstValid)
    (hsecond : CoherentlyImplementsOn second
      (Quantum.run secondCircuit) SecondValid)
    (hfirstClassical : HPFree firstCircuit)
    (hvalid : ∀ state, FirstValid state →
      SecondValid (run firstCircuit state)) :
    CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have hseq := hfirst.seq hsecond (by
    intro state hstate
    rw [run_ket_agrees_classical firstCircuit state hfirstClassical]
    exact supportedOn_ket SecondValid _ (hvalid state hstate))
  apply hseq.congrIdeal
  intro state _
  exact (Quantum.run_append firstCircuit secondCircuit (ket state)).symm

/-- Replacing every reverse path-AND by X-measure/reset coherently implements the same
leaf-action traversal.  The only cross-layer obligation is that each classical leaf action leaves
the decoder interface unchanged. -/
theorem unaryAction_coherent
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas)
    (hleaf : UnaryLeafPreserves leafAction
      (control :: tree.indexWires.dedup ++ ancillas))
    (hhp : UnaryLeafHPFree leafAction) :
    CoherentlyImplementsOn
      (unaryAction order leafAction tree control ancillas)
      (Quantum.run (unaryActionUnitary order leafAction tree control ancillas))
      (Clean ancillas) := by
  induction hlayout with
  | leaf label control ancillas hlocal =>
      exact CoherentlyImplementsOn.unitary
        (leafAction label control) (Clean ancillas)
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip, hpathRest⟩ :=
        unaryActionNode_parts indexBit control path zero one rest hlocal
      have hzeroRoles : ∀ wire,
          wire ∈ path :: zero.indexWires.dedup ++ rest →
            wire ∈ control ::
              (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
                (path :: rest) :=
        actionTree_zero_decoder_subset indexBit control path zero one rest
      have honeRoles : ∀ wire,
          wire ∈ path :: one.indexWires.dedup ++ rest →
            wire ∈ control ::
              (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
                (path :: rest) :=
        actionTree_one_decoder_subset indexBit control path zero one rest
      have hzeroLeaf : UnaryLeafPreserves leafAction
          (path :: zero.indexWires.dedup ++ rest) := by
        intro label childControl hchildControl state wire hwire
        exact hleaf label childControl (hzeroRoles childControl hchildControl)
          state wire (hzeroRoles wire hwire)
      have honeLeaf : UnaryLeafPreserves leafAction
          (path :: one.indexWires.dedup ++ rest) := by
        intro label childControl hchildControl state wire hwire
        exact hleaf label childControl (honeRoles childControl hchildControl)
          state wire (honeRoles wire hwire)
      have hzeroPreserves : ∀ state,
          ActionZeroPathReady control indexBit path rest state →
          ActionZeroPathReady control indexBit path rest
            (run (unaryActionUnitary order leafAction zero path rest) state) := by
        intro state hready
        have hpreserves := unaryActionUnitary_preservesProtected
          order leafAction zero path rest
          (control ::
            (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
              (path :: rest))
          state hzero hleaf hzeroRoles hready.1
        refine ⟨?_, ?_⟩
        · intro wire hwire
          rw [hpreserves wire (by simp [hwire])]
          exact hready.1 wire hwire
        · unfold ActionZeroPathReady at hready
          unfold ZeroAndComputed at hready ⊢
          rw [hpreserves control (by simp),
            hpreserves indexBit (by simp [UnaryActionTree.indexWires]),
            hpreserves path (by simp)]
          exact hready.2
      have honePreserves : ∀ state,
          ActionOnePathReady control indexBit path rest state →
          ActionOnePathReady control indexBit path rest
            (run (unaryActionUnitary order leafAction one path rest) state) := by
        intro state hready
        have hpreserves := unaryActionUnitary_preservesProtected
          order leafAction one path rest
          (control ::
            (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
              (path :: rest))
          state hone hleaf honeRoles hready.1
        refine ⟨?_, ?_⟩
        · intro wire hwire
          rw [hpreserves wire (by simp [hwire])]
          exact hready.1 wire hwire
        · unfold ActionOnePathReady at hready
          rw [hpreserves path (by simp),
            hpreserves control (by simp),
            hpreserves indexBit (by simp [UnaryActionTree.indexWires])]
          exact hready.2
      have herase : CoherentlyImplementsOn
          (eraseZeroAnd control indexBit path)
          (Quantum.run (computeZeroAnd control indexBit path))
          (ActionZeroPathReady control indexBit path rest) :=
        unaryAction_coherent_mono
          (eraseZeroAnd_coherent control indexBit path hci hcp hip)
          (fun _ hready ↦ hready.2)
      have htoggleOne := CoherentlyImplementsOn.unitary
        [.CX control path] (ActionOnePathReady control indexBit path rest)
      have htoggleZero := CoherentlyImplementsOn.unitary
        [.CX control path] (ActionZeroPathReady control indexBit path rest)
      have ihOneReady : CoherentlyImplementsOn
          (unaryAction order leafAction one path rest)
          (Quantum.run (unaryActionUnitary order leafAction one path rest))
          (ActionOnePathReady control indexBit path rest) :=
        unaryAction_coherent_mono (ihOne honeLeaf)
          (fun _ hready ↦ hready.1)
      have ihZeroReady : CoherentlyImplementsOn
          (unaryAction order leafAction zero path rest)
          (Quantum.run (unaryActionUnitary order leafAction zero path rest))
          (ActionZeroPathReady control indexBit path rest) :=
        unaryAction_coherent_mono (ihZero hzeroLeaf)
          (fun _ hready ↦ hready.1)
      have hcompute := CoherentlyImplementsOn.unitary
        (computeZeroAnd control indexBit path) (Clean (path :: rest))
      cases order with
      | inc =>
          have hback := unaryAction_coherent_seq_circuits htoggleOne herase
            (by simp) (by
              intro state hready
              simpa only [Classical.run_cons, Classical.run_nil] using
                actionZeroPathReady_after_one_toggle
                  control indexBit path rest state hcp hip hpathRest hready)
          have honeChunk := unaryAction_coherent_seq_circuits ihOneReady hback
            (unaryActionUnitary_HPFree .inc leafAction one path rest hhp)
            honePreserves
          have htoggleChunk := unaryAction_coherent_seq_circuits
            htoggleZero honeChunk (by simp) (by
              intro state hready
              simpa only [Classical.run_cons, Classical.run_nil] using
                actionOnePathReady_after_zero_toggle
                  control indexBit path rest state hcp hip hpathRest hready)
          have hzeroChunk := unaryAction_coherent_seq_circuits
            ihZeroReady htoggleChunk
            (unaryActionUnitary_HPFree .inc leafAction zero path rest hhp)
            hzeroPreserves
          have hall := unaryAction_coherent_seq_circuits hcompute hzeroChunk
            (computeZeroAnd_HPFree control indexBit path)
            (fun state hclean ↦ actionZeroPathReady_after_compute
              control indexBit path rest state hci hcp hip hpathRest hclean)
          simpa only [unaryAction, unaryActionUnitary,
            AdaptiveCircuit.seq, List.append_assoc] using hall
      | dec =>
          have hzeroErase := unaryAction_coherent_seq_circuits
            ihZeroReady herase
            (unaryActionUnitary_HPFree .dec leafAction zero path rest hhp)
            hzeroPreserves
          have htoggleZeroChunk := unaryAction_coherent_seq_circuits
            htoggleOne hzeroErase (by simp) (by
              intro state hready
              simpa only [Classical.run_cons, Classical.run_nil] using
                actionZeroPathReady_after_one_toggle
                  control indexBit path rest state hcp hip hpathRest hready)
          have honeChunk := unaryAction_coherent_seq_circuits
            ihOneReady htoggleZeroChunk
            (unaryActionUnitary_HPFree .dec leafAction one path rest hhp)
            honePreserves
          have htoggleOneChunk := unaryAction_coherent_seq_circuits
            htoggleZero honeChunk (by simp) (by
              intro state hready
              simpa only [Classical.run_cons, Classical.run_nil] using
                actionOnePathReady_after_zero_toggle
                  control indexBit path rest state hcp hip hpathRest hready)
          have hall := unaryAction_coherent_seq_circuits hcompute htoggleOneChunk
            (computeZeroAnd_HPFree control indexBit path)
            (fun state hclean ↦ actionZeroPathReady_after_compute
              control indexBit path rest state hci hcp hip hpathRest hclean)
          simpa only [unaryAction, unaryActionUnitary,
            AdaptiveCircuit.seq, List.append_assoc] using hall

/-- Physical well-formedness of every adaptive branch. -/
theorem unaryAction_wellFormed
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas)
    (hleaf : UnaryLeafWellFormed leafAction tree
      (control :: tree.indexWires.dedup ++ ancillas)) :
    (unaryAction order leafAction tree control ancillas).WellFormed := by
  induction hlayout with
  | leaf label control ancillas hlocal =>
      exact ⟨hleaf label (by simp [UnaryActionTree.labels]) control (by simp),
        trivial⟩
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip, hpathRest⟩ :=
        unaryActionNode_parts indexBit control path zero one rest hlocal
      have hzeroLeaf : UnaryLeafWellFormed leafAction zero
          (path :: zero.indexWires.dedup ++ rest) := by
        intro label hlabel childControl hchildControl
        exact hleaf label (by
          simp [UnaryActionTree.labels, hlabel]) childControl
          (actionTree_zero_decoder_subset indexBit control path zero one rest
            childControl hchildControl)
      have honeLeaf : UnaryLeafWellFormed leafAction one
          (path :: one.indexWires.dedup ++ rest) := by
        intro label hlabel childControl hchildControl
        exact hleaf label (by
          simp [UnaryActionTree.labels, hlabel]) childControl
          (actionTree_one_decoder_subset indexBit control path zero one rest
            childControl hchildControl)
      have hcompute :=
        computeZeroAnd_wellFormed control indexBit path hci hcp hip
      have htoggle : CircuitWellFormed [.CX control path] := by
        simp [CircuitWellFormed, Gate.WellFormed, hcp]
      have herase :=
        eraseZeroAnd_wellFormed control indexBit path hci hcp hip
      cases order with
      | inc =>
          rw [unaryAction]
          exact ⟨hcompute,
            AdaptiveCircuit.WellFormed.seq (ihZero hzeroLeaf)
              ⟨htoggle,
                AdaptiveCircuit.WellFormed.seq (ihOne honeLeaf)
                  ⟨htoggle, herase⟩⟩⟩
      | dec =>
          rw [unaryAction]
          exact ⟨hcompute, ⟨htoggle,
            AdaptiveCircuit.WellFormed.seq (ihOne honeLeaf)
              ⟨htoggle,
                AdaptiveCircuit.WellFormed.seq (ihZero hzeroLeaf) herase⟩⟩⟩

private theorem unaryAction_measurementCount_seq
    (first second : AdaptiveCircuit) :
    (first.seq second).measurementCount =
      first.measurementCount + second.measurementCount := by
  induction first with
  | done =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount, ih]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount,
        ihFalse, ihTrue, Nat.add_max_add_right, Nat.add_assoc]

private theorem unaryAction_tCount_seq
    (first second : AdaptiveCircuit) :
    (first.seq second).tCount = first.tCount + second.tCount := by
  induction first with
  | done =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount, ih, Nat.add_assoc]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount,
        ihFalse, ihTrue, Nat.add_max_add_right]

/-- Exactly one path-AND is measured at each internal decision node. -/
theorem unaryAction_measurementCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    (unaryAction order leafAction tree control ancillas).measurementCount =
      tree.internalNodes := by
  induction hlayout with
  | leaf label control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [unaryAction] <;>
        simp [AdaptiveCircuit.measurementCount,
          unaryAction_measurementCount_seq, ihZero, ihOne,
          UnaryActionTree.internalNodes] <;>
        omega

/-- Measurement removes the reverse Toffoli at each decision node; leaf costs are unchanged. -/
theorem unaryAction_tCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    (unaryAction order leafAction tree control ancillas).tCount =
      tree.leafCostSum (fun label wire ↦
        ShorECDLP.tCount (leafAction label wire)) control ancillas +
        7 * tree.internalNodes := by
  induction hlayout with
  | leaf label control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [unaryAction] <;>
        simp [AdaptiveCircuit.tCount, unaryAction_tCount_seq,
          ihZero, ihOne, UnaryActionTree.leafCostSum,
          UnaryActionTree.internalNodes, tCost] <;>
        omega

end

end ShorECDLP.Paper2607_13816
