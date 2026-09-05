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

/-- Branch visitation order on a caller-supplied tree.  `inc` visits the zero subtree first and
`dec` visits the one subtree first, matching the supplement's local `order="inc"` / `order="dec"`
switch.  Numeric increasing/decreasing label order additionally requires the supplement's
sorted/deduplicated-label, highest-varying-bit tree-construction certificate; that concrete builder
is outside this generic control-flow boundary. -/
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

/-- Leaf labels in the dynamic order selected by the source traversal. -/
def visitLabels : UnaryOrder → UnaryActionTree → List Nat
  | _, .leaf label => [label]
  | .inc, .node _ zero one => visitLabels .inc zero ++ visitLabels .inc one
  | .dec, .node _ zero one => visitLabels .dec one ++ visitLabels .dec zero

@[simp]
theorem visitLabels_inc (tree : UnaryActionTree) :
    tree.visitLabels .inc = tree.labels := by
  induction tree with
  | leaf => rfl
  | node indexBit zero one ihZero ihOne =>
      simp [visitLabels, labels, ihZero, ihOne]

@[simp]
theorem visitLabels_dec (tree : UnaryActionTree) :
    tree.visitLabels .dec = tree.labels.reverse := by
  induction tree with
  | leaf => rfl
  | node indexBit zero one ihZero ihOne =>
      simp [visitLabels, labels, ihZero, ihOne]

@[simp]
theorem mem_visitLabels
    (order : UnaryOrder) (tree : UnaryActionTree) (label : Nat) :
    label ∈ tree.visitLabels order ↔ label ∈ tree.labels := by
  cases order <;> simp

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

/-- Gate-independent execution model for a circuit-valued unary traversal.  It records the
temporary path-bit values explicitly, but replaces each leaf circuit by its supplied classical
state transformer.  The final update at an internal node is the semantic effect of reversing its
computed path AND. -/
def runLeafState
    (order : UnaryOrder)
    (leafState : Nat → Wire → BasisState → BasisState) :
    UnaryActionTree → Wire → List Wire → BasisState → BasisState
  | .leaf label, control, _, state => leafState label control state
  | .node indexBit zero one, control, path :: rest, state =>
      let first := state[path ↦ state control && !state indexBit]
      match order with
      | .inc =>
          let afterZero := zero.runLeafState order leafState path rest first
          let switched :=
            afterZero[path ↦ Bool.xor (afterZero path) (afterZero control)]
          let afterOne := one.runLeafState order leafState path rest switched
          let switchedBack :=
            afterOne[path ↦ Bool.xor (afterOne path) (afterOne control)]
          switchedBack[path ↦ false]
      | .dec =>
          let switched :=
            first[path ↦ Bool.xor (first path) (first control)]
          let afterOne := one.runLeafState order leafState path rest switched
          let switchedBack :=
            afterOne[path ↦ Bool.xor (afterOne path) (afterOne control)]
          let afterZero := zero.runLeafState order leafState path rest switchedBack
          afterZero[path ↦ false]
  | .node _ _ _, _, [], state => state

/-- Gate-independent ordered leaf trace with decoder-path details erased.  `routeState` is frozen:
its index bits choose the unique active leaf, while every leaf is still visited in source order.
This is the useful semantic boundary for range scans, whose live accumulator changes at every
leaf but whose equality pulse is active only on the routed boundary label. -/
def runLogicalTree
    (order : UnaryOrder)
    (leafState : Nat → Bool → BasisState → BasisState) :
    UnaryActionTree → Bool → BasisState → BasisState → BasisState
  | .leaf label, active, _, state => leafState label active state
  | .node indexBit zero one, active, routeState, state =>
      let zeroActive := active && !routeState indexBit
      let oneActive := active && routeState indexBit
      match order with
      | .inc =>
          one.runLogicalTree order leafState oneActive routeState
            (zero.runLogicalTree order leafState zeroActive routeState state)
      | .dec =>
          zero.runLogicalTree order leafState zeroActive routeState
            (one.runLogicalTree order leafState oneActive routeState state)

/-- Ordered labels paired with the Boolean equality pulse carried by their dynamic path wire. -/
def visitPulses :
    UnaryOrder → UnaryActionTree → Bool → BasisState → List (Nat × Bool)
  | _, .leaf label, active, _ => [(label, active)]
  | .inc, .node indexBit zero one, active, routeState =>
      zero.visitPulses .inc (active && !routeState indexBit) routeState ++
        one.visitPulses .inc (active && routeState indexBit) routeState
  | .dec, .node indexBit zero one, active, routeState =>
      one.visitPulses .dec (active && routeState indexBit) routeState ++
        zero.visitPulses .dec (active && !routeState indexBit) routeState

@[simp]
theorem visitPulses_labels
    (order : UnaryOrder) (tree : UnaryActionTree)
    (active : Bool) (routeState : BasisState) :
    (tree.visitPulses order active routeState).map Prod.fst =
      tree.visitLabels order := by
  induction tree generalizing order active with
  | leaf => rfl
  | node indexBit zero one ihZero ihOne =>
      cases order <;>
        simp [visitPulses, visitLabels, ihZero, ihOne]

@[simp]
theorem visitPulses_false
    (order : UnaryOrder) (tree : UnaryActionTree) (routeState : BasisState) :
    tree.visitPulses order false routeState =
      (tree.visitLabels order).map fun label => (label, false) := by
  induction tree generalizing order with
  | leaf => rfl
  | node indexBit zero one ihZero ihOne =>
      cases order <;>
        simp [visitPulses, visitLabels, ihZero, ihOne]

private theorem map_routePulse_false_of_not_mem
    (labels : List Nat) (route : Nat) (hroute : route ∉ labels) :
    labels.map (fun label => (label, decide (label = route))) =
      labels.map (fun label => (label, false)) := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      simp only [List.mem_cons, not_or] at hroute
      simp [Ne.symm hroute.1, ih hroute.2]

/-- The decoder-erased recursion is exactly a left fold over its ordered leaf/pulse trace. -/
theorem runLogicalTree_eq_foldl
    (order : UnaryOrder)
    (leafState : Nat → Bool → BasisState → BasisState)
    (tree : UnaryActionTree) (active : Bool)
    (routeState state : BasisState) :
    tree.runLogicalTree order leafState active routeState state =
      (tree.visitPulses order active routeState).foldl
        (fun current pulse => leafState pulse.1 pulse.2 current) state := by
  induction tree generalizing order active state with
  | leaf => rfl
  | node indexBit zero one ihZero ihOne =>
      cases order with
      | inc =>
          simp only [runLogicalTree, visitPulses, List.foldl_append]
          rw [← ihZero, ← ihOne]
      | dec =>
          simp only [runLogicalTree, visitPulses, List.foldl_append]
          rw [← ihOne, ← ihZero]

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

/-- With duplicate-free labels, the pulse trace is true exactly at the routed leaf. -/
theorem visitPulses_eq_route
    (order : UnaryOrder) (tree : UnaryActionTree)
    (active : Bool) (routeState : BasisState)
    (hnodup : tree.labels.Nodup) :
    tree.visitPulses order active routeState =
      (tree.visitLabels order).map fun label =>
        (label, active && decide (label = tree.routeLabel routeState)) := by
  induction tree generalizing order active with
  | leaf label =>
      cases active <;> simp [visitPulses, visitLabels, routeLabel]
  | node indexBit zero one ihZero ihOne =>
      simp only [labels, List.nodup_append] at hnodup
      obtain ⟨hzeroNodup, honeNodup, hcross⟩ := hnodup
      cases active with
      | false => simp [visitPulses_false]
      | true =>
          cases hbit : routeState indexBit with
          | false =>
              have hrmem : zero.routeLabel routeState ∈ zero.labels :=
                routeLabel_mem_labels zero routeState
              have hrnot : zero.routeLabel routeState ∉ one.labels := by
                intro hone
                exact hcross (zero.routeLabel routeState) hrmem
                  (zero.routeLabel routeState) hone rfl
              cases order with
              | inc =>
                  have hrnotVisit :
                      zero.routeLabel routeState ∉ one.visitLabels .inc := by
                    simpa using hrnot
                  simp only [visitPulses, hbit, Bool.not_false, Bool.and_true,
                    Bool.and_false, ihZero .inc true hzeroNodup,
                    visitPulses_false, Bool.true_and]
                  rw [← map_routePulse_false_of_not_mem
                    (one.visitLabels .inc) (zero.routeLabel routeState) hrnotVisit]
                  simp [visitLabels, routeLabel, hbit]
              | dec =>
                  have hrnotVisit :
                      zero.routeLabel routeState ∉ one.visitLabels .dec := by
                    simpa using hrnot
                  simp only [visitPulses, hbit, Bool.not_false, Bool.and_true,
                    Bool.and_false, ihZero .dec true hzeroNodup,
                    visitPulses_false, Bool.true_and]
                  rw [← map_routePulse_false_of_not_mem
                    (one.visitLabels .dec) (zero.routeLabel routeState) hrnotVisit]
                  simp [visitLabels, routeLabel, hbit]
          | true =>
              have hrmem : one.routeLabel routeState ∈ one.labels :=
                routeLabel_mem_labels one routeState
              have hrnot : one.routeLabel routeState ∉ zero.labels := by
                intro hzero
                exact hcross (one.routeLabel routeState) hzero
                  (one.routeLabel routeState) hrmem rfl
              cases order with
              | inc =>
                  have hrnotVisit :
                      one.routeLabel routeState ∉ zero.visitLabels .inc := by
                    simpa using hrnot
                  simp only [visitPulses, hbit, Bool.not_true, Bool.and_false,
                    Bool.and_true, visitPulses_false,
                    ihOne .inc true honeNodup, Bool.true_and]
                  rw [← map_routePulse_false_of_not_mem
                    (zero.visitLabels .inc) (one.routeLabel routeState) hrnotVisit]
                  simp [visitLabels, routeLabel, hbit]
              | dec =>
                  have hrnotVisit :
                      one.routeLabel routeState ∉ zero.visitLabels .dec := by
                    simpa using hrnot
                  simp only [visitPulses, hbit, Bool.not_true, Bool.and_false,
                    Bool.and_true, visitPulses_false,
                    ihOne .dec true honeNodup, Bool.true_and]
                  rw [← map_routePulse_false_of_not_mem
                    (zero.visitLabels .dec) (one.routeLabel routeState) hrnotVisit]
                  simp [visitLabels, routeLabel, hbit]

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

theorem Layout.control_not_mem_ancillas
    {tree : UnaryActionTree} {control : Wire} {ancillas : List Wire}
    (hlayout : tree.Layout control ancillas) :
    control ∉ ancillas := by
  cases hlayout with
  | leaf label control ancillas hlocal =>
      exact (List.nodup_cons.mp hlocal).1
  | node indexBit control path zero one rest hlocal hzero hone =>
      simp only [List.nodup_cons] at hlocal
      exact fun hmem => hlocal.1 (by simp [hmem])

end UnaryActionTree

/-- Two basis states agree away from a named decoder interface. -/
def AgreesOutside (protectedWires : List Wire)
    (left right : BasisState) : Prop :=
  ∀ wire, wire ∉ protectedWires → left wire = right wire

/-- A logical leaf trace does not change the erased decoder interface. -/
def LogicalLeafPreserves
    (leafState : Nat → Bool → BasisState → BasisState)
    (protectedWires : List Wire) : Prop :=
  ∀ label active state wire, wire ∈ protectedWires →
    leafState label active state wire = state wire

/-- A logical leaf trace cannot observe changes confined to the erased decoder interface, provided
the caller-supplied stable root control still agrees.  The extra equality is needed by source
leaves which read the external root control as data while ignoring transient decoder-path wires. -/
def LogicalLeafRespectsOutside
    (leafState : Nat → Bool → BasisState → BasisState)
    (protectedWires : List Wire) (stableRoot : Wire) : Prop :=
  ∀ label active left right, AgreesOutside protectedWires left right →
    left stableRoot = right stableRoot →
    AgreesOutside protectedWires
      (leafState label active left) (leafState label active right)

/-- The physical leaf state uses its dynamic path wire only through that wire's Boolean value. -/
def UnaryLeafRunsLogically
    (leafState : Nat → Wire → BasisState → BasisState)
    (logicalLeafState : Nat → Bool → BasisState → BasisState)
    (protectedWires : List Wire) : Prop :=
  ∀ label control, control ∈ protectedWires → ∀ state,
    leafState label control state =
      logicalLeafState label (state control) state

private theorem AgreesOutside.updateLeft
    {protectedWires : List Wire} {left right : BasisState}
    (h : AgreesOutside protectedWires left right)
    (wire : Wire) (value : Bool) (hwire : wire ∈ protectedWires) :
    AgreesOutside protectedWires (left[wire ↦ value]) right := by
  intro other hother
  rw [upd_other left wire value (by
    intro equality
    subst other
    exact hother hwire)]
  exact h other hother

/-- Logical source-order execution preserves the declared decoder interface. -/
theorem UnaryActionTree.runLogicalTree_preserves
    (order : UnaryOrder)
    (leafState : Nat → Bool → BasisState → BasisState)
    (tree : UnaryActionTree) (active : Bool)
    (routeState state : BasisState) (protectedWires : List Wire)
    (hleaf : LogicalLeafPreserves leafState protectedWires) :
    ∀ wire, wire ∈ protectedWires →
      tree.runLogicalTree order leafState active routeState state wire =
        state wire := by
  induction tree generalizing active state with
  | leaf label =>
      intro wire hwire
      exact hleaf label active state wire hwire
  | node indexBit zero one ihZero ihOne =>
      intro wire hwire
      cases order with
      | inc =>
          rw [UnaryActionTree.runLogicalTree,
            ihOne (active && routeState indexBit) _ wire hwire,
            ihZero (active && !routeState indexBit) state wire hwire]
      | dec =>
          rw [UnaryActionTree.runLogicalTree,
            ihZero (active && !routeState indexBit) _ wire hwire,
            ihOne (active && routeState indexBit) state wire hwire]

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

/-- Source traversal with a genuinely adaptive program at every leaf.  Decoder
compute/toggle/cleanup order is identical to `unaryAction`; only the leaf payload differs. -/
def unaryAdaptiveAction
    (order : UnaryOrder)
    (leafAction : Nat → Wire → AdaptiveCircuit) :
    UnaryActionTree → Wire → List Wire → AdaptiveCircuit
  | .leaf label, control, _ => leafAction label control
  | .node indexBit zero one, control, path :: rest =>
      match order with
      | .inc =>
          .unitary (computeZeroAnd control indexBit path)
            ((unaryAdaptiveAction order leafAction zero path rest).seq
              (.unitary [.CX control path]
                ((unaryAdaptiveAction order leafAction one path rest).seq
                  (.unitary [.CX control path]
                    (eraseZeroAnd control indexBit path)))))
      | .dec =>
          .unitary (computeZeroAnd control indexBit path)
            (.unitary [.CX control path]
              ((unaryAdaptiveAction order leafAction one path rest).seq
                (.unitary [.CX control path]
                  ((unaryAdaptiveAction order leafAction zero path rest).seq
                    (eraseZeroAnd control indexBit path)))))
  | .node _ _ _, _, [] => .done

@[simp]
theorem unaryAdaptiveAction_unitary
    (order : UnaryOrder) (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire) :
    unaryAdaptiveAction order
        (fun label dynamic ↦ .unitary (leafAction label dynamic) .done)
        tree control ancillas =
      unaryAction order leafAction tree control ancillas := by
  induction tree generalizing control ancillas with
  | leaf label => rfl
  | node indexBit zero one ihZero ihOne =>
      cases ancillas with
      | nil => rfl
      | cons path rest =>
          cases order <;>
            simp [unaryAdaptiveAction, unaryAction, ihZero, ihOne]

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

/-- Every adaptive leaf coherently refines the corresponding coherent leaf on a clean
caller-supplied work bank. -/
def UnaryAdaptiveLeafCoherentOn
    (leafAdaptive : Nat → Wire → AdaptiveCircuit)
    (leafUnitary : Nat → Wire → Circuit)
    (labels : List Nat) (dynamicWires extraWires : List Wire) : Prop :=
  ∀ label, label ∈ labels → ∀ control, control ∈ dynamicWires →
    CoherentlyImplementsOn
      (leafAdaptive label control)
      (Quantum.run (leafUnitary label control))
      (fun state ↦ Clean extraWires state)

/-- Every leaf action reached by this tree is physically well formed. -/
def UnaryLeafWellFormed
    (leafAction : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (protectedWires : List Wire) : Prop :=
  ∀ label ∈ tree.labels, ∀ control ∈ protectedWires,
    CircuitWellFormed (leafAction label control)

/-- Every adaptive leaf reached by this tree is physically well formed. -/
def UnaryAdaptiveLeafWellFormed
    (leafAction : Nat → Wire → AdaptiveCircuit)
    (tree : UnaryActionTree) (protectedWires : List Wire) : Prop :=
  ∀ label ∈ tree.labels, ∀ control ∈ protectedWires,
    (leafAction label control).WellFormed

/-- Direct classical meaning of every circuit-valued leaf. -/
def UnaryLeafRunsAs
    (leafAction : Nat → Wire → Circuit)
    (leafState : Nat → Wire → BasisState → BasisState) : Prop :=
  ∀ label control state,
    Classical.run (leafAction label control) state = leafState label control state

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

private theorem unaryActionNode_index_ne_path
    (indexBit control path : Wire) (zero one : UnaryActionTree)
    (rest : List Wire)
    (hlocal :
      (control ::
        ((UnaryActionTree.node indexBit zero one).indexWires.dedup ++
          (path :: rest))).Nodup) :
    ∀ wire, wire ∈ (UnaryActionTree.node indexBit zero one).indexWires →
      wire ≠ path := by
  intro wire hwire
  have htail := (List.nodup_cons.mp hlocal).2
  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp htail
  exact hcross wire (List.mem_dedup.mpr hwire) path (by simp)

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

/-- A unary traversal preserves any caller-declared protected interface that contains its
decoder roles, provided every leaf preserves that same interface.  This strengthened form is
used by source range scans whose leaf actions also share a live accumulator. -/
theorem unaryActionUnitary_preserves
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
        state wire :=
  unaryActionUnitary_preservesProtected order leafAction tree control ancillas
    protectedWires state hlayout hleaf hroles hclean

/-- Direct whole-state semantics of the coherent circuit-valued traversal.  The theorem exposes
the exact ordered leaf-state execution while proving, rather than assuming, that every temporary
path AND is restored. -/
theorem run_unaryActionUnitary_as_runLeafState
    (order : UnaryOrder)
    (leafAction : Nat → Wire → Circuit)
    (leafState : Nat → Wire → BasisState → BasisState)
    (tree : UnaryActionTree) (control : Wire)
    (ancillas protectedWires : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout control ancillas)
    (hruns : UnaryLeafRunsAs leafAction leafState)
    (hleaf : UnaryLeafPreserves leafAction protectedWires)
    (hroles : ∀ wire,
      wire ∈ control :: tree.indexWires.dedup ++ ancillas →
        wire ∈ protectedWires)
    (hclean : Clean ancillas state) :
    run (unaryActionUnitary order leafAction tree control ancillas) state =
      tree.runLeafState order leafState control ancillas state := by
  induction hlayout generalizing state with
  | leaf label control ancillas hlocal =>
      exact hruns label control state
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
          have hzeroState : afterZero =
              zero.runLeafState .inc leafState path rest first := by
            exact ihZero first hzeroRoles hrestCleanFirst
          have hzeroPreserves : ∀ wire, wire ∈ protectedWires →
              afterZero wire = first wire := by
            intro wire hwire
            exact unaryActionUnitary_preserves .inc leafAction zero path rest
              protectedWires first hzero hleaf hzeroRoles hrestCleanFirst wire hwire
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
          have honeState : afterOne =
              one.runLeafState .inc leafState path rest switched := by
            exact ihOne switched honeRoles hrestCleanSwitched
          have honePreserves : ∀ wire, wire ∈ protectedWires →
              afterOne wire = switched wire := by
            intro wire hwire
            exact unaryActionUnitary_preserves .inc leafAction one path rest
              protectedWires switched hone hleaf honeRoles hrestCleanSwitched wire hwire
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
          rw [unaryActionUnitary, Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append, Classical.run_append]
          change run (computeZeroAnd control indexBit path) switchedBack = _
          rw [hcleanup]
          simp only [UnaryActionTree.runLeafState]
          simp only [switchedBack, Classical.applyGate, honeState, switched,
            hzeroState, hfirst]
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
          have honeState : afterOne =
              one.runLeafState .dec leafState path rest switched := by
            exact ihOne switched honeRoles hrestCleanSwitched
          have honePreserves : ∀ wire, wire ∈ protectedWires →
              afterOne wire = switched wire := by
            intro wire hwire
            exact unaryActionUnitary_preserves .dec leafAction one path rest
              protectedWires switched hone hleaf honeRoles hrestCleanSwitched wire hwire
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
          have hzeroState : afterZero =
              zero.runLeafState .dec leafState path rest switchedBack := by
            exact ihZero switchedBack hzeroRoles hrestCleanSwitchedBack
          have hzeroPreserves : ∀ wire, wire ∈ protectedWires →
              afterZero wire = switchedBack wire := by
            intro wire hwire
            exact unaryActionUnitary_preserves .dec leafAction zero path rest
              protectedWires switchedBack hzero hleaf hzeroRoles
                hrestCleanSwitchedBack wire hwire
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
          rw [unaryActionUnitary, Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append, Classical.run_append]
          change run (computeZeroAnd control indexBit path) afterZero = _
          rw [hcleanup]
          simp only [UnaryActionTree.runLeafState]
          simp only [hzeroState, switchedBack, Classical.applyGate, honeState,
            switched, hfirst]

private theorem runLeafState_agreesOutside_runLogicalTree
    (order : UnaryOrder)
    (leafAction : Nat → Wire → Circuit)
    (leafState : Nat → Wire → BasisState → BasisState)
    (logicalLeafState : Nat → Bool → BasisState → BasisState)
    (tree : UnaryActionTree) (control stableRoot : Wire)
    (ancillas protectedWires : List Wire)
    (state routeState logicalState : BasisState) (active : Bool)
    (hlayout : tree.Layout control ancillas)
    (hruns : UnaryLeafRunsAs leafAction leafState)
    (hlogical : UnaryLeafRunsLogically leafState logicalLeafState protectedWires)
    (hleaf : UnaryLeafPreserves leafAction protectedWires)
    (hlogicalPreserves : LogicalLeafPreserves logicalLeafState protectedWires)
    (hlogicalOutside :
      LogicalLeafRespectsOutside logicalLeafState protectedWires stableRoot)
    (hroles : ∀ wire,
      wire ∈ control :: tree.indexWires.dedup ++ ancillas →
        wire ∈ protectedWires)
    (houtside : AgreesOutside protectedWires state logicalState)
    (hstableProtected : stableRoot ∈ protectedWires)
    (hstableAncillas : stableRoot ∉ ancillas)
    (hstable : state stableRoot = logicalState stableRoot)
    (hcontrol : state control = active)
    (hroute : ∀ wire, wire ∈ tree.indexWires →
      state wire = routeState wire)
    (hclean : Clean ancillas state) :
    AgreesOutside protectedWires
      (tree.runLeafState order leafState control ancillas state)
      (tree.runLogicalTree order logicalLeafState active routeState logicalState) := by
  induction hlayout generalizing state logicalState active with
  | leaf label control ancillas hlocal =>
      rw [UnaryActionTree.runLeafState, UnaryActionTree.runLogicalTree,
        hlogical label control (hroles control (by simp)) state, hcontrol]
      exact hlogicalOutside label active state logicalState houtside hstable
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip, hpathRest⟩ :=
        unaryActionNode_parts indexBit control path zero one rest hlocal
      have hindexPath :=
        unaryActionNode_index_ne_path indexBit control path zero one rest hlocal
      have hpathProtected : path ∈ protectedWires := hroles path (by simp)
      have hcontrolProtected : control ∈ protectedWires := hroles control (by simp)
      have hindexProtected : indexBit ∈ protectedWires := hroles indexBit (by
        simp [UnaryActionTree.indexWires])
      have hstablePath : stableRoot ≠ path := by
        intro equality
        subst stableRoot
        exact hstableAncillas (by simp)
      have hstableRest : stableRoot ∉ rest := by
        intro hmem
        exact hstableAncillas (by simp [hmem])
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
      let zeroActive := active && !routeState indexBit
      let oneActive := active && routeState indexBit
      let first := state[path ↦ state control && !state indexBit]
      have hfirstOutside : AgreesOutside protectedWires first logicalState :=
        houtside.updateLeft path _ hpathProtected
      have hfirstStable : first stableRoot = logicalState stableRoot := by
        simp only [first]
        rw [upd_other state path _ hstablePath]
        exact hstable
      have hfirstClean : Clean rest first := by
        intro wire hwire
        simp only [first]
        rw [upd_other state path _ (by
          intro equality
          subst wire
          exact hpathRest hwire)]
        exact hclean wire (by simp [hwire])
      have hfirstPath : first path = zeroActive := by
        simp only [first]
        rw [upd_same, hcontrol,
          hroute indexBit (by simp [UnaryActionTree.indexWires])]
      have hfirstRoute : ∀ wire,
          wire ∈ (UnaryActionTree.node indexBit zero one).indexWires →
            first wire = routeState wire := by
        intro wire hwire
        simp only [first]
        rw [upd_other state path _ (hindexPath wire hwire)]
        exact hroute wire hwire
      have hzeroRoute : ∀ wire, wire ∈ zero.indexWires →
          first wire = routeState wire := by
        intro wire hwire
        exact hfirstRoute wire
          (actionTree_indices_subset_node indexBit zero one wire hwire)
      have honeRouteFirst : ∀ wire, wire ∈ one.indexWires →
          first wire = routeState wire := by
        intro wire hwire
        exact hfirstRoute wire
          (actionTree_one_indices_subset_node indexBit zero one wire hwire)
      cases order with
      | inc =>
          let afterZero :=
            zero.runLeafState .inc leafState path rest first
          let logicalAfterZero :=
            zero.runLogicalTree .inc logicalLeafState zeroActive routeState logicalState
          have hzeroOutside :
              AgreesOutside protectedWires afterZero logicalAfterZero := by
            simpa only [afterZero, logicalAfterZero] using
              ihZero first logicalState zeroActive hzeroRoles hfirstOutside
                hstableRest hfirstStable hfirstPath hzeroRoute hfirstClean
          have hzeroRun :
              Classical.run
                  (unaryActionUnitary .inc leafAction zero path rest) first =
                afterZero := by
            simpa only [afterZero] using
              run_unaryActionUnitary_as_runLeafState .inc leafAction leafState
                zero path rest protectedWires first hzero hruns hleaf
                hzeroRoles hfirstClean
          have hzeroPreserves : ∀ wire, wire ∈ protectedWires →
              afterZero wire = first wire := by
            intro wire hwire
            rw [← hzeroRun]
            exact unaryActionUnitary_preserves .inc leafAction zero path rest
              protectedWires first hzero hleaf hzeroRoles hfirstClean wire hwire
          have hlogicalZeroPreserves :
              logicalAfterZero stableRoot = logicalState stableRoot := by
            exact zero.runLogicalTree_preserves .inc logicalLeafState zeroActive
              routeState logicalState protectedWires hlogicalPreserves
                stableRoot hstableProtected
          let switched :=
            afterZero[path ↦ Bool.xor (afterZero path) (afterZero control)]
          have hswitchedOutside :
              AgreesOutside protectedWires switched logicalAfterZero :=
            hzeroOutside.updateLeft path _ hpathProtected
          have hswitchedStable :
              switched stableRoot = logicalAfterZero stableRoot := by
            simp only [switched]
            rw [upd_other afterZero path _ hstablePath,
              hzeroPreserves stableRoot hstableProtected,
              hfirstStable, hlogicalZeroPreserves]
          have hswitchedClean : Clean rest switched := by
            intro wire hwire
            simp only [switched]
            rw [upd_other afterZero path _ (by
              intro equality
              subst wire
              exact hpathRest hwire),
              hzeroPreserves wire (hzeroRoles wire (by simp [hwire]))]
            exact hfirstClean wire hwire
          have hswitchedPath : switched path = oneActive := by
            simp only [switched]
            rw [upd_same,
              hzeroPreserves path hpathProtected,
              hzeroPreserves control hcontrolProtected,
              hfirstPath]
            simp only [first]
            rw [upd_other state path _ hcp, hcontrol]
            simp only [zeroActive, oneActive]
            cases active <;> cases routeState indexBit <;> rfl
          have honeRoute : ∀ wire, wire ∈ one.indexWires →
              switched wire = routeState wire := by
            intro wire hwire
            have hparent :=
              actionTree_one_indices_subset_node indexBit zero one wire hwire
            simp only [switched]
            rw [upd_other afterZero path _ (hindexPath wire hparent),
              hzeroPreserves wire (hroles wire (by
                simp [UnaryActionTree.indexWires, hwire])),
              honeRouteFirst wire hwire]
          let afterOne :=
            one.runLeafState .inc leafState path rest switched
          let logicalAfterOne :=
            one.runLogicalTree .inc logicalLeafState oneActive routeState logicalAfterZero
          have honeOutside :
              AgreesOutside protectedWires afterOne logicalAfterOne := by
            simpa only [afterOne, logicalAfterOne] using
              ihOne switched logicalAfterZero oneActive honeRoles hswitchedOutside
                hstableRest hswitchedStable hswitchedPath honeRoute
                hswitchedClean
          let switchedBack :=
            afterOne[path ↦ Bool.xor (afterOne path) (afterOne control)]
          have hbackOutside :
              AgreesOutside protectedWires switchedBack logicalAfterOne :=
            honeOutside.updateLeft path _ hpathProtected
          have hfinalOutside :
              AgreesOutside protectedWires
                (switchedBack[path ↦ false]) logicalAfterOne :=
            hbackOutside.updateLeft path false hpathProtected
          simpa only [UnaryActionTree.runLeafState,
            UnaryActionTree.runLogicalTree, zeroActive, oneActive,
            first, afterZero, logicalAfterZero, switched,
            afterOne, logicalAfterOne, switchedBack] using hfinalOutside
      | dec =>
          let switched :=
            first[path ↦ Bool.xor (first path) (first control)]
          have hswitchedOutside :
              AgreesOutside protectedWires switched logicalState :=
            hfirstOutside.updateLeft path _ hpathProtected
          have hswitchedStable : switched stableRoot = logicalState stableRoot := by
            simp only [switched]
            rw [upd_other first path _ hstablePath]
            exact hfirstStable
          have hswitchedClean : Clean rest switched := by
            intro wire hwire
            simp only [switched]
            rw [upd_other first path _ (by
              intro equality
              subst wire
              exact hpathRest hwire)]
            exact hfirstClean wire hwire
          have hswitchedPath : switched path = oneActive := by
            simp only [switched]
            rw [upd_same, hfirstPath]
            simp only [first]
            rw [upd_other state path _ hcp, hcontrol]
            simp only [zeroActive, oneActive]
            cases active <;> cases routeState indexBit <;> rfl
          have honeRoute : ∀ wire, wire ∈ one.indexWires →
              switched wire = routeState wire := by
            intro wire hwire
            have hparent :=
              actionTree_one_indices_subset_node indexBit zero one wire hwire
            simp only [switched]
            rw [upd_other first path _ (hindexPath wire hparent),
              honeRouteFirst wire hwire]
          let afterOne :=
            one.runLeafState .dec leafState path rest switched
          let logicalAfterOne :=
            one.runLogicalTree .dec logicalLeafState oneActive routeState logicalState
          have honeOutside :
              AgreesOutside protectedWires afterOne logicalAfterOne := by
            simpa only [afterOne, logicalAfterOne] using
              ihOne switched logicalState oneActive honeRoles hswitchedOutside
                hstableRest hswitchedStable hswitchedPath honeRoute
                hswitchedClean
          have honeRun :
              Classical.run
                  (unaryActionUnitary .dec leafAction one path rest) switched =
                afterOne := by
            simpa only [afterOne] using
              run_unaryActionUnitary_as_runLeafState .dec leafAction leafState
                one path rest protectedWires switched hone hruns hleaf
                honeRoles hswitchedClean
          have honePreserves : ∀ wire, wire ∈ protectedWires →
              afterOne wire = switched wire := by
            intro wire hwire
            rw [← honeRun]
            exact unaryActionUnitary_preserves .dec leafAction one path rest
              protectedWires switched hone hleaf honeRoles hswitchedClean wire hwire
          have hlogicalOnePreserves :
              logicalAfterOne stableRoot = logicalState stableRoot := by
            exact one.runLogicalTree_preserves .dec logicalLeafState oneActive
              routeState logicalState protectedWires hlogicalPreserves
                stableRoot hstableProtected
          let switchedBack :=
            afterOne[path ↦ Bool.xor (afterOne path) (afterOne control)]
          have hbackOutside :
              AgreesOutside protectedWires switchedBack logicalAfterOne :=
            honeOutside.updateLeft path _ hpathProtected
          have hbackStable :
              switchedBack stableRoot = logicalAfterOne stableRoot := by
            simp only [switchedBack]
            rw [upd_other afterOne path _ hstablePath,
              honePreserves stableRoot hstableProtected,
              hswitchedStable, hlogicalOnePreserves]
          have hbackClean : Clean rest switchedBack := by
            intro wire hwire
            simp only [switchedBack]
            rw [upd_other afterOne path _ (by
              intro equality
              subst wire
              exact hpathRest hwire),
              honePreserves wire (honeRoles wire (by simp [hwire]))]
            exact hswitchedClean wire hwire
          have hbackPath : switchedBack path = zeroActive := by
            simp only [switchedBack]
            rw [upd_same,
              honePreserves path hpathProtected,
              honePreserves control hcontrolProtected,
              hswitchedPath]
            simp only [switched]
            rw [upd_other first path _ hcp]
            simp only [first]
            rw [upd_other state path _ hcp, hcontrol]
            simp only [zeroActive, oneActive]
            cases active <;> cases routeState indexBit <;> rfl
          have hzeroRouteBack : ∀ wire, wire ∈ zero.indexWires →
              switchedBack wire = routeState wire := by
            intro wire hwire
            have hparent :=
              actionTree_indices_subset_node indexBit zero one wire hwire
            simp only [switchedBack]
            rw [upd_other afterOne path _ (hindexPath wire hparent),
              honePreserves wire (hroles wire (by
                simp [UnaryActionTree.indexWires, hwire])),
              show switched wire = first wire by
                simp only [switched]
                rw [upd_other first path _ (hindexPath wire hparent)],
              hfirstRoute wire hparent]
          let afterZero :=
            zero.runLeafState .dec leafState path rest switchedBack
          let logicalAfterZero :=
            zero.runLogicalTree .dec logicalLeafState zeroActive routeState logicalAfterOne
          have hzeroOutside :
              AgreesOutside protectedWires afterZero logicalAfterZero := by
            simpa only [afterZero, logicalAfterZero] using
              ihZero switchedBack logicalAfterOne zeroActive hzeroRoles hbackOutside
                hstableRest hbackStable hbackPath hzeroRouteBack hbackClean
          have hfinalOutside :
              AgreesOutside protectedWires
                (afterZero[path ↦ false]) logicalAfterZero :=
            hzeroOutside.updateLeft path false hpathProtected
          simpa only [UnaryActionTree.runLeafState,
            UnaryActionTree.runLogicalTree, zeroActive, oneActive,
            first, switched, afterOne, logicalAfterOne,
            switchedBack, afterZero, logicalAfterZero] using hfinalOutside

/-- Direct decoder-erased semantics of a coherent circuit-valued traversal.  The frozen index
state selects the active equality pulse, while the logical trace visits every leaf in exactly the
same source order. -/
theorem run_unaryActionUnitary_as_runLogicalTree
    (order : UnaryOrder)
    (leafAction : Nat → Wire → Circuit)
    (leafState : Nat → Wire → BasisState → BasisState)
    (logicalLeafState : Nat → Bool → BasisState → BasisState)
    (tree : UnaryActionTree) (control : Wire)
    (ancillas protectedWires : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout control ancillas)
    (hruns : UnaryLeafRunsAs leafAction leafState)
    (hlogical : UnaryLeafRunsLogically leafState logicalLeafState protectedWires)
    (hleaf : UnaryLeafPreserves leafAction protectedWires)
    (hlogicalPreserves : LogicalLeafPreserves logicalLeafState protectedWires)
    (hlogicalOutside :
      LogicalLeafRespectsOutside logicalLeafState protectedWires control)
    (hroles : ∀ wire,
      wire ∈ control :: tree.indexWires.dedup ++ ancillas →
        wire ∈ protectedWires)
    (hclean : Clean ancillas state) :
    Classical.run
        (unaryActionUnitary order leafAction tree control ancillas) state =
      tree.runLogicalTree order logicalLeafState (state control) state state := by
  have hrun := run_unaryActionUnitary_as_runLeafState order leafAction leafState
    tree control ancillas protectedWires state hlayout hruns hleaf hroles hclean
  have houtside := runLeafState_agreesOutside_runLogicalTree order leafAction leafState
    logicalLeafState tree control control ancillas protectedWires state state state
    (state control) hlayout hruns hlogical hleaf hlogicalPreserves hlogicalOutside
    hroles (by intro wire hwire; rfl) (hroles control (by simp))
    hlayout.control_not_mem_ancillas rfl rfl (by intro wire hwire; rfl) hclean
  have hphysical := unaryActionUnitary_preserves order leafAction tree control ancillas
    protectedWires state hlayout hleaf hroles hclean
  have hlogicalProtected := tree.runLogicalTree_preserves order logicalLeafState
    (state control) state state protectedWires hlogicalPreserves
  rw [hrun]
  funext wire
  by_cases hwire : wire ∈ protectedWires
  · rw [show tree.runLeafState order leafState control ancillas state wire = state wire by
        rw [← hrun]
        exact hphysical wire hwire,
      hlogicalProtected wire hwire]
  · exact houtside wire hwire

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

private theorem unary_clean_preserved_by_circuit
    (support extra : List Wire) (circuit : Circuit)
    (huses : PaperCircuitUsesOnly support circuit)
    (hdisjoint : List.Disjoint support extra) :
    ∀ state, Clean extra state → Clean extra (run circuit state) := by
  rw [List.disjoint_left] at hdisjoint
  intro state hclean wire hwire
  rw [huses.preservesOutside state (fun hsupport ↦ hdisjoint hsupport hwire)]
  exact hclean wire hwire

private theorem unaryNode_compute_usesOnly
    (indexBit control path : Wire) (zero one : UnaryActionTree)
    (rest : List Wire) :
    PaperCircuitUsesOnly
      (control ::
        (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
          path :: rest)
      (computeZeroAnd control indexBit path) := by
  simp [computeZeroAnd, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires,
    UnaryActionTree.indexWires]

private theorem unaryNode_toggle_usesOnly
    (indexBit control path : Wire) (zero one : UnaryActionTree)
    (rest : List Wire) :
    PaperCircuitUsesOnly
      (control ::
        (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
          path :: rest)
      ([.CX control path] : Circuit) := by
  simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires,
    UnaryActionTree.indexWires]

theorem unaryLayout_decoderNodup
    {tree : UnaryActionTree} {control : Wire} {ancillas : List Wire}
    (hlayout : tree.Layout control ancillas) :
    (control :: tree.indexWires.dedup ++ ancillas).Nodup := by
  cases hlayout with
  | leaf label control ancillas hlocal =>
      simpa [UnaryActionTree.indexWires] using hlocal
  | node indexBit control path zero one rest hlocal hzero hone =>
      exact hlocal

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

/-- A source traversal whose leaf payloads also use measurement uncomputation coherently
implements the literal coherent traversal. `extraWires` is the clean leaf-work bank; the combined
layout prevents decoder operations from touching it. -/
theorem unaryAdaptiveAction_coherent_on
    (order : UnaryOrder)
    (leafAdaptive : Nat → Wire → AdaptiveCircuit)
    (leafUnitary : Nat → Wire → Circuit)
    (tree : UnaryActionTree) (control : Wire)
    (ancillas extraWires : List Wire)
    (hlayout : tree.Layout control ancillas)
    (hfullLayout :
      ((control :: tree.indexWires.dedup ++ ancillas) ++ extraWires).Nodup)
    (hleaf : UnaryLeafPreserves leafUnitary
      ((control :: tree.indexWires.dedup ++ ancillas) ++ extraWires))
    (hleafCoherent : UnaryAdaptiveLeafCoherentOn leafAdaptive leafUnitary
      tree.labels (control :: tree.indexWires.dedup ++ ancillas) extraWires)
    (hhp : UnaryLeafHPFree leafUnitary) :
    CoherentlyImplementsOn
      (unaryAdaptiveAction order leafAdaptive tree control ancillas)
      (Quantum.run
        (unaryActionUnitary order leafUnitary tree control ancillas))
      (fun state ↦ Clean ancillas state ∧ Clean extraWires state) := by
  induction hlayout with
  | leaf label control ancillas hlocal =>
      apply unaryAction_coherent_mono
        (hleafCoherent label (by simp [UnaryActionTree.labels]) control (by simp))
      exact fun _ hready ↦ hready.2
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip, hpathRest⟩ :=
        unaryActionNode_parts indexBit control path zero one rest hlocal
      let decoderWires :=
        control ::
          (UnaryActionTree.node indexBit zero one).indexWires.dedup ++
            path :: rest
      let protectedWires := decoderWires ++ extraWires
      have hfullParts := List.nodup_append.mp hfullLayout
      have hdecoderExtra : List.Disjoint decoderWires extraWires := by
        rw [List.disjoint_left]
        intro wire hdecoder hextra
        exact hfullParts.2.2 wire hdecoder wire hextra rfl
      have hzeroRoles : ∀ wire,
          wire ∈ path :: zero.indexWires.dedup ++ rest →
            wire ∈ decoderWires :=
        actionTree_zero_decoder_subset indexBit control path zero one rest
      have honeRoles : ∀ wire,
          wire ∈ path :: one.indexWires.dedup ++ rest →
            wire ∈ decoderWires :=
        actionTree_one_decoder_subset indexBit control path zero one rest
      have hzeroFull :
          ((path :: zero.indexWires.dedup ++ rest) ++ extraWires).Nodup := by
        refine List.nodup_append.mpr
          ⟨unaryLayout_decoderNodup hzero, hfullParts.2.1, ?_⟩
        intro first hfirst second hsecond
        exact hfullParts.2.2 first (hzeroRoles first hfirst) second hsecond
      have honeFull :
          ((path :: one.indexWires.dedup ++ rest) ++ extraWires).Nodup := by
        refine List.nodup_append.mpr
          ⟨unaryLayout_decoderNodup hone, hfullParts.2.1, ?_⟩
        intro first hfirst second hsecond
        exact hfullParts.2.2 first (honeRoles first hfirst) second hsecond
      have hzeroLeaf : UnaryLeafPreserves leafUnitary
          ((path :: zero.indexWires.dedup ++ rest) ++ extraWires) := by
        intro label childControl hchildControl state wire hwire
        apply hleaf label childControl (by
          rcases List.mem_append.mp hchildControl with hchildControl | hchildControl
          · exact List.mem_append.mpr
              (Or.inl (hzeroRoles childControl hchildControl))
          · exact List.mem_append.mpr (Or.inr hchildControl)) state wire
        rcases List.mem_append.mp hwire with hwire | hwire
        · exact List.mem_append.mpr (Or.inl (hzeroRoles wire hwire))
        · exact List.mem_append.mpr (Or.inr hwire)
      have honeLeaf : UnaryLeafPreserves leafUnitary
          ((path :: one.indexWires.dedup ++ rest) ++ extraWires) := by
        intro label childControl hchildControl state wire hwire
        apply hleaf label childControl (by
          rcases List.mem_append.mp hchildControl with hchildControl | hchildControl
          · exact List.mem_append.mpr
              (Or.inl (honeRoles childControl hchildControl))
          · exact List.mem_append.mpr (Or.inr hchildControl)) state wire
        rcases List.mem_append.mp hwire with hwire | hwire
        · exact List.mem_append.mpr (Or.inl (honeRoles wire hwire))
        · exact List.mem_append.mpr (Or.inr hwire)
      have hzeroCoherent : UnaryAdaptiveLeafCoherentOn leafAdaptive leafUnitary
          zero.labels (path :: zero.indexWires.dedup ++ rest) extraWires := by
        intro label hlabel childControl hchildControl
        exact hleafCoherent label (by
          simp [UnaryActionTree.labels, hlabel]) childControl
          (hzeroRoles childControl hchildControl)
      have honeCoherent : UnaryAdaptiveLeafCoherentOn leafAdaptive leafUnitary
          one.labels (path :: one.indexWires.dedup ++ rest) extraWires := by
        intro label hlabel childControl hchildControl
        exact hleafCoherent label (by
          simp [UnaryActionTree.labels, hlabel]) childControl
          (honeRoles childControl hchildControl)
      have hleafProtected : UnaryLeafPreserves leafUnitary protectedWires := by
        simpa [protectedWires, decoderWires] using hleaf
      have hcontrolDecoder : control ∈ decoderWires := by
        simp [decoderWires]
      have hindexDecoder : indexBit ∈ decoderWires := by
        simp [decoderWires, UnaryActionTree.indexWires]
      have hpathDecoder : path ∈ decoderWires := by
        simp [decoderWires]
      have hzeroPreservesAll : ∀ state,
          (ActionZeroPathReady control indexBit path rest state ∧
            Clean extraWires state) →
          ∀ wire, wire ∈ protectedWires →
            run (unaryActionUnitary order leafUnitary zero path rest) state wire =
              state wire := by
        intro state hready
        exact unaryActionUnitary_preservesProtected order leafUnitary zero
          path rest protectedWires state hzero hleafProtected
          (fun wire hwire ↦ List.mem_append.mpr
            (Or.inl (hzeroRoles wire hwire))) hready.1.1
      have honePreservesAll : ∀ state,
          (ActionOnePathReady control indexBit path rest state ∧
            Clean extraWires state) →
          ∀ wire, wire ∈ protectedWires →
            run (unaryActionUnitary order leafUnitary one path rest) state wire =
              state wire := by
        intro state hready
        exact unaryActionUnitary_preservesProtected order leafUnitary one
          path rest protectedWires state hone hleafProtected
          (fun wire hwire ↦ List.mem_append.mpr
            (Or.inl (honeRoles wire hwire))) hready.1.1
      have hzeroPreserves : ∀ state,
          (ActionZeroPathReady control indexBit path rest state ∧
            Clean extraWires state) →
          (ActionZeroPathReady control indexBit path rest
              (run (unaryActionUnitary order leafUnitary zero path rest) state) ∧
            Clean extraWires
              (run (unaryActionUnitary order leafUnitary zero path rest) state)) := by
        intro state hready
        have hpreserves := hzeroPreservesAll state hready
        constructor
        · refine ⟨?_, ?_⟩
          · intro wire hwire
            rw [hpreserves wire (List.mem_append.mpr
              (Or.inl (hzeroRoles wire (by simp [hwire]))))]
            exact hready.1.1 wire hwire
          · unfold ActionZeroPathReady at hready
            unfold ZeroAndComputed at hready ⊢
            rw [hpreserves control (List.mem_append.mpr (Or.inl hcontrolDecoder)),
              hpreserves indexBit (List.mem_append.mpr (Or.inl hindexDecoder)),
              hpreserves path (List.mem_append.mpr (Or.inl hpathDecoder))]
            exact hready.1.2
        · intro wire hwire
          rw [hpreserves wire (List.mem_append.mpr (Or.inr hwire))]
          exact hready.2 wire hwire
      have honePreserves : ∀ state,
          (ActionOnePathReady control indexBit path rest state ∧
            Clean extraWires state) →
          (ActionOnePathReady control indexBit path rest
              (run (unaryActionUnitary order leafUnitary one path rest) state) ∧
            Clean extraWires
              (run (unaryActionUnitary order leafUnitary one path rest) state)) := by
        intro state hready
        have hpreserves := honePreservesAll state hready
        constructor
        · refine ⟨?_, ?_⟩
          · intro wire hwire
            rw [hpreserves wire (List.mem_append.mpr
              (Or.inl (honeRoles wire (by simp [hwire]))))]
            exact hready.1.1 wire hwire
          · unfold ActionOnePathReady at hready
            rw [hpreserves path (List.mem_append.mpr (Or.inl hpathDecoder)),
              hpreserves control (List.mem_append.mpr (Or.inl hcontrolDecoder)),
              hpreserves indexBit (List.mem_append.mpr (Or.inl hindexDecoder))]
            exact hready.1.2
        · intro wire hwire
          rw [hpreserves wire (List.mem_append.mpr (Or.inr hwire))]
          exact hready.2 wire hwire
      have ihZeroReady : CoherentlyImplementsOn
          (unaryAdaptiveAction order leafAdaptive zero path rest)
          (Quantum.run (unaryActionUnitary order leafUnitary zero path rest))
          (fun state ↦ ActionZeroPathReady control indexBit path rest state ∧
            Clean extraWires state) :=
        unaryAction_coherent_mono
          (ihZero hzeroFull hzeroLeaf hzeroCoherent)
          (fun _ hready ↦ ⟨hready.1.1, hready.2⟩)
      have ihOneReady : CoherentlyImplementsOn
          (unaryAdaptiveAction order leafAdaptive one path rest)
          (Quantum.run (unaryActionUnitary order leafUnitary one path rest))
          (fun state ↦ ActionOnePathReady control indexBit path rest state ∧
            Clean extraWires state) :=
        unaryAction_coherent_mono
          (ihOne honeFull honeLeaf honeCoherent)
          (fun _ hready ↦ ⟨hready.1.1, hready.2⟩)
      have herase := eraseZeroAnd_coherent control indexBit path hci hcp hip
      have heraseExtra : CoherentlyImplementsOn
          (eraseZeroAnd control indexBit path)
          (Quantum.run (computeZeroAnd control indexBit path))
          (fun state ↦ ActionZeroPathReady control indexBit path rest state ∧
            Clean extraWires state) :=
        unaryAction_coherent_mono herase (fun _ hready ↦ hready.1.2)
      have htoggleOne := CoherentlyImplementsOn.unitary [.CX control path]
        (fun state ↦ ActionOnePathReady control indexBit path rest state ∧
          Clean extraWires state)
      have htoggleZero := CoherentlyImplementsOn.unitary [.CX control path]
        (fun state ↦ ActionZeroPathReady control indexBit path rest state ∧
          Clean extraWires state)
      have hcompute := CoherentlyImplementsOn.unitary
        (computeZeroAnd control indexBit path)
        (fun state ↦ Clean (path :: rest) state ∧ Clean extraWires state)
      have hcomputeExtra := unary_clean_preserved_by_circuit
        decoderWires extraWires (computeZeroAnd control indexBit path)
        (unaryNode_compute_usesOnly indexBit control path zero one rest)
        hdecoderExtra
      have htoggleExtra := unary_clean_preserved_by_circuit
        decoderWires extraWires ([.CX control path] : Circuit)
        (unaryNode_toggle_usesOnly indexBit control path zero one rest)
        hdecoderExtra
      have hcomputeReady : ∀ state,
          (Clean (path :: rest) state ∧ Clean extraWires state) →
          (ActionZeroPathReady control indexBit path rest
              (run (computeZeroAnd control indexBit path) state) ∧
            Clean extraWires
              (run (computeZeroAnd control indexBit path) state)) := by
        intro state hclean
        exact ⟨actionZeroPathReady_after_compute control indexBit path rest state
          hci hcp hip hpathRest hclean.1, hcomputeExtra state hclean.2⟩
      have htoOneReady : ∀ state,
          (ActionZeroPathReady control indexBit path rest state ∧
            Clean extraWires state) →
          (ActionOnePathReady control indexBit path rest
              (run [.CX control path] state) ∧
            Clean extraWires (run [.CX control path] state)) := by
        intro state hready
        constructor
        · simpa only [Classical.run_cons, Classical.run_nil] using
            actionOnePathReady_after_zero_toggle control indexBit path rest state
              hcp hip hpathRest hready.1
        · exact htoggleExtra state hready.2
      have htoZeroReady : ∀ state,
          (ActionOnePathReady control indexBit path rest state ∧
            Clean extraWires state) →
          (ActionZeroPathReady control indexBit path rest
              (run [.CX control path] state) ∧
            Clean extraWires (run [.CX control path] state)) := by
        intro state hready
        constructor
        · simpa only [Classical.run_cons, Classical.run_nil] using
            actionZeroPathReady_after_one_toggle control indexBit path rest state
              hcp hip hpathRest hready.1
        · exact htoggleExtra state hready.2
      cases order with
      | inc =>
          have hback := unaryAction_coherent_seq_circuits htoggleOne heraseExtra
            (by simp) htoZeroReady
          have honeChunk := unaryAction_coherent_seq_circuits ihOneReady hback
            (unaryActionUnitary_HPFree .inc leafUnitary one path rest hhp)
            honePreserves
          have htoggleChunk := unaryAction_coherent_seq_circuits
            htoggleZero honeChunk (by simp) htoOneReady
          have hzeroChunk := unaryAction_coherent_seq_circuits
            ihZeroReady htoggleChunk
            (unaryActionUnitary_HPFree .inc leafUnitary zero path rest hhp)
            hzeroPreserves
          have hall := unaryAction_coherent_seq_circuits hcompute hzeroChunk
            (computeZeroAnd_HPFree control indexBit path) hcomputeReady
          simpa only [unaryAdaptiveAction, unaryActionUnitary,
            AdaptiveCircuit.seq, List.append_assoc] using hall
      | dec =>
          have hzeroErase := unaryAction_coherent_seq_circuits
            ihZeroReady heraseExtra
            (unaryActionUnitary_HPFree .dec leafUnitary zero path rest hhp)
            hzeroPreserves
          have htoggleZeroChunk := unaryAction_coherent_seq_circuits
            htoggleOne hzeroErase (by simp) htoZeroReady
          have honeChunk := unaryAction_coherent_seq_circuits
            ihOneReady htoggleZeroChunk
            (unaryActionUnitary_HPFree .dec leafUnitary one path rest hhp)
            honePreserves
          have htoggleOneChunk := unaryAction_coherent_seq_circuits
            htoggleZero honeChunk (by simp) htoOneReady
          have hall := unaryAction_coherent_seq_circuits hcompute htoggleOneChunk
            (computeZeroAnd_HPFree control indexBit path) hcomputeReady
          simpa only [unaryAdaptiveAction, unaryActionUnitary,
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

/-- Physical well-formedness when the unary leaf payloads are themselves adaptive. -/
theorem unaryAdaptiveAction_wellFormed
    (order : UnaryOrder)
    (leafAction : Nat → Wire → AdaptiveCircuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas)
    (hleaf : UnaryAdaptiveLeafWellFormed leafAction tree
      (control :: tree.indexWires.dedup ++ ancillas)) :
    (unaryAdaptiveAction order leafAction tree control ancillas).WellFormed := by
  induction hlayout with
  | leaf label control ancillas hlocal =>
      exact hleaf label (by simp [UnaryActionTree.labels]) control (by simp)
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip, _⟩ :=
        unaryActionNode_parts indexBit control path zero one rest hlocal
      have hzeroLeaf : UnaryAdaptiveLeafWellFormed leafAction zero
          (path :: zero.indexWires.dedup ++ rest) := by
        intro label hlabel childControl hchildControl
        exact hleaf label (by
          simp [UnaryActionTree.labels, hlabel]) childControl
          (actionTree_zero_decoder_subset indexBit control path zero one rest
            childControl hchildControl)
      have honeLeaf : UnaryAdaptiveLeafWellFormed leafAction one
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
      have herase := eraseZeroAnd_wellFormed control indexBit path hci hcp hip
      cases order with
      | inc =>
          rw [unaryAdaptiveAction]
          exact ⟨hcompute,
            AdaptiveCircuit.WellFormed.seq (ihZero hzeroLeaf)
              ⟨htoggle,
                AdaptiveCircuit.WellFormed.seq (ihOne honeLeaf)
                  ⟨htoggle, herase⟩⟩⟩
      | dec =>
          rw [unaryAdaptiveAction]
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

/-- Adaptive measurements are the leaf-local measurements plus one decoder erasure at each
internal node. -/
theorem unaryAdaptiveAction_measurementCount
    (order : UnaryOrder)
    (leafAction : Nat → Wire → AdaptiveCircuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    (unaryAdaptiveAction order leafAction tree control ancillas).measurementCount =
      tree.leafCostSum
          (fun label dynamic ↦ (leafAction label dynamic).measurementCount)
          control ancillas +
        tree.internalNodes := by
  induction hlayout with
  | leaf label control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [unaryAdaptiveAction] <;>
        simp [AdaptiveCircuit.measurementCount,
          unaryAction_measurementCount_seq, ihZero, ihOne,
          UnaryActionTree.leafCostSum, UnaryActionTree.internalNodes] <;>
        omega

/-- Adaptive T cost is the sum of the actual leaf programs plus the one forward decoder AND at
each internal node. -/
theorem unaryAdaptiveAction_tCount
    (order : UnaryOrder)
    (leafAction : Nat → Wire → AdaptiveCircuit)
    (tree : UnaryActionTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    (unaryAdaptiveAction order leafAction tree control ancillas).tCount =
      tree.leafCostSum
          (fun label dynamic ↦ (leafAction label dynamic).tCount)
          control ancillas +
        7 * tree.internalNodes := by
  induction hlayout with
  | leaf label control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [unaryAdaptiveAction] <;>
        simp [AdaptiveCircuit.tCount, unaryAction_tCount_seq,
          ihZero, ihOne, UnaryActionTree.leafCostSum,
          UnaryActionTree.internalNodes, tCost] <;>
        omega

end

end ShorECDLP.Paper2607_13816
