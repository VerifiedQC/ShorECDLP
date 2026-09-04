import ShorECDLP.Submission.«2607_13816».EEA.UnaryAction

/-!
# Synchronized dual-endpoint unary traversal

The remainder interval block in the pinned supplement uses `dual_unary_iteration_tight`: two
endpoint decoders follow the same pruned label tree, expose both equality controls at each leaf,
and erase both path ANDs in reverse compute order.  This module formalizes that exact generic
control-flow layer.  Arithmetic remains a leaf action, so later interval blocks can instantiate
the traversal without duplicating its measurement and resource proof.

As in `UnaryAction.lean`, branch order is local to a caller-supplied tree.  The supplement's
concrete sorted/deduplicated-label, highest-varying-bit tree builder and the certificate connecting
that builder to numeric label order remain outside this generic synchronized traversal.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-- One pruned label tree with the corresponding index wire from each endpoint register. -/
inductive DualUnaryActionTree where
  | leaf (label : Nat)
  | node (indexBitA indexBitB : Wire)
      (zero one : DualUnaryActionTree)
deriving DecidableEq, Repr

namespace DualUnaryActionTree

def indexAWires : DualUnaryActionTree → List Wire
  | .leaf _ => []
  | .node indexBitA _ zero one =>
      indexBitA :: (zero.indexAWires ++ one.indexAWires)

def indexBWires : DualUnaryActionTree → List Wire
  | .leaf _ => []
  | .node _ indexBitB zero one =>
      indexBitB :: (zero.indexBWires ++ one.indexBWires)

def internalNodes : DualUnaryActionTree → Nat
  | .leaf _ => 0
  | .node _ _ zero one =>
      1 + zero.internalNodes + one.internalNodes

def leaves : DualUnaryActionTree → Nat
  | .leaf _ => 1
  | .node _ _ zero one => zero.leaves + one.leaves

def labels : DualUnaryActionTree → List Nat
  | .leaf label => [label]
  | .node _ _ zero one => zero.labels ++ one.labels

/-- Gate-independent whole-state execution of a synchronized dual traversal.  It exposes the
ordered leaf-state actions and the temporary path values explicitly, then clears both path wires
in the source's reverse `B`-then-`A` order. -/
def runLeafState
    (order : UnaryOrder)
    (leafState : Nat → Wire → Wire → BasisState → BasisState) :
    DualUnaryActionTree → Wire → Wire → List Wire → List Wire →
      BasisState → BasisState
  | .leaf label, controlA, controlB, _, _, state =>
      leafState label controlA controlB state
  | .node indexBitA indexBitB zero one,
      controlA, controlB, pathA :: restA, pathB :: restB, state =>
      let afterA := state[pathA ↦ state controlA && !state indexBitA]
      let first := afterA[pathB ↦ afterA controlB && !afterA indexBitB]
      match order with
      | .inc =>
          let afterZero := zero.runLeafState order leafState
            pathA pathB restA restB first
          let switchedA := Classical.applyGate (.CX controlA pathA) afterZero
          let switched := Classical.applyGate (.CX controlB pathB) switchedA
          let afterOne := one.runLeafState order leafState
            pathA pathB restA restB switched
          let switchedB := Classical.applyGate (.CX controlB pathB) afterOne
          let switchedBack := Classical.applyGate (.CX controlA pathA) switchedB
          switchedBack[pathB ↦ false][pathA ↦ false]
      | .dec =>
          let switchedA := Classical.applyGate (.CX controlA pathA) first
          let switched := Classical.applyGate (.CX controlB pathB) switchedA
          let afterOne := one.runLeafState order leafState
            pathA pathB restA restB switched
          let switchedB := Classical.applyGate (.CX controlB pathB) afterOne
          let switchedBack := Classical.applyGate (.CX controlA pathA) switchedB
          let afterZero := zero.runLeafState order leafState
            pathA pathB restA restB switchedBack
          afterZero[pathB ↦ false][pathA ↦ false]
  | .node _ _ _ _, _, _, _, _, state => state

/-- Sum a leaf-local resource over the paired dynamic controls exposed by the tree. -/
def leafCostSum
    (leafCost : Nat → Wire → Wire → Nat) :
    DualUnaryActionTree → Wire → Wire → List Wire → List Wire → Nat
  | .leaf label, controlA, controlB, _, _ => leafCost label controlA controlB
  | .node _ _ zero one, _, _, pathA :: restA, pathB :: restB =>
      zero.leafCostSum leafCost pathA pathB restA restB +
        one.leafCostSum leafCost pathA pathB restA restB
  | .node _ _ _ _, _, _, _, _ => 0

def decoderWires
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire) : List Wire :=
  [controlA, controlB].dedup ++
    (tree.indexAWires.dedup ++
      (tree.indexBWires.dedup ++ (ancillasA ++ ancillasB)))

/-- Both endpoint registers and both reusable path stacks form one disjoint decoder layout.
The two external controls may be the same wire, as they are in the source interval block. -/
inductive Layout :
    DualUnaryActionTree → Wire → Wire → List Wire → List Wire → Prop where
  | leaf
      (label : Nat) (controlA controlB : Wire)
      (ancillasA ancillasB : List Wire)
      (hlocal : (decoderWires (.leaf label) controlA controlB ancillasA ancillasB).Nodup) :
      Layout (.leaf label) controlA controlB ancillasA ancillasB
  | node
      (indexBitA indexBitB controlA controlB pathA pathB : Wire)
      (zero one : DualUnaryActionTree)
      (restA restB : List Wire)
      (hlocal :
        (decoderWires (.node indexBitA indexBitB zero one)
          controlA controlB (pathA :: restA) (pathB :: restB)).Nodup)
      (hzero : Layout zero pathA pathB restA restB)
      (hone : Layout one pathA pathB restA restB) :
      Layout (.node indexBitA indexBitB zero one)
        controlA controlB (pathA :: restA) (pathB :: restB)

end DualUnaryActionTree

/-- Coherent reference, including the supplement's reverse `B`-then-`A` AND cleanup order. -/
def dualUnaryActionUnitary
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit) :
    DualUnaryActionTree → Wire → Wire → List Wire → List Wire → Circuit
  | .leaf label, controlA, controlB, _, _ =>
      leafAction label controlA controlB
  | .node indexBitA indexBitB zero one,
      controlA, controlB, pathA :: restA, pathB :: restB =>
      match order with
      | .inc =>
          computeZeroAnd controlA indexBitA pathA ++
            computeZeroAnd controlB indexBitB pathB ++
            dualUnaryActionUnitary order leafAction zero pathA pathB restA restB ++
            [.CX controlA pathA, .CX controlB pathB] ++
            dualUnaryActionUnitary order leafAction one pathA pathB restA restB ++
            [.CX controlB pathB, .CX controlA pathA] ++
            computeZeroAnd controlB indexBitB pathB ++
            computeZeroAnd controlA indexBitA pathA
      | .dec =>
          computeZeroAnd controlA indexBitA pathA ++
            computeZeroAnd controlB indexBitB pathB ++
            [.CX controlA pathA, .CX controlB pathB] ++
            dualUnaryActionUnitary order leafAction one pathA pathB restA restB ++
            [.CX controlB pathB, .CX controlA pathA] ++
            dualUnaryActionUnitary order leafAction zero pathA pathB restA restB ++
            computeZeroAnd controlB indexBitB pathB ++
            computeZeroAnd controlA indexBitA pathA
  | .node _ _ _ _, _, _, _, _ => []

/-- Measurement-assisted cleanup of a pair of path ANDs in the source's reverse compute order. -/
def eraseDualZeroAnd
    (controlA indexBitA pathA controlB indexBitB pathB : Wire) : AdaptiveCircuit :=
  (eraseZeroAnd controlB indexBitB pathB).seq
    (eraseZeroAnd controlA indexBitA pathA)

/-- Adaptive synchronized traversal from `dual_unary_iteration_tight`. -/
def dualUnaryAction
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit) :
    DualUnaryActionTree → Wire → Wire →
      List Wire → List Wire → AdaptiveCircuit
  | .leaf label, controlA, controlB, _, _ =>
      .unitary (leafAction label controlA controlB) .done
  | .node indexBitA indexBitB zero one,
      controlA, controlB, pathA :: restA, pathB :: restB =>
      match order with
      | .inc =>
          .unitary (computeZeroAnd controlA indexBitA pathA)
            (.unitary (computeZeroAnd controlB indexBitB pathB)
              ((dualUnaryAction order leafAction zero pathA pathB restA restB).seq
                (.unitary [.CX controlA pathA, .CX controlB pathB]
                  ((dualUnaryAction order leafAction one pathA pathB restA restB).seq
                    (.unitary [.CX controlB pathB, .CX controlA pathA]
                      (eraseDualZeroAnd controlA indexBitA pathA
                        controlB indexBitB pathB))))))
      | .dec =>
          .unitary (computeZeroAnd controlA indexBitA pathA)
            (.unitary (computeZeroAnd controlB indexBitB pathB)
              (.unitary [.CX controlA pathA, .CX controlB pathB]
                ((dualUnaryAction order leafAction one pathA pathB restA restB).seq
                  (.unitary [.CX controlB pathB, .CX controlA pathA]
                    ((dualUnaryAction order leafAction zero pathA pathB restA restB).seq
                      (eraseDualZeroAnd controlA indexBitA pathA
                        controlB indexBitB pathB))))))
  | .node _ _ _ _, _, _, _, _ => .done

/-- A dual leaf action preserves a caller-selected interface whenever its two dynamic controls
come from the declared decoder interface. -/
def DualUnaryLeafPreservesOn
    (leafAction : Nat → Wire → Wire → Circuit)
    (labels : List Nat) (dynamicWires protectedWires : List Wire) : Prop :=
  ∀ label, label ∈ labels → ∀ controlA controlB,
    controlA ∈ dynamicWires → controlB ∈ dynamicWires →
      ∀ state wire, wire ∈ protectedWires →
        run (leafAction label controlA controlB) state wire = state wire

/-- Common specialization where the decoder itself is the preserved interface. -/
def DualUnaryLeafPreserves
    (leafAction : Nat → Wire → Wire → Circuit)
    (protectedWires : List Wire) : Prop :=
  ∀ label controlA controlB,
    controlA ∈ protectedWires → controlB ∈ protectedWires →
      ∀ state wire, wire ∈ protectedWires →
        run (leafAction label controlA controlB) state wire = state wire

/-- The supplied state action is the direct basis semantics of every paired leaf circuit. -/
def DualUnaryLeafRunsAs
    (leafAction : Nat → Wire → Wire → Circuit)
    (leafState : Nat → Wire → Wire → BasisState → BasisState)
    (protectedWires : List Wire) : Prop :=
  ∀ label controlA controlB,
    controlA ∈ protectedWires → controlB ∈ protectedWires →
      ∀ state, Classical.run (leafAction label controlA controlB) state =
        leafState label controlA controlB state

/-- Every instantiated leaf circuit stays inside one caller-declared physical support. -/
def DualUnaryLeafUsesOnly
    (leafAction : Nat → Wire → Wire → Circuit)
    (labels : List Nat) (support : List Wire) : Prop :=
  ∀ label, label ∈ labels → ∀ controlA controlB,
    controlA ∈ support → controlB ∈ support →
      PaperCircuitUsesOnly support (leafAction label controlA controlB)

def DualUnaryLeafHPFree
    (leafAction : Nat → Wire → Wire → Circuit) : Prop :=
  ∀ label controlA controlB, HPFree (leafAction label controlA controlB)

def DualUnaryLeafWellFormed
    (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (protectedWires : List Wire) : Prop :=
  ∀ label ∈ tree.labels, ∀ controlA ∈ protectedWires,
    ∀ controlB ∈ protectedWires,
      CircuitWellFormed (leafAction label controlA controlB)

private theorem dualUnaryNode_parts
    (indexBitA indexBitB controlA controlB pathA pathB : Wire)
    (zero one : DualUnaryActionTree) (restA restB : List Wire)
    (hlocal :
      (DualUnaryActionTree.decoderWires
        (.node indexBitA indexBitB zero one)
        controlA controlB (pathA :: restA) (pathB :: restB)).Nodup) :
    controlA ≠ indexBitA ∧ controlA ≠ pathA ∧ indexBitA ≠ pathA ∧
    controlB ≠ indexBitB ∧ controlB ≠ pathB ∧ indexBitB ≠ pathB ∧
    pathA ≠ pathB ∧ pathA ∉ restA ∧ pathA ∉ restB ∧
    pathB ∉ restA ∧ pathB ∉ restB ∧
    controlA ≠ pathB ∧ indexBitA ≠ pathB ∧
    controlB ≠ pathA ∧ indexBitB ≠ pathA := by
  rw [DualUnaryActionTree.decoderWires] at hlocal
  obtain ⟨hcontrols, hafterControls, hcontrolsCross⟩ :=
    List.nodup_append.mp hlocal
  obtain ⟨hindicesA, hafterA, hindicesACross⟩ :=
    List.nodup_append.mp hafterControls
  obtain ⟨hindicesB, hancillas, hindicesBCross⟩ :=
    List.nodup_append.mp hafterA
  obtain ⟨hancillasA, hancillasB, hancillasCross⟩ :=
    List.nodup_append.mp hancillas
  have hcontrolAMem : controlA ∈ [controlA, controlB].dedup := by simp
  have hcontrolBMem : controlB ∈ [controlA, controlB].dedup := by simp
  have hindexAMem : indexBitA ∈
      (DualUnaryActionTree.node indexBitA indexBitB zero one).indexAWires.dedup := by
    simp [DualUnaryActionTree.indexAWires]
  have hindexBMem : indexBitB ∈
      (DualUnaryActionTree.node indexBitA indexBitB zero one).indexBWires.dedup := by
    simp [DualUnaryActionTree.indexBWires]
  have hcontrolAIndexA : controlA ≠ indexBitA :=
    hcontrolsCross controlA hcontrolAMem indexBitA (by simp [hindexAMem])
  have hcontrolAPathA : controlA ≠ pathA :=
    hcontrolsCross controlA hcontrolAMem pathA (by simp)
  have hindexAPathA : indexBitA ≠ pathA :=
    hindicesACross indexBitA hindexAMem pathA (by simp)
  have hcontrolBIndexB : controlB ≠ indexBitB :=
    hcontrolsCross controlB hcontrolBMem indexBitB (by simp [hindexBMem])
  have hcontrolBPathB : controlB ≠ pathB :=
    hcontrolsCross controlB hcontrolBMem pathB (by simp)
  have hindexBPathB : indexBitB ≠ pathB :=
    hindicesBCross indexBitB hindexBMem pathB (by simp)
  have hpathAPathB : pathA ≠ pathB :=
    hancillasCross pathA (by simp) pathB (by simp)
  have hpathARestA : pathA ∉ restA :=
    (List.nodup_cons.mp hancillasA).1
  have hpathBRestB : pathB ∉ restB :=
    (List.nodup_cons.mp hancillasB).1
  have hpathARestB : pathA ∉ restB := by
    intro hmem
    exact (hancillasCross pathA (by simp) pathA (by simp [hmem])) rfl
  have hpathBRestA : pathB ∉ restA := by
    intro hmem
    exact (hancillasCross pathB (by simp [hmem]) pathB (by simp)) rfl
  have hcontrolAPathB : controlA ≠ pathB :=
    hcontrolsCross controlA hcontrolAMem pathB (by simp)
  have hindexAPathB : indexBitA ≠ pathB :=
    hindicesACross indexBitA hindexAMem pathB (by simp)
  have hcontrolBPathA : controlB ≠ pathA :=
    hcontrolsCross controlB hcontrolBMem pathA (by simp)
  have hindexBPathA : indexBitB ≠ pathA :=
    hindicesBCross indexBitB hindexBMem pathA (by simp)
  exact ⟨hcontrolAIndexA, hcontrolAPathA, hindexAPathA,
    hcontrolBIndexB, hcontrolBPathB, hindexBPathB,
    hpathAPathB, hpathARestA, hpathARestB,
    hpathBRestA, hpathBRestB,
    hcontrolAPathB, hindexAPathB, hcontrolBPathA, hindexBPathA⟩

private theorem dualZero_decoder_subset
    (indexBitA indexBitB controlA controlB pathA pathB : Wire)
    (zero one : DualUnaryActionTree) (restA restB : List Wire) :
    ∀ wire,
      wire ∈ DualUnaryActionTree.decoderWires zero pathA pathB restA restB →
        wire ∈ DualUnaryActionTree.decoderWires
          (.node indexBitA indexBitB zero one)
          controlA controlB (pathA :: restA) (pathB :: restB) := by
  intro wire hwire
  simp only [DualUnaryActionTree.decoderWires, List.mem_append,
    List.mem_dedup, DualUnaryActionTree.indexAWires,
    DualUnaryActionTree.indexBWires, List.mem_cons] at hwire ⊢
  aesop

private theorem dualOne_decoder_subset
    (indexBitA indexBitB controlA controlB pathA pathB : Wire)
    (zero one : DualUnaryActionTree) (restA restB : List Wire) :
    ∀ wire,
      wire ∈ DualUnaryActionTree.decoderWires one pathA pathB restA restB →
        wire ∈ DualUnaryActionTree.decoderWires
          (.node indexBitA indexBitB zero one)
          controlA controlB (pathA :: restA) (pathB :: restB) := by
  intro wire hwire
  simp only [DualUnaryActionTree.decoderWires, List.mem_append,
    List.mem_dedup, DualUnaryActionTree.indexAWires,
    DualUnaryActionTree.indexBWires, List.mem_cons] at hwire ⊢
  aesop

/-- The coherent dual traversal is classical whenever every paired leaf action is. -/
theorem dualUnaryActionUnitary_HPFree
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hleaf : DualUnaryLeafHPFree leafAction) :
    HPFree
      (dualUnaryActionUnitary order leafAction tree
        controlA controlB ancillasA ancillasB) := by
  induction tree generalizing controlA controlB ancillasA ancillasB with
  | leaf label =>
      simpa [dualUnaryActionUnitary] using hleaf label controlA controlB
  | node indexBitA indexBitB zero one ihZero ihOne =>
      cases ancillasA with
      | nil => simp [dualUnaryActionUnitary]
      | cons pathA restA =>
          cases ancillasB with
          | nil => simp [dualUnaryActionUnitary]
          | cons pathB restB =>
              cases order <;>
                simp [dualUnaryActionUnitary, ihZero, ihOne]

/-- Physical well-formedness of the coherent paired traversal. -/
theorem dualUnaryActionUnitary_wellFormed
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hleaf : DualUnaryLeafWellFormed leafAction tree
      (tree.decoderWires controlA controlB ancillasA ancillasB)) :
    CircuitWellFormed
      (dualUnaryActionUnitary order leafAction tree
        controlA controlB ancillasA ancillasB) := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal =>
      exact hleaf label (by simp [DualUnaryActionTree.labels])
        controlA (by simp [DualUnaryActionTree.decoderWires])
        controlB (by simp [DualUnaryActionTree.decoderWires])
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      obtain ⟨hca, hcpa, hia, hcb, hcpb, hib, _, _, _, _, _, _, _, _, _⟩ :=
        dualUnaryNode_parts indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB hlocal
      have hzeroLeaf : DualUnaryLeafWellFormed leafAction zero
          (zero.decoderWires pathA pathB restA restB) := by
        intro label hlabel childA hchildA childB hchildB
        exact hleaf label (by simp [DualUnaryActionTree.labels, hlabel])
          childA (dualZero_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB childA hchildA)
          childB (dualZero_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB childB hchildB)
      have honeLeaf : DualUnaryLeafWellFormed leafAction one
          (one.decoderWires pathA pathB restA restB) := by
        intro label hlabel childA hchildA childB hchildB
        exact hleaf label (by simp [DualUnaryActionTree.labels, hlabel])
          childA (dualOne_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB childA hchildA)
          childB (dualOne_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB childB hchildB)
      have hcomputeA :=
        computeZeroAnd_wellFormed controlA indexBitA pathA hca hcpa hia
      have hcomputeB :=
        computeZeroAnd_wellFormed controlB indexBitB pathB hcb hcpb hib
      have htoggleForward :
          CircuitWellFormed [.CX controlA pathA, .CX controlB pathB] := by
        simp [CircuitWellFormed, Gate.WellFormed, hcpa, hcpb]
      have htoggleReverse :
          CircuitWellFormed [.CX controlB pathB, .CX controlA pathA] := by
        simp [CircuitWellFormed, Gate.WellFormed, hcpa, hcpb]
      cases order with
      | inc =>
          rw [dualUnaryActionUnitary]
          simp only [circuitWellFormed_append]
          exact ⟨⟨⟨⟨⟨⟨⟨hcomputeA, hcomputeB⟩,
            ihZero hzeroLeaf⟩, htoggleForward⟩, ihOne honeLeaf⟩,
            htoggleReverse⟩, hcomputeB⟩, hcomputeA⟩
      | dec =>
          rw [dualUnaryActionUnitary]
          simp only [circuitWellFormed_append]
          exact ⟨⟨⟨⟨⟨⟨⟨hcomputeA, hcomputeB⟩,
            htoggleForward⟩, ihOne honeLeaf⟩, htoggleReverse⟩,
            ihZero hzeroLeaf⟩, hcomputeB⟩, hcomputeA⟩

/-- Four coherent path-AND Toffolis are used at each synchronized internal node. -/
theorem dualUnaryActionUnitary_toffoliCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB) :
    eeaToffoliCount
        (dualUnaryActionUnitary order leafAction tree
          controlA controlB ancillasA ancillasB) =
      tree.leafCostSum
          (fun label wireA wireB ↦
            eeaToffoliCount (leafAction label wireA wireB))
          controlA controlB ancillasA ancillasB +
        4 * tree.internalNodes := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal => rfl
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [dualUnaryActionUnitary] <;>
        simp only [eeaToffoliCount_append] <;>
        rw [ihZero, ihOne] <;>
        simp only [computeZeroAnd_toffoliCount] <;>
        simp [eeaToffoliCount, DualUnaryActionTree.leafCostSum,
          DualUnaryActionTree.internalNodes] <;>
        omega

/-- The paired path switches contribute four CNOTs at each synchronized internal node. -/
theorem dualUnaryActionUnitary_cnotCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB) :
    eeaCnotCount
        (dualUnaryActionUnitary order leafAction tree
          controlA controlB ancillasA ancillasB) =
      tree.leafCostSum
          (fun label wireA wireB ↦
            eeaCnotCount (leafAction label wireA wireB))
          controlA controlB ancillasA ancillasB +
        4 * tree.internalNodes := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal => rfl
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [dualUnaryActionUnitary] <;>
        simp only [eeaCnotCount_append] <;>
        rw [ihZero, ihOne] <;>
        simp only [computeZeroAnd_cnotCount] <;>
        simp [eeaCnotCount, DualUnaryActionTree.leafCostSum,
          DualUnaryActionTree.internalNodes] <;>
        omega

/-- Framework T cost of the coherent paired traversal. -/
theorem dualUnaryActionUnitary_tCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB) :
    ShorECDLP.tCount
        (dualUnaryActionUnitary order leafAction tree
          controlA controlB ancillasA ancillasB) =
      tree.leafCostSum
          (fun label wireA wireB ↦
            ShorECDLP.tCount (leafAction label wireA wireB))
          controlA controlB ancillasA ancillasB +
        28 * tree.internalNodes := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal => rfl
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [dualUnaryActionUnitary] <;>
        simp only [tCount_append] <;>
        rw [ihZero, ihOne] <;>
        simp [computeZeroAnd, ShorECDLP.tCount, tCost,
          DualUnaryActionTree.leafCostSum,
          DualUnaryActionTree.internalNodes] <;>
        omega

theorem eraseDualZeroAnd_wellFormed
    (controlA indexBitA pathA controlB indexBitB pathB : Wire)
    (hca : controlA ≠ indexBitA) (hcpa : controlA ≠ pathA)
    (hia : indexBitA ≠ pathA)
    (hcb : controlB ≠ indexBitB) (hcpb : controlB ≠ pathB)
    (hib : indexBitB ≠ pathB) :
    (eraseDualZeroAnd controlA indexBitA pathA
      controlB indexBitB pathB).WellFormed := by
  exact AdaptiveCircuit.WellFormed.seq
    (eraseZeroAnd_wellFormed controlB indexBitB pathB hcb hcpb hib)
    (eraseZeroAnd_wellFormed controlA indexBitA pathA hca hcpa hia)

/-- Every adaptive branch is physically well formed. -/
theorem dualUnaryAction_wellFormed
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hleaf : DualUnaryLeafWellFormed leafAction tree
      (tree.decoderWires controlA controlB ancillasA ancillasB)) :
    (dualUnaryAction order leafAction tree
      controlA controlB ancillasA ancillasB).WellFormed := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal =>
      exact ⟨hleaf label (by simp [DualUnaryActionTree.labels])
        controlA (by simp [DualUnaryActionTree.decoderWires])
        controlB (by simp [DualUnaryActionTree.decoderWires]), trivial⟩
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      obtain ⟨hca, hcpa, hia, hcb, hcpb, hib, _, _, _, _, _, _, _, _, _⟩ :=
        dualUnaryNode_parts indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB hlocal
      have hzeroLeaf : DualUnaryLeafWellFormed leafAction zero
          (zero.decoderWires pathA pathB restA restB) := by
        intro label hlabel childA hchildA childB hchildB
        exact hleaf label (by simp [DualUnaryActionTree.labels, hlabel])
          childA (dualZero_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB childA hchildA)
          childB (dualZero_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB childB hchildB)
      have honeLeaf : DualUnaryLeafWellFormed leafAction one
          (one.decoderWires pathA pathB restA restB) := by
        intro label hlabel childA hchildA childB hchildB
        exact hleaf label (by simp [DualUnaryActionTree.labels, hlabel])
          childA (dualOne_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB childA hchildA)
          childB (dualOne_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB childB hchildB)
      have hcomputeA :=
        computeZeroAnd_wellFormed controlA indexBitA pathA hca hcpa hia
      have hcomputeB :=
        computeZeroAnd_wellFormed controlB indexBitB pathB hcb hcpb hib
      have htoggleForward :
          CircuitWellFormed [.CX controlA pathA, .CX controlB pathB] := by
        simp [CircuitWellFormed, Gate.WellFormed, hcpa, hcpb]
      have htoggleReverse :
          CircuitWellFormed [.CX controlB pathB, .CX controlA pathA] := by
        simp [CircuitWellFormed, Gate.WellFormed, hcpa, hcpb]
      have herase := eraseDualZeroAnd_wellFormed
        controlA indexBitA pathA controlB indexBitB pathB
        hca hcpa hia hcb hcpb hib
      cases order with
      | inc =>
          rw [dualUnaryAction]
          exact ⟨hcomputeA, ⟨hcomputeB,
            AdaptiveCircuit.WellFormed.seq (ihZero hzeroLeaf)
              ⟨htoggleForward,
                AdaptiveCircuit.WellFormed.seq (ihOne honeLeaf)
                  ⟨htoggleReverse, herase⟩⟩⟩⟩
      | dec =>
          rw [dualUnaryAction]
          exact ⟨hcomputeA, ⟨hcomputeB, ⟨htoggleForward,
            AdaptiveCircuit.WellFormed.seq (ihOne honeLeaf)
              ⟨htoggleReverse,
                AdaptiveCircuit.WellFormed.seq (ihZero hzeroLeaf) herase⟩⟩⟩⟩

private theorem dualUnaryAction_measurementCount_seq
    (first second : AdaptiveCircuit) :
    (first.seq second).measurementCount =
      first.measurementCount + second.measurementCount := by
  induction first with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount, ih]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount,
        ihFalse, ihTrue, Nat.add_max_add_right, Nat.add_assoc]

private theorem dualUnaryAction_tCount_seq
    (first second : AdaptiveCircuit) :
    (first.seq second).tCount = first.tCount + second.tCount := by
  induction first with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount, ih, Nat.add_assoc]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount,
        ihFalse, ihTrue, Nat.add_max_add_right]

@[simp]
theorem eraseDualZeroAnd_measurementCount
    (controlA indexBitA pathA controlB indexBitB pathB : Wire) :
    (eraseDualZeroAnd controlA indexBitA pathA
      controlB indexBitB pathB).measurementCount = 2 := by
  simp [eraseDualZeroAnd, dualUnaryAction_measurementCount_seq,
    eraseZeroAnd, AdaptiveCircuit.measurementCount]

@[simp]
theorem eraseDualZeroAnd_tCount
    (controlA indexBitA pathA controlB indexBitB pathB : Wire) :
    (eraseDualZeroAnd controlA indexBitA pathA
      controlB indexBitB pathB).tCount = 0 := by
  simp [eraseDualZeroAnd, dualUnaryAction_tCount_seq,
    eraseZeroAnd, AdaptiveCircuit.tCount,
    ShorECDLP.tCount, tCost]

/-- Exactly two path ANDs are measured per synchronized internal node. -/
theorem dualUnaryAction_measurementCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB) :
    (dualUnaryAction order leafAction tree
      controlA controlB ancillasA ancillasB).measurementCount =
        2 * tree.internalNodes := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal => rfl
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [dualUnaryAction] <;>
        simp [AdaptiveCircuit.measurementCount,
          dualUnaryAction_measurementCount_seq, ihZero, ihOne,
          DualUnaryActionTree.internalNodes] <;>
        omega

/-- Measurement removes the two reverse Toffolis; forward path computation costs fourteen T. -/
theorem dualUnaryAction_tCount
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB) :
    (dualUnaryAction order leafAction tree
      controlA controlB ancillasA ancillasB).tCount =
      tree.leafCostSum
          (fun label wireA wireB ↦
            ShorECDLP.tCount (leafAction label wireA wireB))
          controlA controlB ancillasA ancillasB +
        14 * tree.internalNodes := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal => rfl
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      cases order <;>
        rw [dualUnaryAction] <;>
        simp [AdaptiveCircuit.tCount, dualUnaryAction_tCount_seq,
          ihZero, ihOne, DualUnaryActionTree.leafCostSum,
          DualUnaryActionTree.internalNodes, tCost] <;>
        omega

private def DualZeroPathReady
    (controlA indexBitA pathA controlB indexBitB pathB : Wire)
    (restA restB : List Wire) (state : BasisState) : Prop :=
  Clean restA state ∧ Clean restB state ∧
    ZeroAndComputed controlA indexBitA pathA state ∧
    ZeroAndComputed controlB indexBitB pathB state

private def DualOnePathReady
    (controlA indexBitA pathA controlB indexBitB pathB : Wire)
    (restA restB : List Wire) (state : BasisState) : Prop :=
  Clean restA state ∧ Clean restB state ∧
    state pathA = (state controlA && state indexBitA) ∧
    state pathB = (state controlB && state indexBitB)

private theorem dualZeroPathReady_after_compute
    (controlA indexBitA pathA controlB indexBitB pathB : Wire)
    (restA restB : List Wire) (state : BasisState)
    (hca : controlA ≠ indexBitA) (hcpa : controlA ≠ pathA)
    (hia : indexBitA ≠ pathA)
    (hcb : controlB ≠ indexBitB) (hcpb : controlB ≠ pathB)
    (hib : indexBitB ≠ pathB)
    (hpathAPathB : pathA ≠ pathB)
    (hpathARestA : pathA ∉ restA) (hpathARestB : pathA ∉ restB)
    (hpathBRestA : pathB ∉ restA) (hpathBRestB : pathB ∉ restB)
    (hcontrolAPathB : controlA ≠ pathB)
    (hindexAPathB : indexBitA ≠ pathB)
    (hcleanA : Clean (pathA :: restA) state)
    (hcleanB : Clean (pathB :: restB) state) :
    DualZeroPathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB
      (run (computeZeroAnd controlB indexBitB pathB)
        (run (computeZeroAnd controlA indexBitA pathA) state)) := by
  have hpathAFalse : state pathA = false := hcleanA pathA (by simp)
  have hpathBFalse : state pathB = false := hcleanB pathB (by simp)
  let afterA := run (computeZeroAnd controlA indexBitA pathA) state
  have hafterA : afterA =
      state[pathA ↦ state controlA && !state indexBitA] := by
    simpa only [afterA] using run_computeZeroAnd
      controlA indexBitA pathA state hca hcpa hia hpathAFalse
  have hpathBAfterA : afterA pathB = false := by
    rw [hafterA, upd_other state pathA _ (Ne.symm hpathAPathB)]
    exact hpathBFalse
  let afterB := run (computeZeroAnd controlB indexBitB pathB) afterA
  have hafterB : afterB =
      afterA[pathB ↦ afterA controlB && !afterA indexBitB] := by
    simpa only [afterB] using run_computeZeroAnd
      controlB indexBitB pathB afterA hcb hcpb hib hpathBAfterA
  change DualZeroPathReady controlA indexBitA pathA
    controlB indexBitB pathB restA restB afterB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro wire hwire
    rw [hafterB, upd_other afterA pathB _ (by
      intro equality
      subst wire
      exact hpathBRestA hwire)]
    rw [hafterA, upd_other state pathA _ (by
      intro equality
      subst wire
      exact hpathARestA hwire)]
    exact hcleanA wire (by simp [hwire])
  · intro wire hwire
    rw [hafterB, upd_other afterA pathB _ (by
      intro equality
      subst wire
      exact hpathBRestB hwire)]
    rw [hafterA, upd_other state pathA _ (by
      intro equality
      subst wire
      exact hpathARestB hwire)]
    exact hcleanB wire (by simp [hwire])
  · unfold ZeroAndComputed
    rw [hafterB]
    simp only [upd_other afterA pathB _ hcontrolAPathB,
      upd_other afterA pathB _ hindexAPathB,
      upd_other afterA pathB _ hpathAPathB]
    rw [hafterA]
    simp [upd, hcpa, hia]
  · unfold ZeroAndComputed
    rw [hafterB]
    simp [upd, hcpb, hib]

private theorem dualOnePathReady_after_forwardToggle
    (controlA indexBitA pathA controlB indexBitB pathB : Wire)
    (restA restB : List Wire) (state : BasisState)
    (hcpa : controlA ≠ pathA) (hia : indexBitA ≠ pathA)
    (hcpb : controlB ≠ pathB) (hib : indexBitB ≠ pathB)
    (hpathAPathB : pathA ≠ pathB)
    (hpathARestA : pathA ∉ restA) (hpathARestB : pathA ∉ restB)
    (hpathBRestA : pathB ∉ restA) (hpathBRestB : pathB ∉ restB)
    (hcontrolAPathB : controlA ≠ pathB)
    (hindexAPathB : indexBitA ≠ pathB)
    (hcontrolBPathA : controlB ≠ pathA)
    (hindexBPathA : indexBitB ≠ pathA)
    (hready : DualZeroPathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB state) :
    DualOnePathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB
      (run [.CX controlA pathA, .CX controlB pathB] state) := by
  let afterA := Classical.applyGate (.CX controlA pathA) state
  let afterB := Classical.applyGate (.CX controlB pathB) afterA
  change DualOnePathReady controlA indexBitA pathA
    controlB indexBitB pathB restA restB afterB
  unfold DualZeroPathReady at hready
  unfold ZeroAndComputed at hready
  unfold DualOnePathReady
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro wire hwire
    change afterA[pathB ↦ Bool.xor (afterA pathB) (afterA controlB)] wire = false
    rw [upd_other afterA pathB _ (by
      intro equality
      subst wire
      exact hpathBRestA hwire)]
    change state[pathA ↦ Bool.xor (state pathA) (state controlA)] wire = false
    rw [upd_other state pathA _ (by
      intro equality
      subst wire
      exact hpathARestA hwire)]
    exact hready.1 wire hwire
  · intro wire hwire
    change afterA[pathB ↦ Bool.xor (afterA pathB) (afterA controlB)] wire = false
    rw [upd_other afterA pathB _ (by
      intro equality
      subst wire
      exact hpathBRestB hwire)]
    change state[pathA ↦ Bool.xor (state pathA) (state controlA)] wire = false
    rw [upd_other state pathA _ (by
      intro equality
      subst wire
      exact hpathARestB hwire)]
    exact hready.2.1 wire hwire
  · have hafterBPathA : afterB pathA = afterA pathA := by
      simpa [afterB, Classical.applyGate] using
        upd_other afterA pathB (Bool.xor (afterA pathB) (afterA controlB)) hpathAPathB
    have hafterBControlA : afterB controlA = afterA controlA := by
      simpa [afterB, Classical.applyGate] using
        upd_other afterA pathB (Bool.xor (afterA pathB) (afterA controlB)) hcontrolAPathB
    have hafterBIndexA : afterB indexBitA = afterA indexBitA := by
      simpa [afterB, Classical.applyGate] using
        upd_other afterA pathB (Bool.xor (afterA pathB) (afterA controlB)) hindexAPathB
    have hafterAPathA :
        afterA pathA = Bool.xor (state pathA) (state controlA) := by
      simp [afterA, Classical.applyGate]
    have hafterAControlA : afterA controlA = state controlA := by
      simpa [afterA, Classical.applyGate] using
        upd_other state pathA (Bool.xor (state pathA) (state controlA)) hcpa
    have hafterAIndexA : afterA indexBitA = state indexBitA := by
      simpa [afterA, Classical.applyGate] using
        upd_other state pathA (Bool.xor (state pathA) (state controlA)) hia
    rw [hafterBPathA, hafterBControlA, hafterBIndexA,
      hafterAPathA, hafterAControlA, hafterAIndexA, hready.2.2.1]
    cases state controlA <;> cases state indexBitA <;> decide
  · have hafterBPathB :
        afterB pathB = Bool.xor (afterA pathB) (afterA controlB) := by
      simp [afterB, Classical.applyGate]
    have hafterBControlB : afterB controlB = afterA controlB := by
      simpa [afterB, Classical.applyGate] using
        upd_other afterA pathB (Bool.xor (afterA pathB) (afterA controlB)) hcpb
    have hafterBIndexB : afterB indexBitB = afterA indexBitB := by
      simpa [afterB, Classical.applyGate] using
        upd_other afterA pathB (Bool.xor (afterA pathB) (afterA controlB)) hib
    have hafterAPathB : afterA pathB = state pathB := by
      simpa [afterA, Classical.applyGate] using
        upd_other state pathA (Bool.xor (state pathA) (state controlA))
          (Ne.symm hpathAPathB)
    have hafterAControlB : afterA controlB = state controlB := by
      simpa [afterA, Classical.applyGate] using
        upd_other state pathA (Bool.xor (state pathA) (state controlA)) hcontrolBPathA
    have hafterAIndexB : afterA indexBitB = state indexBitB := by
      simpa [afterA, Classical.applyGate] using
        upd_other state pathA (Bool.xor (state pathA) (state controlA)) hindexBPathA
    rw [hafterBPathB, hafterBControlB, hafterBIndexB,
      hafterAPathB, hafterAControlB, hafterAIndexB, hready.2.2.2]
    cases state controlB <;> cases state indexBitB <;> decide

private theorem dualZeroPathReady_after_reverseToggle
    (controlA indexBitA pathA controlB indexBitB pathB : Wire)
    (restA restB : List Wire) (state : BasisState)
    (hcpa : controlA ≠ pathA) (hia : indexBitA ≠ pathA)
    (hcpb : controlB ≠ pathB) (hib : indexBitB ≠ pathB)
    (hpathAPathB : pathA ≠ pathB)
    (hpathARestA : pathA ∉ restA) (hpathARestB : pathA ∉ restB)
    (hpathBRestA : pathB ∉ restA) (hpathBRestB : pathB ∉ restB)
    (hcontrolAPathB : controlA ≠ pathB)
    (hindexAPathB : indexBitA ≠ pathB)
    (hcontrolBPathA : controlB ≠ pathA)
    (hindexBPathA : indexBitB ≠ pathA)
    (hready : DualOnePathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB state) :
    DualZeroPathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB
      (run [.CX controlB pathB, .CX controlA pathA] state) := by
  let afterB := Classical.applyGate (.CX controlB pathB) state
  let afterA := Classical.applyGate (.CX controlA pathA) afterB
  change DualZeroPathReady controlA indexBitA pathA
    controlB indexBitB pathB restA restB afterA
  unfold DualOnePathReady at hready
  unfold DualZeroPathReady
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro wire hwire
    change afterB[pathA ↦ Bool.xor (afterB pathA) (afterB controlA)] wire = false
    rw [upd_other afterB pathA _ (by
      intro equality
      subst wire
      exact hpathARestA hwire)]
    change state[pathB ↦ Bool.xor (state pathB) (state controlB)] wire = false
    rw [upd_other state pathB _ (by
      intro equality
      subst wire
      exact hpathBRestA hwire)]
    exact hready.1 wire hwire
  · intro wire hwire
    change afterB[pathA ↦ Bool.xor (afterB pathA) (afterB controlA)] wire = false
    rw [upd_other afterB pathA _ (by
      intro equality
      subst wire
      exact hpathARestB hwire)]
    change state[pathB ↦ Bool.xor (state pathB) (state controlB)] wire = false
    rw [upd_other state pathB _ (by
      intro equality
      subst wire
      exact hpathBRestB hwire)]
    exact hready.2.1 wire hwire
  · unfold ZeroAndComputed
    have hafterAPathA :
        afterA pathA = Bool.xor (afterB pathA) (afterB controlA) := by
      simp [afterA, Classical.applyGate]
    have hafterAControlA : afterA controlA = afterB controlA := by
      simpa [afterA, Classical.applyGate] using
        upd_other afterB pathA (Bool.xor (afterB pathA) (afterB controlA)) hcpa
    have hafterAIndexA : afterA indexBitA = afterB indexBitA := by
      simpa [afterA, Classical.applyGate] using
        upd_other afterB pathA (Bool.xor (afterB pathA) (afterB controlA)) hia
    have hafterBPathA : afterB pathA = state pathA := by
      simpa [afterB, Classical.applyGate] using
        upd_other state pathB (Bool.xor (state pathB) (state controlB)) hpathAPathB
    have hafterBControlA : afterB controlA = state controlA := by
      simpa [afterB, Classical.applyGate] using
        upd_other state pathB (Bool.xor (state pathB) (state controlB)) hcontrolAPathB
    have hafterBIndexA : afterB indexBitA = state indexBitA := by
      simpa [afterB, Classical.applyGate] using
        upd_other state pathB (Bool.xor (state pathB) (state controlB)) hindexAPathB
    rw [hafterAPathA, hafterAControlA, hafterAIndexA,
      hafterBPathA, hafterBControlA, hafterBIndexA, hready.2.2.1]
    cases state controlA <;> cases state indexBitA <;> decide
  · unfold ZeroAndComputed
    have hafterAPathB : afterA pathB = afterB pathB := by
      simpa [afterA, Classical.applyGate] using
        upd_other afterB pathA (Bool.xor (afterB pathA) (afterB controlA))
          (Ne.symm hpathAPathB)
    have hafterAControlB : afterA controlB = afterB controlB := by
      simpa [afterA, Classical.applyGate] using
        upd_other afterB pathA (Bool.xor (afterB pathA) (afterB controlA)) hcontrolBPathA
    have hafterAIndexB : afterA indexBitB = afterB indexBitB := by
      simpa [afterA, Classical.applyGate] using
        upd_other afterB pathA (Bool.xor (afterB pathA) (afterB controlA)) hindexBPathA
    have hafterBPathB :
        afterB pathB = Bool.xor (state pathB) (state controlB) := by
      simp [afterB, Classical.applyGate]
    have hafterBControlB : afterB controlB = state controlB := by
      simpa [afterB, Classical.applyGate] using
        upd_other state pathB (Bool.xor (state pathB) (state controlB)) hcpb
    have hafterBIndexB : afterB indexBitB = state indexBitB := by
      simpa [afterB, Classical.applyGate] using
        upd_other state pathB (Bool.xor (state pathB) (state controlB)) hib
    rw [hafterAPathB, hafterAControlB, hafterAIndexB,
      hafterBPathB, hafterBControlB, hafterBIndexB, hready.2.2.2]
    cases state controlB <;> cases state indexBitB <;> decide

private theorem run_dualZeroAnd_cleanup
    (controlA indexBitA pathA controlB indexBitB pathB : Wire)
    (restA restB : List Wire) (state : BasisState)
    (hca : controlA ≠ indexBitA) (hcpa : controlA ≠ pathA)
    (hia : indexBitA ≠ pathA)
    (hcb : controlB ≠ indexBitB) (hcpb : controlB ≠ pathB)
    (hib : indexBitB ≠ pathB)
    (hpathAPathB : pathA ≠ pathB)
    (hcontrolAPathB : controlA ≠ pathB)
    (hindexAPathB : indexBitA ≠ pathB)
    (hready : DualZeroPathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB state) :
    run
        (computeZeroAnd controlB indexBitB pathB ++
          computeZeroAnd controlA indexBitA pathA)
        state =
      state[pathB ↦ false][pathA ↦ false] := by
  unfold DualZeroPathReady at hready
  have hcleanupB := run_computeZeroAnd_of_computed
    controlB indexBitB pathB state hcb hcpb hib hready.2.2.2
  have hreadyA : ZeroAndComputed controlA indexBitA pathA
      state[pathB ↦ false] := by
    unfold ZeroAndComputed at hready ⊢
    rw [upd_other state pathB false hpathAPathB,
      upd_other state pathB false hcontrolAPathB,
      upd_other state pathB false hindexAPathB]
    exact hready.2.2.1
  rw [Classical.run_append, hcleanupB]
  exact run_computeZeroAnd_of_computed
    controlA indexBitA pathA state[pathB ↦ false]
      hca hcpa hia hreadyA

private theorem dualZeroPathReady_preserved
    (indexBitA indexBitB controlA controlB pathA pathB : Wire)
    (zero one : DualUnaryActionTree) (restA restB : List Wire)
    (protectedWires : List Wire) (state next : BasisState)
    (hroles : ∀ wire,
      wire ∈ DualUnaryActionTree.decoderWires
        (.node indexBitA indexBitB zero one)
        controlA controlB (pathA :: restA) (pathB :: restB) →
          wire ∈ protectedWires)
    (hready : DualZeroPathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB state)
    (hpreserves : ∀ wire, wire ∈ protectedWires →
      next wire = state wire) :
    DualZeroPathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB next := by
  unfold DualZeroPathReady at hready ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro wire hwire
    rw [hpreserves wire (hroles wire (by
      simp [DualUnaryActionTree.decoderWires, hwire]))]
    exact hready.1 wire hwire
  · intro wire hwire
    rw [hpreserves wire (hroles wire (by
      simp [DualUnaryActionTree.decoderWires, hwire]))]
    exact hready.2.1 wire hwire
  · unfold ZeroAndComputed at hready ⊢
    rw [hpreserves pathA (hroles pathA (by
        simp [DualUnaryActionTree.decoderWires])),
      hpreserves controlA (hroles controlA (by
        simp [DualUnaryActionTree.decoderWires])),
      hpreserves indexBitA (hroles indexBitA (by
        simp [DualUnaryActionTree.decoderWires,
          DualUnaryActionTree.indexAWires]))]
    exact hready.2.2.1
  · unfold ZeroAndComputed at hready ⊢
    rw [hpreserves pathB (hroles pathB (by
        simp [DualUnaryActionTree.decoderWires])),
      hpreserves controlB (hroles controlB (by
        simp [DualUnaryActionTree.decoderWires])),
      hpreserves indexBitB (hroles indexBitB (by
        simp [DualUnaryActionTree.decoderWires,
          DualUnaryActionTree.indexBWires]))]
    exact hready.2.2.2

private theorem dualOnePathReady_preserved
    (indexBitA indexBitB controlA controlB pathA pathB : Wire)
    (zero one : DualUnaryActionTree) (restA restB : List Wire)
    (protectedWires : List Wire) (state next : BasisState)
    (hroles : ∀ wire,
      wire ∈ DualUnaryActionTree.decoderWires
        (.node indexBitA indexBitB zero one)
        controlA controlB (pathA :: restA) (pathB :: restB) →
          wire ∈ protectedWires)
    (hready : DualOnePathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB state)
    (hpreserves : ∀ wire, wire ∈ protectedWires →
      next wire = state wire) :
    DualOnePathReady controlA indexBitA pathA
      controlB indexBitB pathB restA restB next := by
  unfold DualOnePathReady at hready ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro wire hwire
    rw [hpreserves wire (hroles wire (by
      simp [DualUnaryActionTree.decoderWires, hwire]))]
    exact hready.1 wire hwire
  · intro wire hwire
    rw [hpreserves wire (hroles wire (by
      simp [DualUnaryActionTree.decoderWires, hwire]))]
    exact hready.2.1 wire hwire
  · rw [hpreserves pathA (hroles pathA (by
        simp [DualUnaryActionTree.decoderWires])),
      hpreserves controlA (hroles controlA (by
        simp [DualUnaryActionTree.decoderWires])),
      hpreserves indexBitA (hroles indexBitA (by
        simp [DualUnaryActionTree.decoderWires,
          DualUnaryActionTree.indexAWires]))]
    exact hready.2.2.1
  · rw [hpreserves pathB (hroles pathB (by
        simp [DualUnaryActionTree.decoderWires])),
      hpreserves controlB (hroles controlB (by
        simp [DualUnaryActionTree.decoderWires])),
      hpreserves indexBitB (hroles indexBitB (by
        simp [DualUnaryActionTree.decoderWires,
          DualUnaryActionTree.indexBWires]))]
    exact hready.2.2.2

private theorem dualUnaryActionUnitary_preservesProtected
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB dynamicWires protectedWires : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hleaf : DualUnaryLeafPreservesOn leafAction tree.labels
      dynamicWires protectedWires)
    (hdynamic : ∀ wire,
      wire ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        wire ∈ dynamicWires)
    (hroles : ∀ wire,
      wire ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        wire ∈ protectedWires)
    (hcleanA : Clean ancillasA state)
    (hcleanB : Clean ancillasB state) :
    ∀ wire, wire ∈ protectedWires →
      run (dualUnaryActionUnitary order leafAction tree
        controlA controlB ancillasA ancillasB) state wire = state wire := by
  induction hlayout generalizing state dynamicWires protectedWires with
  | leaf label controlA controlB ancillasA ancillasB hlocal =>
      intro wire hwire
      exact hleaf label (by simp [DualUnaryActionTree.labels]) controlA controlB
        (hdynamic controlA (by simp [DualUnaryActionTree.decoderWires]))
        (hdynamic controlB (by simp [DualUnaryActionTree.decoderWires]))
        state wire hwire
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      obtain ⟨hca, hcpa, hia, hcb, hcpb, hib,
        hpathAPathB, hpathARestA, hpathARestB,
        hpathBRestA, hpathBRestB,
        hcontrolAPathB, hindexAPathB,
        hcontrolBPathA, hindexBPathA⟩ :=
        dualUnaryNode_parts indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB hlocal
      have hpathAFalse : state pathA = false := hcleanA pathA (by simp)
      have hpathBFalse : state pathB = false := hcleanB pathB (by simp)
      let afterA := run (computeZeroAnd controlA indexBitA pathA) state
      have hafterA : afterA =
          state[pathA ↦ state controlA && !state indexBitA] := by
        simpa only [afterA] using run_computeZeroAnd
          controlA indexBitA pathA state hca hcpa hia hpathAFalse
      have hpathBAfterA : afterA pathB = false := by
        rw [hafterA, upd_other state pathA _ (Ne.symm hpathAPathB)]
        exact hpathBFalse
      let first := run (computeZeroAnd controlB indexBitB pathB) afterA
      have hfirst : first =
          afterA[pathB ↦ afterA controlB && !afterA indexBitB] := by
        simpa only [first] using run_computeZeroAnd
          controlB indexBitB pathB afterA hcb hcpb hib hpathBAfterA
      have hreadyFirst : DualZeroPathReady controlA indexBitA pathA
          controlB indexBitB pathB restA restB first := by
        simpa only [first, afterA] using dualZeroPathReady_after_compute
          controlA indexBitA pathA controlB indexBitB pathB restA restB state
          hca hcpa hia hcb hcpb hib hpathAPathB
          hpathARestA hpathARestB hpathBRestA hpathBRestB
          hcontrolAPathB hindexAPathB hcleanA hcleanB
      have hzeroRoles : ∀ wire,
          wire ∈ zero.decoderWires pathA pathB restA restB →
            wire ∈ protectedWires := by
        intro wire hwire
        exact hroles wire
          (dualZero_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB wire hwire)
      have hzeroDynamic : ∀ wire,
          wire ∈ zero.decoderWires pathA pathB restA restB →
            wire ∈ dynamicWires := by
        intro wire hwire
        exact hdynamic wire
          (dualZero_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB wire hwire)
      have honeRoles : ∀ wire,
          wire ∈ one.decoderWires pathA pathB restA restB →
            wire ∈ protectedWires := by
        intro wire hwire
        exact hroles wire
          (dualOne_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB wire hwire)
      have honeDynamic : ∀ wire,
          wire ∈ one.decoderWires pathA pathB restA restB →
            wire ∈ dynamicWires := by
        intro wire hwire
        exact hdynamic wire
          (dualOne_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB wire hwire)
      have hzeroLeaf : DualUnaryLeafPreservesOn leafAction zero.labels
          dynamicWires protectedWires := by
        intro label hlabel
        exact hleaf label (by
          simp [DualUnaryActionTree.labels, hlabel])
      have honeLeaf : DualUnaryLeafPreservesOn leafAction one.labels
          dynamicWires protectedWires := by
        intro label hlabel
        exact hleaf label (by
          simp [DualUnaryActionTree.labels, hlabel])
      cases order with
      | inc =>
          let afterZero := run
            (dualUnaryActionUnitary .inc leafAction zero
              pathA pathB restA restB) first
          have hzeroPreserves : ∀ wire, wire ∈ protectedWires →
              afterZero wire = first wire := by
            intro wire hwire
            exact ihZero dynamicWires protectedWires first hzeroLeaf hzeroDynamic hzeroRoles
              hreadyFirst.1 hreadyFirst.2.1 wire hwire
          have hreadyAfterZero : DualZeroPathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterZero :=
            dualZeroPathReady_preserved
              indexBitA indexBitB controlA controlB pathA pathB
              zero one restA restB protectedWires first afterZero
              hroles hreadyFirst hzeroPreserves
          let switched := run
            [.CX controlA pathA, .CX controlB pathB] afterZero
          have hreadySwitched : DualOnePathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB switched := by
            simpa only [switched] using dualOnePathReady_after_forwardToggle
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterZero hcpa hia hcpb hib hpathAPathB
              hpathARestA hpathARestB hpathBRestA hpathBRestB
              hcontrolAPathB hindexAPathB hcontrolBPathA hindexBPathA
              hreadyAfterZero
          let afterOne := run
            (dualUnaryActionUnitary .inc leafAction one
              pathA pathB restA restB) switched
          have honePreserves : ∀ wire, wire ∈ protectedWires →
              afterOne wire = switched wire := by
            intro wire hwire
            exact ihOne dynamicWires protectedWires switched honeLeaf honeDynamic honeRoles
              hreadySwitched.1 hreadySwitched.2.1 wire hwire
          have hreadyAfterOne : DualOnePathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterOne :=
            dualOnePathReady_preserved
              indexBitA indexBitB controlA controlB pathA pathB
              zero one restA restB protectedWires switched afterOne
              hroles hreadySwitched honePreserves
          let switchedBack := run
            [.CX controlB pathB, .CX controlA pathA] afterOne
          have hreadyBack : DualZeroPathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB switchedBack := by
            simpa only [switchedBack] using dualZeroPathReady_after_reverseToggle
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterOne hcpa hia hcpb hib hpathAPathB
              hpathARestA hpathARestB hpathBRestA hpathBRestB
              hcontrolAPathB hindexAPathB hcontrolBPathA hindexBPathA
              hreadyAfterOne
          have hcleanup := run_dualZeroAnd_cleanup
            controlA indexBitA pathA controlB indexBitB pathB
            restA restB switchedBack hca hcpa hia hcb hcpb hib
            hpathAPathB hcontrolAPathB hindexAPathB hreadyBack
          have hforwardOther : ∀ wire, wire ≠ pathA → wire ≠ pathB →
              switched wire = afterZero wire := by
            intro wire hwireA hwireB
            change Classical.applyGate (.CX controlB pathB)
              (Classical.applyGate (.CX controlA pathA) afterZero) wire =
                afterZero wire
            simp only [Classical.applyGate]
            rw [upd_other _ pathB _ hwireB, upd_other _ pathA _ hwireA]
          have hreverseOther : ∀ wire, wire ≠ pathA → wire ≠ pathB →
              switchedBack wire = afterOne wire := by
            intro wire hwireA hwireB
            change Classical.applyGate (.CX controlA pathA)
              (Classical.applyGate (.CX controlB pathB) afterOne) wire =
                afterOne wire
            simp only [Classical.applyGate]
            rw [upd_other _ pathA _ hwireA, upd_other _ pathB _ hwireB]
          have hfirstOther : ∀ wire, wire ≠ pathA → wire ≠ pathB →
              first wire = state wire := by
            intro wire hwireA hwireB
            rw [hfirst, upd_other afterA pathB _ hwireB,
              hafterA, upd_other state pathA _ hwireA]
          intro wire hwire
          rw [dualUnaryActionUnitary,
            Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append]
          change run
            (computeZeroAnd controlB indexBitB pathB ++
              computeZeroAnd controlA indexBitA pathA)
            switchedBack wire = state wire
          rw [hcleanup]
          by_cases hwireA : wire = pathA
          · subst wire
            simp [hpathAFalse]
          · by_cases hwireB : wire = pathB
            · subst wire
              simp [upd, hpathBFalse]
            · rw [upd_other _ pathA false hwireA,
                upd_other switchedBack pathB false hwireB,
                hreverseOther wire hwireA hwireB,
                honePreserves wire hwire,
                hforwardOther wire hwireA hwireB,
                hzeroPreserves wire hwire,
                hfirstOther wire hwireA hwireB]
      | dec =>
          let switched := run
            [.CX controlA pathA, .CX controlB pathB] first
          have hreadySwitched : DualOnePathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB switched := by
            simpa only [switched] using dualOnePathReady_after_forwardToggle
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB first hcpa hia hcpb hib hpathAPathB
              hpathARestA hpathARestB hpathBRestA hpathBRestB
              hcontrolAPathB hindexAPathB hcontrolBPathA hindexBPathA
              hreadyFirst
          let afterOne := run
            (dualUnaryActionUnitary .dec leafAction one
              pathA pathB restA restB) switched
          have honePreserves : ∀ wire, wire ∈ protectedWires →
              afterOne wire = switched wire := by
            intro wire hwire
            exact ihOne dynamicWires protectedWires switched honeLeaf honeDynamic honeRoles
              hreadySwitched.1 hreadySwitched.2.1 wire hwire
          have hreadyAfterOne : DualOnePathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterOne :=
            dualOnePathReady_preserved
              indexBitA indexBitB controlA controlB pathA pathB
              zero one restA restB protectedWires switched afterOne
              hroles hreadySwitched honePreserves
          let switchedBack := run
            [.CX controlB pathB, .CX controlA pathA] afterOne
          have hreadyBack : DualZeroPathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB switchedBack := by
            simpa only [switchedBack] using dualZeroPathReady_after_reverseToggle
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterOne hcpa hia hcpb hib hpathAPathB
              hpathARestA hpathARestB hpathBRestA hpathBRestB
              hcontrolAPathB hindexAPathB hcontrolBPathA hindexBPathA
              hreadyAfterOne
          let afterZero := run
            (dualUnaryActionUnitary .dec leafAction zero
              pathA pathB restA restB) switchedBack
          have hzeroPreserves : ∀ wire, wire ∈ protectedWires →
              afterZero wire = switchedBack wire := by
            intro wire hwire
            exact ihZero dynamicWires protectedWires switchedBack hzeroLeaf
              hzeroDynamic hzeroRoles
              hreadyBack.1 hreadyBack.2.1 wire hwire
          have hreadyAfterZero : DualZeroPathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterZero :=
            dualZeroPathReady_preserved
              indexBitA indexBitB controlA controlB pathA pathB
              zero one restA restB protectedWires switchedBack afterZero
              hroles hreadyBack hzeroPreserves
          have hcleanup := run_dualZeroAnd_cleanup
            controlA indexBitA pathA controlB indexBitB pathB
            restA restB afterZero hca hcpa hia hcb hcpb hib
            hpathAPathB hcontrolAPathB hindexAPathB hreadyAfterZero
          have hforwardOther : ∀ wire, wire ≠ pathA → wire ≠ pathB →
              switched wire = first wire := by
            intro wire hwireA hwireB
            change Classical.applyGate (.CX controlB pathB)
              (Classical.applyGate (.CX controlA pathA) first) wire = first wire
            simp only [Classical.applyGate]
            rw [upd_other _ pathB _ hwireB, upd_other _ pathA _ hwireA]
          have hreverseOther : ∀ wire, wire ≠ pathA → wire ≠ pathB →
              switchedBack wire = afterOne wire := by
            intro wire hwireA hwireB
            change Classical.applyGate (.CX controlA pathA)
              (Classical.applyGate (.CX controlB pathB) afterOne) wire =
                afterOne wire
            simp only [Classical.applyGate]
            rw [upd_other _ pathA _ hwireA, upd_other _ pathB _ hwireB]
          have hfirstOther : ∀ wire, wire ≠ pathA → wire ≠ pathB →
              first wire = state wire := by
            intro wire hwireA hwireB
            rw [hfirst, upd_other afterA pathB _ hwireB,
              hafterA, upd_other state pathA _ hwireA]
          intro wire hwire
          rw [dualUnaryActionUnitary,
            Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append]
          change run
            (computeZeroAnd controlB indexBitB pathB ++
              computeZeroAnd controlA indexBitA pathA)
            afterZero wire = state wire
          rw [hcleanup]
          by_cases hwireA : wire = pathA
          · subst wire
            simp [hpathAFalse]
          · by_cases hwireB : wire = pathB
            · subst wire
              simp [upd, hpathBFalse]
            · rw [upd_other _ pathA false hwireA,
                upd_other afterZero pathB false hwireB,
                hzeroPreserves wire hwire,
                hreverseOther wire hwireA hwireB,
                honePreserves wire hwire,
                hforwardOther wire hwireA hwireB,
                hfirstOther wire hwireA hwireB]

private theorem dualUnaryActionUnitary_usesOnly_impl
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB support : List Wire)
    (hdecoder : ∀ wire,
      wire ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        wire ∈ support)
    (hleaf : DualUnaryLeafUsesOnly leafAction tree.labels support) :
    PaperCircuitUsesOnly support
      (dualUnaryActionUnitary order leafAction tree
        controlA controlB ancillasA ancillasB) := by
  induction tree generalizing controlA controlB ancillasA ancillasB with
  | leaf label =>
      apply hleaf label (by simp [DualUnaryActionTree.labels]) controlA controlB
      · exact hdecoder controlA (by
          simp [DualUnaryActionTree.decoderWires])
      · exact hdecoder controlB (by
          simp [DualUnaryActionTree.decoderWires])
  | node indexBitA indexBitB zero one ihZero ihOne =>
      cases ancillasA with
      | nil => simp [dualUnaryActionUnitary, PaperCircuitUsesOnly]
      | cons pathA restA =>
          cases ancillasB with
          | nil => simp [dualUnaryActionUnitary, PaperCircuitUsesOnly]
          | cons pathB restB =>
              have hcontrolA : controlA ∈ support := hdecoder controlA (by
                simp [DualUnaryActionTree.decoderWires])
              have hcontrolB : controlB ∈ support := hdecoder controlB (by
                simp [DualUnaryActionTree.decoderWires])
              have hindexA : indexBitA ∈ support := hdecoder indexBitA (by
                simp [DualUnaryActionTree.decoderWires,
                  DualUnaryActionTree.indexAWires])
              have hindexB : indexBitB ∈ support := hdecoder indexBitB (by
                simp [DualUnaryActionTree.decoderWires,
                  DualUnaryActionTree.indexBWires])
              have hpathA : pathA ∈ support := hdecoder pathA (by
                simp [DualUnaryActionTree.decoderWires])
              have hpathB : pathB ∈ support := hdecoder pathB (by
                simp [DualUnaryActionTree.decoderWires])
              have hzeroDecoder : ∀ wire,
                  wire ∈ zero.decoderWires pathA pathB restA restB →
                    wire ∈ support := by
                intro wire hwire
                apply hdecoder wire
                simp only [DualUnaryActionTree.decoderWires,
                  DualUnaryActionTree.indexAWires,
                  DualUnaryActionTree.indexBWires, List.mem_append,
                  List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
                aesop
              have honeDecoder : ∀ wire,
                  wire ∈ one.decoderWires pathA pathB restA restB →
                    wire ∈ support := by
                intro wire hwire
                apply hdecoder wire
                simp only [DualUnaryActionTree.decoderWires,
                  DualUnaryActionTree.indexAWires,
                  DualUnaryActionTree.indexBWires, List.mem_append,
                  List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hwire ⊢
                aesop
              have hzeroLeaf : DualUnaryLeafUsesOnly leafAction zero.labels support := by
                intro label hlabel
                exact hleaf label (by
                  simp [DualUnaryActionTree.labels, hlabel])
              have honeLeaf : DualUnaryLeafUsesOnly leafAction one.labels support := by
                intro label hlabel
                exact hleaf label (by
                  simp [DualUnaryActionTree.labels, hlabel])
              have hcomputeA : PaperCircuitUsesOnly support
                  (computeZeroAnd controlA indexBitA pathA) := by
                simp [computeZeroAnd, PaperCircuitUsesOnly, PaperGateUsesOnly,
                  gateWires, hcontrolA, hindexA, hpathA]
              have hcomputeB : PaperCircuitUsesOnly support
                  (computeZeroAnd controlB indexBitB pathB) := by
                simp [computeZeroAnd, PaperCircuitUsesOnly, PaperGateUsesOnly,
                  gateWires, hcontrolB, hindexB, hpathB]
              have hforward : PaperCircuitUsesOnly support
                  ([.CX controlA pathA, .CX controlB pathB] : Circuit) := by
                simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires,
                  hcontrolA, hcontrolB, hpathA, hpathB]
              have hreverse : PaperCircuitUsesOnly support
                  ([.CX controlB pathB, .CX controlA pathA] : Circuit) := by
                simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires,
                  hcontrolA, hcontrolB, hpathA, hpathB]
              have hzero := ihZero pathA pathB restA restB hzeroDecoder hzeroLeaf
              have hone := ihOne pathA pathB restA restB honeDecoder honeLeaf
              cases order with
              | inc =>
                  simp only [dualUnaryActionUnitary]
                  exact PaperCircuitUsesOnly.append
                    (PaperCircuitUsesOnly.append
                      (PaperCircuitUsesOnly.append
                        (PaperCircuitUsesOnly.append
                          (PaperCircuitUsesOnly.append
                            (PaperCircuitUsesOnly.append
                              (PaperCircuitUsesOnly.append hcomputeA hcomputeB)
                              hzero) hforward) hone) hreverse) hcomputeB) hcomputeA
              | dec =>
                  simp only [dualUnaryActionUnitary]
                  exact PaperCircuitUsesOnly.append
                    (PaperCircuitUsesOnly.append
                      (PaperCircuitUsesOnly.append
                        (PaperCircuitUsesOnly.append
                          (PaperCircuitUsesOnly.append
                            (PaperCircuitUsesOnly.append
                              (PaperCircuitUsesOnly.append hcomputeA hcomputeB)
                              hforward) hone) hreverse) hzero) hcomputeB) hcomputeA

/-- The coherent synchronized traversal stays inside the union supplied by its caller. -/
theorem dualUnaryActionUnitary_usesOnly
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB support : List Wire)
    (hdecoder : ∀ wire,
      wire ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        wire ∈ support)
    (hleaf : DualUnaryLeafUsesOnly leafAction tree.labels support) :
    PaperCircuitUsesOnly support
      (dualUnaryActionUnitary order leafAction tree
        controlA controlB ancillasA ancillasB) :=
  dualUnaryActionUnitary_usesOnly_impl order leafAction tree controlA controlB
    ancillasA ancillasB support hdecoder hleaf

/-- A synchronized traversal preserves a caller-declared interface when its actual decoder wires
are separately tracked as the admissible dynamic controls. -/
theorem dualUnaryActionUnitary_preservesOn
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB dynamicWires protectedWires : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hleaf : DualUnaryLeafPreservesOn leafAction tree.labels
      dynamicWires protectedWires)
    (hdynamic : ∀ wire,
      wire ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        wire ∈ dynamicWires)
    (hroles : ∀ wire,
      wire ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        wire ∈ protectedWires)
    (hcleanA : Clean ancillasA state)
    (hcleanB : Clean ancillasB state) :
    ∀ wire, wire ∈ protectedWires →
      run (dualUnaryActionUnitary order leafAction tree
        controlA controlB ancillasA ancillasB) state wire = state wire :=
  dualUnaryActionUnitary_preservesProtected order leafAction tree
    controlA controlB ancillasA ancillasB dynamicWires protectedWires state hlayout
    hleaf hdynamic hroles hcleanA hcleanB

/-- Direct whole-state semantics of the coherent synchronized traversal.  The theorem exposes the
exact ordered paired-leaf execution while proving that both temporary decoder stacks are restored. -/
theorem run_dualUnaryActionUnitary_as_runLeafState
    (order : UnaryOrder)
    (leafAction : Nat → Wire → Wire → Circuit)
    (leafState : Nat → Wire → Wire → BasisState → BasisState)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB protectedWires : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hruns : DualUnaryLeafRunsAs leafAction leafState protectedWires)
    (hleaf : DualUnaryLeafPreserves leafAction protectedWires)
    (hroles : ∀ wire,
      wire ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        wire ∈ protectedWires)
    (hcleanA : Clean ancillasA state)
    (hcleanB : Clean ancillasB state) :
    run (dualUnaryActionUnitary order leafAction tree
        controlA controlB ancillasA ancillasB) state =
      tree.runLeafState order leafState controlA controlB
        ancillasA ancillasB state := by
  induction hlayout generalizing state with
  | leaf label controlA controlB ancillasA ancillasB hlocal =>
      exact hruns label controlA controlB
        (hroles controlA (by simp [DualUnaryActionTree.decoderWires]))
        (hroles controlB (by simp [DualUnaryActionTree.decoderWires])) state
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      obtain ⟨hca, hcpa, hia, hcb, hcpb, hib,
        hpathAPathB, hpathARestA, hpathARestB,
        hpathBRestA, hpathBRestB,
        hcontrolAPathB, hindexAPathB,
        hcontrolBPathA, hindexBPathA⟩ :=
        dualUnaryNode_parts indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB hlocal
      have hpathAFalse : state pathA = false := hcleanA pathA (by simp)
      have hpathBFalse : state pathB = false := hcleanB pathB (by simp)
      let afterA := run (computeZeroAnd controlA indexBitA pathA) state
      have hafterA : afterA =
          state[pathA ↦ state controlA && !state indexBitA] := by
        simpa only [afterA] using run_computeZeroAnd
          controlA indexBitA pathA state hca hcpa hia hpathAFalse
      have hpathBAfterA : afterA pathB = false := by
        rw [hafterA, upd_other state pathA _ (Ne.symm hpathAPathB)]
        exact hpathBFalse
      let first := run (computeZeroAnd controlB indexBitB pathB) afterA
      have hfirst : first =
          afterA[pathB ↦ afterA controlB && !afterA indexBitB] := by
        simpa only [first] using run_computeZeroAnd
          controlB indexBitB pathB afterA hcb hcpb hib hpathBAfterA
      have hreadyFirst : DualZeroPathReady controlA indexBitA pathA
          controlB indexBitB pathB restA restB first := by
        simpa only [first, afterA] using dualZeroPathReady_after_compute
          controlA indexBitA pathA controlB indexBitB pathB restA restB state
          hca hcpa hia hcb hcpb hib hpathAPathB
          hpathARestA hpathARestB hpathBRestA hpathBRestB
          hcontrolAPathB hindexAPathB hcleanA hcleanB
      have hzeroRoles : ∀ wire,
          wire ∈ zero.decoderWires pathA pathB restA restB →
            wire ∈ protectedWires := by
        intro wire hwire
        exact hroles wire
          (dualZero_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB wire hwire)
      have honeRoles : ∀ wire,
          wire ∈ one.decoderWires pathA pathB restA restB →
            wire ∈ protectedWires := by
        intro wire hwire
        exact hroles wire
          (dualOne_decoder_subset indexBitA indexBitB controlA controlB
            pathA pathB zero one restA restB wire hwire)
      cases order with
      | inc =>
          let afterZero := run
            (dualUnaryActionUnitary .inc leafAction zero
              pathA pathB restA restB) first
          have hzeroState : afterZero =
              zero.runLeafState .inc leafState pathA pathB restA restB first := by
            exact ihZero first hzeroRoles hreadyFirst.1 hreadyFirst.2.1
          have hzeroPreserves : ∀ wire, wire ∈ protectedWires →
              afterZero wire = first wire := by
            intro wire hwire
            exact dualUnaryActionUnitary_preservesProtected .inc leafAction zero
              pathA pathB restA restB protectedWires protectedWires first hzero
              (fun label _ ↦ hleaf label)
              hzeroRoles hzeroRoles hreadyFirst.1 hreadyFirst.2.1 wire hwire
          have hreadyAfterZero : DualZeroPathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterZero :=
            dualZeroPathReady_preserved
              indexBitA indexBitB controlA controlB pathA pathB
              zero one restA restB protectedWires first afterZero
              hroles hreadyFirst hzeroPreserves
          let switched := run
            [.CX controlA pathA, .CX controlB pathB] afterZero
          have hswitchedModel : switched =
              Classical.applyGate (.CX controlB pathB)
                (Classical.applyGate (.CX controlA pathA) afterZero) := rfl
          have hreadySwitched : DualOnePathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB switched := by
            simpa only [switched] using dualOnePathReady_after_forwardToggle
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterZero hcpa hia hcpb hib hpathAPathB
              hpathARestA hpathARestB hpathBRestA hpathBRestB
              hcontrolAPathB hindexAPathB hcontrolBPathA hindexBPathA
              hreadyAfterZero
          let afterOne := run
            (dualUnaryActionUnitary .inc leafAction one
              pathA pathB restA restB) switched
          have honeState : afterOne =
              one.runLeafState .inc leafState pathA pathB restA restB switched := by
            exact ihOne switched honeRoles hreadySwitched.1 hreadySwitched.2.1
          have honePreserves : ∀ wire, wire ∈ protectedWires →
              afterOne wire = switched wire := by
            intro wire hwire
            exact dualUnaryActionUnitary_preservesProtected .inc leafAction one
              pathA pathB restA restB protectedWires protectedWires switched hone
              (fun label _ ↦ hleaf label)
              honeRoles honeRoles hreadySwitched.1 hreadySwitched.2.1 wire hwire
          have hreadyAfterOne : DualOnePathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterOne :=
            dualOnePathReady_preserved
              indexBitA indexBitB controlA controlB pathA pathB
              zero one restA restB protectedWires switched afterOne
              hroles hreadySwitched honePreserves
          let switchedBack := run
            [.CX controlB pathB, .CX controlA pathA] afterOne
          have hswitchedBackModel : switchedBack =
              Classical.applyGate (.CX controlA pathA)
                (Classical.applyGate (.CX controlB pathB) afterOne) := rfl
          have hreadyBack : DualZeroPathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB switchedBack := by
            simpa only [switchedBack] using dualZeroPathReady_after_reverseToggle
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterOne hcpa hia hcpb hib hpathAPathB
              hpathARestA hpathARestB hpathBRestA hpathBRestB
              hcontrolAPathB hindexAPathB hcontrolBPathA hindexBPathA
              hreadyAfterOne
          have hcleanup := run_dualZeroAnd_cleanup
            controlA indexBitA pathA controlB indexBitB pathB
            restA restB switchedBack hca hcpa hia hcb hcpb hib
            hpathAPathB hcontrolAPathB hindexAPathB hreadyBack
          rw [dualUnaryActionUnitary,
            Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append]
          change run
            (computeZeroAnd controlB indexBitB pathB ++
              computeZeroAnd controlA indexBitA pathA)
            switchedBack = _
          rw [hcleanup]
          simp only [DualUnaryActionTree.runLeafState]
          rw [← hafterA, ← hfirst, ← hzeroState, ← hswitchedModel,
            ← honeState, ← hswitchedBackModel]
      | dec =>
          let switched := run
            [.CX controlA pathA, .CX controlB pathB] first
          have hswitched : switched =
              Classical.applyGate (.CX controlB pathB)
                (Classical.applyGate (.CX controlA pathA) first) := rfl
          have hreadySwitched : DualOnePathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB switched := by
            simpa only [switched] using dualOnePathReady_after_forwardToggle
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB first hcpa hia hcpb hib hpathAPathB
              hpathARestA hpathARestB hpathBRestA hpathBRestB
              hcontrolAPathB hindexAPathB hcontrolBPathA hindexBPathA
              hreadyFirst
          let afterOne := run
            (dualUnaryActionUnitary .dec leafAction one
              pathA pathB restA restB) switched
          have honeState : afterOne =
              one.runLeafState .dec leafState pathA pathB restA restB switched := by
            exact ihOne switched honeRoles hreadySwitched.1 hreadySwitched.2.1
          have honePreserves : ∀ wire, wire ∈ protectedWires →
              afterOne wire = switched wire := by
            intro wire hwire
            exact dualUnaryActionUnitary_preservesProtected .dec leafAction one
              pathA pathB restA restB protectedWires protectedWires switched hone
              (fun label _ ↦ hleaf label)
              honeRoles honeRoles hreadySwitched.1 hreadySwitched.2.1 wire hwire
          have hreadyAfterOne : DualOnePathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterOne :=
            dualOnePathReady_preserved
              indexBitA indexBitB controlA controlB pathA pathB
              zero one restA restB protectedWires switched afterOne
              hroles hreadySwitched honePreserves
          let switchedBack := run
            [.CX controlB pathB, .CX controlA pathA] afterOne
          have hswitchedBack : switchedBack =
              Classical.applyGate (.CX controlA pathA)
                (Classical.applyGate (.CX controlB pathB) afterOne) := rfl
          have hreadyBack : DualZeroPathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB switchedBack := by
            simpa only [switchedBack] using dualZeroPathReady_after_reverseToggle
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterOne hcpa hia hcpb hib hpathAPathB
              hpathARestA hpathARestB hpathBRestA hpathBRestB
              hcontrolAPathB hindexAPathB hcontrolBPathA hindexBPathA
              hreadyAfterOne
          let afterZero := run
            (dualUnaryActionUnitary .dec leafAction zero
              pathA pathB restA restB) switchedBack
          have hzeroState : afterZero =
              zero.runLeafState .dec leafState pathA pathB restA restB switchedBack := by
            exact ihZero switchedBack hzeroRoles hreadyBack.1 hreadyBack.2.1
          have hzeroPreserves : ∀ wire, wire ∈ protectedWires →
              afterZero wire = switchedBack wire := by
            intro wire hwire
            exact dualUnaryActionUnitary_preservesProtected .dec leafAction zero
              pathA pathB restA restB protectedWires protectedWires switchedBack hzero
              (fun label _ ↦ hleaf label)
              hzeroRoles hzeroRoles hreadyBack.1 hreadyBack.2.1 wire hwire
          have hreadyAfterZero : DualZeroPathReady
              controlA indexBitA pathA controlB indexBitB pathB
              restA restB afterZero :=
            dualZeroPathReady_preserved
              indexBitA indexBitB controlA controlB pathA pathB
              zero one restA restB protectedWires switchedBack afterZero
              hroles hreadyBack hzeroPreserves
          have hcleanup := run_dualZeroAnd_cleanup
            controlA indexBitA pathA controlB indexBitB pathB
            restA restB afterZero hca hcpa hia hcb hcpb hib
            hpathAPathB hcontrolAPathB hindexAPathB hreadyAfterZero
          rw [dualUnaryActionUnitary,
            Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append,
            Classical.run_append, Classical.run_append]
          change run
            (computeZeroAnd controlB indexBitB pathB ++
              computeZeroAnd controlA indexBitA pathA)
            afterZero = _
          rw [hcleanup]
          simp only [DualUnaryActionTree.runLeafState]
          rw [← hafterA, ← hfirst, ← hswitched, ← honeState,
            ← hswitchedBack, ← hzeroState]

/-- The coherent synchronized traversal restores its complete paired decoder interface whenever
every leaf action preserves that interface. -/
theorem dualUnaryActionUnitary_preservesDecoder
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire) (state : BasisState)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hleaf : DualUnaryLeafPreserves leafAction
      (tree.decoderWires controlA controlB ancillasA ancillasB))
    (hcleanA : Clean ancillasA state)
    (hcleanB : Clean ancillasB state) :
    ∀ wire,
      wire ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        run (dualUnaryActionUnitary order leafAction tree
          controlA controlB ancillasA ancillasB) state wire = state wire := by
  exact dualUnaryActionUnitary_preservesProtected
    order leafAction tree controlA controlB ancillasA ancillasB
      (tree.decoderWires controlA controlB ancillasA ancillasB)
      (tree.decoderWires controlA controlB ancillasA ancillasB)
      state hlayout (fun label _ ↦ hleaf label)
      (fun _ hwire ↦ hwire) (fun _ hwire ↦ hwire)
      hcleanA hcleanB

/-- Both coherent path banks are restored clean. -/
theorem dualUnaryActionUnitary_clean
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire) (state : BasisState)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hleaf : DualUnaryLeafPreserves leafAction
      (tree.decoderWires controlA controlB ancillasA ancillasB))
    (hcleanA : Clean ancillasA state)
    (hcleanB : Clean ancillasB state) :
    Clean ancillasA
        (run (dualUnaryActionUnitary order leafAction tree
          controlA controlB ancillasA ancillasB) state) ∧
      Clean ancillasB
        (run (dualUnaryActionUnitary order leafAction tree
          controlA controlB ancillasA ancillasB) state) := by
  constructor
  · intro wire hwire
    rw [dualUnaryActionUnitary_preservesDecoder
      order leafAction tree controlA controlB ancillasA ancillasB state
      hlayout hleaf hcleanA hcleanB wire (by
        simp [DualUnaryActionTree.decoderWires, hwire])]
    exact hcleanA wire hwire
  · intro wire hwire
    rw [dualUnaryActionUnitary_preservesDecoder
      order leafAction tree controlA controlB ancillasA ancillasB state
      hlayout hleaf hcleanA hcleanB wire (by
        simp [DualUnaryActionTree.decoderWires, hwire])]
    exact hcleanB wire hwire

private theorem dualUnaryAction_coherent_mono
    {program : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid Stronger : BasisState → Prop}
    (hrefines : CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ state, Stronger state → Valid state) :
    CoherentlyImplementsOn program ideal Stronger := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch state hstate ↦
    hbranch state (hsub state hstate)

private theorem dualUnaryAction_coherent_seq_circuits
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

/-- Measuring the two synchronized path ANDs in reverse compute order coherently implements the
corresponding pair of ordinary reverse Toffolis. -/
theorem eraseDualZeroAnd_coherent
    (controlA indexBitA pathA controlB indexBitB pathB : Wire)
    (restA restB : List Wire)
    (hca : controlA ≠ indexBitA) (hcpa : controlA ≠ pathA)
    (hia : indexBitA ≠ pathA)
    (hcb : controlB ≠ indexBitB) (hcpb : controlB ≠ pathB)
    (hib : indexBitB ≠ pathB)
    (hpathAPathB : pathA ≠ pathB)
    (hcontrolAPathB : controlA ≠ pathB)
    (hindexAPathB : indexBitA ≠ pathB) :
    CoherentlyImplementsOn
      (eraseDualZeroAnd controlA indexBitA pathA
        controlB indexBitB pathB)
      (Quantum.run
        (computeZeroAnd controlB indexBitB pathB ++
          computeZeroAnd controlA indexBitA pathA))
      (DualZeroPathReady controlA indexBitA pathA
        controlB indexBitB pathB restA restB) := by
  have heraseB : CoherentlyImplementsOn
      (eraseZeroAnd controlB indexBitB pathB)
      (Quantum.run (computeZeroAnd controlB indexBitB pathB))
      (DualZeroPathReady controlA indexBitA pathA
        controlB indexBitB pathB restA restB) :=
    dualUnaryAction_coherent_mono
      (eraseZeroAnd_coherent controlB indexBitB pathB hcb hcpb hib)
      (fun _ hready ↦ hready.2.2.2)
  have heraseA := eraseZeroAnd_coherent
    controlA indexBitA pathA hca hcpa hia
  have hseq := dualUnaryAction_coherent_seq_circuits
    heraseB heraseA (computeZeroAnd_HPFree controlB indexBitB pathB) (by
      intro state hready
      unfold DualZeroPathReady at hready
      have hcleanupB := run_computeZeroAnd_of_computed
        controlB indexBitB pathB state hcb hcpb hib hready.2.2.2
      rw [hcleanupB]
      unfold ZeroAndComputed at hready ⊢
      rw [upd_other state pathB false hpathAPathB,
        upd_other state pathB false hcontrolAPathB,
        upd_other state pathB false hindexAPathB]
      exact hready.2.2.1)
  simpa only [eraseDualZeroAnd] using hseq

/-- Replacing both reverse path-ANDs at every synchronized node by B-then-A measurement/reset
coherently implements the exact paired unitary traversal. -/
theorem dualUnaryAction_coherent
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hleaf : DualUnaryLeafPreserves leafAction
      (tree.decoderWires controlA controlB ancillasA ancillasB))
    (hhp : DualUnaryLeafHPFree leafAction) :
    CoherentlyImplementsOn
      (dualUnaryAction order leafAction tree
        controlA controlB ancillasA ancillasB)
      (Quantum.run (dualUnaryActionUnitary order leafAction tree
        controlA controlB ancillasA ancillasB))
      (fun state ↦ Clean ancillasA state ∧ Clean ancillasB state) := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal =>
      exact CoherentlyImplementsOn.unitary
        (leafAction label controlA controlB)
        (fun state ↦ Clean ancillasA state ∧ Clean ancillasB state)
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      obtain ⟨hca, hcpa, hia, hcb, hcpb, hib,
        hpathAPathB, hpathARestA, hpathARestB,
        hpathBRestA, hpathBRestB,
        hcontrolAPathB, hindexAPathB,
        hcontrolBPathA, hindexBPathA⟩ :=
        dualUnaryNode_parts indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB hlocal
      let protectedWires :=
        (DualUnaryActionTree.node indexBitA indexBitB zero one).decoderWires
          controlA controlB (pathA :: restA) (pathB :: restB)
      have hzeroRoles : ∀ wire,
          wire ∈ zero.decoderWires pathA pathB restA restB →
            wire ∈ protectedWires :=
        dualZero_decoder_subset indexBitA indexBitB controlA controlB
          pathA pathB zero one restA restB
      have honeRoles : ∀ wire,
          wire ∈ one.decoderWires pathA pathB restA restB →
            wire ∈ protectedWires :=
        dualOne_decoder_subset indexBitA indexBitB controlA controlB
          pathA pathB zero one restA restB
      have hzeroLeaf : DualUnaryLeafPreserves leafAction
          (zero.decoderWires pathA pathB restA restB) := by
        intro label childA childB hchildA hchildB state wire hwire
        exact hleaf label childA childB
          (hzeroRoles childA hchildA) (hzeroRoles childB hchildB)
          state wire (hzeroRoles wire hwire)
      have honeLeaf : DualUnaryLeafPreserves leafAction
          (one.decoderWires pathA pathB restA restB) := by
        intro label childA childB hchildA hchildB state wire hwire
        exact hleaf label childA childB
          (honeRoles childA hchildA) (honeRoles childB hchildB)
          state wire (honeRoles wire hwire)
      have hzeroPreserves : ∀ state,
          DualZeroPathReady controlA indexBitA pathA
            controlB indexBitB pathB restA restB state →
          DualZeroPathReady controlA indexBitA pathA
            controlB indexBitB pathB restA restB
            (run (dualUnaryActionUnitary order leafAction zero
              pathA pathB restA restB) state) := by
        intro state hready
        have hpreserves := dualUnaryActionUnitary_preservesProtected
          order leafAction zero pathA pathB restA restB protectedWires
          protectedWires state hzero (fun label _ ↦ hleaf label)
          hzeroRoles hzeroRoles
          hready.1 hready.2.1
        exact dualZeroPathReady_preserved
          indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB protectedWires state
          (run (dualUnaryActionUnitary order leafAction zero
            pathA pathB restA restB) state)
          (fun _ hwire ↦ hwire) hready hpreserves
      have honePreserves : ∀ state,
          DualOnePathReady controlA indexBitA pathA
            controlB indexBitB pathB restA restB state →
          DualOnePathReady controlA indexBitA pathA
            controlB indexBitB pathB restA restB
            (run (dualUnaryActionUnitary order leafAction one
              pathA pathB restA restB) state) := by
        intro state hready
        have hpreserves := dualUnaryActionUnitary_preservesProtected
          order leafAction one pathA pathB restA restB protectedWires
          protectedWires state hone (fun label _ ↦ hleaf label)
          honeRoles honeRoles
          hready.1 hready.2.1
        exact dualOnePathReady_preserved
          indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB protectedWires state
          (run (dualUnaryActionUnitary order leafAction one
            pathA pathB restA restB) state)
          (fun _ hwire ↦ hwire) hready hpreserves
      have ihZeroReady : CoherentlyImplementsOn
          (dualUnaryAction order leafAction zero pathA pathB restA restB)
          (Quantum.run (dualUnaryActionUnitary order leafAction zero
            pathA pathB restA restB))
          (DualZeroPathReady controlA indexBitA pathA
            controlB indexBitB pathB restA restB) :=
        dualUnaryAction_coherent_mono (ihZero hzeroLeaf)
          (fun _ hready ↦ ⟨hready.1, hready.2.1⟩)
      have ihOneReady : CoherentlyImplementsOn
          (dualUnaryAction order leafAction one pathA pathB restA restB)
          (Quantum.run (dualUnaryActionUnitary order leafAction one
            pathA pathB restA restB))
          (DualOnePathReady controlA indexBitA pathA
            controlB indexBitB pathB restA restB) :=
        dualUnaryAction_coherent_mono (ihOne honeLeaf)
          (fun _ hready ↦ ⟨hready.1, hready.2.1⟩)
      have herase := eraseDualZeroAnd_coherent
        controlA indexBitA pathA controlB indexBitB pathB restA restB
        hca hcpa hia hcb hcpb hib hpathAPathB
        hcontrolAPathB hindexAPathB
      have htoggleForward := CoherentlyImplementsOn.unitary
        [.CX controlA pathA, .CX controlB pathB]
        (DualZeroPathReady controlA indexBitA pathA
          controlB indexBitB pathB restA restB)
      have htoggleReverse := CoherentlyImplementsOn.unitary
        [.CX controlB pathB, .CX controlA pathA]
        (DualOnePathReady controlA indexBitA pathA
          controlB indexBitB pathB restA restB)
      have hcomputeA := CoherentlyImplementsOn.unitary
        (computeZeroAnd controlA indexBitA pathA)
        (fun state ↦ Clean (pathA :: restA) state ∧
          Clean (pathB :: restB) state)
      have hcomputeB := CoherentlyImplementsOn.unitary
        (computeZeroAnd controlB indexBitB pathB) (fun _ ↦ True)
      have hcomputePair := dualUnaryAction_coherent_seq_circuits
        hcomputeA hcomputeB (computeZeroAnd_HPFree controlA indexBitA pathA)
        (fun _ _ ↦ trivial)
      have hcomputeReady : ∀ state,
          (Clean (pathA :: restA) state ∧ Clean (pathB :: restB) state) →
          DualZeroPathReady controlA indexBitA pathA
            controlB indexBitB pathB restA restB
            (run
              (computeZeroAnd controlA indexBitA pathA ++
                computeZeroAnd controlB indexBitB pathB)
              state) := by
        intro state hclean
        simpa only [Classical.run_append] using
          dualZeroPathReady_after_compute
            controlA indexBitA pathA controlB indexBitB pathB
            restA restB state hca hcpa hia hcb hcpb hib
            hpathAPathB hpathARestA hpathARestB
            hpathBRestA hpathBRestB hcontrolAPathB hindexAPathB
            hclean.1 hclean.2
      cases order with
      | inc =>
          have hback := dualUnaryAction_coherent_seq_circuits
            htoggleReverse herase (by simp) (by
              intro state hready
              simpa only [Classical.run_cons, Classical.run_nil] using
                dualZeroPathReady_after_reverseToggle
                  controlA indexBitA pathA controlB indexBitB pathB
                  restA restB state hcpa hia hcpb hib hpathAPathB
                  hpathARestA hpathARestB hpathBRestA hpathBRestB
                  hcontrolAPathB hindexAPathB
                  hcontrolBPathA hindexBPathA hready)
          have honeChunk := dualUnaryAction_coherent_seq_circuits
            ihOneReady hback
            (dualUnaryActionUnitary_HPFree .inc leafAction one
              pathA pathB restA restB hhp)
            honePreserves
          have htoggleChunk := dualUnaryAction_coherent_seq_circuits
            htoggleForward honeChunk (by simp) (by
              intro state hready
              simpa only [Classical.run_cons, Classical.run_nil] using
                dualOnePathReady_after_forwardToggle
                  controlA indexBitA pathA controlB indexBitB pathB
                  restA restB state hcpa hia hcpb hib hpathAPathB
                  hpathARestA hpathARestB hpathBRestA hpathBRestB
                  hcontrolAPathB hindexAPathB
                  hcontrolBPathA hindexBPathA hready)
          have hzeroChunk := dualUnaryAction_coherent_seq_circuits
            ihZeroReady htoggleChunk
            (dualUnaryActionUnitary_HPFree .inc leafAction zero
              pathA pathB restA restB hhp)
            hzeroPreserves
          have hall := dualUnaryAction_coherent_seq_circuits
            hcomputePair hzeroChunk (by
              simp [computeZeroAnd_HPFree]) hcomputeReady
          simpa only [dualUnaryAction, dualUnaryActionUnitary,
            AdaptiveCircuit.seq, List.append_assoc] using hall
      | dec =>
          have hzeroErase := dualUnaryAction_coherent_seq_circuits
            ihZeroReady herase
            (dualUnaryActionUnitary_HPFree .dec leafAction zero
              pathA pathB restA restB hhp)
            hzeroPreserves
          have htoggleZeroChunk := dualUnaryAction_coherent_seq_circuits
            htoggleReverse hzeroErase (by simp) (by
              intro state hready
              simpa only [Classical.run_cons, Classical.run_nil] using
                dualZeroPathReady_after_reverseToggle
                  controlA indexBitA pathA controlB indexBitB pathB
                  restA restB state hcpa hia hcpb hib hpathAPathB
                  hpathARestA hpathARestB hpathBRestA hpathBRestB
                  hcontrolAPathB hindexAPathB
                  hcontrolBPathA hindexBPathA hready)
          have honeChunk := dualUnaryAction_coherent_seq_circuits
            ihOneReady htoggleZeroChunk
            (dualUnaryActionUnitary_HPFree .dec leafAction one
              pathA pathB restA restB hhp)
            honePreserves
          have htoggleOneChunk := dualUnaryAction_coherent_seq_circuits
            htoggleForward honeChunk (by simp) (by
              intro state hready
              simpa only [Classical.run_cons, Classical.run_nil] using
                dualOnePathReady_after_forwardToggle
                  controlA indexBitA pathA controlB indexBitB pathB
                  restA restB state hcpa hia hcpb hib hpathAPathB
                  hpathARestA hpathARestB hpathBRestA hpathBRestB
                  hcontrolAPathB hindexAPathB
                  hcontrolBPathA hindexBPathA hready)
          have hall := dualUnaryAction_coherent_seq_circuits
            hcomputePair htoggleOneChunk (by
              simp [computeZeroAnd_HPFree]) hcomputeReady
          simpa only [dualUnaryAction, dualUnaryActionUnitary,
            AdaptiveCircuit.seq, List.append_assoc] using hall

end

end ShorECDLP.Paper2607_13816
