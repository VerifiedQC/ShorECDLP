import ShorECDLP.Submission.«2607_13816».EEA.MeasuredAnd

/-!
# Measured unary iteration

This is the pruned binary decision tree from the pinned supplement's `unary_iteration_tight`.
Each internal node computes `path = control AND NOT indexBit`, visits the zero subtree, toggles
the path to `control AND indexBit`, visits the one subtree, toggles back, and erases the path AND
by measurement.  Leaves expose the selected path by toggling a dedicated marker wire; later EEA
blocks replace that marker action with the corresponding location-controlled arithmetic cell.
-/

namespace ShorECDLP.Paper2607_13816

open Classical Quantum

noncomputable section

/-- A source-level pruned unary decision tree.  Internal nodes store the actual index wire chosen
by `_split_bit`; a leaf stores its label and a dedicated observable marker. -/
inductive UnaryTree where
  | leaf (label : Nat) (marker : Wire)
  | node (indexBit : Wire) (zero one : UnaryTree)
deriving DecidableEq, Repr

namespace UnaryTree

def outputs : UnaryTree → List Wire
  | .leaf _ marker => [marker]
  | .node _ zero one => zero.outputs ++ one.outputs

def indexWires : UnaryTree → List Wire
  | .leaf _ _ => []
  | .node indexBit zero one =>
      indexBit :: (zero.indexWires ++ one.indexWires)

def internalNodes : UnaryTree → Nat
  | .leaf _ _ => 0
  | .node _ zero one => 1 + zero.internalNodes + one.internalNodes

def leaves : UnaryTree → Nat
  | .leaf _ _ => 1
  | .node _ zero one => zero.leaves + one.leaves

/-- Marker selected by following the stored index bits. -/
def routeMarker : UnaryTree → BasisState → Wire
  | .leaf _ marker, _ => marker
  | .node indexBit zero one, state =>
      if state indexBit then one.routeMarker state
      else zero.routeMarker state

/-- Label selected by the same route. -/
def routeLabel : UnaryTree → BasisState → Nat
  | .leaf label _, _ => label
  | .node indexBit zero one, state =>
      if state indexBit then one.routeLabel state
      else zero.routeLabel state

theorem routeMarker_mem_outputs
    (tree : UnaryTree) (state : BasisState) :
    tree.routeMarker state ∈ tree.outputs := by
  induction tree with
  | leaf label marker => simp [routeMarker, outputs]
  | node indexBit zero one ihZero ihOne =>
      cases hbit : state indexBit <;>
        simp [routeMarker, outputs, hbit, ihZero, ihOne]

theorem routeMarker_congr
    (tree : UnaryTree) (left right : BasisState)
    (h : ∀ wire ∈ tree.indexWires, left wire = right wire) :
    tree.routeMarker left = tree.routeMarker right := by
  induction tree with
  | leaf label marker => rfl
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
      simp only [routeMarker, hbit]
      split
      · exact ihOne hone
      · exact ihZero hzero

/-- Physical layout certificate.  Index wires may be reused at different tree nodes, hence the
deduplication; markers and path ancillas are globally distinct from every protected wire. -/
inductive Layout : UnaryTree → Wire → List Wire → Prop where
  | leaf
      (label : Nat) (marker control : Wire) (ancillas : List Wire)
      (hlocal : (control :: ancillas ++ [marker]).Nodup) :
      Layout (.leaf label marker) control ancillas
  | node
      (indexBit control path : Wire)
      (zero one : UnaryTree) (rest : List Wire)
      (hlocal :
        (control ::
          ((UnaryTree.node indexBit zero one).indexWires.dedup ++
            (path :: rest) ++
              (UnaryTree.node indexBit zero one).outputs)).Nodup)
      (hzero : Layout zero path rest)
      (hone : Layout one path rest) :
      Layout (.node indexBit zero one) control (path :: rest)

end UnaryTree

/-- Coherent reference traversal, with a Toffoli used for every reverse path-AND. -/
def unaryIterationUnitary : UnaryTree → Wire → List Wire → Circuit
  | .leaf _ marker, control, _ => [.CX control marker]
  | .node indexBit zero one, control, path :: rest =>
      computeZeroAnd control indexBit path ++
        unaryIterationUnitary zero path rest ++
        [.CX control path] ++
        unaryIterationUnitary one path rest ++
        [.CX control path] ++
        computeZeroAnd control indexBit path
  | .node _ _ _, _, [] => []

/-- Adaptive traversal with the final path-AND at every node erased by X-measure/reset. -/
def unaryIteration : UnaryTree → Wire → List Wire → AdaptiveCircuit
  | .leaf _ marker, control, _ =>
      .unitary [.CX control marker] .done
  | .node indexBit zero one, control, path :: rest =>
      .unitary (computeZeroAnd control indexBit path)
        ((unaryIteration zero path rest).seq
          (.unitary [.CX control path]
            ((unaryIteration one path rest).seq
              (.unitary [.CX control path]
                (eraseZeroAnd control indexBit path)))))
  | .node _ _ _, _, [] => .done

private theorem unaryNode_head_distinct
    (indexBit control path : Wire) (zero one : UnaryTree)
    (rest : List Wire)
    (hlocal :
      (control ::
        ((UnaryTree.node indexBit zero one).indexWires.dedup ++
          (path :: rest) ++
            (UnaryTree.node indexBit zero one).outputs)).Nodup) :
    control ≠ indexBit ∧ control ≠ path ∧ indexBit ≠ path := by
  have htail :
      ((UnaryTree.node indexBit zero one).indexWires.dedup ++
        ((path :: rest) ++
          (UnaryTree.node indexBit zero one).outputs)).Nodup := by
    simpa [List.append_assoc] using (List.nodup_cons.mp hlocal).2
  obtain ⟨_, _, hindexCross⟩ := List.nodup_append.mp htail
  have hcontrolAll := (List.nodup_cons.mp hlocal).1
  have hindexMem : indexBit ∈
      (UnaryTree.node indexBit zero one).indexWires.dedup := by
    simp [UnaryTree.indexWires]
  have hci : control ≠ indexBit := by
    intro equality
    apply hcontrolAll
    rw [equality]
    exact List.mem_append_left _
      (List.mem_append_left _ hindexMem)
  have hcp : control ≠ path := by
    intro equality
    apply hcontrolAll
    rw [equality]
    exact List.mem_append_left _
      (List.mem_append_right _ (by simp))
  exact ⟨hci, hcp,
    hindexCross indexBit hindexMem path (by simp)⟩

/-- The coherent tree changes exactly the marker selected by the index bits and the external
control.  All path ancillas are restored. -/
theorem run_unaryIterationUnitary
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout control ancillas)
    (hclean : Clean ancillas state) :
    Classical.run (unaryIterationUnitary tree control ancillas) state =
      Classical.applyGate (.CX control (tree.routeMarker state)) state := by
  induction hlayout generalizing state with
  | leaf label marker control ancillas hlocal =>
      rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      have htail :
          (((UnaryTree.node indexBit zero one).indexWires.dedup) ++
            ((path :: rest) ++
              (UnaryTree.node indexBit zero one).outputs)).Nodup := by
        simpa [List.append_assoc] using (List.nodup_cons.mp hlocal).2
      obtain ⟨hindices, hancOutputsNodup, hindexCross⟩ :=
        List.nodup_append.mp htail
      obtain ⟨hancillas, houtputs, hancOutputCross⟩ :=
        List.nodup_append.mp hancOutputsNodup
      have hcontrolAll :
          control ∉
            ((UnaryTree.node indexBit zero one).indexWires.dedup ++
              (path :: rest) ++
                (UnaryTree.node indexBit zero one).outputs) :=
        (List.nodup_cons.mp hlocal).1
      have hindexMem : indexBit ∈
          (UnaryTree.node indexBit zero one).indexWires.dedup := by
        simp [UnaryTree.indexWires]
      have hci : control ≠ indexBit := by
        intro equality
        apply hcontrolAll
        rw [equality]
        exact List.mem_append_left _
          (List.mem_append_left _ hindexMem)
      have hcp : control ≠ path := by
        intro equality
        apply hcontrolAll
        rw [equality]
        exact List.mem_append_left _
          (List.mem_append_right _ (by simp))
      have hip : indexBit ≠ path :=
        hindexCross indexBit hindexMem path (by simp)
      have hpathRest : path ∉ rest :=
        (List.nodup_cons.mp hancillas).1
      have hpathFalse : state path = false :=
        hclean path (by simp)
      have hrestClean : Clean rest state := by
        intro wire hwire
        exact hclean wire (by simp [hwire])
      let first := Classical.run
        (computeZeroAnd control indexBit path) state
      have hfirst :
          first = state[path ↦ state control && !state indexBit] := by
        simpa only [first] using run_computeZeroAnd
          control indexBit path state hci hcp hip hpathFalse
      have hrestCleanFirst : Clean rest first := by
        rw [hfirst]
        intro wire hwire
        rw [upd_other state path _ (by
          intro equality
          subst wire
          exact hpathRest hwire)]
        exact hrestClean wire hwire
      have hzeroOutput : zero.routeMarker state ∈
          (UnaryTree.node indexBit zero one).outputs := by
        exact List.mem_append_left one.outputs
          (zero.routeMarker_mem_outputs state)
      have honeOutput : one.routeMarker state ∈
          (UnaryTree.node indexBit zero one).outputs := by
        exact List.mem_append_right zero.outputs
          (one.routeMarker_mem_outputs state)
      have hpathZero : path ≠ zero.routeMarker state :=
        hancOutputCross path (by simp) _ hzeroOutput
      have hpathOne : path ≠ one.routeMarker state :=
        hancOutputCross path (by simp) _ honeOutput
      have hcontrolZero : control ≠ zero.routeMarker state := by
        intro equality
        apply hcontrolAll
        rw [equality]
        exact List.mem_append_right _ hzeroOutput
      have hcontrolOne : control ≠ one.routeMarker state := by
        intro equality
        apply hcontrolAll
        rw [equality]
        exact List.mem_append_right _ honeOutput
      have hindexZero : indexBit ≠ zero.routeMarker state :=
        hindexCross indexBit hindexMem _
          (List.mem_append_right (path :: rest) hzeroOutput)
      have hindexOne : indexBit ≠ one.routeMarker state :=
        hindexCross indexBit hindexMem _
          (List.mem_append_right (path :: rest) honeOutput)
      have houtputsSplit : (zero.outputs ++ one.outputs).Nodup := by
        simpa [UnaryTree.outputs] using houtputs
      have hzeroOne : zero.routeMarker state ≠ one.routeMarker state :=
        (List.nodup_append.mp houtputsSplit).2.2
          (zero.routeMarker state) (zero.routeMarker_mem_outputs state)
          (one.routeMarker state) (one.routeMarker_mem_outputs state)
      have hzeroRouteFirst :
          zero.routeMarker first = zero.routeMarker state := by
        apply zero.routeMarker_congr
        intro wire hwire
        have hwIndex : wire ∈
            (UnaryTree.node indexBit zero one).indexWires.dedup := by
          simp [UnaryTree.indexWires, hwire]
        have hwPath : wire ≠ path :=
          hindexCross wire hwIndex path (by simp)
        rw [hfirst, upd_other state path _ hwPath]
      have hzeroRun := ihZero first hrestCleanFirst
      rw [hzeroRouteFirst] at hzeroRun
      let afterZero := Classical.run
        (unaryIterationUnitary zero path rest) first
      have hafterZero :
          afterZero = Classical.applyGate
            (.CX path (zero.routeMarker state)) first := by
        simpa only [afterZero] using hzeroRun
      have hrestCleanAfterZero : Clean rest afterZero := by
        rw [hafterZero]
        intro wire hwire
        have hw : wire ≠ zero.routeMarker state :=
          hancOutputCross wire (by simp [hwire]) _ hzeroOutput
        change
          first[zero.routeMarker state ↦
            Bool.xor (first (zero.routeMarker state)) (first path)] wire = false
        rw [upd_other first _ _ hw]
        exact hrestCleanFirst wire hwire
      let switched := Classical.applyGate (.CX control path) afterZero
      have hrestCleanSwitched : Clean rest switched := by
        intro wire hwire
        have hw : wire ≠ path := by
          intro equality
          subst wire
          exact hpathRest hwire
        change
          afterZero[path ↦ Bool.xor (afterZero path) (afterZero control)] wire =
            false
        rw [upd_other afterZero path _ hw]
        exact hrestCleanAfterZero wire hwire
      have honeRouteSwitched :
          one.routeMarker switched = one.routeMarker state := by
        apply one.routeMarker_congr
        intro wire hwire
        have hwIndex : wire ∈
            (UnaryTree.node indexBit zero one).indexWires.dedup := by
          simp [UnaryTree.indexWires, hwire]
        have hwPath : wire ≠ path :=
          hindexCross wire hwIndex path (by simp)
        have hwZero : wire ≠ zero.routeMarker state :=
          hindexCross wire hwIndex _
            (List.mem_append_right (path :: rest) hzeroOutput)
        simp [switched, hafterZero, hfirst, Classical.applyGate, upd,
          hwPath, hwZero]
      have honeRun := ihOne switched hrestCleanSwitched
      rw [honeRouteSwitched] at honeRun
      let afterOne := Classical.run
        (unaryIterationUnitary one path rest) switched
      have hafterOne :
          afterOne = Classical.applyGate
            (.CX path (one.routeMarker state)) switched := by
        simpa only [afterOne] using honeRun
      let switchedBack := Classical.applyGate (.CX control path) afterOne
      have hzeroComputedBack :
          ZeroAndComputed control indexBit path switchedBack := by
        unfold ZeroAndComputed
        cases hc : state control <;> cases hb : state indexBit <;>
          simp [switchedBack, switched, hafterOne, hafterZero, hfirst,
            Classical.applyGate, upd,
            hcp, hip, hpathZero, hpathOne,
            hcontrolZero, hcontrolOne, hindexZero, hindexOne,
            hc, hb]
      have hcleanup := run_computeZeroAnd_of_computed
        control indexBit path switchedBack hci hcp hip hzeroComputedBack
      rw [unaryIterationUnitary, Classical.run_append,
        Classical.run_append, Classical.run_append,
        Classical.run_append, Classical.run_append]
      change
        Classical.run (computeZeroAnd control indexBit path) switchedBack = _
      rw [hcleanup]
      cases hbit : state indexBit <;> cases hcontrol : state control <;>
        funext wire <;>
        by_cases hwPath : wire = path <;>
        by_cases hwZero : wire = zero.routeMarker state <;>
        by_cases hwOne : wire = one.routeMarker state <;>
        simp [UnaryTree.routeMarker, switchedBack, switched,
          hafterOne, hafterZero, hfirst,
          Classical.applyGate, upd, hcp,
          hpathZero, Ne.symm hpathZero, hpathOne, Ne.symm hpathOne,
          hcontrolZero, hcontrolOne,
          hzeroOne, Ne.symm hzeroOne,
          hpathFalse, hbit, hcontrol, hwPath, hwZero, hwOne]

/-- Apart from its selected marker, the coherent traversal preserves every basis wire. -/
private theorem run_unaryIterationUnitary_eq_on
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout control ancillas)
    (hclean : Clean ancillas state)
    (wire : Wire) (hwire : wire ∉ tree.outputs) :
    Classical.run (unaryIterationUnitary tree control ancillas) state wire =
      state wire := by
  rw [run_unaryIterationUnitary tree control ancillas state hlayout hclean]
  have hroute : tree.routeMarker state ∈ tree.outputs :=
    tree.routeMarker_mem_outputs state
  have hne : wire ≠ tree.routeMarker state := by
    intro equality
    apply hwire
    rwa [equality]
  simp [Classical.applyGate, upd, hne]

/-- The coherent reference is entirely classical. -/
@[simp]
theorem unaryIterationUnitary_HPFree
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire) :
    HPFree (unaryIterationUnitary tree control ancillas) := by
  induction tree generalizing control ancillas with
  | leaf label marker => simp [unaryIterationUnitary]
  | node indexBit zero one ihZero ihOne =>
      cases ancillas with
      | nil => simp [unaryIterationUnitary]
      | cons path rest =>
          simp [unaryIterationUnitary, ihZero, ihOne]

/-- Every reverse path-AND in the coherent reference restores the clean bank. -/
theorem unaryIterationUnitary_clean
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (state : BasisState)
    (hlayout : tree.Layout control ancillas)
    (hclean : Clean ancillas state) :
    Clean ancillas
      (Classical.run (unaryIterationUnitary tree control ancillas) state) := by
  rw [run_unaryIterationUnitary tree control ancillas state hlayout hclean]
  intro wire hwire
  have hmarker : tree.routeMarker state ∈ tree.outputs :=
    tree.routeMarker_mem_outputs state
  cases hlayout with
  | leaf label marker control ancillas hlocal =>
      have hcross := (List.nodup_append.mp
        (List.nodup_cons.mp hlocal).2).2.2
      have hw : wire ≠ marker := by
        intro equality
        subst wire
        exact hcross marker hwire marker (by simp) rfl
      change
        state[marker ↦ Bool.xor (state marker) (state control)] wire = false
      rw [upd_other state marker _ hw]
      exact hclean wire hwire
  | node indexBit control path zero one rest hlocal hzero hone =>
      have hprefix :
          ((UnaryTree.node indexBit zero one).indexWires.dedup ++
            ((path :: rest) ++
              (UnaryTree.node indexBit zero one).outputs)).Nodup := by
        simpa [List.append_assoc] using (List.nodup_cons.mp hlocal).2
      have hsplit := List.nodup_append.mp hprefix
      have htailNodup :
          ((path :: rest) ++
            (UnaryTree.node indexBit zero one).outputs).Nodup := by
        simpa [List.append_assoc] using hsplit.2.1
      have hancOutputs := (List.nodup_append.mp htailNodup).2.2
      have hw : wire ≠
          (UnaryTree.node indexBit zero one).routeMarker state := by
        intro equality
        subst wire
        exact hancOutputs
          ((UnaryTree.node indexBit zero one).routeMarker state) hwire
          ((UnaryTree.node indexBit zero one).routeMarker state) hmarker rfl
      change
        state[(UnaryTree.node indexBit zero one).routeMarker state ↦
          Bool.xor
            (state ((UnaryTree.node indexBit zero one).routeMarker state))
            (state control)] wire = false
      rw [upd_other state _ _ hw]
      exact hclean wire hwire

/-- Physical well-formedness of the coherent reference. -/
theorem unaryIterationUnitary_wellFormed
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    CircuitWellFormed (unaryIterationUnitary tree control ancillas) := by
  induction hlayout with
  | leaf label marker control ancillas hlocal =>
      have hcm : control ≠ marker := by
        intro equality
        subst marker
        exact (List.nodup_cons.mp hlocal).1 (by simp)
      simp [unaryIterationUnitary, CircuitWellFormed,
        Gate.WellFormed, hcm]
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip⟩ :=
        unaryNode_head_distinct indexBit control path zero one rest hlocal
      have hcompute :=
        computeZeroAnd_wellFormed control indexBit path hci hcp hip
      have htoggle : CircuitWellFormed [.CX control path] := by
        simp [CircuitWellFormed, Gate.WellFormed, hcp]
      rw [unaryIterationUnitary]
      simp only [circuitWellFormed_append]
      exact ⟨⟨⟨⟨⟨hcompute, ihZero⟩, htoggle⟩, ihOne⟩, htoggle⟩,
        hcompute⟩

/-- Constructor-derived coherent Toffoli count: compute and reverse-uncompute at every node. -/
theorem unaryIterationUnitary_toffoliCount
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    eeaToffoliCount (unaryIterationUnitary tree control ancillas) =
      2 * tree.internalNodes := by
  induction hlayout with
  | leaf label marker control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      rw [unaryIterationUnitary]
      simp only [eeaToffoliCount_append]
      rw [ihZero, ihOne]
      simp only [computeZeroAnd_toffoliCount]
      simp [eeaToffoliCount, UnaryTree.internalNodes]
      omega

/-- Constructor-derived coherent CNOT count: one leaf marker plus two path toggles per node. -/
theorem unaryIterationUnitary_cnotCount
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    eeaCnotCount (unaryIterationUnitary tree control ancillas) =
      tree.leaves + 2 * tree.internalNodes := by
  induction hlayout with
  | leaf label marker control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      rw [unaryIterationUnitary]
      simp only [eeaCnotCount_append]
      rw [ihZero, ihOne]
      simp only [computeZeroAnd_cnotCount]
      simp [eeaCnotCount, UnaryTree.leaves, UnaryTree.internalNodes]
      omega

/-- Constructor-derived coherent T count. -/
theorem unaryIterationUnitary_tCount
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    ShorECDLP.tCount (unaryIterationUnitary tree control ancillas) =
      14 * tree.internalNodes := by
  induction hlayout with
  | leaf label marker control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      rw [unaryIterationUnitary]
      simp only [tCount_append]
      rw [ihZero, ihOne]
      simp [computeZeroAnd, ShorECDLP.tCount, tCost,
        UnaryTree.internalNodes]
      omega

private def ZeroPathReady
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState) : Prop :=
  Clean rest state ∧ ZeroAndComputed control indexBit path state

private def OnePathReady
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState) : Prop :=
  Clean rest state ∧
    state path = (state control && state indexBit)

private theorem zeroPathReady_after_compute
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState)
    (hci : control ≠ indexBit) (hcp : control ≠ path)
    (hip : indexBit ≠ path) (hpathRest : path ∉ rest)
    (hclean : Clean (path :: rest) state) :
    ZeroPathReady control indexBit path rest
      (Classical.run (computeZeroAnd control indexBit path) state) := by
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

private theorem onePathReady_after_zero_toggle
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState)
    (hcp : control ≠ path) (hip : indexBit ≠ path)
    (hpathRest : path ∉ rest)
    (hready : ZeroPathReady control indexBit path rest state) :
    OnePathReady control indexBit path rest
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
  · unfold ZeroPathReady at hready
    unfold ZeroAndComputed at hready
    simp only [Classical.applyGate]
    cases hc : state control <;> cases hi : state indexBit <;>
      simp [upd, hcp, hip, hready.2, hc, hi]

private theorem zeroPathReady_after_one_toggle
    (control indexBit path : Wire) (rest : List Wire)
    (state : BasisState)
    (hcp : control ≠ path) (hip : indexBit ≠ path)
    (hpathRest : path ∉ rest)
    (hready : OnePathReady control indexBit path rest state) :
    ZeroPathReady control indexBit path rest
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
  · unfold OnePathReady at hready
    unfold ZeroAndComputed
    simp only [Classical.applyGate]
    cases hc : state control <;> cases hi : state indexBit <;>
      simp [upd, hcp, hip, hready.2, hc, hi]

private theorem coherent_mono
    {program : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid Stronger : BasisState → Prop}
    (hrefines : CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ state, Stronger state → Valid state) :
    CoherentlyImplementsOn program ideal Stronger := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch state hstate =>
    hbranch state (hsub state hstate)

/-- Normalize coherent sequential composition to the ordinary appended-circuit semantics. -/
private theorem coherent_seq_circuits
    {first second : AdaptiveCircuit}
    {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : CoherentlyImplementsOn first
      (Quantum.run firstCircuit) FirstValid)
    (hsecond : CoherentlyImplementsOn second
      (Quantum.run secondCircuit) SecondValid)
    (hfirstClassical : Classical.HPFree firstCircuit)
    (hvalid : ∀ state, FirstValid state →
      SecondValid (Classical.run firstCircuit state)) :
    CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have hseq := hfirst.seq hsecond (by
    intro state hstate
    rw [run_ket_agrees_classical firstCircuit state hfirstClassical]
    exact supportedOn_ket SecondValid _ (hvalid state hstate))
  apply hseq.congrIdeal
  intro state _
  exact (Quantum.run_append firstCircuit secondCircuit (ket state)).symm

private theorem unaryNode_protected_outputs
    (indexBit control path : Wire) (zero one : UnaryTree)
    (rest : List Wire)
    (hlocal :
      (control ::
        ((UnaryTree.node indexBit zero one).indexWires.dedup ++
          (path :: rest) ++
            (UnaryTree.node indexBit zero one).outputs)).Nodup) :
    control ∉ (UnaryTree.node indexBit zero one).outputs ∧
      indexBit ∉ (UnaryTree.node indexBit zero one).outputs ∧
      path ∉ (UnaryTree.node indexBit zero one).outputs ∧
      path ∉ rest := by
  have htail :
      ((UnaryTree.node indexBit zero one).indexWires.dedup ++
        ((path :: rest) ++
          (UnaryTree.node indexBit zero one).outputs)).Nodup := by
    simpa [List.append_assoc] using (List.nodup_cons.mp hlocal).2
  obtain ⟨_, hancOutputsNodup, hindexCross⟩ :=
    List.nodup_append.mp htail
  obtain ⟨hancillas, _, hancOutputCross⟩ :=
    List.nodup_append.mp hancOutputsNodup
  have hcontrolAll := (List.nodup_cons.mp hlocal).1
  have hindexMem : indexBit ∈
      (UnaryTree.node indexBit zero one).indexWires.dedup := by
    simp [UnaryTree.indexWires]
  refine ⟨?_, ?_, ?_, (List.nodup_cons.mp hancillas).1⟩
  · intro houtput
    apply hcontrolAll
    exact List.mem_append_right _ houtput
  · intro houtput
    exact (hindexCross indexBit hindexMem indexBit
      (List.mem_append_right (path :: rest) houtput)) rfl
  · intro houtput
    exact (hancOutputCross path (by simp) path houtput) rfl

/-- The measured traversal coherently implements the same routed-marker permutation as the
ordinary compute/uncompute tree. -/
theorem unaryIteration_coherent
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    CoherentlyImplementsOn
      (unaryIteration tree control ancillas)
      (Quantum.run (unaryIterationUnitary tree control ancillas))
      (Clean ancillas) := by
  induction hlayout with
  | leaf label marker control ancillas hlocal =>
      exact CoherentlyImplementsOn.unitary
        [.CX control marker] (Clean ancillas)
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip⟩ :=
        unaryNode_head_distinct indexBit control path zero one rest hlocal
      obtain ⟨hcontrolOutputs, hindexOutputs, hpathOutputs, hpathRest⟩ :=
        unaryNode_protected_outputs indexBit control path zero one rest hlocal
      have hcontrolZero : control ∉ zero.outputs := by
        intro hwire
        exact hcontrolOutputs (List.mem_append_left one.outputs hwire)
      have hcontrolOne : control ∉ one.outputs := by
        intro hwire
        exact hcontrolOutputs (List.mem_append_right zero.outputs hwire)
      have hindexZero : indexBit ∉ zero.outputs := by
        intro hwire
        exact hindexOutputs (List.mem_append_left one.outputs hwire)
      have hindexOne : indexBit ∉ one.outputs := by
        intro hwire
        exact hindexOutputs (List.mem_append_right zero.outputs hwire)
      have hpathZero : path ∉ zero.outputs := by
        intro hwire
        exact hpathOutputs (List.mem_append_left one.outputs hwire)
      have hpathOne : path ∉ one.outputs := by
        intro hwire
        exact hpathOutputs (List.mem_append_right zero.outputs hwire)
      have hzeroPreserves : ∀ state,
          ZeroPathReady control indexBit path rest state →
          ZeroPathReady control indexBit path rest
            (Classical.run
              (unaryIterationUnitary zero path rest) state) := by
        intro state hready
        refine ⟨unaryIterationUnitary_clean zero path rest state hzero
          hready.1, ?_⟩
        unfold ZeroPathReady at hready
        unfold ZeroAndComputed at hready ⊢
        rw [run_unaryIterationUnitary_eq_on zero path rest state hzero
          hready.1 path hpathZero]
        rw [run_unaryIterationUnitary_eq_on zero path rest state hzero
          hready.1 control hcontrolZero]
        rw [run_unaryIterationUnitary_eq_on zero path rest state hzero
          hready.1 indexBit hindexZero]
        exact hready.2
      have honePreserves : ∀ state,
          OnePathReady control indexBit path rest state →
          OnePathReady control indexBit path rest
            (Classical.run
              (unaryIterationUnitary one path rest) state) := by
        intro state hready
        refine ⟨unaryIterationUnitary_clean one path rest state hone
          hready.1, ?_⟩
        rw [run_unaryIterationUnitary_eq_on one path rest state hone
          hready.1 path hpathOne]
        rw [run_unaryIterationUnitary_eq_on one path rest state hone
          hready.1 control hcontrolOne]
        rw [run_unaryIterationUnitary_eq_on one path rest state hone
          hready.1 indexBit hindexOne]
        exact hready.2
      have herase : CoherentlyImplementsOn
          (eraseZeroAnd control indexBit path)
          (Quantum.run (computeZeroAnd control indexBit path))
          (ZeroPathReady control indexBit path rest) :=
        coherent_mono
          (eraseZeroAnd_coherent control indexBit path hci hcp hip)
          (fun _ hready => hready.2)
      have htoggleOne := CoherentlyImplementsOn.unitary
        [.CX control path] (OnePathReady control indexBit path rest)
      have hback := coherent_seq_circuits htoggleOne herase (by simp) (by
        intro state hready
        simpa only [Classical.run_cons, Classical.run_nil] using
          zeroPathReady_after_one_toggle control indexBit path rest state
            hcp hip hpathRest hready)
      have ihOneReady : CoherentlyImplementsOn
          (unaryIteration one path rest)
          (Quantum.run (unaryIterationUnitary one path rest))
          (OnePathReady control indexBit path rest) :=
        coherent_mono ihOne (fun _ hready => hready.1)
      have honeChunk := coherent_seq_circuits ihOneReady hback
        (unaryIterationUnitary_HPFree one path rest) honePreserves
      have htoggleZero := CoherentlyImplementsOn.unitary
        [.CX control path] (ZeroPathReady control indexBit path rest)
      have htoggleChunk := coherent_seq_circuits htoggleZero honeChunk
        (by simp) (by
          intro state hready
          simpa only [Classical.run_cons, Classical.run_nil] using
            onePathReady_after_zero_toggle control indexBit path rest state
              hcp hip hpathRest hready)
      have ihZeroReady : CoherentlyImplementsOn
          (unaryIteration zero path rest)
          (Quantum.run (unaryIterationUnitary zero path rest))
          (ZeroPathReady control indexBit path rest) :=
        coherent_mono ihZero (fun _ hready => hready.1)
      have hzeroChunk := coherent_seq_circuits ihZeroReady htoggleChunk
        (unaryIterationUnitary_HPFree zero path rest) hzeroPreserves
      have hcompute := CoherentlyImplementsOn.unitary
        (computeZeroAnd control indexBit path) (Clean (path :: rest))
      have hall := coherent_seq_circuits hcompute hzeroChunk
        (computeZeroAnd_HPFree control indexBit path)
        (fun state hclean => zeroPathReady_after_compute
          control indexBit path rest state hci hcp hip hpathRest hclean)
      simpa only [unaryIteration, unaryIterationUnitary,
        AdaptiveCircuit.seq, List.append_assoc] using hall

/-- Physical well-formedness of every adaptive branch. -/
theorem unaryIteration_wellFormed
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    (unaryIteration tree control ancillas).WellFormed := by
  induction hlayout with
  | leaf label marker control ancillas hlocal =>
      have hcm : control ≠ marker := by
        intro equality
        subst marker
        exact (List.nodup_cons.mp hlocal).1 (by simp)
      simp [unaryIteration, AdaptiveCircuit.WellFormed,
        CircuitWellFormed, Gate.WellFormed, hcm]
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      obtain ⟨hci, hcp, hip⟩ :=
        unaryNode_head_distinct indexBit control path zero one rest hlocal
      have hcompute :=
        computeZeroAnd_wellFormed control indexBit path hci hcp hip
      have htoggle : CircuitWellFormed [.CX control path] := by
        simp [CircuitWellFormed, Gate.WellFormed, hcp]
      have herase :=
        eraseZeroAnd_wellFormed control indexBit path hci hcp hip
      rw [unaryIteration]
      exact ⟨hcompute,
        AdaptiveCircuit.WellFormed.seq ihZero
          ⟨htoggle,
            AdaptiveCircuit.WellFormed.seq ihOne ⟨htoggle, herase⟩⟩⟩

private theorem adaptiveMeasurementCount_seq
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

private theorem adaptiveTCount_seq
    (first second : AdaptiveCircuit) :
    (first.seq second).tCount =
      first.tCount + second.tCount := by
  induction first with
  | done =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount, ih, Nat.add_assoc]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.tCount,
        ihFalse, ihTrue, Nat.add_max_add_right]

/-- Exactly one path-AND is measured at each internal decision node. -/
theorem unaryIteration_measurementCount
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    (unaryIteration tree control ancillas).measurementCount =
      tree.internalNodes := by
  induction hlayout with
  | leaf label marker control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      rw [unaryIteration]
      simp [AdaptiveCircuit.measurementCount, adaptiveMeasurementCount_seq,
        ihZero, ihOne, UnaryTree.internalNodes]
      omega

/-- Measurement removes the reverse Toffoli, leaving seven T gates per internal node. -/
theorem unaryIteration_tCount
    (tree : UnaryTree) (control : Wire) (ancillas : List Wire)
    (hlayout : tree.Layout control ancillas) :
    (unaryIteration tree control ancillas).tCount =
      7 * tree.internalNodes := by
  induction hlayout with
  | leaf label marker control ancillas hlocal => rfl
  | node indexBit control path zero one rest hlocal hzero hone ihZero ihOne =>
      rw [unaryIteration]
      simp [AdaptiveCircuit.tCount, adaptiveTCount_seq,
        ihZero, ihOne, UnaryTree.internalNodes, tCost]
      omega

end


end ShorECDLP.Paper2607_13816
