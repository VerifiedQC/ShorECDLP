import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf

/-!
# Cleanup of the paired interval traversals

The decreasing and increasing interval traversals are not syntactic adjoints: their arithmetic
leaves are the two halves of a Cuccaro cell, and the source visits the tree in opposite orders.
This module proves the semantic invariant needed at the complete interval boundary: after the
paired traversals, only the per-label target lanes may differ from the input state.  The proof is
valid for dirty arithmetic state and therefore composes across the source's intervening sign
update.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

/-- No gate of `circuit` mentions any wire in `protectedWires`. -/
def PaperCircuitAvoids (protectedWires : List Wire) (circuit : Circuit) : Prop :=
  ∀ gate ∈ circuit, ∀ wire ∈ gateWires gate, wire ∉ protectedWires

namespace PaperCircuitAvoids

private theorem append
    {protectedWires : List Wire} {first second : Circuit}
    (hfirst : PaperCircuitAvoids protectedWires first)
    (hsecond : PaperCircuitAvoids protectedWires second) :
    PaperCircuitAvoids protectedWires (first ++ second) := by
  intro gate hgate wire hwire
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact hfirst gate hgate wire hwire
  · exact hsecond gate hgate wire hwire

/-- A circuit confined to a support disjoint from the protected interface avoids that interface. -/
theorem ofUsesOnly
    {protectedWires support : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly support circuit)
    (hdisjoint : List.Disjoint protectedWires support) :
    PaperCircuitAvoids protectedWires circuit := by
  rw [List.disjoint_left] at hdisjoint
  intro gate hgate wire hwire hprotected
  exact hdisjoint hprotected (huses gate hgate wire hwire)

private theorem adjoint
    {protectedWires : List Wire} {circuit : Circuit}
    (havoid : PaperCircuitAvoids protectedWires circuit) :
    PaperCircuitAvoids protectedWires circuit.adjoint := by
  induction circuit with
  | nil => simp [Circuit.adjoint, PaperCircuitAvoids]
  | cons gate circuit ih =>
      rw [circuit_adjoint_cons]
      have htail : PaperCircuitAvoids protectedWires circuit := by
        intro next hnext
        exact havoid next (by simp [hnext])
      apply append (ih htail)
      intro next hnext wire hwire
      have hnext : next = gate.adjoint := by simpa using hnext
      subst next
      have horiginal := havoid gate (by simp) wire
      cases gate <;> exact horiginal (by simpa [gateWires] using hwire)

/-- A circuit disjoint from an interface transports equality away from that interface. -/
theorem run_agreesOutside
    {protectedWires : List Wire} {circuit : Circuit}
    (havoid : PaperCircuitAvoids protectedWires circuit)
    {left right : BasisState}
    (hagree : AgreesOutside protectedWires left right) :
    AgreesOutside protectedWires (run circuit left) (run circuit right) := by
  induction circuit generalizing left right with
  | nil => exact hagree
  | cons gate circuit ih =>
      have hgate : ∀ wire ∈ gateWires gate, wire ∉ protectedWires :=
        havoid gate (by simp)
      have htail : PaperCircuitAvoids protectedWires circuit := by
        intro next hnext
        exact havoid next (by simp [hnext])
      apply ih htail
      intro wire hwire
      cases gate with
      | X target =>
          by_cases hwt : wire = target
          · subst wire
            simp [Classical.applyGate, upd,
              hagree target (hgate target (by simp [gateWires]))]
          · simpa [Classical.applyGate, upd, hwt] using hagree wire hwire
      | H target => exact hagree wire hwire
      | CX control target =>
          by_cases hwt : wire = target
          · subst wire
            simp [Classical.applyGate, upd,
              hagree target (hgate target (by simp [gateWires])),
              hagree control (hgate control (by simp [gateWires]))]
          · simpa [Classical.applyGate, upd, hwt] using hagree wire hwire
      | CCX first second target =>
          by_cases hwt : wire = target
          · subst wire
            simp [Classical.applyGate, upd,
              hagree target (hgate target (by simp [gateWires])),
              hagree first (hgate first (by simp [gateWires])),
              hagree second (hgate second (by simp [gateWires]))]
          · simpa [Classical.applyGate, upd, hwt] using hagree wire hwire
      | P direction exponent target => exact hagree wire hwire

end PaperCircuitAvoids

private theorem agreesOutside_append_trans
    {first second : List Wire} {left middle right : BasisState}
    (hleft : AgreesOutside first left middle)
    (hright : AgreesOutside second middle right) :
    AgreesOutside (first ++ second) left right := by
  intro wire hwire
  simp only [List.mem_append, not_or] at hwire
  rw [hleft wire hwire.1, hright wire hwire.2]

private theorem PaperCircuitAvoids.frame
    {protectedWires : List Wire} {before middle after : Circuit}
    (hafter : after = before.adjoint)
    (hbefore : PaperCircuitAvoids protectedWires before)
    (hmiddle : ∀ state, AgreesOutside protectedWires (run middle state) state)
    (hwellFormed : CircuitWellFormed before) :
    ∀ state, AgreesOutside protectedWires
      (run (before ++ middle ++ after) state) state := by
  intro state
  simp only [Classical.run_append]
  have htransport := hbefore.adjoint.run_agreesOutside (hmiddle (run before state))
  have hadjoint := run_adjoint_run_classical before hwellFormed state
  intro wire hwire
  rw [hafter]
  rw [htransport wire hwire]
  exact congrFun hadjoint wire

private theorem PaperCircuitAvoids.nest
    {innerWires outerWires : List Wire}
    {outerFirst inner outerSecond : Circuit}
    (hinner : ∀ state, AgreesOutside innerWires (run inner state) state)
    (houter : ∀ state, AgreesOutside outerWires
      (run (outerFirst ++ outerSecond) state) state)
    (hsecond : PaperCircuitAvoids innerWires outerSecond) :
    ∀ state, AgreesOutside (innerWires ++ outerWires)
      (run (outerFirst ++ inner ++ outerSecond) state) state := by
  intro state
  simp only [Classical.run_append]
  have htransport := hsecond.run_agreesOutside (hinner (run outerFirst state))
  exact agreesOutside_append_trans htransport (by
    simpa only [Classical.run_append] using houter state)

private theorem rippleCell_pair_preserves
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (state : BasisState)
    (hlayout : [control, target, addend, carry, scratch].Nodup) :
    let after := run (rippleSecondCell mode control target addend carry scratch)
      (run (rippleFirstCell mode control target addend carry scratch) state)
    after control = state control ∧ after addend = state addend ∧
      after carry = state carry ∧ after scratch = state scratch := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hlayout
  rcases hlayout with
    ⟨⟨hcontrolTarget, hcontrolAddend, hcontrolCarry, hcontrolScratch⟩,
      ⟨⟨htargetAddend, htargetCarry, htargetScratch⟩,
        ⟨⟨haddendCarry, haddendScratch⟩, ⟨hcarryScratch, _⟩⟩⟩⟩
  cases mode <;> cases hc : state control <;> cases ht : state target <;>
    cases ha : state addend <;> cases hcarry : state carry <;>
    cases hscratch : state scratch <;>
    simp [rippleFirstCell, rippleSecondCell, controlledMaj, controlledUma,
      controlledUmaInv, controlledMajInv, cleanC3X, Classical.run,
      Classical.applyGate, upd, hcontrolTarget, hcontrolAddend,
      hcontrolCarry, hcontrolScratch, htargetAddend, htargetCarry,
      htargetScratch, haddendCarry, haddendScratch, hcarryScratch,
      Ne.symm htargetAddend, Ne.symm htargetCarry,
      Ne.symm htargetScratch, Ne.symm haddendCarry, Ne.symm haddendScratch,
      Ne.symm hcarryScratch, hc, ht, ha, hcarry, hscratch]

/-- The source's first and second Cuccaro half-cells restore every wire except their target,
without assuming that the shared v-chain scratch starts clean. -/
private theorem rippleCell_pair_preservesOutsideTarget
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (state : BasisState)
    (hlayout : [control, target, addend, carry, scratch].Nodup) :
    AgreesOutside [target]
      (run (rippleFirstCell mode control target addend carry scratch ++
        rippleSecondCell mode control target addend carry scratch) state)
      state := by
  intro wire hwire
  simp only [List.mem_singleton] at hwire
  have hpair := rippleCell_pair_preserves mode control target addend carry scratch
    state hlayout
  simp only [Classical.run_append] at hpair ⊢
  by_cases hcontrol : wire = control
  · subst wire
    exact hpair.1
  · by_cases haddend : wire = addend
    · subst wire
      exact hpair.2.1
    · by_cases hcarry : wire = carry
      · subst wire
        exact hpair.2.2.1
      · by_cases hscratch : wire = scratch
        · subst wire
          exact hpair.2.2.2
        · simpa only [Classical.run_append] using
            (PaperCircuitUsesOnly.append
              (rippleFirstCell_usesOnly mode control target addend carry scratch)
              (rippleSecondCell_usesOnly mode control target addend carry scratch)).preservesOutside
                state (by simp [hcontrol, hwire, haddend, hcarry, hscratch])

private theorem run_toggleEqConstUnderControl_twice_cleanup
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (state : BasisState)
    (hlayout : EqControlLayout root register accumulator flag scratches)
    (hclean : Clean (flag :: scratches) state) :
    run (toggleEqConstUnderControl root register value accumulator flag scratches)
        (run (toggleEqConstUnderControl root register value accumulator flag scratches)
          state) = state := by
  let circuit := toggleEqConstUnderControl root register value accumulator flag scratches
  let after := run circuit state
  have hfirst : after =
      state[accumulator ↦ Bool.xor (state accumulator)
        (state root && registerMatches register value state)] := by
    exact run_toggleEqConstUnderControl root register value accumulator flag scratches
      state hlayout hclean
  have hcleanAfter : Clean (flag :: scratches) after := by
    exact toggleEqConstUnderControl_clean root register value accumulator flag scratches
      state hlayout hclean
  have hsecond := run_toggleEqConstUnderControl root register value accumulator flag scratches
    after hlayout hcleanAfter
  change run circuit after = state
  rw [hsecond, hfirst]
  have haccRoot : accumulator ≠ root := by
    intro h
    subst root
    simpa using (List.nodup_cons.mp hlayout.2).1
  have haccRegister : accumulator ∉ register := by
    intro h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hlayout.2).2).1 (by simp [h])
  have hmatch :
      registerMatches register value
          state[accumulator ↦ Bool.xor (state accumulator)
            (state root && registerMatches register value state)] =
        registerMatches register value state := by
    exact registerMatchesFrom_upd_not_mem register value 0 state accumulator _
      haccRegister
  funext wire
  by_cases hwire : wire = accumulator
  · subst wire
    simp [upd, Ne.symm haccRoot, hmatch]
  · simp [upd, hwire]

/-- The separately handled top lane restores every wire except its target.  The equality work
starts clean, while the extra premise records the concrete allocator fact that the top target is
outside the enclosing right-equality selector. -/
theorem topSpecialLeaf_pair_preservesOutsideTarget
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (state : BasisState)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches)
    (hclean : Clean (eqFlag :: eqScratches) state)
    (htargetRight : target ∉
      (rightRoot :: accumulator :: rightRegister ++ eqFlag :: eqScratches)) :
    AgreesOutside [target]
      (run (topSpecialFirstLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch eqFlag eqScratches
          rightRoot leftRoot ++
        topSpecialSecondLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch eqFlag eqScratches
          rightRoot leftRoot) state)
      state := by
  have heqFlag : eqFlag = rippleScratch := hlayout.2.2.2.1
  subst eqFlag
  let right := toggleEqConstUnderControl rightRoot rightRegister topValue
    accumulator rippleScratch eqScratches
  let left := toggleEqConstUnderControl leftRoot leftRegister topValue
    accumulator rippleScratch eqScratches
  let firstCell := rippleFirstCell mode accumulator target addend carry rippleScratch
  let secondCell := rippleSecondCell mode accumulator target addend carry rippleScratch
  let afterRight := run right state
  let afterFirstCell := run firstCell afterRight
  have hrightClean : Clean (rippleScratch :: eqScratches) afterRight := by
    exact toggleEqConstUnderControl_clean rightRoot rightRegister topValue accumulator
      rippleScratch eqScratches state hlayout.1 hclean
  have hafterFirstCellClean :
      Clean (rippleScratch :: eqScratches) afterFirstCell := by
    intro wire hwire
    rcases List.mem_cons.mp hwire with hsame | hwire
    · subst wire
      change run (rippleFirstCell mode accumulator target addend carry rippleScratch)
          afterRight rippleScratch = false
      rw [rippleFirstCell_preservesScratch mode accumulator target addend carry
        rippleScratch afterRight hlayout.2.2.1]
      exact hrightClean rippleScratch (by simp)
    · have hdisjoint := hlayout.2.2.2.2
      rw [List.disjoint_left] at hdisjoint
      change run (rippleFirstCell mode accumulator target addend carry rippleScratch)
          afterRight wire = false
      rw [(rippleFirstCell_usesOnly mode accumulator target addend carry
        rippleScratch).preservesOutside afterRight (hdisjoint hwire)]
      exact hrightClean wire (by simp [hwire])
  have hleftCancel : run left (run left afterFirstCell) = afterFirstCell := by
    exact run_toggleEqConstUnderControl_twice_cleanup leftRoot leftRegister topValue
      accumulator rippleScratch eqScratches afterFirstCell hlayout.2.1
      hafterFirstCellClean
  have hrightCancel : run right (run right state) = state := by
    exact run_toggleEqConstUnderControl_twice_cleanup rightRoot rightRegister topValue
      accumulator rippleScratch eqScratches state hlayout.1 hclean
  have hcellPair : AgreesOutside [target]
      (run (firstCell ++ secondCell) afterRight) afterRight := by
    exact rippleCell_pair_preservesOutsideTarget mode accumulator target addend carry
      rippleScratch afterRight hlayout.2.2.1
  have hrightAvoids : PaperCircuitAvoids [target] right := by
    apply PaperCircuitAvoids.ofUsesOnly
      (toggleEqConstUnderControl_usesOnly rightRoot rightRegister topValue accumulator
        rippleScratch eqScratches)
    rw [List.disjoint_left]
    intro wire hwire hsupport
    simp only [List.mem_singleton] at hwire
    subst wire
    exact htargetRight hsupport
  have htransport := hrightAvoids.run_agreesOutside hcellPair
  have hactual :
      run (topSpecialFirstLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch rippleScratch eqScratches
          rightRoot leftRoot ++
        topSpecialSecondLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch rippleScratch eqScratches
          rightRoot leftRoot) state =
        run right (run (firstCell ++ secondCell) (run right state)) := by
    simp only [topSpecialFirstLeaf, topSpecialSecondLeaf, Classical.run_append]
    rw [hleftCancel]
  intro wire hwire
  have htransportWire := htransport wire hwire
  simp only [Classical.run_append] at htransportWire
  rw [hrightCancel] at htransportWire
  rw [hactual]
  simpa only [right, firstCell, secondCell, afterRight, Classical.run_append] using
    htransportWire

@[simp]
private theorem endpointLeafToggle_adjoint
    (topSpecial : Bool) (label : Nat)
    (endpointTop control accumulator : Wire) :
    (endpointLeafToggle topSpecial label endpointTop control accumulator).adjoint =
      endpointLeafToggle topSpecial label endpointTop control accumulator := by
  by_cases hmasked : maskedZeroLeaf topSpecial label <;>
    simp [endpointLeafToggle, hmasked, Circuit.adjoint]

private theorem run_endpointLeafToggle_twice
    (topSpecial : Bool) (label : Nat)
    (endpointTop control accumulator : Wire) (state : BasisState)
    (hlayout : [control, endpointTop, accumulator].Nodup) :
    run (endpointLeafToggle topSpecial label endpointTop control accumulator)
        (run (endpointLeafToggle topSpecial label endpointTop control accumulator) state) =
      state := by
  simpa only [endpointLeafToggle_adjoint] using
    (run_adjoint_run_classical
      (endpointLeafToggle topSpecial label endpointTop control accumulator)
      (endpointLeafToggle_wellFormed topSpecial label endpointTop control accumulator hlayout)
      state)

private theorem intervalLeaf_pair_preservesOutsideTarget
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    AgreesOutside [target]
      (run (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl ++
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl) state)
      state := by
  unfold IntervalLeafLayout intervalLeafSupport at hlayout
  obtain ⟨hcontrols, hroles, hcross⟩ := List.nodup_append.mp hlayout
  have hrightMem : rightControl ∈ [rightControl, leftControl].dedup := by simp
  have hleftMem : leftControl ∈ [rightControl, leftControl].dedup := by simp
  have hrightLayout : [rightControl, rightTop, accumulator].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    refine ⟨⟨hcross rightControl hrightMem rightTop (by simp),
      hcross rightControl hrightMem accumulator (by simp)⟩, ?_⟩
    constructor
    · intro equality
      exact (List.nodup_cons.mp hroles).1 (by simp [equality])
    · trivial
  have hleftLayout : [leftControl, leftTop, accumulator].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    refine ⟨⟨hcross leftControl hleftMem leftTop (by simp),
      hcross leftControl hleftMem accumulator (by simp)⟩, ?_⟩
    constructor
    · intro equality
      exact (List.nodup_cons.mp (List.nodup_cons.mp hroles).2).1
        (by simp [equality])
    · trivial
  have hcell : [accumulator, target, addend, carry, scratch].Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp hroles).2).2
  have htargetRightControl : target ≠ rightControl :=
    Ne.symm (hcross rightControl hrightMem target (by simp))
  have htargetLeftControl : target ≠ leftControl :=
    Ne.symm (hcross leftControl hleftMem target (by simp))
  have htargetRightTop : target ≠ rightTop := by
    intro equality
    exact (List.nodup_cons.mp hroles).1 (by simp [equality])
  have htargetLeftTop : target ≠ leftTop := by
    intro equality
    exact (List.nodup_cons.mp (List.nodup_cons.mp hroles).2).1
      (by simp [equality])
  have htargetAccumulator : target ≠ accumulator := by
    intro equality
    exact (List.nodup_cons.mp hcell).1 (by simp [equality])
  let right := endpointLeafToggle topSpecial label rightTop rightControl accumulator
  let left := endpointLeafToggle topSpecial label leftTop leftControl accumulator
  let firstCell := rippleFirstCell mode accumulator target addend carry scratch
  let secondCell := rippleSecondCell mode accumulator target addend carry scratch
  have hleftCancel : ∀ next, run left (run left next) = next := by
    intro next
    exact run_endpointLeafToggle_twice topSpecial label leftTop leftControl
      accumulator next hleftLayout
  have hrightCancel : run right (run right state) = state :=
    run_endpointLeafToggle_twice topSpecial label rightTop rightControl
      accumulator state hrightLayout
  have hcellPair : AgreesOutside [target]
      (run (firstCell ++ secondCell) (run right state)) (run right state) :=
    rippleCell_pair_preservesOutsideTarget mode accumulator target addend carry
      scratch (run right state) hcell
  have hrightAvoids : PaperCircuitAvoids [target] right := by
    apply PaperCircuitAvoids.ofUsesOnly
      (endpointLeafToggle_usesOnly topSpecial label rightTop rightControl accumulator)
    rw [List.disjoint_left]
    intro wire hwire hsupport
    simp only [List.mem_singleton] at hwire
    subst wire
    simp [htargetRightControl, htargetRightTop, htargetAccumulator] at hsupport
  have htransport := hrightAvoids.run_agreesOutside hcellPair
  have hactual :
      run (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl ++
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl) state =
        run right (run (firstCell ++ secondCell) (run right state)) := by
    simp only [intervalFirstLeaf, intervalSecondLeaf, Classical.run_append]
    rw [hleftCancel]
  intro wire hwire
  have htransportWire := htransport wire hwire
  simp only [Classical.run_append] at htransportWire
  rw [hrightCancel] at htransportWire
  rw [hactual]
  simpa only [right, firstCell, secondCell, Classical.run_append] using htransportWire

private theorem run_run_adjoint_classical
    (circuit : Circuit) (hwellFormed : CircuitWellFormed circuit)
    (state : BasisState) :
    run circuit (run circuit.adjoint state) = state := by
  have hadjoint : CircuitWellFormed circuit.adjoint :=
    (circuitWellFormed_adjoint circuit).mpr hwellFormed
  have hinverse := run_adjoint_run_classical circuit.adjoint hadjoint state
  simpa [circuit_adjoint_adjoint] using hinverse

@[simp]
private theorem computeZeroAnd_adjoint
    (control indexBit target : Wire) :
    (computeZeroAnd control indexBit target).adjoint =
      computeZeroAnd control indexBit target := by
  simp [computeZeroAnd, Circuit.adjoint]

private theorem dualZero_decoder_subset
    (indexBitA indexBitB controlA controlB pathA pathB : Wire)
    (zero one : DualUnaryActionTree) (restA restB : List Wire) :
    ∀ wire,
      wire ∈ zero.decoderWires pathA pathB restA restB →
        wire ∈ (DualUnaryActionTree.node indexBitA indexBitB zero one).decoderWires
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
      wire ∈ one.decoderWires pathA pathB restA restB →
        wire ∈ (DualUnaryActionTree.node indexBitA indexBitB zero one).decoderWires
          controlA controlB (pathA :: restA) (pathB :: restB) := by
  intro wire hwire
  simp only [DualUnaryActionTree.decoderWires, List.mem_append,
    List.mem_dedup, DualUnaryActionTree.indexAWires,
    DualUnaryActionTree.indexBWires, List.mem_cons] at hwire ⊢
  aesop

/-- A dual traversal is disjoint from a protected interface when its decoder and every reachable
leaf are disjoint from that interface. -/
theorem dualUnaryActionUnitary_avoids
    (order : UnaryOrder) (leafAction : Nat → Wire → Wire → Circuit)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB protectedWires : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hdecoder : ∀ wire,
      wire ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        wire ∉ protectedWires)
    (hleaf : ∀ label, label ∈ tree.labels →
      ∀ childA, childA ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
      ∀ childB, childB ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
        PaperCircuitAvoids protectedWires (leafAction label childA childB)) :
    PaperCircuitAvoids protectedWires
      (dualUnaryActionUnitary order leafAction tree
        controlA controlB ancillasA ancillasB) := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal =>
      exact hleaf label (by simp [DualUnaryActionTree.labels]) controlA
        (by simp [DualUnaryActionTree.decoderWires]) controlB
        (by simp [DualUnaryActionTree.decoderWires])
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      have hcontrolA := hdecoder controlA (by
        simp [DualUnaryActionTree.decoderWires])
      have hcontrolB := hdecoder controlB (by
        simp [DualUnaryActionTree.decoderWires])
      have hindexA := hdecoder indexBitA (by
        simp [DualUnaryActionTree.decoderWires,
          DualUnaryActionTree.indexAWires])
      have hindexB := hdecoder indexBitB (by
        simp [DualUnaryActionTree.decoderWires,
          DualUnaryActionTree.indexBWires])
      have hpathA := hdecoder pathA (by
        simp [DualUnaryActionTree.decoderWires])
      have hpathB := hdecoder pathB (by
        simp [DualUnaryActionTree.decoderWires])
      have hzeroSubset : ∀ wire,
          wire ∈ zero.decoderWires pathA pathB restA restB →
            wire ∈ (DualUnaryActionTree.node indexBitA indexBitB zero one).decoderWires
              controlA controlB (pathA :: restA) (pathB :: restB) :=
        dualZero_decoder_subset indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB
      have honeSubset : ∀ wire,
          wire ∈ one.decoderWires pathA pathB restA restB →
            wire ∈ (DualUnaryActionTree.node indexBitA indexBitB zero one).decoderWires
              controlA controlB (pathA :: restA) (pathB :: restB) :=
        dualOne_decoder_subset indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB
      have hzeroLeaf : ∀ label, label ∈ zero.labels →
          ∀ childA, childA ∈ zero.decoderWires pathA pathB restA restB →
          ∀ childB, childB ∈ zero.decoderWires pathA pathB restA restB →
            PaperCircuitAvoids protectedWires (leafAction label childA childB) := by
        intro label hlabel childA hchildA childB hchildB
        exact hleaf label (by simp [DualUnaryActionTree.labels, hlabel])
          childA (hzeroSubset childA hchildA) childB (hzeroSubset childB hchildB)
      have honeLeaf : ∀ label, label ∈ one.labels →
          ∀ childA, childA ∈ one.decoderWires pathA pathB restA restB →
          ∀ childB, childB ∈ one.decoderWires pathA pathB restA restB →
            PaperCircuitAvoids protectedWires (leafAction label childA childB) := by
        intro label hlabel childA hchildA childB hchildB
        exact hleaf label (by simp [DualUnaryActionTree.labels, hlabel])
          childA (honeSubset childA hchildA) childB (honeSubset childB hchildB)
      have hcomputeA : PaperCircuitAvoids protectedWires
          (computeZeroAnd controlA indexBitA pathA) := by
        simp [PaperCircuitAvoids, computeZeroAnd, gateWires,
          hcontrolA, hindexA, hpathA]
      have hcomputeB : PaperCircuitAvoids protectedWires
          (computeZeroAnd controlB indexBitB pathB) := by
        simp [PaperCircuitAvoids, computeZeroAnd, gateWires,
          hcontrolB, hindexB, hpathB]
      have hforward : PaperCircuitAvoids protectedWires
          ([.CX controlA pathA, .CX controlB pathB] : Circuit) := by
        simp [PaperCircuitAvoids, gateWires,
          hcontrolA, hcontrolB, hpathA, hpathB]
      have hreverse : PaperCircuitAvoids protectedWires
          ([.CX controlB pathB, .CX controlA pathA] : Circuit) := by
        simp [PaperCircuitAvoids, gateWires,
          hcontrolA, hcontrolB, hpathA, hpathB]
      have hzero := ihZero (fun wire hwire ↦ hdecoder wire (hzeroSubset wire hwire))
        hzeroLeaf
      have hone := ihOne (fun wire hwire ↦ hdecoder wire (honeSubset wire hwire))
        honeLeaf
      cases order with
      | inc =>
          simp only [dualUnaryActionUnitary]
          repeat' apply PaperCircuitAvoids.append
          all_goals assumption
      | dec =>
          simp only [dualUnaryActionUnitary]
          repeat' apply PaperCircuitAvoids.append
          all_goals assumption

private theorem dualUnaryActionUnitary_pair_preservesOutside
    (firstLeaf secondLeaf : Nat → Wire → Wire → Circuit)
    (targetAt : Nat → Wire)
    (tree : DualUnaryActionTree) (controlA controlB : Wire)
    (ancillasA ancillasB : List Wire)
    (hlayout : tree.Layout controlA controlB ancillasA ancillasB)
    (hlabels : tree.labels.Nodup)
    (htargetDecoder : ∀ label, label ∈ tree.labels →
      targetAt label ∉ tree.decoderWires controlA controlB ancillasA ancillasB)
    (hpair : ∀ label, label ∈ tree.labels →
      ∀ childA, childA ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
      ∀ childB, childB ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
      ∀ state, AgreesOutside [targetAt label]
        (run (firstLeaf label childA childB ++ secondLeaf label childA childB) state)
        state)
    (hsecondCross : ∀ label, label ∈ tree.labels →
      ∀ childA, childA ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
      ∀ childB, childB ∈ tree.decoderWires controlA controlB ancillasA ancillasB →
      ∀ other, other ∈ tree.labels → other ≠ label →
        PaperCircuitAvoids [targetAt other] (secondLeaf label childA childB)) :
    ∀ state, AgreesOutside (tree.labels.map targetAt)
      (run (dualUnaryActionUnitary .dec firstLeaf tree controlA controlB ancillasA ancillasB ++
        dualUnaryActionUnitary .inc secondLeaf tree controlA controlB ancillasA ancillasB) state)
      state := by
  induction hlayout with
  | leaf label controlA controlB ancillasA ancillasB hlocal =>
      intro state
      simpa [dualUnaryActionUnitary, DualUnaryActionTree.labels] using
        hpair label (by simp [DualUnaryActionTree.labels]) controlA
          (by simp [DualUnaryActionTree.decoderWires]) controlB
          (by simp [DualUnaryActionTree.decoderWires]) state
  | node indexBitA indexBitB controlA controlB pathA pathB
      zero one restA restB hlocal hzero hone ihZero ihOne =>
      intro state
      have hzeroSubset : ∀ wire,
          wire ∈ zero.decoderWires pathA pathB restA restB →
            wire ∈ (DualUnaryActionTree.node indexBitA indexBitB zero one).decoderWires
              controlA controlB (pathA :: restA) (pathB :: restB) :=
        dualZero_decoder_subset indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB
      have honeSubset : ∀ wire,
          wire ∈ one.decoderWires pathA pathB restA restB →
            wire ∈ (DualUnaryActionTree.node indexBitA indexBitB zero one).decoderWires
              controlA controlB (pathA :: restA) (pathB :: restB) :=
        dualOne_decoder_subset indexBitA indexBitB controlA controlB pathA pathB
          zero one restA restB
      have hzeroNodup : zero.labels.Nodup :=
        (List.nodup_append.mp (by simpa [DualUnaryActionTree.labels] using hlabels)).1
      have honeNodup : one.labels.Nodup :=
        (List.nodup_append.mp (by simpa [DualUnaryActionTree.labels] using hlabels)).2.1
      have hlabelCross :=
        (List.nodup_append.mp (by simpa [DualUnaryActionTree.labels] using hlabels)).2.2
      have hlabelDisjoint : List.Disjoint zero.labels one.labels := by
        rw [List.disjoint_left]
        intro left hleft hright
        exact hlabelCross left hleft left hright rfl
      have hzeroTargetDecoder : ∀ label, label ∈ zero.labels →
          targetAt label ∉ zero.decoderWires pathA pathB restA restB := by
        intro label hlabel hwire
        exact htargetDecoder label (by
          simp [DualUnaryActionTree.labels, hlabel]) (hzeroSubset _ hwire)
      have honeTargetDecoder : ∀ label, label ∈ one.labels →
          targetAt label ∉ one.decoderWires pathA pathB restA restB := by
        intro label hlabel hwire
        exact htargetDecoder label (by
          simp [DualUnaryActionTree.labels, hlabel]) (honeSubset _ hwire)
      have hzeroPair := ihZero hzeroNodup hzeroTargetDecoder
        (fun label hlabel childA hchildA childB hchildB next ↦
          hpair label (by simp [DualUnaryActionTree.labels, hlabel])
            childA (hzeroSubset childA hchildA) childB
            (hzeroSubset childB hchildB) next)
        (fun label hlabel childA hchildA childB hchildB other hother hne ↦
          hsecondCross label (by simp [DualUnaryActionTree.labels, hlabel])
            childA (hzeroSubset childA hchildA) childB
            (hzeroSubset childB hchildB) other
            (by simp [DualUnaryActionTree.labels, hother]) hne)
      have honePair := ihOne honeNodup honeTargetDecoder
        (fun label hlabel childA hchildA childB hchildB next ↦
          hpair label (by simp [DualUnaryActionTree.labels, hlabel])
            childA (honeSubset childA hchildA) childB
            (honeSubset childB hchildB) next)
        (fun label hlabel childA hchildA childB hchildB other hother hne ↦
          hsecondCross label (by simp [DualUnaryActionTree.labels, hlabel])
            childA (honeSubset childA hchildA) childB
            (honeSubset childB hchildB) other
            (by simp [DualUnaryActionTree.labels, hother]) hne)
      let zeroTargets := zero.labels.map targetAt
      let oneTargets := one.labels.map targetAt
      let allTargets := zeroTargets ++ oneTargets
      let compute := computeZeroAnd controlA indexBitA pathA ++
        computeZeroAnd controlB indexBitB pathB
      let toggle : Circuit := [.CX controlA pathA, .CX controlB pathB]
      let firstZero := dualUnaryActionUnitary .dec firstLeaf zero
        pathA pathB restA restB
      let firstOne := dualUnaryActionUnitary .dec firstLeaf one
        pathA pathB restA restB
      let secondZero := dualUnaryActionUnitary .inc secondLeaf zero
        pathA pathB restA restB
      let secondOne := dualUnaryActionUnitary .inc secondLeaf one
        pathA pathB restA restB
      have hdecoderAvoid : ∀ wire,
          wire ∈ (DualUnaryActionTree.node indexBitA indexBitB zero one).decoderWires
              controlA controlB (pathA :: restA) (pathB :: restB) →
            wire ∉ allTargets := by
        intro wire hwire htarget
        simp only [allTargets, zeroTargets, oneTargets, List.mem_append,
          List.mem_map] at htarget
        rcases htarget with ⟨label, hlabel, rfl⟩ | ⟨label, hlabel, rfl⟩
        · exact htargetDecoder label (by
            simp [DualUnaryActionTree.labels, hlabel]) hwire
        · exact htargetDecoder label (by
            simp [DualUnaryActionTree.labels, hlabel]) hwire
      have hdecoderAvoids : PaperCircuitAvoids allTargets compute := by
        simp only [compute]
        apply PaperCircuitAvoids.append
        · simp [PaperCircuitAvoids, computeZeroAnd, gateWires,
            hdecoderAvoid controlA (by simp [DualUnaryActionTree.decoderWires]),
            hdecoderAvoid indexBitA (by simp [DualUnaryActionTree.decoderWires,
              DualUnaryActionTree.indexAWires]),
            hdecoderAvoid pathA (by simp [DualUnaryActionTree.decoderWires])]
        · simp [PaperCircuitAvoids, computeZeroAnd, gateWires,
            hdecoderAvoid controlB (by simp [DualUnaryActionTree.decoderWires]),
            hdecoderAvoid indexBitB (by simp [DualUnaryActionTree.decoderWires,
              DualUnaryActionTree.indexBWires]),
            hdecoderAvoid pathB (by simp [DualUnaryActionTree.decoderWires])]
      have htoggleAvoids : PaperCircuitAvoids allTargets toggle := by
        simp [PaperCircuitAvoids, toggle, gateWires,
          hdecoderAvoid controlA (by simp [DualUnaryActionTree.decoderWires]),
          hdecoderAvoid controlB (by simp [DualUnaryActionTree.decoderWires]),
          hdecoderAvoid pathA (by simp [DualUnaryActionTree.decoderWires]),
          hdecoderAvoid pathB (by simp [DualUnaryActionTree.decoderWires])]
      have hsecondOneAvoidsZero : PaperCircuitAvoids zeroTargets secondOne := by
        apply dualUnaryActionUnitary_avoids .inc secondLeaf one pathA pathB
          restA restB zeroTargets hone
        · intro wire hwire
          have hwireRoot := honeSubset wire hwire
          intro hprotected
          simp only [zeroTargets, List.mem_map] at hprotected
          obtain ⟨label, hlabel, rfl⟩ := hprotected
          exact htargetDecoder label (by
            simp [DualUnaryActionTree.labels, hlabel]) hwireRoot
        · intro label hlabel childA hchildA childB hchildB gate hgate wire hwire
            hprotected
          simp only [zeroTargets, List.mem_map] at hprotected
          obtain ⟨other, hother, rfl⟩ := hprotected
          have hne : other ≠ label := by
            intro equality
            subst other
            exact hlabelDisjoint hother hlabel
          exact hsecondCross label (by
              simp [DualUnaryActionTree.labels, hlabel])
            childA (honeSubset childA hchildA) childB
            (honeSubset childB hchildB) other
            (by simp [DualUnaryActionTree.labels, hother]) hne gate hgate
              (targetAt other) hwire (by simp)
      obtain ⟨hca, hcpa, hia, hcb, hcpb, hib, _, _, _, _, _, _, _, _, _⟩ :=
        DualUnaryActionTree.Layout.nodeParts indexBitA indexBitB controlA controlB
          pathA pathB zero one restA restB hlocal
      have hcomputeWF : CircuitWellFormed compute := by
        simp only [compute, circuitWellFormed_append]
        exact ⟨computeZeroAnd_wellFormed controlA indexBitA pathA hca hcpa hia,
          computeZeroAnd_wellFormed controlB indexBitB pathB hcb hcpb hib⟩
      have htoggleWF : CircuitWellFormed toggle := by
        simp [toggle, CircuitWellFormed, Gate.WellFormed, hcpa, hcpb]
      have hzeroFrame : ∀ next, AgreesOutside zeroTargets
          (run (firstZero ++ secondZero) next) next := by
        simpa [firstZero, secondZero, zeroTargets] using hzeroPair
      have honeFrame : ∀ next, AgreesOutside oneTargets
          (run (firstOne ++ secondOne) next) next := by
        simpa [firstOne, secondOne, oneTargets] using honePair
      have hzeroWrapped : ∀ next, AgreesOutside zeroTargets
          (run (toggle.adjoint ++ (firstZero ++ secondZero) ++ toggle) next) next := by
        exact PaperCircuitAvoids.frame rfl
          (PaperCircuitAvoids.adjoint (by
            exact fun gate hgate wire hwire hprotected ↦
              htoggleAvoids gate hgate wire hwire (by
                simp only [allTargets, List.mem_append]
                exact Or.inl hprotected)))
          hzeroFrame ((circuitWellFormed_adjoint toggle).mpr htoggleWF)
      have hmiddle : ∀ next, AgreesOutside allTargets
          (run (firstOne ++
            (toggle.adjoint ++ (firstZero ++ secondZero) ++ toggle) ++
            secondOne) next) next := by
        simpa [allTargets] using PaperCircuitAvoids.nest hzeroWrapped honeFrame
          hsecondOneAvoidsZero
      have htoggleWrapped : ∀ next, AgreesOutside allTargets
          (run (toggle ++
            (firstOne ++
              (toggle.adjoint ++ (firstZero ++ secondZero) ++ toggle) ++
              secondOne) ++ toggle.adjoint) next) next :=
        PaperCircuitAvoids.frame rfl htoggleAvoids hmiddle htoggleWF
      have hcomputeWrapped : ∀ next, AgreesOutside allTargets
          (run (compute ++
            (toggle ++
              (firstOne ++
                (toggle.adjoint ++ (firstZero ++ secondZero) ++ toggle) ++
                secondOne) ++ toggle.adjoint) ++ compute.adjoint) next) next :=
        PaperCircuitAvoids.frame rfl hdecoderAvoids htoggleWrapped hcomputeWF
      have htoggleAdjoint : toggle.adjoint =
          ([.CX controlB pathB, .CX controlA pathA] : Circuit) := by
        simp [toggle, Circuit.adjoint]
      have hfirstShape :
          dualUnaryActionUnitary .dec firstLeaf
              (.node indexBitA indexBitB zero one) controlA controlB
              (pathA :: restA) (pathB :: restB) =
            compute ++ toggle ++ firstOne ++ toggle.adjoint ++ firstZero ++
              compute.adjoint := by
        simp only [dualUnaryActionUnitary, compute, firstZero, firstOne,
          circuit_adjoint_append, computeZeroAnd_adjoint, htoggleAdjoint]
        simp [toggle]
      have hsecondShape :
          dualUnaryActionUnitary .inc secondLeaf
              (.node indexBitA indexBitB zero one) controlA controlB
              (pathA :: restA) (pathB :: restB) =
            compute ++ secondZero ++ toggle ++ secondOne ++ toggle.adjoint ++
              compute.adjoint := by
        simp only [dualUnaryActionUnitary, compute, secondZero, secondOne,
          circuit_adjoint_append, computeZeroAnd_adjoint, htoggleAdjoint]
        simp [toggle]
      have hcollapse :
          run (dualUnaryActionUnitary .dec firstLeaf
                (.node indexBitA indexBitB zero one) controlA controlB
                (pathA :: restA) (pathB :: restB) ++
              dualUnaryActionUnitary .inc secondLeaf
                (.node indexBitA indexBitB zero one) controlA controlB
                (pathA :: restA) (pathB :: restB)) state =
            run (compute ++
              (toggle ++
                (firstOne ++
                  (toggle.adjoint ++ (firstZero ++ secondZero) ++ toggle) ++
                  secondOne) ++ toggle.adjoint) ++ compute.adjoint) state := by
        rw [hfirstShape, hsecondShape]
        simp only [Classical.run_append]
        rw [run_run_adjoint_classical compute hcomputeWF]
      rw [hcollapse]
      simpa [DualUnaryActionTree.labels, allTargets, zeroTargets, oneTargets] using
        hcomputeWrapped state

private theorem intervalLeafLayout_of_decoder
    (protectedWires : List Wire)
    (rightControl leftControl rightTop leftTop accumulator target addend carry scratch : Wire)
    (hroles : [rightTop, leftTop, accumulator, target, addend, carry, scratch].Nodup)
    (houtside : DecoderOutsideIntervalRoles protectedWires rightTop leftTop
      accumulator target addend carry scratch)
    (hright : rightControl ∈ protectedWires)
    (hleft : leftControl ∈ protectedWires) :
    IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch := by
  rw [IntervalLeafLayout, intervalLeafSupport]
  apply List.nodup_append.mpr
  refine ⟨List.nodup_dedup _, hroles, ?_⟩
  rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
  intro control hcontrol role hrole equality
  have hprotected : control ∈ protectedWires := by
    simp only [List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hcontrol
    rcases hcontrol with rfl | rfl
    · exact hright
    · exact hleft
  apply houtside hprotected
  simpa [equality] using hrole

/-- Opposite source-order interval traversals restore every wire except the per-label targets.
The cross-label premise says that a later leaf's target is distinct from all roles of the current
leaf; the concrete interval allocator discharges it from its single global `Nodup` layout. -/
theorem intervalTraversals_pair_preservesOutsideTargets
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt)
    (hlabels : tree.labels.Nodup)
    (hseparate : ∀ label, label ∈ tree.labels →
      ∀ other, other ∈ tree.labels → other ≠ label →
        targetAt other ∉
          [rightTop, leftTop, accumulator, targetAt label, addendAt label, carry, scratch]) :
    AgreesOutside (tree.labels.map targetAt)
      (run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths ++
        intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state)
      state := by
  let decoder := tree.decoderWires rightRoot leftRoot rightPaths leftPaths
  let firstLeaf := fun label rightControl leftControl ↦
    intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
      (targetAt label) (addendAt label) carry scratch label rightControl leftControl
  let secondLeaf := fun label rightControl leftControl ↦
    intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
      (targetAt label) (addendAt label) carry scratch label rightControl leftControl
  have htargetDecoder : ∀ label, label ∈ tree.labels →
      targetAt label ∉ decoder := by
    intro label hlabel htarget
    have houtside := (hlayout.2 label hlabel).2
    rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
    exact houtside htarget (by simp)
  apply dualUnaryActionUnitary_pair_preservesOutside firstLeaf secondLeaf targetAt tree
    rightRoot leftRoot rightPaths leftPaths hlayout.1 hlabels htargetDecoder
  · intro label hlabel rightControl hright leftControl hleft next
    exact intervalLeaf_pair_preservesOutsideTarget mode topSpecial rightTop leftTop
      accumulator (targetAt label) (addendAt label) carry scratch label
      rightControl leftControl next
      (intervalLeafLayout_of_decoder decoder rightControl leftControl rightTop leftTop
        accumulator (targetAt label) (addendAt label) carry scratch
        (hlayout.2 label hlabel).1 (hlayout.2 label hlabel).2 hright hleft)
  · intro label hlabel rightControl hright leftControl hleft other hother hne
    apply PaperCircuitAvoids.ofUsesOnly
      (intervalSecondLeaf_usesOnly mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch label rightControl leftControl)
    rw [List.disjoint_left]
    intro wire hwire hsupport
    simp only [List.mem_singleton] at hwire
    subst wire
    rw [intervalLeafSupport] at hsupport
    rcases List.mem_append.mp hsupport with hcontrols | hroles
    · simp only [List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hcontrols
      rcases hcontrols with rfl | rfl
      · exact htargetDecoder other hother hright
      · exact htargetDecoder other hother hleft
    · exact hseparate label hlabel other hother hne hroles

end ShorECDLP.Paper2607_13816
