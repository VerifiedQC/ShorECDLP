import ShorECDLP.Framework.Classical.Semantics
import ShorECDLP.Framework.CostModel
import Lean.Elab.Tactic.Omega

/-!
# Reversible bit primitives for the paper EEA

This file starts the circuit refinement of Algorithm 3 in arXiv:2607.13816v2.  The
constructors below are literal `{X, CX, CCX}` circuits drawn from the supplement:

* the three-gate Fredkin decomposition used for circular shifts and location-controlled swaps;
* the supplement's standalone, dormant four-Toffoli dirty-ancilla alternative for a
  three-controlled X; and
* the three-Toffoli coherent-cleanup specialization of `mcx_vchain` used by `_apply_cell` when
  `MEASUREMENT_UNCOMPUTE = False`.  The supplement's adaptive mode replaces its final cleanup
  Toffoli with measurement and feed-forward correction.

Their public contracts expose the complete basis-state action, restoration of each work wire under
its stated premise, physical well-formedness, named-wire locality, and constructor-derived resource
counts.  No resource-only primitive or dependency on the Naive submission is introduced.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

/-- Every role of a gate is drawn from the declared physical support. -/
def PaperGateUsesOnly (support : List Wire) (gate : Gate) : Prop :=
  ∀ wire ∈ gateWires gate, wire ∈ support

/-- Every gate in a circuit uses only the declared physical support. -/
def PaperCircuitUsesOnly (support : List Wire) (circuit : Circuit) : Prop :=
  ∀ gate ∈ circuit, PaperGateUsesOnly support gate

theorem PaperCircuitUsesOnly.append
    {support : List Wire} {first second : Circuit}
    (hfirst : PaperCircuitUsesOnly support first)
    (hsecond : PaperCircuitUsesOnly support second) :
    PaperCircuitUsesOnly support (first ++ second) := by
  intro gate hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact hfirst gate hgate
  · exact hsecond gate hgate

theorem PaperCircuitUsesOnly.mono
    {small large : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly small circuit)
    (hsubset : ∀ wire, wire ∈ small → wire ∈ large) :
    PaperCircuitUsesOnly large circuit := by
  intro gate hgate wire hwire
  exact hsubset wire (huses gate hgate wire hwire)

/-- A circuit which uses only `support` leaves every other basis wire unchanged. -/
theorem PaperCircuitUsesOnly.preservesOutside
    {support : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly support circuit)
    (state : BasisState) {wire : Wire} (hwire : wire ∉ support) :
    run circuit state wire = state wire := by
  induction circuit generalizing state with
  | nil => rfl
  | cons gate circuit ih =>
      rw [run_cons]
      have hgate := huses gate (by simp)
      have htail : PaperCircuitUsesOnly support circuit := by
        intro next hnext
        exact huses next (by simp [hnext])
      rw [ih htail]
      cases gate with
      | X target =>
          have hne : wire ≠ target := by
            intro equality
            subst wire
            exact hwire (hgate target (by simp [gateWires]))
          simp [applyGate, upd, hne]
      | H target =>
          rfl
      | CX control target =>
          have hne : wire ≠ target := by
            intro equality
            subst wire
            exact hwire (hgate target (by simp [gateWires]))
          simp [applyGate, upd, hne]
      | CCX first second target =>
          have hne : wire ≠ target := by
            intro equality
            subst wire
            exact hwire (hgate target (by simp [gateWires]))
          simp [applyGate, upd, hne]
      | P direction exponent target =>
          rfl

/-- A local circuit's output on its support depends only on the input values on that support. -/
theorem PaperCircuitUsesOnly.run_congrOn
    {support : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly support circuit)
    (left right : BasisState)
    (hagree : ∀ wire, wire ∈ support → left wire = right wire) :
    ∀ wire, wire ∈ support →
      run circuit left wire = run circuit right wire := by
  induction circuit generalizing left right with
  | nil => exact hagree
  | cons gate circuit ih =>
      have hgate := huses gate (by simp)
      have htail : PaperCircuitUsesOnly support circuit := by
        intro next hnext
        exact huses next (by simp [hnext])
      apply ih htail
      intro wire hwire
      cases gate with
      | X target =>
          by_cases hwt : wire = target
          · subst wire
            simp [Classical.applyGate, upd,
              hagree target (hgate target (by simp [gateWires]))]
          · simpa [Classical.applyGate, upd, hwt] using hagree wire hwire
      | H target =>
          exact hagree wire hwire
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
      | P direction exponent target =>
          exact hagree wire hwire

/-- Submission-side Toffoli count for the paper construction. -/
def eeaToffoliCount (circuit : Circuit) : Nat :=
  (circuit.map fun gate => match gate with
    | .CCX _ _ _ => 1
    | _ => 0).sum

/-- Submission-side CNOT count for the paper construction. -/
def eeaCnotCount (circuit : Circuit) : Nat :=
  (circuit.map fun gate => match gate with
    | .CX _ _ => 1
    | _ => 0).sum

theorem eeaToffoliCount_append (first second : Circuit) :
    eeaToffoliCount (first ++ second) =
      eeaToffoliCount first + eeaToffoliCount second := by
  simp [eeaToffoliCount, List.map_append]

theorem eeaCnotCount_append (first second : Circuit) :
    eeaCnotCount (first ++ second) =
      eeaCnotCount first + eeaCnotCount second := by
  simp [eeaCnotCount, List.map_append]

/-- The supplemental generator's three-gate Fredkin decomposition. -/
def controlledSwap (control left right : Wire) : Circuit :=
  [.CX right left, .CCX control left right, .CX right left]

/-- Exact basis-state action of the controlled swap. -/
theorem run_controlledSwap
    (control left right : Wire) (state : BasisState)
    (hcl : control ≠ left) (hcr : control ≠ right) (hlr : left ≠ right) :
    run (controlledSwap control left right) state =
      if state control then
        state[left ↦ state right][right ↦ state left]
      else state := by
  have hrl : right ≠ left := Ne.symm hlr
  funext wire
  by_cases hwc : wire = control
  · subst wire
    cases hc : state control <;>
      simp [controlledSwap, run, applyGate, upd, hcl, hcr,
        hlr, hrl, hc]
  · by_cases hwl : wire = left
    · subst wire
      cases hc : state control <;> cases hl : state left <;>
        cases hr : state right <;>
        simp [controlledSwap, run, applyGate, upd, hcl,
          hlr, hrl, hc, hl, hr]
    · by_cases hwr : wire = right
      · subst wire
        cases hc : state control <;> cases hl : state left <;>
          cases hr : state right <;>
          simp [controlledSwap, run, applyGate, upd, hcl,
            hlr, hrl, hc, hl, hr]
      · cases hc : state control <;>
          simp [controlledSwap, run, applyGate, upd, hwl, hwr, hc]

/-- A controlled swap is physically well formed when its three roles are distinct. -/
theorem controlledSwap_wellFormed
    (control left right : Wire)
    (hcl : control ≠ left) (hcr : control ≠ right) (hlr : left ≠ right) :
    CircuitWellFormed (controlledSwap control left right) := by
  simp [controlledSwap, CircuitWellFormed, Gate.WellFormed,
    hcl, hcr, hlr, hlr.symm]

/-- A controlled swap is a classical reversible circuit. -/
@[simp]
theorem controlledSwap_HPFree (control left right : Wire) :
    HPFree (controlledSwap control left right) := by
  simp [controlledSwap]

/-- Exact support of the controlled-swap decomposition. -/
theorem controlledSwap_usesOnly (control left right : Wire) :
    PaperCircuitUsesOnly [control, left, right]
      (controlledSwap control left right) := by
  simp [PaperCircuitUsesOnly, PaperGateUsesOnly, controlledSwap, gateWires]

/-- A controlled swap costs one Toffoli and two CNOTs. -/
@[simp]
theorem controlledSwap_tCount (control left right : Wire) :
    tCount (controlledSwap control left right) = 7 := rfl

@[simp]
theorem controlledSwap_toffoliCount (control left right : Wire) :
    eeaToffoliCount (controlledSwap control left right) = 1 := rfl

@[simp]
theorem controlledSwap_cnotCount (control left right : Wire) :
    eeaCnotCount (controlledSwap control left right) = 2 := rfl

/-- Exact three-controlled X using one dirty ancilla and four Toffolis. -/
def dirtyC3X
    (first second third target dirty : Wire) : Circuit :=
  [.CCX first second dirty,
    .CCX third dirty target,
    .CCX first second dirty,
    .CCX third dirty target]

private theorem nodupFive_parts
    (first second third target dirty : Wire)
    (hnd : [first, second, third, target, dirty].Nodup) :
    first ≠ second ∧ first ≠ target ∧ first ≠ dirty ∧
      second ≠ target ∧ second ≠ dirty ∧ third ≠ dirty ∧
      third ≠ target ∧ dirty ≠ target := by
  have hfirst : first ∉ [second, third, target, dirty] :=
    (List.nodup_cons.mp hnd).1
  have htail := (List.nodup_cons.mp hnd).2
  have hsecond : second ∉ [third, target, dirty] :=
    (List.nodup_cons.mp htail).1
  have htail := (List.nodup_cons.mp htail).2
  have hthird : third ∉ [target, dirty] :=
    (List.nodup_cons.mp htail).1
  have htail := (List.nodup_cons.mp htail).2
  have htarget : target ∉ [dirty] :=
    (List.nodup_cons.mp htail).1
  constructor
  · intro equality
    exact hfirst (by simp [equality])
  constructor
  · intro equality
    exact hfirst (by simp [equality])
  constructor
  · intro equality
    exact hfirst (by simp [equality])
  constructor
  · intro equality
    exact hsecond (by simp [equality])
  constructor
  · intro equality
    exact hsecond (by simp [equality])
  constructor
  · intro equality
    exact hthird (by simp [equality])
  constructor
  · intro equality
    exact hthird (by simp [equality])
  · intro equality
    exact htarget (by simp [equality])

/-- Exact basis-state action of the dirty-ancilla construction.  The dirty bit is arbitrary and
is restored; the target is toggled by the conjunction of the three controls. -/
theorem run_dirtyC3X
    (first second third target dirty : Wire) (state : BasisState)
    (hnd : [first, second, third, target, dirty].Nodup) :
    run (dirtyC3X first second third target dirty) state =
      state[target ↦ Bool.xor (state target)
        (state first && state second && state third)] := by
  obtain ⟨_, hfTarget, hfd, hsTarget, hsd, htd, htTarget, hdirtyTarget⟩ :=
    nodupFive_parts first second third target dirty hnd
  have htargetDirty : target ≠ dirty := Ne.symm hdirtyTarget
  funext wire
  by_cases hwtarget : wire = target
  · subst wire
    cases hf : state first <;> cases hs : state second <;>
      cases ht : state third <;> cases hd : state dirty <;>
      cases hout : state target <;>
      simp [dirtyC3X, run, applyGate, upd, hfTarget, hfd, hsTarget, hsd, htd, htTarget,
        hdirtyTarget, htargetDirty,
        hf, hs, ht, hd, hout]
  · by_cases hwd : wire = dirty
    · subst wire
      cases hf : state first <;> cases hs : state second <;>
        cases ht : state third <;> cases hd : state dirty <;>
        cases hout : state target <;>
        simp [dirtyC3X, run, applyGate, upd, hfTarget, hfd, hsTarget, hsd, htd, htTarget,
          hdirtyTarget, htargetDirty,
          hf, hs, ht, hd, hout]
    · simp [dirtyC3X, run, applyGate, upd, hwtarget, hwd]

/-- The dirty three-control construction is physically well formed on five distinct wires. -/
theorem dirtyC3X_wellFormed
    (first second third target dirty : Wire)
    (hnd : [first, second, third, target, dirty].Nodup) :
    CircuitWellFormed (dirtyC3X first second third target dirty) := by
  obtain ⟨hfs, _, hfd, _, hsd, htd, htTarget, hdirtyTarget⟩ :=
    nodupFive_parts first second third target dirty hnd
  simp [dirtyC3X, CircuitWellFormed, Gate.WellFormed,
    hfs, hfd, hsd, htd, htTarget, hdirtyTarget]

/-- The dirty construction is entirely classical. -/
@[simp]
theorem dirtyC3X_HPFree
    (first second third target dirty : Wire) :
    HPFree (dirtyC3X first second third target dirty) := by
  simp [dirtyC3X]

/-- Exact support of the dirty three-control construction. -/
theorem dirtyC3X_usesOnly
    (first second third target dirty : Wire) :
    PaperCircuitUsesOnly [first, second, third, target, dirty]
      (dirtyC3X first second third target dirty) := by
  simp [PaperCircuitUsesOnly, PaperGateUsesOnly, dirtyC3X, gateWires]

/-- The dirty construction uses exactly four Toffolis. -/
@[simp]
theorem dirtyC3X_tCount
    (first second third target dirty : Wire) :
    tCount (dirtyC3X first second third target dirty) = 28 := rfl

@[simp]
theorem dirtyC3X_toffoliCount
    (first second third target dirty : Wire) :
    eeaToffoliCount (dirtyC3X first second third target dirty) = 4 := rfl

@[simp]
theorem dirtyC3X_cnotCount
    (first second third target dirty : Wire) :
    eeaCnotCount (dirtyC3X first second third target dirty) = 0 := rfl

/-! ## Clean-v-chain three-controlled X -/

/-- The three-control specialization of the pinned supplement's clean `mcx_vchain` in coherent
`MEASUREMENT_UNCOMPUTE = False` mode: compute the conjunction of the first two controls, use it with
the third control, then restore the clean scratch bit coherently. -/
def cleanC3X
    (first second third target scratch : Wire) : Circuit :=
  [.CCX first second scratch, .CCX third scratch target,
    .CCX first second scratch]

/-- Exact basis-state action of the coherent clean-v-chain construction. -/
theorem run_cleanC3X
    (first second third target scratch : Wire) (state : BasisState)
    (hnd : [first, second, third, target, scratch].Nodup)
    (hclean : state scratch = false) :
    run (cleanC3X first second third target scratch) state =
      state[target ↦ Bool.xor (state target)
        (state first && state second && state third)] := by
  obtain ⟨_, hfTarget, hfs, hsTarget, hss, hthirdScratch,
    _, hscratchTarget⟩ :=
    nodupFive_parts first second third target scratch hnd
  have htargetScratch : target ≠ scratch := Ne.symm hscratchTarget
  funext wire
  by_cases hwtarget : wire = target
  · subst wire
    cases hf : state first <;> cases hs : state second <;>
      cases ht : state third <;> cases hout : state target <;>
      simp [cleanC3X, run, applyGate, upd, hfTarget, hfs,
        hsTarget, hss, hthirdScratch,
        hscratchTarget, htargetScratch, hclean, hf, hs, ht, hout]
  · by_cases hws : wire = scratch
    · subst wire
      cases hf : state first <;> cases hs : state second <;>
        cases ht : state third <;> cases hout : state target <;>
        simp [cleanC3X, run, applyGate, upd, hfTarget, hfs,
          hsTarget, hss, hthirdScratch,
          hscratchTarget, htargetScratch, hclean, hf, hs, ht, hout]
    · simp [cleanC3X, run, applyGate, upd, hwtarget, hws]

/-- The clean-v-chain construction is physically well formed on five distinct wires. -/
theorem cleanC3X_wellFormed
    (first second third target scratch : Wire)
    (hnd : [first, second, third, target, scratch].Nodup) :
    CircuitWellFormed (cleanC3X first second third target scratch) := by
  obtain ⟨hfs, _, hfScratch, _, hsScratch, hthirdScratch,
    hthirdTarget, hscratchTarget⟩ :=
    nodupFive_parts first second third target scratch hnd
  simp [cleanC3X, CircuitWellFormed, Gate.WellFormed,
    hfs, hfScratch, hsScratch, hthirdScratch, hthirdTarget, hscratchTarget]

@[simp]
theorem cleanC3X_HPFree
    (first second third target scratch : Wire) :
    HPFree (cleanC3X first second third target scratch) := by
  simp [cleanC3X]

theorem cleanC3X_usesOnly
    (first second third target scratch : Wire) :
    PaperCircuitUsesOnly [first, second, third, target, scratch]
      (cleanC3X first second third target scratch) := by
  simp [PaperCircuitUsesOnly, PaperGateUsesOnly, cleanC3X, gateWires]

@[simp]
theorem cleanC3X_tCount
    (first second third target scratch : Wire) :
    tCount (cleanC3X first second third target scratch) = 21 := rfl

@[simp]
theorem cleanC3X_toffoliCount
    (first second third target scratch : Wire) :
    eeaToffoliCount (cleanC3X first second third target scratch) = 3 := rfl

@[simp]
theorem cleanC3X_cnotCount
    (first second third target scratch : Wire) :
    eeaCnotCount (cleanC3X first second third target scratch) = 0 := rfl

/-! ## Controlled circular shift -/

/-- Values read from named wires in list order. -/
def wireValues (wires : List Wire) (state : BasisState) : List Bool :=
  wires.map state

/-- A one-position left rotation of an ordinary list. -/
def rotateLeftOne : List α → List α
  | [] => []
  | head :: tail => tail ++ [head]

/-- The adjacent-Fredkin cascade used by the supplement for a controlled one-position left
rotation.  For `[w₀,w₁,...,wₘ]` it swaps `(w₀,w₁)`, then `(w₁,w₂)`, and so on. -/
def controlledRotateLeftOne (control : Wire) : List Wire → Circuit
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      controlledSwap control first second ++
        controlledRotateLeftOne control (second :: rest)

/-- The controlled rotation touches only the control and the rotated register. -/
theorem controlledRotateLeftOne_usesOnly
    (control : Wire) : ∀ register : List Wire,
    PaperCircuitUsesOnly (control :: register)
      (controlledRotateLeftOne control register) := by
  intro register
  induction register with
  | nil => simp [controlledRotateLeftOne, PaperCircuitUsesOnly]
  | cons first tail ih =>
      cases tail with
      | nil => simp [controlledRotateLeftOne, PaperCircuitUsesOnly]
      | cons second rest =>
          rw [controlledRotateLeftOne]
          apply PaperCircuitUsesOnly.append
          · apply (controlledSwap_usesOnly control first second).mono
            intro wire hwire
            simp at hwire
            rcases hwire with rfl | rfl | rfl <;> simp
          · apply ih.mono
            intro wire hwire
            simp only [List.mem_cons] at hwire ⊢
            rcases hwire with rfl | rfl | hwire
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr hwire))

/-- The adjacent-Fredkin cascade is H/P-free. -/
@[simp]
theorem controlledRotateLeftOne_HPFree
    (control : Wire) : ∀ register : List Wire,
    HPFree (controlledRotateLeftOne control register) := by
  intro register
  induction register with
  | nil => simp [controlledRotateLeftOne]
  | cons first tail ih =>
      cases tail with
      | nil => simp [controlledRotateLeftOne]
      | cons second rest =>
          simp [controlledRotateLeftOne, ih]

/-- The control wire is never modified by the rotation cascade. -/
theorem controlledRotateLeftOne_control
    (control : Wire) : ∀ (register : List Wire) (state : BasisState),
    control ∉ register →
    run (controlledRotateLeftOne control register) state control =
      state control := by
  intro register
  induction register with
  | nil => simp [controlledRotateLeftOne]
  | cons first tail ih =>
      cases tail with
      | nil => simp [controlledRotateLeftOne]
      | cons second rest =>
          intro state hcontrol
          simp only [List.mem_cons, not_or] at hcontrol
          have hcontrolTail : control ∉ second :: rest := by
            simpa only [List.mem_cons, not_or] using hcontrol.2
          rw [controlledRotateLeftOne, run_append]
          rw [ih _ hcontrolTail]
          simp [controlledSwap, run, applyGate, upd,
            hcontrol.1, hcontrol.2.1]

/-- Exact register action of the controlled adjacent-Fredkin cascade. -/
theorem run_controlledRotateLeftOne_values
    (control : Wire) : ∀ (register : List Wire) (state : BasisState),
    (control :: register).Nodup →
    wireValues register
        (run (controlledRotateLeftOne control register) state) =
      if state control then rotateLeftOne (wireValues register state)
      else wireValues register state := by
  intro register
  induction register with
  | nil => simp [controlledRotateLeftOne, wireValues, rotateLeftOne]
  | cons first tail ih =>
      cases tail with
      | nil =>
          intro state hnd
          cases hc : state control <;>
            simp [controlledRotateLeftOne, wireValues, rotateLeftOne]
      | cons second rest =>
          intro state hnd
          have hcontrol : control ∉ first :: second :: rest :=
            (List.nodup_cons.mp hnd).1
          have hregister : (first :: second :: rest).Nodup :=
            (List.nodup_cons.mp hnd).2
          have hfirst : first ∉ second :: rest :=
            (List.nodup_cons.mp hregister).1
          have htail : (second :: rest).Nodup :=
            (List.nodup_cons.mp hregister).2
          have hsecond : second ∉ rest :=
            (List.nodup_cons.mp htail).1
          have hrecursive : (control :: second :: rest).Nodup := by
            apply List.nodup_cons.mpr
            exact ⟨fun h => hcontrol (List.mem_cons_of_mem first h), htail⟩
          have hcl : control ≠ first := by
            intro equality
            exact hcontrol (by simp [equality])
          have hcs : control ≠ second := by
            intro equality
            exact hcontrol (by simp [equality])
          have hfs : first ≠ second := by
            intro equality
            exact hfirst (by simp [equality])
          let swapped := run (controlledSwap control first second) state
          have hswap := run_controlledSwap control first second state hcl hcs hfs
          have hcontrolSwapped : swapped control = state control := by
            dsimp only [swapped]
            rw [hswap]
            split <;> simp [upd, hcl, hcs]
          have hfirstOutside : first ∉ control :: second :: rest := by
            intro hmem
            rcases List.mem_cons.mp hmem with equality | hmem
            · exact hcl equality.symm
            · exact hfirst hmem
          have hfirstFinal :
              run (controlledRotateLeftOne control (second :: rest)) swapped first =
                swapped first :=
            (controlledRotateLeftOne_usesOnly control (second :: rest)).preservesOutside
              swapped hfirstOutside
          rw [controlledRotateLeftOne, run_append]
          change
            run (controlledRotateLeftOne control (second :: rest)) swapped first ::
                wireValues (second :: rest)
                  (run (controlledRotateLeftOne control (second :: rest)) swapped) =
              if state control then
                rotateLeftOne (wireValues (first :: second :: rest) state)
              else wireValues (first :: second :: rest) state
          rw [hfirstFinal, ih swapped hrecursive, hcontrolSwapped]
          simp only [swapped]
          rw [hswap]
          cases hc : state control with
          | false =>
              simp [wireValues]
          | true =>
              simp [wireValues, rotateLeftOne, upd, hfs]
              intro wire hwire
              have hwFirst : wire ≠ first := by
                intro equality
                subst wire
                exact hfirst (List.mem_cons_of_mem second hwire)
              have hwSecond : wire ≠ second := by
                intro equality
                subst wire
                exact hsecond hwire
              simp [hwFirst, hwSecond]

/-- The rotation cascade is physically well formed on a duplicate-free layout. -/
theorem controlledRotateLeftOne_wellFormed
    (control : Wire) : ∀ register : List Wire,
    (control :: register).Nodup →
    CircuitWellFormed (controlledRotateLeftOne control register) := by
  intro register
  induction register with
  | nil => simp [controlledRotateLeftOne]
  | cons first tail ih =>
      cases tail with
      | nil => simp [controlledRotateLeftOne]
      | cons second rest =>
          intro hnd
          have hcontrol : control ∉ first :: second :: rest :=
            (List.nodup_cons.mp hnd).1
          have hregister : (first :: second :: rest).Nodup :=
            (List.nodup_cons.mp hnd).2
          have hfirst : first ∉ second :: rest :=
            (List.nodup_cons.mp hregister).1
          have htail : (second :: rest).Nodup :=
            (List.nodup_cons.mp hregister).2
          have hrecursive : (control :: second :: rest).Nodup := by
            apply List.nodup_cons.mpr
            exact ⟨fun h => hcontrol (List.mem_cons_of_mem first h), htail⟩
          have hcl : control ≠ first := by
            intro equality
            exact hcontrol (by simp [equality])
          have hcs : control ≠ second := by
            intro equality
            exact hcontrol (by simp [equality])
          have hfs : first ≠ second := by
            intro equality
            exact hfirst (by simp [equality])
          rw [controlledRotateLeftOne, circuitWellFormed_append]
          exact ⟨controlledSwap_wellFormed control first second hcl hcs hfs,
            ih hrecursive⟩

/-- One Fredkin is used per adjacent pair. -/
theorem controlledRotateLeftOne_toffoliCount
    (control : Wire) : ∀ register : List Wire,
    eeaToffoliCount (controlledRotateLeftOne control register) =
      register.length - 1 := by
  intro register
  induction register with
  | nil => rfl
  | cons first tail ih =>
      cases tail with
      | nil => rfl
      | cons second rest =>
          rw [controlledRotateLeftOne, eeaToffoliCount_append,
            controlledSwap_toffoliCount, ih]
          simp
          omega

/-- The exact CNOT count is twice the number of adjacent pairs. -/
theorem controlledRotateLeftOne_cnotCount
    (control : Wire) : ∀ register : List Wire,
    eeaCnotCount (controlledRotateLeftOne control register) =
      2 * (register.length - 1) := by
  intro register
  induction register with
  | nil => rfl
  | cons first tail ih =>
      cases tail with
      | nil => rfl
      | cons second rest =>
          rw [controlledRotateLeftOne, eeaCnotCount_append,
            controlledSwap_cnotCount, ih]
          simp
          omega

/-- The T count follows structurally from one Toffoli per adjacent pair. -/
theorem controlledRotateLeftOne_tCount
    (control : Wire) : ∀ register : List Wire,
    tCount (controlledRotateLeftOne control register) =
      7 * (register.length - 1) := by
  intro register
  induction register with
  | nil => rfl
  | cons first tail ih =>
      cases tail with
      | nil => rfl
      | cons second rest =>
          rw [controlledRotateLeftOne, tCount_append,
            controlledSwap_tCount, ih]
          simp
          omega

/-! ## Literal inverse shift -/

private theorem applyGate_adjoint_applyGate
    (gate : Gate) (hgate : gate.WellFormed) (state : BasisState) :
    applyGate gate.adjoint (applyGate gate state) = state := by
  cases gate with
  | X target =>
      funext wire
      by_cases hwire : wire = target <;>
        simp [applyGate, upd, hwire]
  | H target => rfl
  | CX control target =>
      have hct : control ≠ target := by
        simpa [Gate.WellFormed] using hgate
      funext wire
      by_cases hwire : wire = target
      · subst wire
        cases hc : state control <;> cases ht : state target <;>
          simp [applyGate, upd, hct, hc, ht]
      · simp [applyGate, upd, hwire]
  | CCX first second target =>
      obtain ⟨hfs, hft, hst⟩ := hgate
      funext wire
      by_cases hwire : wire = target
      · subst wire
        cases hf : state first <;> cases hs : state second <;>
          cases ht : state target <;>
          simp [applyGate, upd, hft, hst, hf, hs, ht]
      · simp [applyGate, upd, hwire]
  | P direction exponent target => rfl

/-- Classical execution of a physically well-formed circuit followed by its literal adjoint
restores the complete basis state. -/
theorem run_adjoint_run_classical
    (circuit : Circuit) (hwellFormed : CircuitWellFormed circuit)
    (state : BasisState) :
    run circuit.adjoint (run circuit state) = state := by
  induction circuit generalizing state with
  | nil => rfl
  | cons gate circuit ih =>
      have hparts := (circuitWellFormed_cons gate circuit).mp hwellFormed
      rw [run_cons, circuit_adjoint_cons, run_append]
      rw [ih hparts.2]
      simpa [run] using applyGate_adjoint_applyGate gate hparts.1 state

private theorem PaperGateUsesOnly.adjoint
    {support : List Wire} {gate : Gate}
    (huses : PaperGateUsesOnly support gate) :
    PaperGateUsesOnly support gate.adjoint := by
  cases gate <;> simpa [PaperGateUsesOnly, gateWires] using huses

theorem PaperCircuitUsesOnly.adjoint
    {support : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly support circuit) :
    PaperCircuitUsesOnly support circuit.adjoint := by
  induction circuit with
  | nil => simp [PaperCircuitUsesOnly]
  | cons gate circuit ih =>
      rw [circuit_adjoint_cons]
      apply PaperCircuitUsesOnly.append
      · apply ih
        intro next hnext
        exact huses next (by simp [hnext])
      · intro next hnext
        simp only [List.mem_singleton] at hnext
        subst next
        exact (huses gate (by simp)).adjoint

theorem eeaToffoliCount_adjoint (circuit : Circuit) :
    eeaToffoliCount circuit.adjoint = eeaToffoliCount circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [circuit_adjoint_cons, eeaToffoliCount_append, ih]
      cases gate <;> simp [eeaToffoliCount, Nat.add_comm]

theorem eeaCnotCount_adjoint (circuit : Circuit) :
    eeaCnotCount circuit.adjoint = eeaCnotCount circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [circuit_adjoint_cons, eeaCnotCount_append, ih]
      cases gate <;> simp [eeaCnotCount, Nat.add_comm]

private theorem hpFree_adjoint_of_hpFree
    {circuit : Circuit} (hfree : HPFree circuit) :
    HPFree circuit.adjoint := by
  induction circuit with
  | nil => simp
  | cons gate circuit ih =>
      have hparts := (hpFree_cons gate circuit).mp hfree
      rw [circuit_adjoint_cons, hpFree_append]
      constructor
      · exact ih hparts.2
      · cases gate <;> simp_all

/-- The literal inverse of the adjacent-swap cascade; this is the paper's controlled
one-position right rotation. -/
def controlledRotateRightOne (control : Wire) (register : List Wire) : Circuit :=
  (controlledRotateLeftOne control register).adjoint

/-- Left rotation followed by its right-rotation inverse restores every wire. -/
theorem run_controlledRotateRightOne_after_left
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    run (controlledRotateRightOne control register)
        (run (controlledRotateLeftOne control register) state) = state := by
  exact run_adjoint_run_classical
    (controlledRotateLeftOne control register)
    (controlledRotateLeftOne_wellFormed control register hnd) state

theorem controlledRotateRightOne_wellFormed
    (control : Wire) (register : List Wire)
    (hnd : (control :: register).Nodup) :
    CircuitWellFormed (controlledRotateRightOne control register) := by
  exact (circuitWellFormed_adjoint
      (controlledRotateLeftOne control register)).mpr
    (controlledRotateLeftOne_wellFormed control register hnd)

@[simp]
theorem controlledRotateRightOne_HPFree
    (control : Wire) (register : List Wire) :
    HPFree (controlledRotateRightOne control register) := by
  exact hpFree_adjoint_of_hpFree
    (controlledRotateLeftOne_HPFree control register)

theorem controlledRotateRightOne_usesOnly
    (control : Wire) (register : List Wire) :
    PaperCircuitUsesOnly (control :: register)
      (controlledRotateRightOne control register) := by
  exact (controlledRotateLeftOne_usesOnly control register).adjoint

theorem controlledRotateRightOne_toffoliCount
    (control : Wire) (register : List Wire) :
    eeaToffoliCount (controlledRotateRightOne control register) =
      register.length - 1 := by
  rw [controlledRotateRightOne, eeaToffoliCount_adjoint,
    controlledRotateLeftOne_toffoliCount]

theorem controlledRotateRightOne_cnotCount
    (control : Wire) (register : List Wire) :
    eeaCnotCount (controlledRotateRightOne control register) =
      2 * (register.length - 1) := by
  rw [controlledRotateRightOne, eeaCnotCount_adjoint,
    controlledRotateLeftOne_cnotCount]

theorem controlledRotateRightOne_tCount
    (control : Wire) (register : List Wire) :
    tCount (controlledRotateRightOne control register) =
      7 * (register.length - 1) := by
  rw [controlledRotateRightOne, tCount_adjoint,
    controlledRotateLeftOne_tCount]

end ShorECDLP.Paper2607_13816
