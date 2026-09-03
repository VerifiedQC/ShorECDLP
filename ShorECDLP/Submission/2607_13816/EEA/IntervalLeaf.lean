import ShorECDLP.Submission.«2607_13816».EEA.Ripple
import ShorECDLP.Submission.«2607_13816».EEA.TreeBuilder

/-!
# Source-shaped interval-arithmetic leaves

The pinned supplement drives each remainder-window ripple cell with two synchronized endpoint
decoders.  On the first (high-to-low) pass it toggles the range accumulator from the right
endpoint, applies the first Cuccaro cell, and toggles from the left endpoint.  The second
(low-to-high) pass performs the opposite endpoint order around the second cell.

When an interval contains `2^d + 1` labels, the main tree contains `0, ..., 2^d - 1`.  Its leaf
zero is masked by the negated endpoint bit `d`, while the separate label `2^d` is selected by the
supplement's direct equality-control construction.  This file implements those exact coherent
gate streams and proves their basis-state action, decoder preservation, physical well-formedness,
locality, and constructor-derived resource equations.  It does not yet compose the endpoint
affine transforms, zero maps, length writers, or a complete EEA step.  The traversal boundary
keeps the already-certified tree, per-label physical lanes, and full-register layout explicit for
the complete interval block to supply.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

set_option linter.unusedSimpArgs false

/-! ## Clean v-chain used by direct equality controls -/

/-- Conjunction of the values on a list of wires. -/
def wireAnd : List Wire → BasisState → Bool
  | [], _ => true
  | wire :: wires, state => state wire && wireAnd wires state

theorem wireAnd_upd_not_mem
    (wires : List Wire) (state : BasisState) (target : Wire) (value : Bool)
    (hnot : target ∉ wires) :
    wireAnd wires state[target ↦ value] = wireAnd wires state := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [List.mem_cons, not_or] at hnot
      rw [wireAnd, wireAnd, upd_other state target value (by
        exact fun equality ↦ hnot.1 equality.symm), ih hnot.2]

/-- Source-order tail of a clean v-chain.  `accumulator` stores the conjunction accumulated before
`controls`; every nonfinal control consumes one clean scratch wire. -/
def mcxVChainTail (accumulator : Wire) :
    List Wire → Wire → List Wire → Circuit
  | [], _, _ => []
  | [control], target, _ => [.CCX control accumulator target]
  | control :: nextControl :: controls, target, scratch :: scratches =>
      [.CCX control accumulator scratch] ++
        mcxVChainTail scratch (nextControl :: controls) target scratches ++
        [.CCX control accumulator scratch]
  | _ :: _ :: _, _, [] => []

/-- Literal coherent `mcx_vchain` from the pinned generator.  Extra scratch wires are ignored;
the first `controls.length - 2` wires are used and restored.  Outside that capacity premise, the
total Lean fallback does not model Python's exception; source-fidelity, correctness,
well-formedness, and resource claims are capacity-restricted. -/
def mcxVChain : List Wire → Wire → List Wire → Circuit
  | [], target, _ => [.X target]
  | [control], target, _ => [.CX control target]
  | first :: second :: controls, target, scratches =>
      mcxVChainTail second (first :: controls) target scratches

/-- Every physical role supplied to a v-chain is distinct. -/
def McxVChainLayout (controls : List Wire) (target : Wire)
    (scratches : List Wire) : Prop :=
  (controls ++ target :: scratches).Nodup

private theorem mcxVChainTail_childLayout
    (accumulator control nextControl target scratch : Wire)
    (controls scratches : List Wire)
    (hlayout :
      (accumulator :: (control :: nextControl :: controls) ++
        target :: scratch :: scratches).Nodup) :
    (scratch :: (nextControl :: controls) ++ target :: scratches).Nodup := by
  have haccTail := (List.nodup_cons.mp hlayout).1
  have hafterAcc := (List.nodup_cons.mp hlayout).2
  simp only [List.cons_append] at haccTail hafterAcc
  have hcontrolTail := (List.nodup_cons.mp hafterAcc).1
  have hafterControl := (List.nodup_cons.mp hafterAcc).2
  have hnextTail := (List.nodup_cons.mp hafterControl).1
  have hafterNext := (List.nodup_cons.mp hafterControl).2
  obtain ⟨hcontrols, htail, hcross⟩ := List.nodup_append.mp hafterNext
  have htargetTail := (List.nodup_cons.mp htail).1
  have hafterTarget := (List.nodup_cons.mp htail).2
  have hscratchTail := (List.nodup_cons.mp hafterTarget).1
  have hscratches := (List.nodup_cons.mp hafterTarget).2
  have hcontrolsTargetScratches :
      (controls ++ target :: scratches).Nodup :=
    List.nodup_append.mpr ⟨hcontrols,
      List.nodup_cons.mpr ⟨by
        intro hmem
        exact htargetTail (by simp [hmem]), hscratches⟩,
      by
        intro left hleft right hright
        exact hcross left hleft right (by
          rcases List.mem_cons.mp hright with rfl | hwire
          · simp
          · simp [hwire])⟩
  have hnextRest :
      (nextControl :: controls ++ target :: scratches).Nodup :=
    List.nodup_cons.mpr ⟨by
      intro hmem
      exact hnextTail (by
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact List.mem_append_left _ hmem
        · rcases List.mem_cons.mp hmem with rfl | hmem
          · simp
          · simp [hmem]), hcontrolsTargetScratches⟩
  exact List.nodup_cons.mpr ⟨by
    intro hmem
    rcases List.mem_cons.mp hmem with hsame | hmem
    · exact hnextTail (by simp [hsame])
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact (hcross scratch hmem scratch (by simp)) rfl
      · rcases List.mem_cons.mp hmem with hsame | hmem
        · exact htargetTail (by simp [hsame])
        · exact hscratchTail hmem,
    hnextRest⟩

private theorem mcxVChainTail_firstRoles
    (accumulator control nextControl target scratch : Wire)
    (controls scratches : List Wire)
    (hlayout :
      (accumulator :: (control :: nextControl :: controls) ++
        target :: scratch :: scratches).Nodup) :
    [accumulator, control, scratch].Nodup := by
  simp only [List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.mem_append, not_or] at hlayout ⊢
  aesop

private theorem run_mcxVChainTail
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire) (state : BasisState)
    (hnonempty : controls ≠ [])
    (henough : controls.length - 1 ≤ scratches.length)
    (hlayout : (accumulator :: controls ++ target :: scratches).Nodup)
    (hclean : Clean scratches state) :
    run (mcxVChainTail accumulator controls target scratches) state =
      state[target ↦ Bool.xor (state target)
        (state accumulator && wireAnd controls state)] := by
  induction controls generalizing accumulator scratches state with
  | nil => exact (hnonempty rfl).elim
  | cons control controls ih =>
      cases controls with
      | nil =>
          have haccTarget : accumulator ≠ target := by
            intro equality
            exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
          have hcontrolTarget : control ≠ target := by
            have htail := (List.nodup_cons.mp hlayout).2
            simp only [List.cons_append, List.nil_append] at htail
            intro equality
            exact (List.nodup_cons.mp htail).1 (by simp [equality])
          funext wire
          by_cases hwire : wire = target
          · subst wire
            cases ha : state accumulator <;> cases hc : state control <;>
              cases ht : state target <;>
              simp [mcxVChainTail, wireAnd, run, applyGate, upd,
                haccTarget, hcontrolTarget, ha, hc, ht]
          · simp [mcxVChainTail, wireAnd, run, applyGate, upd, hwire]
      | cons nextControl controls =>
          cases scratches with
          | nil =>
              simp only [List.length_cons, List.length_nil] at henough
              omega
          | cons scratch scratches =>
              have hfirstRoles : [accumulator, control, scratch].Nodup :=
                mcxVChainTail_firstRoles accumulator control nextControl target scratch
                  controls scratches hlayout
              have hchildLayout :
                  (scratch :: (nextControl :: controls) ++ target :: scratches).Nodup :=
                mcxVChainTail_childLayout accumulator control nextControl target scratch
                  controls scratches hlayout
              have haccScratch : accumulator ≠ scratch := by
                simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
                  or_false, not_or] at hfirstRoles
                exact hfirstRoles.1.2
              have hcontrolScratch : control ≠ scratch := by
                simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
                  or_false, not_or] at hfirstRoles
                exact hfirstRoles.2.1
              have hscratchTarget : scratch ≠ target := by
                intro equality
                exact (List.nodup_cons.mp hchildLayout).1 (by simp [equality])
              have htargetScratch : target ≠ scratch := Ne.symm hscratchTarget
              have hscratchControls : scratch ∉ nextControl :: controls := by
                intro hmem
                exact (List.nodup_cons.mp hchildLayout).1
                  (List.mem_append_left _ hmem)
              have hnextScratch : nextControl ≠ scratch := by
                intro equality
                exact hscratchControls (by simp [equality])
              have hscratchTailControls : scratch ∉ controls := by
                intro hmem
                exact hscratchControls (by simp [hmem])
              have haccTarget : accumulator ≠ target := by
                intro equality
                exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
              have hcontrolTarget : control ≠ target := by
                have htail := (List.nodup_cons.mp hlayout).2
                simp only [List.cons_append] at htail
                intro equality
                exact (List.nodup_cons.mp htail).1 (by simp [equality])
              have hscratchFalse : state scratch = false :=
                hclean scratch (by simp)
              let first := applyGate (.CCX control accumulator scratch) state
              have hfirst : first =
                  state[scratch ↦ state control && state accumulator] := by
                funext wire
                by_cases hwire : wire = scratch
                · subst wire
                  simp [first, applyGate, upd, hscratchFalse]
                · simp [first, applyGate, upd, hwire]
              have hchildClean : Clean scratches first := by
                intro wire hwire
                rw [hfirst, upd_other state scratch _ (by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hchildLayout).1 (by
                    simp [hwire]))]
                exact hclean wire (by simp [hwire])
              have hchildEnough :
                  (nextControl :: controls).length - 1 ≤ scratches.length := by
                simp only [List.length_cons] at henough ⊢
                omega
              have hchild := ih scratch scratches first (by simp)
                hchildEnough hchildLayout hchildClean
              have hwireAndFirst :
                  wireAnd (nextControl :: controls) first =
                    wireAnd (nextControl :: controls) state := by
                rw [hfirst, wireAnd_upd_not_mem _ _ _ _ hscratchControls]
              have hwireAndTail :
                  wireAnd controls state[scratch ↦ true] =
                    wireAnd controls state := by
                rw [wireAnd_upd_not_mem _ _ _ _ hscratchTailControls]
              rw [mcxVChainTail, run_append, run_append]
              change run [.CCX control accumulator scratch]
                (run (mcxVChainTail scratch (nextControl :: controls)
                  target scratches) first) = _
              rw [hchild]
              funext wire
              by_cases hwireTarget : wire = target
              · subst wire
                cases ha : state accumulator <;> cases hc : state control <;>
                  cases hs : state scratch <;> cases ht : state target <;>
                  cases hw : wireAnd (nextControl :: controls) state <;>
                  simp [first, hfirst, applyGate, wireAnd, upd,
                    haccScratch, hcontrolScratch, hscratchTarget,
                    htargetScratch, hnextScratch, haccTarget, hcontrolTarget,
                    hscratchFalse, hwireAndFirst, hwireAndTail,
                    ha, hc, hs, ht, hw]
              · by_cases hwireScratch : wire = scratch
                · subst wire
                  cases ha : state accumulator <;> cases hc : state control <;>
                    cases hs : state scratch <;> cases ht : state target <;>
                    cases hw : wireAnd (nextControl :: controls) state <;>
                    simp [first, hfirst, applyGate, wireAnd, upd,
                      haccScratch, hcontrolScratch, hscratchTarget,
                      htargetScratch, hnextScratch, haccTarget, hcontrolTarget,
                      hscratchFalse, hwireAndFirst, hwireAndTail,
                      ha, hc, hs, ht, hw]
                · simp [first, hfirst, applyGate, wireAnd, upd,
                    hwireTarget, hwireScratch, haccTarget, hcontrolTarget]

/-- Direct whole-state semantics of the source's clean multi-controlled X. -/
theorem run_mcxVChain
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (state : BasisState)
    (henough : controls.length - 2 ≤ scratches.length)
    (hlayout : McxVChainLayout controls target scratches)
    (hclean : Clean scratches state) :
    run (mcxVChain controls target scratches) state =
      state[target ↦ Bool.xor (state target) (wireAnd controls state)] := by
  cases controls with
  | nil =>
      funext wire
      by_cases hwire : wire = target
      · subst wire
        simp [mcxVChain, wireAnd, run, applyGate, upd]
      · simp [mcxVChain, wireAnd, run, applyGate, upd, hwire]
  | cons first controls =>
      cases controls with
      | nil =>
          have hfirstTarget : first ≠ target := by
            intro equality
            exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
          funext wire
          by_cases hwire : wire = target
          · subst wire
            cases hf : state first <;> cases ht : state target <;>
              simp [mcxVChain, wireAnd, run, applyGate, upd,
                hfirstTarget, hf, ht]
          · simp [mcxVChain, wireAnd, run, applyGate, upd, hwire]
      | cons second controls =>
          have htailLayout :
              (second :: (first :: controls) ++ target :: scratches).Nodup := by
            simp only [McxVChainLayout, List.cons_append, List.nodup_cons,
              List.mem_cons, List.mem_append, not_or] at hlayout ⊢
            aesop
          have htailEnough :
              (first :: controls).length - 1 ≤ scratches.length := by
            simpa using henough
          simpa [mcxVChain, wireAnd, Bool.and_comm, Bool.and_left_comm,
            Bool.and_assoc] using
            run_mcxVChainTail second (first :: controls) target scratches state
              (by simp) htailEnough htailLayout hclean

private theorem mcxVChainTail_HPFree
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire) :
    HPFree (mcxVChainTail accumulator controls target scratches) := by
  induction controls generalizing accumulator scratches with
  | nil => simp [mcxVChainTail]
  | cons control controls ih =>
      cases controls with
      | nil => simp [mcxVChainTail]
      | cons nextControl controls =>
          cases scratches with
          | nil => simp [mcxVChainTail]
          | cons scratch scratches =>
              simp [mcxVChainTail, ih]

@[simp]
theorem mcxVChain_HPFree
    (controls : List Wire) (target : Wire) (scratches : List Wire) :
    HPFree (mcxVChain controls target scratches) := by
  cases controls with
  | nil => simp [mcxVChain]
  | cons first controls =>
      cases controls with
      | nil => simp [mcxVChain]
      | cons second controls =>
          exact mcxVChainTail_HPFree second (first :: controls) target scratches

private theorem mcxVChainTail_usesOnly
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire) :
    PaperCircuitUsesOnly (accumulator :: controls ++ target :: scratches)
      (mcxVChainTail accumulator controls target scratches) := by
  induction controls generalizing accumulator scratches with
  | nil => simp [mcxVChainTail, PaperCircuitUsesOnly]
  | cons control controls ih =>
      cases controls with
      | nil =>
          simp [mcxVChainTail, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
      | cons nextControl controls =>
          cases scratches with
          | nil => simp [mcxVChainTail, PaperCircuitUsesOnly]
          | cons scratch scratches =>
              have hgate : PaperCircuitUsesOnly
                  (accumulator :: control :: nextControl :: controls ++
                    target :: scratch :: scratches)
                  (Gate.CCX control accumulator scratch :: []) := by
                simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
              have hchild : PaperCircuitUsesOnly
                  (accumulator :: control :: nextControl :: controls ++
                    target :: scratch :: scratches)
                  (mcxVChainTail scratch (nextControl :: controls)
                    target scratches) := by
                apply (ih scratch scratches).mono
                intro wire hwire
                simp only [List.mem_cons, List.mem_append] at hwire ⊢
                aesop
              change PaperCircuitUsesOnly
                (accumulator :: control :: nextControl :: controls ++
                  target :: scratch :: scratches)
                ((Gate.CCX control accumulator scratch :: []) ++
                  (mcxVChainTail scratch (nextControl :: controls)
                    target scratches ++
                      (Gate.CCX control accumulator scratch :: [])))
              exact hgate.append (hchild.append hgate)

theorem mcxVChain_usesOnly
    (controls : List Wire) (target : Wire) (scratches : List Wire) :
    PaperCircuitUsesOnly (controls ++ target :: scratches)
      (mcxVChain controls target scratches) := by
  cases controls with
  | nil => simp [mcxVChain, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
  | cons first controls =>
      cases controls with
      | nil =>
          simp [mcxVChain, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
      | cons second controls =>
          apply (mcxVChainTail_usesOnly second (first :: controls)
            target scratches).mono
          intro wire hwire
          simp only [List.mem_cons, List.mem_append] at hwire ⊢
          aesop

private theorem mcxVChainTail_wellFormed
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire)
    (hnonempty : controls ≠ [])
    (henough : controls.length - 1 ≤ scratches.length)
    (hlayout : (accumulator :: controls ++ target :: scratches).Nodup) :
    CircuitWellFormed
      (mcxVChainTail accumulator controls target scratches) := by
  induction controls generalizing accumulator scratches with
  | nil => exact (hnonempty rfl).elim
  | cons control controls ih =>
      cases controls with
      | nil =>
          have hroles : [accumulator, control, target].Nodup := by
            simp only [List.cons_append, List.nil_append, List.nodup_cons,
              List.mem_cons, List.not_mem_nil, or_false, not_or] at hlayout ⊢
            aesop
          have haccControl : accumulator ≠ control := by
            intro equality
            exact (List.nodup_cons.mp hroles).1 (by simp [equality])
          have haccTarget : accumulator ≠ target := by
            intro equality
            exact (List.nodup_cons.mp hroles).1 (by simp [equality])
          have hcontrolTarget : control ≠ target := by
            intro equality
            exact (List.nodup_cons.mp (List.nodup_cons.mp hroles).2).1
              (by simp [equality])
          simp [mcxVChainTail, CircuitWellFormed, Gate.WellFormed,
            haccControl, Ne.symm haccControl, haccTarget, hcontrolTarget]
      | cons nextControl controls =>
          cases scratches with
          | nil =>
              simp only [List.length_cons, List.length_nil] at henough
              omega
          | cons scratch scratches =>
              have hfirstRoles : [accumulator, control, scratch].Nodup :=
                mcxVChainTail_firstRoles accumulator control nextControl target scratch
                  controls scratches hlayout
              have hchildLayout :
                  (scratch :: (nextControl :: controls) ++ target :: scratches).Nodup :=
                mcxVChainTail_childLayout accumulator control nextControl target scratch
                  controls scratches hlayout
              have hchildEnough :
                  (nextControl :: controls).length - 1 ≤ scratches.length := by
                simp only [List.length_cons] at henough ⊢
                omega
              have haccControl : accumulator ≠ control := by
                intro equality
                exact (List.nodup_cons.mp hfirstRoles).1 (by simp [equality])
              have haccScratch : accumulator ≠ scratch := by
                intro equality
                exact (List.nodup_cons.mp hfirstRoles).1 (by simp [equality])
              have hcontrolScratch : control ≠ scratch := by
                intro equality
                exact (List.nodup_cons.mp
                  (List.nodup_cons.mp hfirstRoles).2).1 (by simp [equality])
              have hgate : Gate.WellFormed (.CCX control accumulator scratch) := by
                simp [Gate.WellFormed, haccControl, Ne.symm haccControl,
                  haccScratch, hcontrolScratch]
              rw [mcxVChainTail, circuitWellFormed_append,
                circuitWellFormed_append]
              exact ⟨⟨by simpa [CircuitWellFormed] using hgate,
                ih scratch scratches (by simp) hchildEnough hchildLayout⟩,
                by simpa [CircuitWellFormed] using hgate⟩

theorem mcxVChain_wellFormed
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (henough : controls.length - 2 ≤ scratches.length)
    (hlayout : McxVChainLayout controls target scratches) :
    CircuitWellFormed (mcxVChain controls target scratches) := by
  cases controls with
  | nil => simp [mcxVChain, CircuitWellFormed, Gate.WellFormed]
  | cons first controls =>
      cases controls with
      | nil =>
          have hne : first ≠ target := by
            intro equality
            exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
          simp [mcxVChain, CircuitWellFormed, Gate.WellFormed, hne]
      | cons second controls =>
          apply mcxVChainTail_wellFormed second (first :: controls) target scratches
          · simp
          · simpa using henough
          · simp only [McxVChainLayout, List.cons_append, List.nodup_cons,
              List.mem_cons, List.mem_append, not_or] at hlayout ⊢
            aesop

/-- Constructor-derived coherent Toffoli cost of a clean v-chain. -/
def mcxVChainToffoliCost : Nat → Nat
  | 0 | 1 => 0
  | length + 2 => 2 * length + 1

/-- Constructor-derived CNOT cost of a clean v-chain. -/
def mcxVChainCnotCost : Nat → Nat
  | 1 => 1
  | _ => 0

private theorem mcxVChainTail_toffoliCount
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire)
    (hnonempty : controls ≠ [])
    (henough : controls.length - 1 ≤ scratches.length) :
    eeaToffoliCount (mcxVChainTail accumulator controls target scratches) =
      2 * controls.length - 1 := by
  induction controls generalizing accumulator scratches with
  | nil => exact (hnonempty rfl).elim
  | cons control controls ih =>
      cases controls with
      | nil => rfl
      | cons nextControl controls =>
          cases scratches with
          | nil =>
              simp only [List.length_cons, List.length_nil] at henough
              omega
          | cons scratch scratches =>
              have hchildEnough :
                  (nextControl :: controls).length - 1 ≤ scratches.length := by
                simp only [List.length_cons] at henough ⊢
                omega
              rw [mcxVChainTail, eeaToffoliCount_append,
                eeaToffoliCount_append,
                ih scratch scratches (by simp) hchildEnough]
              simp only [eeaToffoliCount, List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil, List.length_cons]
              omega

@[simp]
theorem mcxVChain_toffoliCount
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (henough : controls.length - 2 ≤ scratches.length) :
    eeaToffoliCount (mcxVChain controls target scratches) =
      mcxVChainToffoliCost controls.length := by
  cases controls with
  | nil => rfl
  | cons first controls =>
      cases controls with
      | nil => rfl
      | cons second controls =>
          rw [mcxVChain]
          rw [mcxVChainTail_toffoliCount second (first :: controls) target scratches
            (by simp) (by simpa using henough)]
          simp [mcxVChainToffoliCost]
          omega

private theorem mcxVChainTail_cnotCount
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire) :
    eeaCnotCount (mcxVChainTail accumulator controls target scratches) = 0 := by
  induction controls generalizing accumulator scratches with
  | nil => rfl
  | cons control controls ih =>
      cases controls with
      | nil => rfl
      | cons nextControl controls =>
          cases scratches with
          | nil => rfl
          | cons scratch scratches =>
              rw [mcxVChainTail, eeaCnotCount_append,
                eeaCnotCount_append, ih scratch scratches]
              rfl

@[simp]
theorem mcxVChain_cnotCount
    (controls : List Wire) (target : Wire) (scratches : List Wire) :
    eeaCnotCount (mcxVChain controls target scratches) =
      mcxVChainCnotCost controls.length := by
  cases controls with
  | nil => rfl
  | cons first controls =>
      cases controls with
      | nil => rfl
      | cons second controls =>
          exact mcxVChainTail_cnotCount second (first :: controls)
            target scratches

private theorem mcxVChainTail_tCount_eq
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire) :
    ShorECDLP.tCount (mcxVChainTail accumulator controls target scratches) =
      7 * eeaToffoliCount
        (mcxVChainTail accumulator controls target scratches) := by
  induction controls generalizing accumulator scratches with
  | nil => rfl
  | cons control controls ih =>
      cases controls with
      | nil => rfl
      | cons nextControl controls =>
          cases scratches with
          | nil => rfl
          | cons scratch scratches =>
              rw [mcxVChainTail, tCount_append, tCount_append,
                eeaToffoliCount_append, eeaToffoliCount_append,
                ih scratch scratches]
              simp only [ShorECDLP.tCount, eeaToffoliCount, List.map_cons,
                List.map_nil, List.map_append, List.sum_cons, List.sum_nil,
                ShorECDLP.tCost]
              omega

@[simp]
theorem mcxVChain_tCount
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (henough : controls.length - 2 ≤ scratches.length) :
    ShorECDLP.tCount (mcxVChain controls target scratches) =
      7 * mcxVChainToffoliCost controls.length := by
  cases controls with
  | nil => rfl
  | cons first controls =>
      cases controls with
      | nil => rfl
      | cons second controls =>
          rw [mcxVChain, mcxVChainTail_tCount_eq,
            mcxVChainTail_toffoliCount second (first :: controls)
              target scratches (by simp) (by simpa using henough)]
          simp [mcxVChainToffoliCost]
          omega

/-! ## Constant-equality controls -/

private theorem applyGate_upd_outside
    (support : List Wire) (gate : Gate)
    (huses : PaperGateUsesOnly support gate)
    (outside : Wire) (value : Bool) (state : BasisState)
    (houtside : outside ∉ support) :
    applyGate gate state[outside ↦ value] =
      (applyGate gate state)[outside ↦ value] := by
  have hnot : outside ∉ gateWires gate := by
    intro hmem
    exact houtside (huses outside hmem)
  cases gate with
  | X target =>
      simp only [gateWires, List.mem_singleton] at hnot
      funext wire
      by_cases hwire : wire = outside
      · subst wire
        simp [applyGate, upd, hnot]
      · by_cases hwireTarget : wire = target
        · subst wire
          simp [applyGate, upd, hwire, hnot, Ne.symm hnot]
        · simp [applyGate, upd, hwire, hwireTarget]
  | H target => rfl
  | CX control target =>
      simp only [gateWires, List.mem_cons, List.mem_singleton, not_or] at hnot
      funext wire
      by_cases hwire : wire = outside
      · subst wire
        simp [applyGate, upd, hnot.1, hnot.2.1]
      · by_cases hwireTarget : wire = target
        · subst wire
          simp [applyGate, upd, hwire, hnot.1, hnot.2.1,
            Ne.symm hnot.1, Ne.symm hnot.2.1]
        · simp [applyGate, upd, hwire, hwireTarget]
  | CCX first second target =>
      simp only [gateWires, List.mem_cons, List.mem_singleton, not_or] at hnot
      funext wire
      by_cases hwire : wire = outside
      · subst wire
        simp [applyGate, upd, hnot.1, hnot.2.1, hnot.2.2.1]
      · by_cases hwireTarget : wire = target
        · subst wire
          simp [applyGate, upd, hwire, hnot.1, hnot.2.1, hnot.2.2.1,
            Ne.symm hnot.1, Ne.symm hnot.2.1, Ne.symm hnot.2.2.1]
        · simp [applyGate, upd, hwire, hwireTarget]
  | P direction exponent target => rfl

/-- Updating a wire outside a circuit's declared support commutes through classical execution. -/
theorem PaperCircuitUsesOnly.run_upd_outside
    {support : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly support circuit)
    (outside : Wire) (value : Bool) (state : BasisState)
    (houtside : outside ∉ support) :
    run circuit state[outside ↦ value] =
      (run circuit state)[outside ↦ value] := by
  induction circuit generalizing state with
  | nil => rfl
  | cons gate circuit ih =>
      have hgate : PaperGateUsesOnly support gate := huses gate (by simp)
      have htail : PaperCircuitUsesOnly support circuit := by
        intro next hnext
        exact huses next (by simp [hnext])
      change run circuit (applyGate gate state[outside ↦ value]) =
        (run circuit (applyGate gate state))[outside ↦ value]
      rw [applyGate_upd_outside support gate hgate outside value state
        houtside, ih htail]

/-- X gates applied to register positions whose corresponding constant bit is zero. -/
def zeroMaskFrom : List Wire → Nat → Nat → Circuit
  | [], _, _ => []
  | wire :: wires, value, bit =>
      (if value.testBit bit then [] else [Gate.X wire]) ++
        zeroMaskFrom wires value (bit + 1)

def zeroMask (register : List Wire) (value : Nat) : Circuit :=
  zeroMaskFrom register value 0

/-- Boolean equality of a little-endian wire list with the low bits of a constant. -/
def registerMatchesFrom : List Wire → Nat → Nat → BasisState → Bool
  | [], _, _, _ => true
  | wire :: wires, value, bit, state =>
      decide (state wire = value.testBit bit) &&
        registerMatchesFrom wires value (bit + 1) state

def registerMatches (register : List Wire) (value : Nat)
    (state : BasisState) : Bool :=
  registerMatchesFrom register value 0 state

theorem registerMatchesFrom_upd_not_mem
    (register : List Wire) (value bit : Nat) (state : BasisState)
    (outside : Wire) (replacement : Bool) (houtside : outside ∉ register) :
    registerMatchesFrom register value bit state[outside ↦ replacement] =
      registerMatchesFrom register value bit state := by
  induction register generalizing bit with
  | nil => rfl
  | cons wire wires ih =>
      simp only [List.mem_cons, not_or] at houtside
      rw [registerMatchesFrom, registerMatchesFrom,
        upd_other state outside replacement (by
          exact fun equality ↦ houtside.1 equality.symm),
        ih (bit + 1) houtside.2]

theorem zeroMaskFrom_usesOnly
    (register : List Wire) (value bit : Nat) :
    PaperCircuitUsesOnly register (zeroMaskFrom register value bit) := by
  induction register generalizing bit with
  | nil => simp [zeroMaskFrom, PaperCircuitUsesOnly]
  | cons wire wires ih =>
      by_cases hbit : value.testBit bit
      · rw [zeroMaskFrom, if_pos hbit]
        simpa using (ih (bit + 1)).mono (by
          intro next hnext
          simp [hnext])
      · rw [zeroMaskFrom, if_neg hbit]
        apply PaperCircuitUsesOnly.append
        · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
        · exact (ih (bit + 1)).mono (by
            intro next hnext
            simp [hnext])

theorem zeroMask_usesOnly (register : List Wire) (value : Nat) :
    PaperCircuitUsesOnly register (zeroMask register value) :=
  zeroMaskFrom_usesOnly register value 0

@[simp]
theorem zeroMaskFrom_HPFree
    (register : List Wire) (value bit : Nat) :
    HPFree (zeroMaskFrom register value bit) := by
  induction register generalizing bit with
  | nil => simp [zeroMaskFrom]
  | cons wire wires ih =>
      by_cases hbit : value.testBit bit <;>
        simp [zeroMaskFrom, hbit, ih]

@[simp]
theorem zeroMask_HPFree (register : List Wire) (value : Nat) :
    HPFree (zeroMask register value) := zeroMaskFrom_HPFree register value 0

theorem zeroMaskFrom_wellFormed
    (register : List Wire) (value bit : Nat) :
    CircuitWellFormed (zeroMaskFrom register value bit) := by
  induction register generalizing bit with
  | nil => simp [zeroMaskFrom]
  | cons wire wires ih =>
      by_cases hbit : value.testBit bit
      · rw [zeroMaskFrom, if_pos hbit]
        simpa using ih (bit + 1)
      · rw [zeroMaskFrom, if_neg hbit, circuitWellFormed_append]
        exact ⟨by simp [CircuitWellFormed, Gate.WellFormed], ih (bit + 1)⟩

theorem zeroMask_wellFormed (register : List Wire) (value : Nat) :
    CircuitWellFormed (zeroMask register value) :=
  zeroMaskFrom_wellFormed register value 0

theorem wireAnd_run_zeroMaskFrom
    (register : List Wire) (value bit : Nat) (state : BasisState)
    (hnd : register.Nodup) :
    wireAnd register (run (zeroMaskFrom register value bit) state) =
      registerMatchesFrom register value bit state := by
  induction register generalizing bit state with
  | nil => rfl
  | cons wire wires ih =>
      have hnot : wire ∉ wires := (List.nodup_cons.mp hnd).1
      have htailNodup : wires.Nodup := (List.nodup_cons.mp hnd).2
      by_cases hbit : value.testBit bit
      · rw [zeroMaskFrom, if_pos hbit]
        simp only [List.nil_append]
        have hwire := (zeroMaskFrom_usesOnly wires value (bit + 1)).preservesOutside
          state hnot
        rw [wireAnd, hwire, ih (bit + 1) state htailNodup,
          registerMatchesFrom]
        cases hw : state wire <;> simp [hbit, hw]
      · rw [zeroMaskFrom, if_neg hbit, run_append]
        let first := run [Gate.X wire] state
        have hfirst : first = state[wire ↦ !state wire] := by
          funext next
          by_cases hnext : next = wire
          · subst next
            simp [first, run, applyGate, upd]
          · simp [first, run, applyGate, upd, hnext]
        have hwire := (zeroMaskFrom_usesOnly wires value (bit + 1)).preservesOutside
          first hnot
        have htailMatch :
            registerMatchesFrom wires value (bit + 1) first =
              registerMatchesFrom wires value (bit + 1) state := by
          rw [hfirst, registerMatchesFrom_upd_not_mem _ _ _ _ _ _ hnot]
        rw [wireAnd, hwire, ih (bit + 1) first htailNodup, htailMatch,
          registerMatchesFrom, hfirst]
        cases hw : state wire <;> simp [hbit, hw, upd]

theorem wireAnd_run_zeroMask
    (register : List Wire) (value : Nat) (state : BasisState)
    (hnd : register.Nodup) :
    wireAnd register (run (zeroMask register value) state) =
      registerMatches register value state :=
  wireAnd_run_zeroMaskFrom register value 0 state hnd

/-- The source emits the same forward-order X-mask loop before and after its equality v-chain.
Distinct register wires make that literal loop an involution. -/
theorem run_zeroMaskFrom_twice
    (register : List Wire) (value bit : Nat) (state : BasisState)
    (hnd : register.Nodup) :
    run (zeroMaskFrom register value bit)
        (run (zeroMaskFrom register value bit) state) = state := by
  induction register generalizing bit state with
  | nil => rfl
  | cons wire wires ih =>
      have hnot : wire ∉ wires := (List.nodup_cons.mp hnd).1
      have htailNodup : wires.Nodup := (List.nodup_cons.mp hnd).2
      by_cases hbit : value.testBit bit
      · rw [zeroMaskFrom, if_pos hbit]
        simpa using ih (bit + 1) state htailNodup
      · let tail := zeroMaskFrom wires value (bit + 1)
        have huses : PaperCircuitUsesOnly wires tail :=
          zeroMaskFrom_usesOnly wires value (bit + 1)
        have htoggle (before : BasisState) :
            run [Gate.X wire] before = before[wire ↦ !before wire] := by
          funext next
          by_cases hnext : next = wire
          · subst next
            simp [run, applyGate, upd]
          · simp [run, applyGate, upd, hnext]
        rw [zeroMaskFrom, if_neg hbit, run_append, run_append]
        change run tail (run [Gate.X wire]
          (run tail (run [Gate.X wire] state))) = state
        rw [htoggle state,
          huses.run_upd_outside wire (!state wire) state hnot]
        have hsecondToggle :
            run [Gate.X wire] ((run tail state)[wire ↦ !state wire]) =
              (run tail state)[wire ↦ state wire] := by
          rw [htoggle]
          funext next
          by_cases hnext : next = wire
          · subst next
            simp [upd]
          · simp [upd, hnext]
        rw [hsecondToggle,
          huses.run_upd_outside wire (state wire) (run tail state) hnot,
          ih (bit + 1) state htailNodup]
        funext next
        by_cases hnext : next = wire
        · subst next
          simp [upd]
        · simp [upd, hnext]

theorem run_zeroMask_twice
    (register : List Wire) (value : Nat) (state : BasisState)
    (hnd : register.Nodup) :
    run (zeroMask register value) (run (zeroMask register value) state) = state :=
  run_zeroMaskFrom_twice register value 0 state hnd

private theorem zeroMaskFrom_toffoliCount
    (register : List Wire) (value bit : Nat) :
    eeaToffoliCount (zeroMaskFrom register value bit) = 0 := by
  induction register generalizing bit with
  | nil => rfl
  | cons wire wires ih =>
      by_cases hbit : value.testBit bit
      · rw [zeroMaskFrom, if_pos hbit]
        simpa using ih (bit + 1)
      · rw [zeroMaskFrom, if_neg hbit, eeaToffoliCount_append,
          ih (bit + 1)]
        rfl

@[simp]
theorem zeroMask_toffoliCount (register : List Wire) (value : Nat) :
    eeaToffoliCount (zeroMask register value) = 0 :=
  zeroMaskFrom_toffoliCount register value 0

private theorem zeroMaskFrom_cnotCount
    (register : List Wire) (value bit : Nat) :
    eeaCnotCount (zeroMaskFrom register value bit) = 0 := by
  induction register generalizing bit with
  | nil => rfl
  | cons wire wires ih =>
      by_cases hbit : value.testBit bit
      · rw [zeroMaskFrom, if_pos hbit]
        simpa using ih (bit + 1)
      · rw [zeroMaskFrom, if_neg hbit, eeaCnotCount_append,
          ih (bit + 1)]
        rfl

@[simp]
theorem zeroMask_cnotCount (register : List Wire) (value : Nat) :
    eeaCnotCount (zeroMask register value) = 0 :=
  zeroMaskFrom_cnotCount register value 0

private theorem zeroMaskFrom_tCount
    (register : List Wire) (value bit : Nat) :
    ShorECDLP.tCount (zeroMaskFrom register value bit) = 0 := by
  induction register generalizing bit with
  | nil => rfl
  | cons wire wires ih =>
      by_cases hbit : value.testBit bit
      · rw [zeroMaskFrom, if_pos hbit]
        simpa using ih (bit + 1)
      · rw [zeroMaskFrom, if_neg hbit, tCount_append,
          ih (bit + 1)]
        rfl

@[simp]
theorem zeroMask_tCount (register : List Wire) (value : Nat) :
    ShorECDLP.tCount (zeroMask register value) = 0 :=
  zeroMaskFrom_tCount register value 0

/-- Literal source equality compute: the same forward-order X-mask loop surrounds the clean
v-chain, so calling this circuit twice uncomputes the equality flag. -/
def computeEqConst (register : List Wire) (value : Nat)
    (flag : Wire) (scratches : List Wire) : Circuit :=
  (zeroMask register value ++ mcxVChain register flag scratches) ++
    zeroMask register value

/-- Layout and clean-v-chain capacity needed by the equality compute. -/
def EqConstLayout (register : List Wire) (flag : Wire)
    (scratches : List Wire) : Prop :=
  register.length - 2 ≤ scratches.length ∧
    McxVChainLayout register flag scratches

private theorem eqConstLayout_registerNodup
    (register : List Wire) (flag : Wire) (scratches : List Wire)
    (hlayout : EqConstLayout register flag scratches) :
    register.Nodup := by
  exact (List.nodup_append.mp hlayout.2).1

private theorem eqConstLayout_flag_not_mem
    (register : List Wire) (flag : Wire) (scratches : List Wire)
    (hlayout : EqConstLayout register flag scratches) :
    flag ∉ register := by
  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hlayout.2
  intro hmem
  exact hcross flag hmem flag (by simp) rfl

private theorem eqConstLayout_scratch_not_mem
    (register : List Wire) (flag : Wire) (scratches : List Wire)
    (hlayout : EqConstLayout register flag scratches) :
    ∀ wire ∈ scratches, wire ∉ register := by
  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp hlayout.2
  intro wire hwire hmem
  exact hcross wire hmem wire (by simp [hwire]) rfl

private theorem eqConstLayout_flag_not_scratch
    (register : List Wire) (flag : Wire) (scratches : List Wire)
    (hlayout : EqConstLayout register flag scratches) :
    flag ∉ scratches := by
  obtain ⟨_, htail, _⟩ := List.nodup_append.mp hlayout.2
  exact (List.nodup_cons.mp htail).1

/-- The equality compute toggles only its flag, exactly when the little-endian register matches
the requested constant; all clean v-chain scratch is restored. -/
theorem run_computeEqConst
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire) (state : BasisState)
    (hlayout : EqConstLayout register flag scratches)
    (hclean : Clean scratches state) :
    run (computeEqConst register value flag scratches) state =
      state[flag ↦ Bool.xor (state flag)
        (registerMatches register value state)] := by
  let mask := zeroMask register value
  let masked := run mask state
  have hregisterNodup :=
    eqConstLayout_registerNodup register flag scratches hlayout
  have hflagOutside :=
    eqConstLayout_flag_not_mem register flag scratches hlayout
  have hmaskUses : PaperCircuitUsesOnly register mask :=
    zeroMask_usesOnly register value
  have hmaskedFlag : masked flag = state flag :=
    hmaskUses.preservesOutside state hflagOutside
  have hmaskedClean : Clean scratches masked := by
    intro scratch hscratch
    change run mask state scratch = false
    rw [hmaskUses.preservesOutside state
      (eqConstLayout_scratch_not_mem register flag scratches hlayout
        scratch hscratch)]
    exact hclean scratch hscratch
  have hchain := run_mcxVChain register flag scratches masked
    hlayout.1 hlayout.2 hmaskedClean
  have hmatch : wireAnd register masked =
      registerMatches register value state := by
    exact wireAnd_run_zeroMask register value state hregisterNodup
  rw [computeEqConst, run_append, run_append]
  change run mask
    (run (mcxVChain register flag scratches) masked) = _
  rw [hchain, hmaskUses.run_upd_outside flag
    (Bool.xor (masked flag) (wireAnd register masked)) masked hflagOutside,
    run_zeroMask_twice register value state hregisterNodup,
    hmaskedFlag, hmatch]

/-- Calling the identical source-order equality compute twice restores the complete basis
state; in particular the equality flag and every v-chain scratch are returned. -/
theorem run_computeEqConst_twice
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire) (state : BasisState)
    (hlayout : EqConstLayout register flag scratches)
    (hclean : Clean scratches state) :
    run (computeEqConst register value flag scratches)
        (run (computeEqConst register value flag scratches) state) = state := by
  let matched := registerMatches register value state
  let after := state[flag ↦ Bool.xor (state flag) matched]
  have hfirst :
      run (computeEqConst register value flag scratches) state = after := by
    simpa only [after, matched] using
      run_computeEqConst register value flag scratches state hlayout hclean
  have hflagNotScratch :=
    eqConstLayout_flag_not_scratch register flag scratches hlayout
  have hcleanAfter : Clean scratches after := by
    intro scratch hscratch
    change state[flag ↦ Bool.xor (state flag) matched] scratch = false
    rw [upd_other state flag _ (by
      intro equality
      subst scratch
      exact hflagNotScratch hscratch)]
    exact hclean scratch hscratch
  rw [hfirst, run_computeEqConst register value flag scratches after
    hlayout hcleanAfter]
  have hflagOutside := eqConstLayout_flag_not_mem register flag scratches hlayout
  have hmatchAfter : registerMatches register value after = matched := by
    change registerMatchesFrom register value 0
      state[flag ↦ Bool.xor (state flag) matched] =
        registerMatchesFrom register value 0 state
    exact registerMatchesFrom_upd_not_mem register value 0 state flag
      (Bool.xor (state flag) matched) hflagOutside
  rw [hmatchAfter]
  funext wire
  by_cases hwire : wire = flag
  · subst wire
    simp [after, upd]
  · simp [after, upd, hwire]

theorem computeEqConst_usesOnly
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire) :
    PaperCircuitUsesOnly (register ++ flag :: scratches)
      (computeEqConst register value flag scratches) := by
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · exact (zeroMask_usesOnly register value).mono (by
        intro wire hwire
        simp [hwire])
    · exact mcxVChain_usesOnly register flag scratches
  · exact (zeroMask_usesOnly register value).mono (by
      intro wire hwire
      simp [hwire])

@[simp]
theorem computeEqConst_HPFree
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire) :
    HPFree (computeEqConst register value flag scratches) := by
  rw [computeEqConst, hpFree_append, hpFree_append]
  exact ⟨⟨zeroMask_HPFree register value,
    mcxVChain_HPFree register flag scratches⟩,
    zeroMask_HPFree register value⟩

theorem computeEqConst_wellFormed
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire)
    (hlayout : EqConstLayout register flag scratches) :
    CircuitWellFormed (computeEqConst register value flag scratches) := by
  rw [computeEqConst, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨zeroMask_wellFormed register value,
    mcxVChain_wellFormed register flag scratches hlayout.1 hlayout.2⟩,
    zeroMask_wellFormed register value⟩

@[simp]
theorem computeEqConst_toffoliCount
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire)
    (henough : register.length - 2 ≤ scratches.length) :
    eeaToffoliCount (computeEqConst register value flag scratches) =
      mcxVChainToffoliCost register.length := by
  rw [computeEqConst, eeaToffoliCount_append,
    eeaToffoliCount_append,
    zeroMask_toffoliCount, mcxVChain_toffoliCount register flag scratches henough]
  omega

@[simp]
theorem computeEqConst_cnotCount
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire) :
    eeaCnotCount (computeEqConst register value flag scratches) =
      mcxVChainCnotCost register.length := by
  rw [computeEqConst, eeaCnotCount_append, eeaCnotCount_append,
    zeroMask_cnotCount,
    mcxVChain_cnotCount]
  omega

@[simp]
theorem computeEqConst_tCount
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire)
    (henough : register.length - 2 ≤ scratches.length) :
    ShorECDLP.tCount (computeEqConst register value flag scratches) =
      7 * mcxVChainToffoliCost register.length := by
  rw [computeEqConst, tCount_append, tCount_append,
    zeroMask_tCount, mcxVChain_tCount register flag scratches henough]
  omega

/-- Compute equality, use it together with an external root control, and uncompute it. -/
def toggleEqConstUnderControl
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire) : Circuit :=
  let compute := computeEqConst register value flag scratches
  (compute ++ [Gate.CCX root flag accumulator]) ++ compute

/-- Complete physical layout for a direct constant-equality leaf. -/
def EqControlLayout
    (root : Wire) (register : List Wire) (accumulator flag : Wire)
    (scratches : List Wire) : Prop :=
  register.length - 2 ≤ scratches.length ∧
    (root :: accumulator :: register ++ flag :: scratches).Nodup

private theorem eqControlLayout_eqConst
    (root : Wire) (register : List Wire) (accumulator flag : Wire)
    (scratches : List Wire)
    (hlayout : EqControlLayout root register accumulator flag scratches) :
    EqConstLayout register flag scratches := by
  refine ⟨hlayout.1, ?_⟩
  exact (List.nodup_cons.mp (List.nodup_cons.mp hlayout.2).2).2

private theorem eqControlLayout_accumulatorOutside
    (root : Wire) (register : List Wire) (accumulator flag : Wire)
    (scratches : List Wire)
    (hlayout : EqControlLayout root register accumulator flag scratches) :
    accumulator ∉ register ++ flag :: scratches := by
  exact (List.nodup_cons.mp (List.nodup_cons.mp hlayout.2).2).1

private theorem eqControlLayout_root_flag_accumulator
    (root : Wire) (register : List Wire) (accumulator flag : Wire)
    (scratches : List Wire)
    (hlayout : EqControlLayout root register accumulator flag scratches) :
    [root, flag, accumulator].Nodup := by
  have hrootTail := (List.nodup_cons.mp hlayout.2).1
  have hafterRoot := (List.nodup_cons.mp hlayout.2).2
  have haccTail := (List.nodup_cons.mp hafterRoot).1
  have hrootAcc : root ≠ accumulator := by
    intro equality
    exact hrootTail (by simp [equality])
  have hrootFlag : root ≠ flag := by
    intro equality
    exact hrootTail (by simp [equality])
  have hflagAcc : flag ≠ accumulator := by
    intro equality
    exact haccTail (by simp [equality])
  simp [hrootAcc, hrootFlag, hflagAcc, Ne.symm hflagAcc]

/-- Direct whole-state action of the source's special-label selector.  Equality work and the
flag are restored, while the caller's range accumulator is toggled exactly on the selected
root-and-constant conjunction. -/
theorem run_toggleEqConstUnderControl
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (state : BasisState)
    (hlayout : EqControlLayout root register accumulator flag scratches)
    (hclean : Clean (flag :: scratches) state) :
    run (toggleEqConstUnderControl root register value accumulator flag scratches)
        state =
      state[accumulator ↦ Bool.xor (state accumulator)
        (state root && registerMatches register value state)] := by
  let compute := computeEqConst register value flag scratches
  let computed := run compute state
  have heqLayout :=
    eqControlLayout_eqConst root register accumulator flag scratches hlayout
  have hcomputeUses :
      PaperCircuitUsesOnly (register ++ flag :: scratches) compute :=
    computeEqConst_usesOnly register value flag scratches
  have haccOutside : accumulator ∉ register ++ flag :: scratches :=
    eqControlLayout_accumulatorOutside root register accumulator flag scratches hlayout
  have hroles : [root, flag, accumulator].Nodup :=
    eqControlLayout_root_flag_accumulator root register accumulator flag scratches hlayout
  have hrootFlag : root ≠ flag := by
    intro equality
    exact (List.nodup_cons.mp hroles).1 (by simp [equality])
  have haccFlag : accumulator ≠ flag := by
    intro equality
    exact (List.nodup_cons.mp (List.nodup_cons.mp hroles).2).1
      (by simp [equality])
  have hcomputed : computed =
      state[flag ↦ registerMatches register value state] := by
    change run compute state = _
    rw [run_computeEqConst register value flag scratches state heqLayout
      (fun wire hwire ↦ hclean wire (by simp [hwire]))]
    rw [hclean flag (by simp)]
    simp
  have hgate :
      run [Gate.CCX root flag accumulator] computed =
        computed[accumulator ↦ Bool.xor (computed accumulator)
          (computed root && computed flag)] := by
    funext wire
    by_cases hwire : wire = accumulator
    · subst wire
      simp [run, applyGate, upd]
    · simp [run, applyGate, upd, hwire]
  rw [toggleEqConstUnderControl, run_append, run_append]
  change run compute
    (run [Gate.CCX root flag accumulator] computed) = _
  rw [hgate,
    hcomputeUses.run_upd_outside accumulator
      (Bool.xor (computed accumulator) (computed root && computed flag))
      computed haccOutside,
    run_computeEqConst_twice register value flag scratches state heqLayout
      (fun wire hwire ↦ hclean wire (by simp [hwire]))]
  rw [hcomputed]
  funext wire
  by_cases hwire : wire = accumulator
  · subst wire
    simp [upd, haccFlag, hrootFlag]
  · simp [upd, hwire]

theorem toggleEqConstUnderControl_usesOnly
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire) :
    PaperCircuitUsesOnly
      (root :: accumulator :: register ++ flag :: scratches)
      (toggleEqConstUnderControl root register value accumulator flag scratches) := by
  let compute := computeEqConst register value flag scratches
  have hcompute : PaperCircuitUsesOnly
      (root :: accumulator :: register ++ flag :: scratches) compute :=
    (computeEqConst_usesOnly register value flag scratches).mono (by
      intro wire hwire
      simp only [List.mem_cons, List.mem_append] at hwire ⊢
      aesop)
  rw [toggleEqConstUnderControl]
  exact (hcompute.append (by
    simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires])).append
      hcompute

@[simp]
theorem toggleEqConstUnderControl_HPFree
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire) :
    HPFree
      (toggleEqConstUnderControl root register value accumulator flag scratches) := by
  let compute := computeEqConst register value flag scratches
  rw [toggleEqConstUnderControl, hpFree_append, hpFree_append]
  exact ⟨⟨computeEqConst_HPFree register value flag scratches, by simp⟩,
    computeEqConst_HPFree register value flag scratches⟩

theorem toggleEqConstUnderControl_wellFormed
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (hlayout : EqControlLayout root register accumulator flag scratches) :
    CircuitWellFormed
      (toggleEqConstUnderControl root register value accumulator flag scratches) := by
  let compute := computeEqConst register value flag scratches
  have hcompute : CircuitWellFormed compute :=
    computeEqConst_wellFormed register value flag scratches
      (eqControlLayout_eqConst root register accumulator flag scratches hlayout)
  have hgate : Gate.WellFormed (.CCX root flag accumulator) := by
    have hroles := eqControlLayout_root_flag_accumulator
      root register accumulator flag scratches hlayout
    have hrootFlag : root ≠ flag := by
      intro equality
      exact (List.nodup_cons.mp hroles).1 (by simp [equality])
    have hrootAccumulator : root ≠ accumulator := by
      intro equality
      exact (List.nodup_cons.mp hroles).1 (by simp [equality])
    have hflagAccumulator : flag ≠ accumulator := by
      intro equality
      exact (List.nodup_cons.mp (List.nodup_cons.mp hroles).2).1
        (by simp [equality])
    exact ⟨hrootFlag, hrootAccumulator, hflagAccumulator⟩
  rw [toggleEqConstUnderControl, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨hcompute, by simpa [CircuitWellFormed] using hgate⟩, hcompute⟩

@[simp]
theorem toggleEqConstUnderControl_toffoliCount
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (henough : register.length - 2 ≤ scratches.length) :
    eeaToffoliCount
        (toggleEqConstUnderControl root register value accumulator flag scratches) =
      2 * mcxVChainToffoliCost register.length + 1 := by
  rw [toggleEqConstUnderControl, eeaToffoliCount_append,
    eeaToffoliCount_append,
    computeEqConst_toffoliCount register value flag scratches henough]
  simp [eeaToffoliCount]
  omega

@[simp]
theorem toggleEqConstUnderControl_cnotCount
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire) :
    eeaCnotCount
        (toggleEqConstUnderControl root register value accumulator flag scratches) =
      2 * mcxVChainCnotCost register.length := by
  rw [toggleEqConstUnderControl, eeaCnotCount_append,
    eeaCnotCount_append,
    computeEqConst_cnotCount]
  simp [eeaCnotCount]
  omega

@[simp]
theorem toggleEqConstUnderControl_tCount
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (henough : register.length - 2 ≤ scratches.length) :
    ShorECDLP.tCount
        (toggleEqConstUnderControl root register value accumulator flag scratches) =
      14 * mcxVChainToffoliCost register.length + 7 := by
  rw [toggleEqConstUnderControl, tCount_append, tCount_append,
    computeEqConst_tCount register value flag scratches henough]
  simp [ShorECDLP.tCount, ShorECDLP.tCost]
  omega

/-! ## Main-tree masked-zero switches -/

/-- The main-tree leaf zero is masked exactly when the separately handled top label exists. -/
def maskedZeroLeaf (topSpecial : Bool) (label : Nat) : Bool :=
  topSpecial && decide (label = 0)

/-- Source literal for an endpoint switch at a main-tree leaf. -/
def endpointLeafToggle
    (topSpecial : Bool) (label : Nat) (endpointTop control accumulator : Wire) :
    Circuit :=
  if maskedZeroLeaf topSpecial label then
    [Gate.X endpointTop, Gate.CCX control endpointTop accumulator,
      Gate.X endpointTop]
  else
    [Gate.CX control accumulator]

/-- Pure Boolean action of a main-tree endpoint switch. -/
def endpointLeafToggleState
    (topSpecial : Bool) (label : Nat) (endpointTop control accumulator : Wire)
    (state : BasisState) : BasisState :=
  state[accumulator ↦ Bool.xor (state accumulator)
    (state control &&
      if maskedZeroLeaf topSpecial label then !state endpointTop else true)]

theorem run_endpointLeafToggle
    (topSpecial : Bool) (label : Nat) (endpointTop control accumulator : Wire)
    (state : BasisState)
    (hlayout : [control, endpointTop, accumulator].Nodup) :
    run (endpointLeafToggle topSpecial label endpointTop control accumulator) state =
      endpointLeafToggleState topSpecial label endpointTop control accumulator state := by
  have hcontrolTop : control ≠ endpointTop := by
    intro equality
    exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
  have hcontrolAccumulator : control ≠ accumulator := by
    intro equality
    exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
  have htopAccumulator : endpointTop ≠ accumulator := by
    intro equality
    exact (List.nodup_cons.mp (List.nodup_cons.mp hlayout).2).1
      (by simp [equality])
  by_cases hmasked : maskedZeroLeaf topSpecial label
  · rw [endpointLeafToggle, if_pos hmasked]
    funext wire
    by_cases hwire : wire = accumulator
    · subst wire
      cases hc : state control <;> cases he : state endpointTop <;>
        cases ha : state accumulator <;>
        simp [endpointLeafToggleState, run, applyGate, upd, hmasked,
          hcontrolTop, hcontrolAccumulator, htopAccumulator,
          Ne.symm hcontrolTop, Ne.symm hcontrolAccumulator,
          Ne.symm htopAccumulator, hc, he, ha]
    · by_cases hwireTop : wire = endpointTop
      · subst wire
        cases hc : state control <;> cases he : state endpointTop <;>
          cases ha : state accumulator <;>
          simp [endpointLeafToggleState, run, applyGate, upd, hmasked,
            hwire, hcontrolTop, hcontrolAccumulator, htopAccumulator,
            Ne.symm hcontrolTop, Ne.symm hcontrolAccumulator,
            Ne.symm htopAccumulator, hc, he, ha]
      · simp [endpointLeafToggleState, run, applyGate, upd, hmasked,
          hwire, hwireTop]
  · rw [endpointLeafToggle, if_neg hmasked]
    funext wire
    by_cases hwire : wire = accumulator
    · subst wire
      cases hc : state control <;> cases ha : state accumulator <;>
        simp [endpointLeafToggleState, run, applyGate, upd, hmasked,
          hcontrolAccumulator, hc, ha]
    · simp [endpointLeafToggleState, run, applyGate, upd, hmasked, hwire]

theorem endpointLeafToggle_usesOnly
    (topSpecial : Bool) (label : Nat) (endpointTop control accumulator : Wire) :
    PaperCircuitUsesOnly [control, endpointTop, accumulator]
      (endpointLeafToggle topSpecial label endpointTop control accumulator) := by
  by_cases hmasked : maskedZeroLeaf topSpecial label <;>
    simp [endpointLeafToggle, hmasked, PaperCircuitUsesOnly,
      PaperGateUsesOnly, gateWires]

@[simp]
theorem endpointLeafToggle_HPFree
    (topSpecial : Bool) (label : Nat) (endpointTop control accumulator : Wire) :
    HPFree (endpointLeafToggle topSpecial label endpointTop control accumulator) := by
  by_cases hmasked : maskedZeroLeaf topSpecial label <;>
    simp [endpointLeafToggle, hmasked]

theorem endpointLeafToggle_wellFormed
    (topSpecial : Bool) (label : Nat) (endpointTop control accumulator : Wire)
    (hlayout : [control, endpointTop, accumulator].Nodup) :
    CircuitWellFormed
      (endpointLeafToggle topSpecial label endpointTop control accumulator) := by
  have hcontrolTop : control ≠ endpointTop := by
    intro equality
    exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
  have hcontrolAccumulator : control ≠ accumulator := by
    intro equality
    exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
  have htopAccumulator : endpointTop ≠ accumulator := by
    intro equality
    exact (List.nodup_cons.mp (List.nodup_cons.mp hlayout).2).1
      (by simp [equality])
  by_cases hmasked : maskedZeroLeaf topSpecial label <;>
    simp [endpointLeafToggle, hmasked, CircuitWellFormed, Gate.WellFormed,
      hcontrolTop, hcontrolAccumulator, htopAccumulator]

@[simp]
theorem endpointLeafToggle_toffoliCount
    (topSpecial : Bool) (label : Nat) (endpointTop control accumulator : Wire) :
    eeaToffoliCount
        (endpointLeafToggle topSpecial label endpointTop control accumulator) =
      if maskedZeroLeaf topSpecial label then 1 else 0 := by
  by_cases hmasked : maskedZeroLeaf topSpecial label <;>
    simp [endpointLeafToggle, hmasked, eeaToffoliCount]

@[simp]
theorem endpointLeafToggle_cnotCount
    (topSpecial : Bool) (label : Nat) (endpointTop control accumulator : Wire) :
    eeaCnotCount
        (endpointLeafToggle topSpecial label endpointTop control accumulator) =
      if maskedZeroLeaf topSpecial label then 0 else 1 := by
  by_cases hmasked : maskedZeroLeaf topSpecial label <;>
    simp [endpointLeafToggle, hmasked, eeaCnotCount]

@[simp]
theorem endpointLeafToggle_tCount
    (topSpecial : Bool) (label : Nat) (endpointTop control accumulator : Wire) :
    ShorECDLP.tCount
        (endpointLeafToggle topSpecial label endpointTop control accumulator) =
      if maskedZeroLeaf topSpecial label then 7 else 0 := by
  by_cases hmasked : maskedZeroLeaf topSpecial label <;>
    simp [endpointLeafToggle, hmasked, ShorECDLP.tCount, ShorECDLP.tCost]

/-! ## Ripple-cell interface used by the interval leaves -/

theorem run_rippleFirstCell_state
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (state : BasisState)
    (hlayout : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    run (rippleFirstCell mode control target addend carry scratch) state =
      writeRippleCell target addend carry
        (rippleFirstBits mode (state control)
          (readRippleCell target addend carry state)) state := by
  cases mode with
  | add => simpa [rippleFirstCell, rippleFirstBits] using
      (run_controlledMaj_state control target addend carry scratch state
        hlayout hclean)
  | sub => simpa [rippleFirstCell, rippleFirstBits] using
      (run_controlledUmaInv_state control target addend carry scratch state
        hlayout hclean)

theorem run_rippleSecondCell_state
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (state : BasisState)
    (hlayout : [control, target, addend, carry, scratch].Nodup)
    (hclean : state scratch = false) :
    run (rippleSecondCell mode control target addend carry scratch) state =
      writeRippleCell target addend carry
        (rippleSecondBits mode (state control)
          (readRippleCell target addend carry state)) state := by
  cases mode with
  | add => simpa [rippleSecondCell, rippleSecondBits] using
      (run_controlledUma_state control target addend carry scratch state
        hlayout hclean)
  | sub => simpa [rippleSecondCell, rippleSecondBits] using
      (run_controlledMajInv_state control target addend carry scratch state
        hlayout hclean)

theorem rippleFirstCell_usesOnly
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, scratch]
      (rippleFirstCell mode control target addend carry scratch) := by
  cases mode with
  | add => exact controlledMaj_usesOnly control target addend carry scratch
  | sub => exact controlledUmaInv_usesOnly control target addend carry scratch

theorem rippleSecondCell_usesOnly
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    PaperCircuitUsesOnly [control, target, addend, carry, scratch]
      (rippleSecondCell mode control target addend carry scratch) := by
  cases mode with
  | add => exact controlledUma_usesOnly control target addend carry scratch
  | sub => exact controlledMajInv_usesOnly control target addend carry scratch

@[simp]
theorem rippleFirstCell_HPFree
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    HPFree (rippleFirstCell mode control target addend carry scratch) := by
  cases mode <;> simp [rippleFirstCell]

@[simp]
theorem rippleSecondCell_HPFree
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    HPFree (rippleSecondCell mode control target addend carry scratch) := by
  cases mode <;> simp [rippleSecondCell]

theorem rippleFirstCell_wellFormed
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (hlayout : [control, target, addend, carry, scratch].Nodup) :
    CircuitWellFormed
      (rippleFirstCell mode control target addend carry scratch) := by
  cases mode with
  | add => exact controlledMaj_wellFormed control target addend carry scratch hlayout
  | sub => exact controlledUmaInv_wellFormed control target addend carry scratch hlayout

theorem rippleSecondCell_wellFormed
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (hlayout : [control, target, addend, carry, scratch].Nodup) :
    CircuitWellFormed
      (rippleSecondCell mode control target addend carry scratch) := by
  cases mode with
  | add => exact controlledUma_wellFormed control target addend carry scratch hlayout
  | sub => exact controlledMajInv_wellFormed control target addend carry scratch hlayout

def rippleFirstCellToffoliCost : RippleMode → Nat
  | .add => 3
  | .sub => 4

def rippleSecondCellToffoliCost : RippleMode → Nat
  | .add => 4
  | .sub => 3

@[simp]
theorem rippleFirstCell_toffoliCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    eeaToffoliCount (rippleFirstCell mode control target addend carry scratch) =
      rippleFirstCellToffoliCost mode := by
  cases mode <;> rfl

@[simp]
theorem rippleSecondCell_toffoliCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    eeaToffoliCount (rippleSecondCell mode control target addend carry scratch) =
      rippleSecondCellToffoliCost mode := by
  cases mode <;> rfl

@[simp]
theorem rippleFirstCell_cnotCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    eeaCnotCount (rippleFirstCell mode control target addend carry scratch) = 2 := by
  cases mode <;> rfl

@[simp]
theorem rippleSecondCell_cnotCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    eeaCnotCount (rippleSecondCell mode control target addend carry scratch) = 2 := by
  cases mode <;> rfl

@[simp]
theorem rippleFirstCell_tCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    ShorECDLP.tCount (rippleFirstCell mode control target addend carry scratch) =
      7 * rippleFirstCellToffoliCost mode := by
  cases mode <;> rfl

@[simp]
theorem rippleSecondCell_tCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    ShorECDLP.tCount (rippleSecondCell mode control target addend carry scratch) =
      7 * rippleSecondCellToffoliCost mode := by
  cases mode <;> rfl

/-! ## Source-shaped interval arithmetic leaves -/

/-- Physical support of either main-tree interval leaf.  The dynamic decoder controls may be the
same wire, exactly as permitted by `DualUnaryActionTree.Layout`; every other role is distinct. -/
def intervalLeafSupport
    (rightControl leftControl rightTop leftTop accumulator target addend carry scratch : Wire) :
    List Wire :=
  [rightControl, leftControl].dedup ++
    [rightTop, leftTop, accumulator, target, addend, carry, scratch]

def IntervalLeafLayout
    (rightControl leftControl rightTop leftTop accumulator target addend carry scratch : Wire) :
    Prop :=
  (intervalLeafSupport rightControl leftControl rightTop leftTop
    accumulator target addend carry scratch).Nodup

private theorem intervalLeafLayout_parts
    (rightControl leftControl rightTop leftTop accumulator target addend carry scratch : Wire)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    [rightControl, rightTop, accumulator].Nodup ∧
      [leftControl, leftTop, accumulator].Nodup ∧
      [accumulator, target, addend, carry, scratch].Nodup := by
  obtain ⟨hcontrols, hroles, hcross⟩ := List.nodup_append.mp hlayout
  have hrightMem : rightControl ∈ [rightControl, leftControl].dedup := by simp
  have hleftMem : leftControl ∈ [rightControl, leftControl].dedup := by simp
  have hrightTopAcc : rightTop ≠ accumulator := by
    intro equality
    exact (List.nodup_cons.mp hroles).1 (by simp [equality])
  have hleftTopAcc : leftTop ≠ accumulator := by
    intro equality
    exact (List.nodup_cons.mp (List.nodup_cons.mp hroles).2).1
      (by simp [equality])
  have hrightControlTop : rightControl ≠ rightTop :=
    hcross rightControl hrightMem rightTop (by simp)
  have hrightControlAcc : rightControl ≠ accumulator :=
    hcross rightControl hrightMem accumulator (by simp)
  have hleftControlTop : leftControl ≠ leftTop :=
    hcross leftControl hleftMem leftTop (by simp)
  have hleftControlAcc : leftControl ≠ accumulator :=
    hcross leftControl hleftMem accumulator (by simp)
  have hcell : [accumulator, target, addend, carry, scratch].Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp hroles).2).2
  constructor
  · simp [hrightControlTop, hrightControlAcc, hrightTopAcc]
  · constructor
    · simp [hleftControlTop, hleftControlAcc, hleftTopAcc]
    · exact hcell

/-- First (high-to-low) leaf: right-endpoint switch, first Cuccaro cell, then left-endpoint
switch.  This is the source's `.dec` leaf action. -/
def intervalFirstLeaf
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) : Circuit :=
  (endpointLeafToggle topSpecial label rightTop rightControl accumulator ++
    rippleFirstCell mode accumulator target addend carry scratch) ++
    endpointLeafToggle topSpecial label leftTop leftControl accumulator

/-- Second (low-to-high) leaf: left-endpoint switch, second Cuccaro cell, then right-endpoint
switch.  This is the source's `.inc` leaf action. -/
def intervalSecondLeaf
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) : Circuit :=
  (endpointLeafToggle topSpecial label leftTop leftControl accumulator ++
    rippleSecondCell mode accumulator target addend carry scratch) ++
    endpointLeafToggle topSpecial label rightTop rightControl accumulator

def intervalFirstLeafState
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState) : BasisState :=
  let afterRight := endpointLeafToggleState topSpecial label
    rightTop rightControl accumulator state
  let afterCell := writeRippleCell target addend carry
    (rippleFirstBits mode (afterRight accumulator)
      (readRippleCell target addend carry afterRight)) afterRight
  endpointLeafToggleState topSpecial label leftTop leftControl accumulator afterCell

def intervalSecondLeafState
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState) : BasisState :=
  let afterLeft := endpointLeafToggleState topSpecial label
    leftTop leftControl accumulator state
  let afterCell := writeRippleCell target addend carry
    (rippleSecondBits mode (afterLeft accumulator)
      (readRippleCell target addend carry afterLeft)) afterLeft
  endpointLeafToggleState topSpecial label rightTop rightControl accumulator afterCell

theorem run_intervalFirstLeaf
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch)
    (hclean : state scratch = false) :
    run (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) state =
      intervalFirstLeafState mode topSpecial rightTop leftTop accumulator
        target addend carry label rightControl leftControl state := by
  obtain ⟨hright, hleft, hcell⟩ := intervalLeafLayout_parts
    rightControl leftControl rightTop leftTop accumulator target addend carry scratch
      hlayout
  have haccScratch : accumulator ≠ scratch := by
    intro equality
    exact (List.nodup_cons.mp hcell).1 (by simp [equality])
  let afterRight := endpointLeafToggleState topSpecial label
    rightTop rightControl accumulator state
  have hafterRight :
      run (endpointLeafToggle topSpecial label rightTop rightControl accumulator) state =
        afterRight := run_endpointLeafToggle topSpecial label rightTop rightControl
          accumulator state hright
  have hcleanAfterRight : afterRight scratch = false := by
    simp [afterRight, endpointLeafToggleState, upd, Ne.symm haccScratch, hclean]
  rw [intervalFirstLeaf, run_append, run_append, hafterRight,
    run_rippleFirstCell_state mode accumulator target addend carry scratch
      afterRight hcell hcleanAfterRight,
    run_endpointLeafToggle topSpecial label leftTop leftControl accumulator _ hleft]
  rfl

theorem run_intervalSecondLeaf
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch)
    (hclean : state scratch = false) :
    run (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) state =
      intervalSecondLeafState mode topSpecial rightTop leftTop accumulator
        target addend carry label rightControl leftControl state := by
  obtain ⟨hright, hleft, hcell⟩ := intervalLeafLayout_parts
    rightControl leftControl rightTop leftTop accumulator target addend carry scratch
      hlayout
  have haccScratch : accumulator ≠ scratch := by
    intro equality
    exact (List.nodup_cons.mp hcell).1 (by simp [equality])
  let afterLeft := endpointLeafToggleState topSpecial label
    leftTop leftControl accumulator state
  have hafterLeft :
      run (endpointLeafToggle topSpecial label leftTop leftControl accumulator) state =
        afterLeft := run_endpointLeafToggle topSpecial label leftTop leftControl
          accumulator state hleft
  have hcleanAfterLeft : afterLeft scratch = false := by
    simp [afterLeft, endpointLeafToggleState, upd, Ne.symm haccScratch, hclean]
  rw [intervalSecondLeaf, run_append, run_append, hafterLeft,
    run_rippleSecondCell_state mode accumulator target addend carry scratch
      afterLeft hcell hcleanAfterLeft,
    run_endpointLeafToggle topSpecial label rightTop rightControl accumulator _ hright]
  rfl

theorem intervalFirstLeaf_usesOnly
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    PaperCircuitUsesOnly
      (intervalLeafSupport rightControl leftControl rightTop leftTop
        accumulator target addend carry scratch)
      (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) := by
  rw [intervalFirstLeaf]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply (endpointLeafToggle_usesOnly topSpecial label
        rightTop rightControl accumulator).mono
      intro wire hwire
      simp only [intervalLeafSupport, List.mem_append, List.mem_cons,
        List.mem_dedup] at hwire ⊢
      aesop
    · apply (rippleFirstCell_usesOnly mode accumulator target addend carry scratch).mono
      intro wire hwire
      simp only [intervalLeafSupport, List.mem_append, List.mem_cons,
        List.mem_dedup] at hwire ⊢
      aesop
  · apply (endpointLeafToggle_usesOnly topSpecial label
      leftTop leftControl accumulator).mono
    intro wire hwire
    simp only [intervalLeafSupport, List.mem_append, List.mem_cons,
      List.mem_dedup] at hwire ⊢
    aesop

theorem intervalSecondLeaf_usesOnly
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    PaperCircuitUsesOnly
      (intervalLeafSupport rightControl leftControl rightTop leftTop
        accumulator target addend carry scratch)
      (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) := by
  rw [intervalSecondLeaf]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply (endpointLeafToggle_usesOnly topSpecial label
        leftTop leftControl accumulator).mono
      intro wire hwire
      simp only [intervalLeafSupport, List.mem_append, List.mem_cons,
        List.mem_dedup] at hwire ⊢
      aesop
    · apply (rippleSecondCell_usesOnly mode accumulator target addend carry scratch).mono
      intro wire hwire
      simp only [intervalLeafSupport, List.mem_append, List.mem_cons,
        List.mem_dedup] at hwire ⊢
      aesop
  · apply (endpointLeafToggle_usesOnly topSpecial label
      rightTop rightControl accumulator).mono
    intro wire hwire
    simp only [intervalLeafSupport, List.mem_append, List.mem_cons,
      List.mem_dedup] at hwire ⊢
    aesop

@[simp]
theorem intervalFirstLeaf_HPFree
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    HPFree (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl) := by
  simp [intervalFirstLeaf]

@[simp]
theorem intervalSecondLeaf_HPFree
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    HPFree (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl) := by
  simp [intervalSecondLeaf]

theorem intervalFirstLeaf_wellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    CircuitWellFormed
      (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) := by
  obtain ⟨hright, hleft, hcell⟩ := intervalLeafLayout_parts
    rightControl leftControl rightTop leftTop accumulator target addend carry scratch
      hlayout
  rw [intervalFirstLeaf, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨endpointLeafToggle_wellFormed topSpecial label rightTop
      rightControl accumulator hright,
    rippleFirstCell_wellFormed mode accumulator target addend carry scratch hcell⟩,
    endpointLeafToggle_wellFormed topSpecial label leftTop
      leftControl accumulator hleft⟩

theorem intervalSecondLeaf_wellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    CircuitWellFormed
      (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) := by
  obtain ⟨hright, hleft, hcell⟩ := intervalLeafLayout_parts
    rightControl leftControl rightTop leftTop accumulator target addend carry scratch
      hlayout
  rw [intervalSecondLeaf, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨endpointLeafToggle_wellFormed topSpecial label leftTop
      leftControl accumulator hleft,
    rippleSecondCell_wellFormed mode accumulator target addend carry scratch hcell⟩,
    endpointLeafToggle_wellFormed topSpecial label rightTop
      rightControl accumulator hright⟩

@[simp]
theorem intervalFirstLeaf_toffoliCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    eeaToffoliCount
        (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl) =
      rippleFirstCellToffoliCost mode +
        if maskedZeroLeaf topSpecial label then 2 else 0 := by
  rw [intervalFirstLeaf, eeaToffoliCount_append,
    eeaToffoliCount_append, rippleFirstCell_toffoliCount,
    endpointLeafToggle_toffoliCount, endpointLeafToggle_toffoliCount]
  split <;> omega

@[simp]
theorem intervalSecondLeaf_toffoliCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    eeaToffoliCount
        (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl) =
      rippleSecondCellToffoliCost mode +
        if maskedZeroLeaf topSpecial label then 2 else 0 := by
  rw [intervalSecondLeaf, eeaToffoliCount_append,
    eeaToffoliCount_append, rippleSecondCell_toffoliCount,
    endpointLeafToggle_toffoliCount, endpointLeafToggle_toffoliCount]
  split <;> omega

@[simp]
theorem intervalFirstLeaf_cnotCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    eeaCnotCount
        (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl) =
      2 + if maskedZeroLeaf topSpecial label then 0 else 2 := by
  rw [intervalFirstLeaf, eeaCnotCount_append,
    eeaCnotCount_append, rippleFirstCell_cnotCount,
    endpointLeafToggle_cnotCount, endpointLeafToggle_cnotCount]
  split <;> omega

@[simp]
theorem intervalSecondLeaf_cnotCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    eeaCnotCount
        (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl) =
      2 + if maskedZeroLeaf topSpecial label then 0 else 2 := by
  rw [intervalSecondLeaf, eeaCnotCount_append,
    eeaCnotCount_append, rippleSecondCell_cnotCount,
    endpointLeafToggle_cnotCount, endpointLeafToggle_cnotCount]
  split <;> omega

@[simp]
theorem intervalFirstLeaf_tCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    ShorECDLP.tCount
        (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl) =
      7 * (rippleFirstCellToffoliCost mode +
        if maskedZeroLeaf topSpecial label then 2 else 0) := by
  rw [intervalFirstLeaf, tCount_append, tCount_append,
    rippleFirstCell_tCount, endpointLeafToggle_tCount,
    endpointLeafToggle_tCount]
  split <;> omega

@[simp]
theorem intervalSecondLeaf_tCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    ShorECDLP.tCount
        (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          target addend carry scratch label rightControl leftControl) =
      7 * (rippleSecondCellToffoliCost mode +
        if maskedZeroLeaf topSpecial label then 2 else 0) := by
  rw [intervalSecondLeaf, tCount_append, tCount_append,
    rippleSecondCell_tCount, endpointLeafToggle_tCount,
    endpointLeafToggle_tCount]
  split <;> omega

private def gateTarget : Gate → Wire
  | .X target | .H target | .P _ _ target => target
  | .CX _ target | .CCX _ _ target => target

private def CircuitWritesOnly (support : List Wire) (circuit : Circuit) : Prop :=
  ∀ gate ∈ circuit, gateTarget gate ∈ support

private theorem CircuitWritesOnly.preservesOutside
    {support : List Wire} {circuit : Circuit}
    (hwrites : CircuitWritesOnly support circuit)
    (state : BasisState) (wire : Wire) (hwire : wire ∉ support) :
    run circuit state wire = state wire := by
  induction circuit generalizing state with
  | nil => rfl
  | cons gate circuit ih =>
      have hgate := hwrites gate (by simp)
      have htail : CircuitWritesOnly support circuit := by
        intro next hnext
        exact hwrites next (by simp [hnext])
      have hne : wire ≠ gateTarget gate := by
        intro equality
        apply hwire
        rw [equality]
        exact hgate
      rw [run_cons, ih htail]
      cases gate <;> simp_all [applyGate, upd, gateTarget]

private theorem intervalFirstLeaf_writesOnly
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    CircuitWritesOnly [rightTop, leftTop, accumulator, target, addend, carry, scratch]
      (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) := by
  cases mode <;> by_cases hmasked : maskedZeroLeaf topSpecial label <;>
    simp [CircuitWritesOnly, gateTarget, intervalFirstLeaf, endpointLeafToggle,
      hmasked, rippleFirstCell, controlledMaj, controlledUmaInv, cleanC3X]

private theorem intervalSecondLeaf_writesOnly
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    CircuitWritesOnly [rightTop, leftTop, accumulator, target, addend, carry, scratch]
      (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) := by
  cases mode <;> by_cases hmasked : maskedZeroLeaf topSpecial label <;>
    simp [CircuitWritesOnly, gateTarget, intervalSecondLeaf, endpointLeafToggle,
      hmasked, rippleSecondCell, controlledUma, controlledMajInv, cleanC3X]

/-- Every decoder wire outside the seven written roles is preserved without a scratch-clean
premise.  This is the contract needed by the generic synchronized traversal. -/
theorem intervalFirstLeaf_preservesOutside
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState) (wire : Wire)
    (hwire : wire ∉ [rightTop, leftTop, accumulator, target, addend, carry, scratch]) :
    run (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) state wire =
      state wire :=
  (intervalFirstLeaf_writesOnly mode topSpecial rightTop leftTop accumulator
    target addend carry scratch label rightControl leftControl).preservesOutside
      state wire hwire

theorem intervalSecondLeaf_preservesOutside
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState) (wire : Wire)
    (hwire : wire ∉ [rightTop, leftTop, accumulator, target, addend, carry, scratch]) :
    run (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) state wire =
      state wire :=
  (intervalSecondLeaf_writesOnly mode topSpecial rightTop leftTop accumulator
    target addend carry scratch label rightControl leftControl).preservesOutside
      state wire hwire

/-- Caller-side condition saying the tree's decoder interface is disjoint from the arithmetic
roles written by a leaf. -/
def DecoderOutsideIntervalRoles
    (protectedWires : List Wire)
    (rightTop leftTop accumulator target addend carry scratch : Wire) : Prop :=
  List.Disjoint protectedWires
    (rightTop :: leftTop :: accumulator :: target :: addend :: carry :: scratch :: [])

theorem intervalFirstLeaf_dualPreserves
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (protectedWires : List Wire)
    (houtside : DecoderOutsideIntervalRoles protectedWires rightTop leftTop
      accumulator target addend carry scratch) :
    DualUnaryLeafPreserves
      (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch) protectedWires := by
  rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
  intro label rightControl leftControl hright hleft state wire hwire
  exact intervalFirstLeaf_preservesOutside mode topSpecial rightTop leftTop
    accumulator target addend carry scratch label rightControl leftControl
      state wire (houtside hwire)

theorem intervalSecondLeaf_dualPreserves
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (protectedWires : List Wire)
    (houtside : DecoderOutsideIntervalRoles protectedWires rightTop leftTop
      accumulator target addend carry scratch) :
    DualUnaryLeafPreserves
      (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch) protectedWires := by
  rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
  intro label rightControl leftControl hright hleft state wire hwire
  exact intervalSecondLeaf_preservesOutside mode topSpecial rightTop leftTop
    accumulator target addend carry scratch label rightControl leftControl
      state wire (houtside hwire)

/-! ## Separately handled top label -/

def topSpecialLeafSupport
    (rightRoot leftRoot : Wire) (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) : List Wire :=
  [rightRoot, leftRoot].dedup ++ rightRegister ++ leftRegister ++
    [accumulator, target, addend, carry, rippleScratch, eqFlag] ++ eqScratches

/-- The two equality controls reuse the ripple's one clean scratch as their temporary equality
flag, exactly as in `eq_scratch = [cell_pool[0]] + Scratch[:base]` in the source.  Only the
remaining equality v-chain pool is disjoint from the ripple roles. -/
def TopSpecialLeafLayout
    (rightRoot leftRoot : Wire) (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) : Prop :=
  EqControlLayout rightRoot rightRegister accumulator eqFlag eqScratches ∧
    EqControlLayout leftRoot leftRegister accumulator eqFlag eqScratches ∧
    [accumulator, target, addend, carry, rippleScratch].Nodup ∧
    eqFlag = rippleScratch ∧
    List.Disjoint eqScratches
      (accumulator :: target :: addend :: carry :: rippleScratch :: [])

def topSpecialFirstLeaf
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) : Circuit :=
  (toggleEqConstUnderControl rightRoot rightRegister topValue accumulator
      eqFlag eqScratches ++
    rippleFirstCell mode accumulator target addend carry rippleScratch) ++
    toggleEqConstUnderControl leftRoot leftRegister topValue accumulator
      eqFlag eqScratches

def topSpecialSecondLeaf
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) : Circuit :=
  (toggleEqConstUnderControl leftRoot leftRegister topValue accumulator
      eqFlag eqScratches ++
    rippleSecondCell mode accumulator target addend carry rippleScratch) ++
    toggleEqConstUnderControl rightRoot rightRegister topValue accumulator
      eqFlag eqScratches

def topSpecialFirstLeafState
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry : Wire)
    (rightRoot leftRoot : Wire) (state : BasisState) : BasisState :=
  let afterRight := state[accumulator ↦ Bool.xor (state accumulator)
    (state rightRoot && registerMatches rightRegister topValue state)]
  let afterCell := writeRippleCell target addend carry
    (rippleFirstBits mode (afterRight accumulator)
      (readRippleCell target addend carry afterRight)) afterRight
  afterCell[accumulator ↦ Bool.xor (afterCell accumulator)
    (afterCell leftRoot && registerMatches leftRegister topValue afterCell)]

def topSpecialSecondLeafState
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry : Wire)
    (rightRoot leftRoot : Wire) (state : BasisState) : BasisState :=
  let afterLeft := state[accumulator ↦ Bool.xor (state accumulator)
    (state leftRoot && registerMatches leftRegister topValue state)]
  let afterCell := writeRippleCell target addend carry
    (rippleSecondBits mode (afterLeft accumulator)
      (readRippleCell target addend carry afterLeft)) afterLeft
  afterCell[accumulator ↦ Bool.xor (afterCell accumulator)
    (afterCell rightRoot && registerMatches rightRegister topValue afterCell)]

private theorem topSpecial_eqClean_after_cell
    (mode : RippleMode) (second : Bool)
    (accumulator target addend carry scratch : Wire)
    (eqScratches : List Wire) (before : BasisState)
    (hcell : [accumulator, target, addend, carry, scratch].Nodup)
    (hclean : Clean (scratch :: eqScratches) before)
    (hdisjoint : List.Disjoint eqScratches
      (accumulator :: target :: addend :: carry :: scratch :: [])) :
    Clean (scratch :: eqScratches)
      (run (if second then
          rippleSecondCell mode accumulator target addend carry scratch
        else rippleFirstCell mode accumulator target addend carry scratch)
        before) := by
  have htargetScratch : target ≠ scratch := by
    intro equality
    exact (List.nodup_cons.mp (List.nodup_cons.mp hcell).2).1
      (by simp [equality])
  have haddendScratch : addend ≠ scratch := by
    intro equality
    exact (List.nodup_cons.mp
      (List.nodup_cons.mp (List.nodup_cons.mp hcell).2).2).1
      (by simp [equality])
  have hcarryScratch : carry ≠ scratch := by
    intro equality
    exact (List.nodup_cons.mp (List.nodup_cons.mp
      (List.nodup_cons.mp (List.nodup_cons.mp hcell).2).2).2).1
      (by simp [equality])
  have hrun :
      run (if second then
          rippleSecondCell mode accumulator target addend carry scratch
        else rippleFirstCell mode accumulator target addend carry scratch) before =
        writeRippleCell target addend carry
          (if second then
              rippleSecondBits mode (before accumulator)
                (readRippleCell target addend carry before)
            else
              rippleFirstBits mode (before accumulator)
                (readRippleCell target addend carry before)) before := by
    by_cases hsecond : second
    · rw [if_pos hsecond, if_pos hsecond]
      exact run_rippleSecondCell_state mode accumulator target addend carry scratch
        before hcell (hclean scratch (by simp))
    · rw [if_neg hsecond, if_neg hsecond]
      exact run_rippleFirstCell_state mode accumulator target addend carry scratch
        before hcell (hclean scratch (by simp))
  rw [hrun]
  intro wire hwire
  rw [List.disjoint_left] at hdisjoint
  rcases List.mem_cons.mp hwire with hsame | hwire
  · subst wire
    simp [writeRippleCell, upd, Ne.symm htargetScratch,
      Ne.symm haddendScratch, Ne.symm hcarryScratch,
      hclean scratch (by simp)]
  · have houtside := hdisjoint hwire
    have htarget : wire ≠ target := by
      intro equality
      exact houtside (by simp [equality])
    have haddend : wire ≠ addend := by
      intro equality
      exact houtside (by simp [equality])
    have hcarry : wire ≠ carry := by
      intro equality
      exact houtside (by simp [equality])
    simp [writeRippleCell, upd, htarget, haddend, hcarry,
      hclean wire (by simp [hwire])]

theorem run_topSpecialFirstLeaf
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (state : BasisState)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches)
    (hclean : Clean (eqFlag :: eqScratches) state) :
    run (topSpecialFirstLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot) state =
      topSpecialFirstLeafState mode topValue rightRegister leftRegister
        accumulator target addend carry rightRoot leftRoot state := by
  have heqFlag : eqFlag = rippleScratch := hlayout.2.2.2.1
  subst eqFlag
  have hworkClean : Clean (rippleScratch :: eqScratches) state := hclean
  let afterRight := state[accumulator ↦ Bool.xor (state accumulator)
    (state rightRoot && registerMatches rightRegister topValue state)]
  have hafterRight :
      run (toggleEqConstUnderControl rightRoot rightRegister topValue accumulator
          rippleScratch eqScratches) state = afterRight :=
    run_toggleEqConstUnderControl rightRoot rightRegister topValue accumulator
      rippleScratch eqScratches state hlayout.1
      hworkClean
  have haccRippleScratch : accumulator ≠ rippleScratch := by
    intro equality
    exact (List.nodup_cons.mp hlayout.2.2.1).1 (by simp [equality])
  have hrippleClean : afterRight rippleScratch = false := by
    simp [afterRight, upd, Ne.symm haccRippleScratch,
      hworkClean rippleScratch (by simp)]
  let afterCell := writeRippleCell target addend carry
    (rippleFirstBits mode (afterRight accumulator)
      (readRippleCell target addend carry afterRight)) afterRight
  have hcellRun :
      run (rippleFirstCell mode accumulator target addend carry rippleScratch)
          afterRight = afterCell :=
    run_rippleFirstCell_state mode accumulator target addend carry rippleScratch
      afterRight hlayout.2.2.1 hrippleClean
  have heqCleanAfterRight : Clean (rippleScratch :: eqScratches) afterRight := by
    intro wire hwire
    have hdisjoint := hlayout.2.2.2.2
    rw [List.disjoint_left] at hdisjoint
    simp only [afterRight]
    have hwireAcc : wire ≠ accumulator := by
      rcases List.mem_cons.mp hwire with rfl | hwire
      · exact Ne.symm haccRippleScratch
      · intro equality
        exact hdisjoint hwire (by simp [equality])
    rw [upd_other state accumulator _ hwireAcc]
    exact hworkClean wire hwire
  have heqCleanAfterCell : Clean (rippleScratch :: eqScratches) afterCell := by
    rw [← hcellRun]
    exact topSpecial_eqClean_after_cell mode false accumulator target addend carry
      rippleScratch eqScratches afterRight hlayout.2.2.1 heqCleanAfterRight
      hlayout.2.2.2.2
  rw [topSpecialFirstLeaf, run_append, run_append, hafterRight, hcellRun,
    run_toggleEqConstUnderControl leftRoot leftRegister topValue accumulator
      rippleScratch eqScratches afterCell hlayout.2.1 heqCleanAfterCell]
  rfl

theorem run_topSpecialSecondLeaf
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (state : BasisState)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches)
    (hclean : Clean (eqFlag :: eqScratches) state) :
    run (topSpecialSecondLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot) state =
      topSpecialSecondLeafState mode topValue rightRegister leftRegister
        accumulator target addend carry rightRoot leftRoot state := by
  have heqFlag : eqFlag = rippleScratch := hlayout.2.2.2.1
  subst eqFlag
  have hworkClean : Clean (rippleScratch :: eqScratches) state := hclean
  let afterLeft := state[accumulator ↦ Bool.xor (state accumulator)
    (state leftRoot && registerMatches leftRegister topValue state)]
  have hafterLeft :
      run (toggleEqConstUnderControl leftRoot leftRegister topValue accumulator
          rippleScratch eqScratches) state = afterLeft :=
    run_toggleEqConstUnderControl leftRoot leftRegister topValue accumulator
      rippleScratch eqScratches state hlayout.2.1
      hworkClean
  have haccRippleScratch : accumulator ≠ rippleScratch := by
    intro equality
    exact (List.nodup_cons.mp hlayout.2.2.1).1 (by simp [equality])
  have hrippleClean : afterLeft rippleScratch = false := by
    simp [afterLeft, upd, Ne.symm haccRippleScratch,
      hworkClean rippleScratch (by simp)]
  let afterCell := writeRippleCell target addend carry
    (rippleSecondBits mode (afterLeft accumulator)
      (readRippleCell target addend carry afterLeft)) afterLeft
  have hcellRun :
      run (rippleSecondCell mode accumulator target addend carry rippleScratch)
          afterLeft = afterCell :=
    run_rippleSecondCell_state mode accumulator target addend carry rippleScratch
      afterLeft hlayout.2.2.1 hrippleClean
  have heqCleanAfterLeft : Clean (rippleScratch :: eqScratches) afterLeft := by
    intro wire hwire
    have hdisjoint := hlayout.2.2.2.2
    rw [List.disjoint_left] at hdisjoint
    simp only [afterLeft]
    have hwireAcc : wire ≠ accumulator := by
      rcases List.mem_cons.mp hwire with rfl | hwire
      · exact Ne.symm haccRippleScratch
      · intro equality
        exact hdisjoint hwire (by simp [equality])
    rw [upd_other state accumulator _ hwireAcc]
    exact hworkClean wire hwire
  have heqCleanAfterCell : Clean (rippleScratch :: eqScratches) afterCell := by
    rw [← hcellRun]
    exact topSpecial_eqClean_after_cell mode true accumulator target addend carry
      rippleScratch eqScratches afterLeft hlayout.2.2.1 heqCleanAfterLeft
      hlayout.2.2.2.2
  rw [topSpecialSecondLeaf, run_append, run_append, hafterLeft, hcellRun,
    run_toggleEqConstUnderControl rightRoot rightRegister topValue accumulator
      rippleScratch eqScratches afterCell hlayout.1 heqCleanAfterCell]
  rfl

theorem topSpecialFirstLeaf_usesOnly
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) :
    PaperCircuitUsesOnly
      (topSpecialLeafSupport rightRoot leftRoot rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches)
      (topSpecialFirstLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot) := by
  rw [topSpecialFirstLeaf]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply (toggleEqConstUnderControl_usesOnly rightRoot rightRegister topValue
        accumulator eqFlag eqScratches).mono
      intro wire hwire
      simp only [topSpecialLeafSupport, List.mem_append, List.mem_cons,
        List.mem_dedup] at hwire ⊢
      aesop
    · apply (rippleFirstCell_usesOnly mode accumulator target addend carry
        rippleScratch).mono
      intro wire hwire
      simp only [topSpecialLeafSupport, List.mem_append, List.mem_cons,
        List.mem_dedup] at hwire ⊢
      aesop
  · apply (toggleEqConstUnderControl_usesOnly leftRoot leftRegister topValue
      accumulator eqFlag eqScratches).mono
    intro wire hwire
    simp only [topSpecialLeafSupport, List.mem_append, List.mem_cons,
      List.mem_dedup] at hwire ⊢
    aesop

theorem topSpecialSecondLeaf_usesOnly
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) :
    PaperCircuitUsesOnly
      (topSpecialLeafSupport rightRoot leftRoot rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches)
      (topSpecialSecondLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot) := by
  rw [topSpecialSecondLeaf]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply (toggleEqConstUnderControl_usesOnly leftRoot leftRegister topValue
        accumulator eqFlag eqScratches).mono
      intro wire hwire
      simp only [topSpecialLeafSupport, List.mem_append, List.mem_cons,
        List.mem_dedup] at hwire ⊢
      aesop
    · apply (rippleSecondCell_usesOnly mode accumulator target addend carry
        rippleScratch).mono
      intro wire hwire
      simp only [topSpecialLeafSupport, List.mem_append, List.mem_cons,
        List.mem_dedup] at hwire ⊢
      aesop
  · apply (toggleEqConstUnderControl_usesOnly rightRoot rightRegister topValue
      accumulator eqFlag eqScratches).mono
    intro wire hwire
    simp only [topSpecialLeafSupport, List.mem_append, List.mem_cons,
      List.mem_dedup] at hwire ⊢
    aesop

@[simp]
theorem topSpecialFirstLeaf_HPFree
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) :
    HPFree (topSpecialFirstLeaf mode topValue rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches
      rightRoot leftRoot) := by
  simp [topSpecialFirstLeaf]

@[simp]
theorem topSpecialSecondLeaf_HPFree
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) :
    HPFree (topSpecialSecondLeaf mode topValue rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches
      rightRoot leftRoot) := by
  simp [topSpecialSecondLeaf]

theorem topSpecialFirstLeaf_wellFormed
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches) :
    CircuitWellFormed
      (topSpecialFirstLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot) := by
  rw [topSpecialFirstLeaf, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨toggleEqConstUnderControl_wellFormed rightRoot rightRegister topValue
      accumulator eqFlag eqScratches hlayout.1,
    rippleFirstCell_wellFormed mode accumulator target addend carry rippleScratch
      hlayout.2.2.1⟩,
    toggleEqConstUnderControl_wellFormed leftRoot leftRegister topValue
      accumulator eqFlag eqScratches hlayout.2.1⟩

theorem topSpecialSecondLeaf_wellFormed
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches) :
    CircuitWellFormed
      (topSpecialSecondLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot) := by
  rw [topSpecialSecondLeaf, circuitWellFormed_append,
    circuitWellFormed_append]
  exact ⟨⟨toggleEqConstUnderControl_wellFormed leftRoot leftRegister topValue
      accumulator eqFlag eqScratches hlayout.2.1,
    rippleSecondCell_wellFormed mode accumulator target addend carry rippleScratch
      hlayout.2.2.1⟩,
    toggleEqConstUnderControl_wellFormed rightRoot rightRegister topValue
      accumulator eqFlag eqScratches hlayout.1⟩

@[simp]
theorem topSpecialFirstLeaf_toffoliCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hrightEnough : rightRegister.length - 2 ≤ eqScratches.length)
    (hleftEnough : leftRegister.length - 2 ≤ eqScratches.length) :
    eeaToffoliCount
        (topSpecialFirstLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch eqFlag eqScratches
          rightRoot leftRoot) =
      (2 * mcxVChainToffoliCost rightRegister.length + 1) +
        rippleFirstCellToffoliCost mode +
        (2 * mcxVChainToffoliCost leftRegister.length + 1) := by
  rw [topSpecialFirstLeaf, eeaToffoliCount_append,
    eeaToffoliCount_append,
    toggleEqConstUnderControl_toffoliCount rightRoot rightRegister topValue
      accumulator eqFlag eqScratches hrightEnough,
    rippleFirstCell_toffoliCount,
    toggleEqConstUnderControl_toffoliCount leftRoot leftRegister topValue
      accumulator eqFlag eqScratches hleftEnough]

@[simp]
theorem topSpecialSecondLeaf_toffoliCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hrightEnough : rightRegister.length - 2 ≤ eqScratches.length)
    (hleftEnough : leftRegister.length - 2 ≤ eqScratches.length) :
    eeaToffoliCount
        (topSpecialSecondLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch eqFlag eqScratches
          rightRoot leftRoot) =
      (2 * mcxVChainToffoliCost leftRegister.length + 1) +
        rippleSecondCellToffoliCost mode +
        (2 * mcxVChainToffoliCost rightRegister.length + 1) := by
  rw [topSpecialSecondLeaf, eeaToffoliCount_append,
    eeaToffoliCount_append,
    toggleEqConstUnderControl_toffoliCount leftRoot leftRegister topValue
      accumulator eqFlag eqScratches hleftEnough,
    rippleSecondCell_toffoliCount,
    toggleEqConstUnderControl_toffoliCount rightRoot rightRegister topValue
      accumulator eqFlag eqScratches hrightEnough]

@[simp]
theorem topSpecialFirstLeaf_cnotCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) :
    eeaCnotCount
        (topSpecialFirstLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch eqFlag eqScratches
          rightRoot leftRoot) =
      2 * mcxVChainCnotCost rightRegister.length + 2 +
        2 * mcxVChainCnotCost leftRegister.length := by
  rw [topSpecialFirstLeaf, eeaCnotCount_append,
    eeaCnotCount_append, toggleEqConstUnderControl_cnotCount,
    rippleFirstCell_cnotCount, toggleEqConstUnderControl_cnotCount]

@[simp]
theorem topSpecialSecondLeaf_cnotCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) :
    eeaCnotCount
        (topSpecialSecondLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch eqFlag eqScratches
          rightRoot leftRoot) =
      2 * mcxVChainCnotCost leftRegister.length + 2 +
        2 * mcxVChainCnotCost rightRegister.length := by
  rw [topSpecialSecondLeaf, eeaCnotCount_append,
    eeaCnotCount_append, toggleEqConstUnderControl_cnotCount,
    rippleSecondCell_cnotCount, toggleEqConstUnderControl_cnotCount]

@[simp]
theorem topSpecialFirstLeaf_tCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hrightEnough : rightRegister.length - 2 ≤ eqScratches.length)
    (hleftEnough : leftRegister.length - 2 ≤ eqScratches.length) :
    ShorECDLP.tCount
        (topSpecialFirstLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch eqFlag eqScratches
          rightRoot leftRoot) =
      7 * ((2 * mcxVChainToffoliCost rightRegister.length + 1) +
        rippleFirstCellToffoliCost mode +
        (2 * mcxVChainToffoliCost leftRegister.length + 1)) := by
  rw [topSpecialFirstLeaf, tCount_append, tCount_append,
    toggleEqConstUnderControl_tCount rightRoot rightRegister topValue
      accumulator eqFlag eqScratches hrightEnough,
    rippleFirstCell_tCount,
    toggleEqConstUnderControl_tCount leftRoot leftRegister topValue
      accumulator eqFlag eqScratches hleftEnough]
  omega

@[simp]
theorem topSpecialSecondLeaf_tCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hrightEnough : rightRegister.length - 2 ≤ eqScratches.length)
    (hleftEnough : leftRegister.length - 2 ≤ eqScratches.length) :
    ShorECDLP.tCount
        (topSpecialSecondLeaf mode topValue rightRegister leftRegister
          accumulator target addend carry rippleScratch eqFlag eqScratches
          rightRoot leftRoot) =
      7 * ((2 * mcxVChainToffoliCost leftRegister.length + 1) +
        rippleSecondCellToffoliCost mode +
        (2 * mcxVChainToffoliCost rightRegister.length + 1)) := by
  rw [topSpecialSecondLeaf, tCount_append, tCount_append,
    toggleEqConstUnderControl_tCount leftRoot leftRegister topValue
      accumulator eqFlag eqScratches hleftEnough,
    rippleSecondCell_tCount,
    toggleEqConstUnderControl_tCount rightRoot rightRegister topValue
      accumulator eqFlag eqScratches hrightEnough]
  omega

/-! ## Binding the main leaves to the synchronized source traversal -/

/-- On a caller-supplied endpoint tree, the first pass visits one-subtrees before zero-subtrees
and applies `intervalFirstLeaf` at every exposed pair of equality controls.  Instantiating `tree`
with the certified `buildSource` result gives the source's decreasing numeric order. -/
def intervalFirstTraversal
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) : Circuit :=
  dualUnaryActionUnitary .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths

/-- On the same caller-supplied tree, the second pass visits zero-subtrees before one-subtrees.
Instantiating `tree` with the certified `buildSource` result gives increasing numeric order. -/
def intervalSecondTraversal
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) : Circuit :=
  dualUnaryActionUnitary .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths

/-- Measurement-uncomputed realization of the caller-supplied first traversal. -/
def intervalFirstTraversalAdaptive
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) : Quantum.AdaptiveCircuit :=
  dualUnaryAction .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths

/-- Measurement-uncomputed realization of the caller-supplied second traversal. -/
def intervalSecondTraversalAdaptive
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) : Quantum.AdaptiveCircuit :=
  dualUnaryAction .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths

/-- Complete caller-side layout for either main-tree arithmetic pass.  It combines the paired
decoder layout, mutual distinctness of the seven written arithmetic roles, and their disjointness
from the whole decoder interface. -/
def IntervalTraversalLayout
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire) : Prop :=
  tree.Layout rightRoot leftRoot rightPaths leftPaths ∧
    ∀ label,
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles
        (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
        rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch

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
  apply (houtside hprotected)
  simpa [equality] using hrole

private theorem intervalFirstLeaf_dualWellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (protectedWires : List Wire)
    (hfamily : ∀ label,
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafWellFormed
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) tree protectedWires := by
  intro label _ rightControl hright leftControl hleft
  exact intervalFirstLeaf_wellFormed mode topSpecial rightTop leftTop accumulator
    (targetAt label) (addendAt label) carry scratch label rightControl leftControl
      (intervalLeafLayout_of_decoder protectedWires rightControl leftControl
        rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch
        (hfamily label).1 (hfamily label).2 hright hleft)

private theorem intervalSecondLeaf_dualWellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (protectedWires : List Wire)
    (hfamily : ∀ label,
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafWellFormed
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) tree protectedWires := by
  intro label _ rightControl hright leftControl hleft
  exact intervalSecondLeaf_wellFormed mode topSpecial rightTop leftTop accumulator
    (targetAt label) (addendAt label) carry scratch label rightControl leftControl
      (intervalLeafLayout_of_decoder protectedWires rightControl leftControl
        rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch
        (hfamily label).1 (hfamily label).2 hright hleft)

private theorem intervalFirstLeafFamily_dualPreserves
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire) (protectedWires : List Wire)
    (hfamily : ∀ label,
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafPreserves
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) protectedWires := by
  intro label rightControl leftControl hright hleft state wire hwire
  have houtside := hfamily label
  rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
  exact intervalFirstLeaf_preservesOutside mode topSpecial rightTop leftTop
    accumulator (targetAt label) (addendAt label) carry scratch
    label rightControl leftControl state wire (houtside hwire)

private theorem intervalSecondLeafFamily_dualPreserves
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire) (protectedWires : List Wire)
    (hfamily : ∀ label,
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafPreserves
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) protectedWires := by
  intro label rightControl leftControl hright hleft state wire hwire
  have houtside := hfamily label
  rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
  exact intervalSecondLeaf_preservesOutside mode topSpecial rightTop leftTop
    accumulator (targetAt label) (addendAt label) carry scratch
    label rightControl leftControl state wire (houtside hwire)

@[simp]
theorem intervalFirstTraversal_HPFree
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) :
    HPFree (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) := by
  rw [intervalFirstTraversal]
  apply dualUnaryActionUnitary_HPFree
  intro label rightControl leftControl
  exact intervalFirstLeaf_HPFree mode topSpecial rightTop leftTop accumulator
    (targetAt label) (addendAt label) carry scratch label rightControl leftControl

@[simp]
theorem intervalSecondTraversal_HPFree
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) :
    HPFree (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) := by
  rw [intervalSecondTraversal]
  apply dualUnaryActionUnitary_HPFree
  intro label rightControl leftControl
  exact intervalSecondLeaf_HPFree mode topSpecial rightTop leftTop accumulator
    (targetAt label) (addendAt label) carry scratch label rightControl leftControl

theorem intervalFirstTraversal_wellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt) :
    CircuitWellFormed
      (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalFirstTraversal]
  exact dualUnaryActionUnitary_wellFormed .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths htree
    (intervalFirstLeaf_dualWellFormed mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths) hfamily)

theorem intervalSecondTraversal_wellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt) :
    CircuitWellFormed
      (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalSecondTraversal]
  exact dualUnaryActionUnitary_wellFormed .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths htree
    (intervalSecondLeaf_dualWellFormed mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths) hfamily)

theorem intervalFirstTraversalAdaptive_wellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt) :
    (intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).WellFormed := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalFirstTraversalAdaptive]
  exact dualUnaryAction_wellFormed .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths htree
    (intervalFirstLeaf_dualWellFormed mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths) hfamily)

theorem intervalSecondTraversalAdaptive_wellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt) :
    (intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).WellFormed := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalSecondTraversalAdaptive]
  exact dualUnaryAction_wellFormed .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths htree
    (intervalSecondLeaf_dualWellFormed mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths) hfamily)

/-- The first arithmetic traversal restores every endpoint-decoder wire. -/
theorem intervalFirstTraversal_preservesDecoder
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt)
    (hcleanRight : Clean rightPaths state) (hcleanLeft : Clean leftPaths state) :
    ∀ wire,
      wire ∈ tree.decoderWires rightRoot leftRoot rightPaths leftPaths →
        run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths)
          state wire = state wire := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalFirstTraversal]
  exact dualUnaryActionUnitary_preservesDecoder .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths state htree
    (intervalFirstLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label ↦ (hfamily label).2))
    hcleanRight hcleanLeft

/-- The second arithmetic traversal restores every endpoint-decoder wire. -/
theorem intervalSecondTraversal_preservesDecoder
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt)
    (hcleanRight : Clean rightPaths state) (hcleanLeft : Clean leftPaths state) :
    ∀ wire,
      wire ∈ tree.decoderWires rightRoot leftRoot rightPaths leftPaths →
        run (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths)
          state wire = state wire := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalSecondTraversal]
  exact dualUnaryActionUnitary_preservesDecoder .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths state htree
    (intervalSecondLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label ↦ (hfamily label).2))
    hcleanRight hcleanLeft

theorem intervalFirstTraversal_clean
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt)
    (hcleanRight : Clean rightPaths state) (hcleanLeft : Clean leftPaths state) :
    Clean rightPaths
        (run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) ∧
      Clean leftPaths
        (run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalFirstTraversal]
  exact dualUnaryActionUnitary_clean .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths state htree
    (intervalFirstLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label ↦ (hfamily label).2))
    hcleanRight hcleanLeft

theorem intervalSecondTraversal_clean
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt)
    (hcleanRight : Clean rightPaths state) (hcleanLeft : Clean leftPaths state) :
    Clean rightPaths
        (run (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) ∧
      Clean leftPaths
        (run (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalSecondTraversal]
  exact dualUnaryActionUnitary_clean .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths state htree
    (intervalSecondLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label ↦ (hfamily label).2))
    hcleanRight hcleanLeft

/-- The adaptive first pass coherently implements the literal coherent first traversal. -/
theorem intervalFirstTraversal_coherent
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt) :
    Quantum.CoherentlyImplementsOn
      (intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths)
      (Quantum.run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths))
      (fun state ↦ Clean rightPaths state ∧ Clean leftPaths state) := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalFirstTraversalAdaptive, intervalFirstTraversal]
  exact dualUnaryAction_coherent .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths htree
    (intervalFirstLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label ↦ (hfamily label).2))
    (by
      intro label rightControl leftControl
      exact intervalFirstLeaf_HPFree mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)

/-- The adaptive second pass coherently implements the literal coherent second traversal. -/
theorem intervalSecondTraversal_coherent
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt) :
    Quantum.CoherentlyImplementsOn
      (intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths)
      (Quantum.run (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths))
      (fun state ↦ Clean rightPaths state ∧ Clean leftPaths state) := by
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalSecondTraversalAdaptive, intervalSecondTraversal]
  exact dualUnaryAction_coherent .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths htree
    (intervalSecondLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label ↦ (hfamily label).2))
    (by
      intro label rightControl leftControl
      exact intervalSecondLeaf_HPFree mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)

theorem intervalFirstTraversal_toffoliCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    eeaToffoliCount
        (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) =
      tree.leafCostSum
          (fun label _ _ ↦ rippleFirstCellToffoliCost mode +
            if maskedZeroLeaf topSpecial label then 2 else 0)
          rightRoot leftRoot rightPaths leftPaths +
        4 * tree.internalNodes := by
  simpa only [intervalFirstTraversal, intervalFirstLeaf_toffoliCount] using
    dualUnaryActionUnitary_toffoliCount .dec
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

theorem intervalSecondTraversal_toffoliCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    eeaToffoliCount
        (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) =
      tree.leafCostSum
          (fun label _ _ ↦ rippleSecondCellToffoliCost mode +
            if maskedZeroLeaf topSpecial label then 2 else 0)
          rightRoot leftRoot rightPaths leftPaths +
        4 * tree.internalNodes := by
  simpa only [intervalSecondTraversal, intervalSecondLeaf_toffoliCount] using
    dualUnaryActionUnitary_toffoliCount .inc
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

theorem intervalFirstTraversal_cnotCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    eeaCnotCount
        (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) =
      tree.leafCostSum
          (fun label _ _ ↦ 2 +
            if maskedZeroLeaf topSpecial label then 0 else 2)
          rightRoot leftRoot rightPaths leftPaths +
        4 * tree.internalNodes := by
  simpa only [intervalFirstTraversal, intervalFirstLeaf_cnotCount] using
    dualUnaryActionUnitary_cnotCount .dec
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

theorem intervalSecondTraversal_cnotCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    eeaCnotCount
        (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) =
      tree.leafCostSum
          (fun label _ _ ↦ 2 +
            if maskedZeroLeaf topSpecial label then 0 else 2)
          rightRoot leftRoot rightPaths leftPaths +
        4 * tree.internalNodes := by
  simpa only [intervalSecondTraversal, intervalSecondLeaf_cnotCount] using
    dualUnaryActionUnitary_cnotCount .inc
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

theorem intervalFirstTraversal_tCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    ShorECDLP.tCount
        (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) =
      tree.leafCostSum
          (fun label _ _ ↦ 7 * (rippleFirstCellToffoliCost mode +
            if maskedZeroLeaf topSpecial label then 2 else 0))
          rightRoot leftRoot rightPaths leftPaths +
        28 * tree.internalNodes := by
  simpa only [intervalFirstTraversal, intervalFirstLeaf_tCount] using
    dualUnaryActionUnitary_tCount .dec
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

theorem intervalSecondTraversal_tCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    ShorECDLP.tCount
        (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) =
      tree.leafCostSum
          (fun label _ _ ↦ 7 * (rippleSecondCellToffoliCost mode +
            if maskedZeroLeaf topSpecial label then 2 else 0))
          rightRoot leftRoot rightPaths leftPaths +
        28 * tree.internalNodes := by
  simpa only [intervalSecondTraversal, intervalSecondLeaf_tCount] using
    dualUnaryActionUnitary_tCount .inc
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

theorem intervalFirstTraversalAdaptive_measurementCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    (intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).measurementCount =
        2 * tree.internalNodes := by
  simpa only [intervalFirstTraversalAdaptive] using
    dualUnaryAction_measurementCount .dec
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

theorem intervalSecondTraversalAdaptive_measurementCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    (intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).measurementCount =
        2 * tree.internalNodes := by
  simpa only [intervalSecondTraversalAdaptive] using
    dualUnaryAction_measurementCount .inc
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

theorem intervalFirstTraversalAdaptive_tCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    (intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).tCount =
      tree.leafCostSum
          (fun label _ _ ↦ 7 * (rippleFirstCellToffoliCost mode +
            if maskedZeroLeaf topSpecial label then 2 else 0))
          rightRoot leftRoot rightPaths leftPaths +
        14 * tree.internalNodes := by
  simpa only [intervalFirstTraversalAdaptive, intervalFirstLeaf_tCount] using
    dualUnaryAction_tCount .dec
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

theorem intervalSecondTraversalAdaptive_tCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (hlayout : tree.Layout rightRoot leftRoot rightPaths leftPaths) :
    (intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).tCount =
      tree.leafCostSum
          (fun label _ _ ↦ 7 * (rippleSecondCellToffoliCost mode +
            if maskedZeroLeaf topSpecial label then 2 else 0))
          rightRoot leftRoot rightPaths leftPaths +
        14 * tree.internalNodes := by
  simpa only [intervalSecondTraversalAdaptive, intervalSecondLeaf_tCount] using
    dualUnaryAction_tCount .inc
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

end ShorECDLP.Paper2607_13816
