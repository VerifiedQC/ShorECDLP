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

/-- Adaptive source-order tail of `mcx_vchain`.  Forward conjunctions and the target toggle stay
unitary; each nonfinal conjunction is erased by X measurement and feed-forward correction. -/
def mcxVChainTailAdaptive (accumulator : Wire) :
    List Wire → Wire → List Wire → Quantum.AdaptiveCircuit
  | [], _, _ => .done
  | [control], target, _ => .unitary [.CCX control accumulator target] .done
  | control :: nextControl :: controls, target, scratch :: scratches =>
      .unitary [.CCX control accumulator scratch]
        ((mcxVChainTailAdaptive scratch (nextControl :: controls) target scratches).seq
          (measuredAndErase control accumulator scratch))
  | _ :: _ :: _, _, [] => .done

/-- Literal adaptive `mcx_vchain` selected by the pinned generator's single global
`MEASUREMENT_UNCOMPUTE` switch. -/
def mcxVChainAdaptive : List Wire → Wire → List Wire → Quantum.AdaptiveCircuit
  | [], target, _ => .unitary [.X target] .done
  | [control], target, _ => .unitary [.CX control target] .done
  | first :: second :: controls, target, scratches =>
      mcxVChainTailAdaptive second (first :: controls) target scratches

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

private theorem mcxVChainTailAdaptive_wellFormed
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire)
    (hnonempty : controls ≠ [])
    (henough : controls.length - 1 ≤ scratches.length)
    (hlayout : (accumulator :: controls ++ target :: scratches).Nodup) :
    (mcxVChainTailAdaptive accumulator controls target scratches).WellFormed := by
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
          exact ⟨by
            simp [CircuitWellFormed, Gate.WellFormed,
              haccControl, Ne.symm haccControl, haccTarget, hcontrolTarget],
            trivial⟩
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
              have hgate : CircuitWellFormed [.CCX control accumulator scratch] := by
                simp [CircuitWellFormed, Gate.WellFormed,
                  haccControl, Ne.symm haccControl,
                  haccScratch, hcontrolScratch]
              rw [mcxVChainTailAdaptive]
              exact ⟨hgate, Quantum.AdaptiveCircuit.WellFormed.seq
                (ih scratch scratches (by simp) hchildEnough hchildLayout)
                (measuredAndErase_wellFormed control accumulator scratch
                  (Ne.symm haccControl))⟩

theorem mcxVChainAdaptive_wellFormed
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (henough : controls.length - 2 ≤ scratches.length)
    (hlayout : McxVChainLayout controls target scratches) :
    (mcxVChainAdaptive controls target scratches).WellFormed := by
  cases controls with
  | nil => exact ⟨by simp [CircuitWellFormed, Gate.WellFormed], trivial⟩
  | cons first controls =>
      cases controls with
      | nil =>
          have hne : first ≠ target := by
            intro equality
            exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
          exact ⟨by
            simp [CircuitWellFormed, Gate.WellFormed, hne], trivial⟩
      | cons second controls =>
          apply mcxVChainTailAdaptive_wellFormed second (first :: controls)
            target scratches
          · simp
          · simpa using henough
          · simp only [McxVChainLayout, List.cons_append, List.nodup_cons,
              List.mem_cons, List.mem_append, not_or] at hlayout ⊢
            aesop

private theorem interval_coherent_seq_circuits
    {first second : Quantum.AdaptiveCircuit}
    {firstCircuit secondCircuit : Circuit}
    {FirstValid SecondValid : BasisState → Prop}
    (hfirst : Quantum.CoherentlyImplementsOn first
      (Quantum.run firstCircuit) FirstValid)
    (hsecond : Quantum.CoherentlyImplementsOn second
      (Quantum.run secondCircuit) SecondValid)
    (hfirstClassical : HPFree firstCircuit)
    (hvalid : ∀ state, FirstValid state →
      SecondValid (run firstCircuit state)) :
    Quantum.CoherentlyImplementsOn (first.seq second)
      (Quantum.run (firstCircuit ++ secondCircuit)) FirstValid := by
  have hseq := hfirst.seq hsecond (by
    intro state hstate
    rw [Quantum.run_ket_agrees_classical firstCircuit state hfirstClassical]
    exact Quantum.supportedOn_ket SecondValid _ (hvalid state hstate))
  apply hseq.congrIdeal
  intro state _
  exact (Quantum.run_append firstCircuit secondCircuit (Quantum.ket state)).symm

private theorem interval_coherent_mono
    {program : Quantum.AdaptiveCircuit}
    {ideal : Quantum.State →ₗ[ℂ] Quantum.State}
    {Valid Stronger : BasisState → Prop}
    (hrefines : Quantum.CoherentlyImplementsOn program ideal Valid)
    (hsub : ∀ state, Stronger state → Valid state) :
    Quantum.CoherentlyImplementsOn program ideal Stronger := by
  rcases hrefines with ⟨coefficients, haligned, hmass⟩
  refine ⟨coefficients, ?_, hmass⟩
  exact haligned.imp fun branch coefficient hbranch state hstate ↦
    hbranch state (hsub state hstate)

private theorem mcxVChainTailAdaptive_coherent
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire)
    (hnonempty : controls ≠ [])
    (henough : controls.length - 1 ≤ scratches.length)
    (hlayout : (accumulator :: controls ++ target :: scratches).Nodup) :
    Quantum.CoherentlyImplementsOn
      (mcxVChainTailAdaptive accumulator controls target scratches)
      (Quantum.run (mcxVChainTail accumulator controls target scratches))
      (fun state ↦ Clean scratches state) := by
  induction controls generalizing accumulator scratches with
  | nil => exact (hnonempty rfl).elim
  | cons control controls ih =>
      cases controls with
      | nil =>
          exact Quantum.CoherentlyImplementsOn.unitary
            [.CCX control accumulator target] (fun state ↦ Clean scratches state)
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
              have haccTarget : accumulator ≠ target := by
                intro equality
                exact (List.nodup_cons.mp hlayout).1 (by simp [equality])
              have hcontrolTarget : control ≠ target := by
                intro equality
                exact (List.nodup_cons.mp (List.nodup_cons.mp hlayout).2).1
                  (by simp [equality])
              have hscratchTarget : scratch ≠ target := by
                intro equality
                exact (List.nodup_cons.mp hchildLayout).1 (by simp [equality])
              let firstCircuit : Circuit := [.CCX control accumulator scratch]
              let childCircuit : Circuit :=
                mcxVChainTail scratch (nextControl :: controls) target scratches
              have hfirst := Quantum.CoherentlyImplementsOn.unitary firstCircuit
                (fun state ↦ Clean (scratch :: scratches) state)
              have hfirstChild : ∀ state, Clean (scratch :: scratches) state →
                  Clean scratches (run firstCircuit state) := by
                intro state hclean wire hwire
                have hwireScratch : wire ≠ scratch := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hchildLayout).1 (by simp [hwire])
                simpa [firstCircuit, Classical.run, Classical.applyGate, upd,
                  hwireScratch] using hclean wire (by simp [hwire])
              have hprefix := interval_coherent_seq_circuits hfirst
                (ih scratch scratches (by simp) hchildEnough hchildLayout)
                (by simp [firstCircuit]) hfirstChild
              have hprefixComputed : ∀ state, Clean (scratch :: scratches) state →
                  PathAndComputed control accumulator scratch
                    (run (firstCircuit ++ childCircuit) state) := by
                intro state hclean
                let firstState := run firstCircuit state
                have hfirstState : firstState =
                    state[scratch ↦ state control && state accumulator] := by
                  funext wire
                  by_cases hwire : wire = scratch
                  · subst wire
                    simp [firstState, firstCircuit, Classical.run,
                      Classical.applyGate, upd, haccControl, hcontrolScratch,
                      haccScratch, hclean scratch (by simp)]
                  · simp [firstState, firstCircuit, Classical.run,
                      Classical.applyGate, upd, hwire]
                have hchildClean : Clean scratches firstState :=
                  hfirstChild state hclean
                have hchildRun := run_mcxVChainTail scratch
                  (nextControl :: controls) target scratches firstState
                  (by simp) hchildEnough hchildLayout hchildClean
                rw [Classical.run_append, hchildRun]
                unfold PathAndComputed
                rw [hfirstState]
                simp [upd, haccControl, hcontrolScratch, haccScratch,
                  haccTarget, hcontrolTarget, hscratchTarget]
              have herase := measuredAndErase_coherent_uncompute
                control accumulator scratch (Ne.symm haccControl)
                  hcontrolScratch haccScratch
              have hall := interval_coherent_seq_circuits hprefix herase
                (by simp [firstCircuit, childCircuit,
                  mcxVChainTail_HPFree]) hprefixComputed
              simpa [mcxVChainTailAdaptive, mcxVChainTail,
                firstCircuit, childCircuit, List.append_assoc] using hall

/-- Every adaptive v-chain branch is coefficient-aligned with the literal coherent v-chain on
the source's clean-scratch domain. -/
theorem mcxVChainAdaptive_coherent
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (henough : controls.length - 2 ≤ scratches.length)
    (hlayout : McxVChainLayout controls target scratches) :
    Quantum.CoherentlyImplementsOn
      (mcxVChainAdaptive controls target scratches)
      (Quantum.run (mcxVChain controls target scratches))
      (fun state ↦ Clean scratches state) := by
  cases controls with
  | nil => exact (Quantum.CoherentlyImplementsOn.unitary
      ([.X target] : Circuit) (fun state ↦ Clean scratches state))
  | cons first controls =>
      cases controls with
      | nil => exact (Quantum.CoherentlyImplementsOn.unitary
          ([.CX first target] : Circuit) (fun state ↦ Clean scratches state))
      | cons second controls =>
          exact mcxVChainTailAdaptive_coherent second (first :: controls)
            target scratches (by simp) (by simpa using henough) (by
              simp only [McxVChainLayout, List.cons_append, List.nodup_cons,
                List.mem_cons, List.mem_append, not_or] at hlayout ⊢
              aesop)

/-- Constructor-derived coherent Toffoli cost of a clean v-chain. -/
def mcxVChainToffoliCost : Nat → Nat
  | 0 | 1 => 0
  | length + 2 => 2 * length + 1

/-- Constructor-derived CNOT cost of a clean v-chain. -/
def mcxVChainCnotCost : Nat → Nat
  | 1 => 1
  | _ => 0

/-- Number of forward Toffolis retained by adaptive v-chain cleanup. -/
def mcxVChainAdaptiveToffoliCost : Nat → Nat
  | 0 | 1 => 0
  | length + 2 => length + 1

/-- Number of X-measured conjunction wires in an adaptive v-chain. -/
def mcxVChainMeasurementCost (length : Nat) : Nat := length - 2

private theorem intervalAdaptive_measurementCount_seq
    (first second : Quantum.AdaptiveCircuit) :
    (first.seq second).measurementCount =
      first.measurementCount + second.measurementCount := by
  induction first with
  | done => simp [Quantum.AdaptiveCircuit.seq,
      Quantum.AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [Quantum.AdaptiveCircuit.seq,
        Quantum.AdaptiveCircuit.measurementCount, ih]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [Quantum.AdaptiveCircuit.seq,
        Quantum.AdaptiveCircuit.measurementCount,
        ihFalse, ihTrue, Nat.add_max_add_right, Nat.add_assoc]

private theorem intervalAdaptive_tCount_seq
    (first second : Quantum.AdaptiveCircuit) :
    (first.seq second).tCount = first.tCount + second.tCount := by
  induction first with
  | done => simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount]
  | unitary circuit next ih =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount,
        ih, Nat.add_assoc]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [Quantum.AdaptiveCircuit.seq, Quantum.AdaptiveCircuit.tCount,
        ihFalse, ihTrue, Nat.add_max_add_right]

private theorem intervalAdaptive_seq_assoc
    (first second third : Quantum.AdaptiveCircuit) :
    (first.seq second).seq third = first.seq (second.seq third) := by
  induction first with
  | done => rfl
  | unitary circuit next ih =>
      simp [Quantum.AdaptiveCircuit.seq, ih]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [Quantum.AdaptiveCircuit.seq, ihFalse, ihTrue]

private theorem mcxVChainTailAdaptive_measurementCount
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire)
    (hnonempty : controls ≠ [])
    (henough : controls.length - 1 ≤ scratches.length) :
    (mcxVChainTailAdaptive accumulator controls target scratches).measurementCount =
      controls.length - 1 := by
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
              rw [mcxVChainTailAdaptive]
              simp only [Quantum.AdaptiveCircuit.measurementCount,
                intervalAdaptive_measurementCount_seq,
                ih scratch scratches (by simp) hchildEnough,
                measuredAndErase_measurementCount, List.length_cons]
              omega

@[simp]
theorem mcxVChainAdaptive_measurementCount
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (henough : controls.length - 2 ≤ scratches.length) :
    (mcxVChainAdaptive controls target scratches).measurementCount =
      mcxVChainMeasurementCost controls.length := by
  cases controls with
  | nil => rfl
  | cons first controls =>
      cases controls with
      | nil => rfl
      | cons second controls =>
          rw [mcxVChainAdaptive,
            mcxVChainTailAdaptive_measurementCount second (first :: controls)
              target scratches (by simp) (by simpa using henough)]
          simp [mcxVChainMeasurementCost]

private theorem mcxVChainTailAdaptive_tCount
    (accumulator : Wire) (controls : List Wire) (target : Wire)
    (scratches : List Wire)
    (hnonempty : controls ≠ [])
    (henough : controls.length - 1 ≤ scratches.length) :
    (mcxVChainTailAdaptive accumulator controls target scratches).tCount =
      7 * controls.length := by
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
              rw [mcxVChainTailAdaptive]
              simp only [Quantum.AdaptiveCircuit.tCount,
                intervalAdaptive_tCount_seq,
                ih scratch scratches (by simp) hchildEnough,
                measuredAndErase_tCount, List.length_cons,
                ShorECDLP.tCount, List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil, ShorECDLP.tCost]
              omega

@[simp]
theorem mcxVChainAdaptive_tCount
    (controls : List Wire) (target : Wire) (scratches : List Wire)
    (henough : controls.length - 2 ≤ scratches.length) :
    (mcxVChainAdaptive controls target scratches).tCount =
      7 * mcxVChainAdaptiveToffoliCost controls.length := by
  cases controls with
  | nil => rfl
  | cons first controls =>
      cases controls with
      | nil => rfl
      | cons second controls =>
          rw [mcxVChainAdaptive,
            mcxVChainTailAdaptive_tCount second (first :: controls)
              target scratches (by simp) (by simpa using henough)]
          simp [mcxVChainAdaptiveToffoliCost]

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

/-- Adaptive equality compute under the source's global measurement-uncompute switch. -/
def computeEqConstAdaptive (register : List Wire) (value : Nat)
    (flag : Wire) (scratches : List Wire) : Quantum.AdaptiveCircuit :=
  .unitary (zeroMask register value)
    ((mcxVChainAdaptive register flag scratches).seq
      (.unitary (zeroMask register value) .done))

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

theorem computeEqConstAdaptive_coherent
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire)
    (hlayout : EqConstLayout register flag scratches) :
    Quantum.CoherentlyImplementsOn
      (computeEqConstAdaptive register value flag scratches)
      (Quantum.run (computeEqConst register value flag scratches))
      (fun state ↦ Clean scratches state) := by
  let mask := zeroMask register value
  have hmaskClean : ∀ state, Clean scratches state →
      Clean scratches (run mask state) := by
    intro state hclean scratch hscratch
    rw [(zeroMask_usesOnly register value).preservesOutside state
      (eqConstLayout_scratch_not_mem register flag scratches hlayout
        scratch hscratch)]
    exact hclean scratch hscratch
  have hprefix := interval_coherent_seq_circuits
    (Quantum.CoherentlyImplementsOn.unitary mask
      (fun state ↦ Clean scratches state))
    (mcxVChainAdaptive_coherent register flag scratches hlayout.1 hlayout.2)
    (zeroMask_HPFree register value) hmaskClean
  have hall := interval_coherent_seq_circuits hprefix
    (Quantum.CoherentlyImplementsOn.unitary mask (fun _ ↦ True))
    (by simp [mask]) (fun _ _ ↦ trivial)
  simpa [computeEqConstAdaptive, computeEqConst, mask,
    List.append_assoc] using hall

theorem computeEqConstAdaptive_wellFormed
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire)
    (hlayout : EqConstLayout register flag scratches) :
    (computeEqConstAdaptive register value flag scratches).WellFormed := by
  exact ⟨zeroMask_wellFormed register value,
    Quantum.AdaptiveCircuit.WellFormed.seq
      (mcxVChainAdaptive_wellFormed register flag scratches hlayout.1 hlayout.2)
      ⟨zeroMask_wellFormed register value, trivial⟩⟩

@[simp]
theorem computeEqConstAdaptive_measurementCount
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire)
    (henough : register.length - 2 ≤ scratches.length) :
    (computeEqConstAdaptive register value flag scratches).measurementCount =
      mcxVChainMeasurementCost register.length := by
  simp [computeEqConstAdaptive, intervalAdaptive_measurementCount_seq,
    Quantum.AdaptiveCircuit.measurementCount,
    mcxVChainAdaptive_measurementCount register flag scratches henough]

@[simp]
theorem computeEqConstAdaptive_tCount
    (register : List Wire) (value : Nat) (flag : Wire)
    (scratches : List Wire)
    (henough : register.length - 2 ≤ scratches.length) :
    (computeEqConstAdaptive register value flag scratches).tCount =
      7 * mcxVChainAdaptiveToffoliCost register.length := by
  simp [computeEqConstAdaptive, intervalAdaptive_tCount_seq,
    Quantum.AdaptiveCircuit.tCount,
    mcxVChainAdaptive_tCount register flag scratches henough]

/-- Compute equality, use it together with an external root control, and uncompute it. -/
def toggleEqConstUnderControl
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire) : Circuit :=
  let compute := computeEqConst register value flag scratches
  (compute ++ [Gate.CCX root flag accumulator]) ++ compute

/-- Adaptive special-label selector: both equality v-chains use measurement cleanup. -/
def toggleEqConstUnderControlAdaptive
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire) : Quantum.AdaptiveCircuit :=
  let compute := computeEqConstAdaptive register value flag scratches
  compute.seq (.unitary [.CCX root flag accumulator] compute)

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

/-- The direct equality toggle restores its shared equality flag and v-chain work. -/
theorem toggleEqConstUnderControl_clean
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (state : BasisState)
    (hlayout : EqControlLayout root register accumulator flag scratches)
    (hclean : Clean (flag :: scratches) state) :
    Clean (flag :: scratches)
      (run (toggleEqConstUnderControl root register value accumulator flag scratches)
        state) := by
  rw [run_toggleEqConstUnderControl root register value accumulator flag scratches
    state hlayout hclean]
  intro wire hwire
  have hwireAccumulator : wire ≠ accumulator := by
    intro equality
    subst wire
    exact eqControlLayout_accumulatorOutside root register accumulator flag
      scratches hlayout (by simp [hwire])
  rw [upd_other state accumulator _ hwireAccumulator]
  exact hclean wire hwire

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

theorem toggleEqConstUnderControlAdaptive_coherent
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (hlayout : EqControlLayout root register accumulator flag scratches) :
    Quantum.CoherentlyImplementsOn
      (toggleEqConstUnderControlAdaptive root register value
        accumulator flag scratches)
      (Quantum.run (toggleEqConstUnderControl root register value
        accumulator flag scratches))
      (fun state ↦ Clean scratches state) := by
  let compute := computeEqConst register value flag scratches
  let adaptiveCompute := computeEqConstAdaptive register value flag scratches
  let gate : Circuit := [.CCX root flag accumulator]
  have heqLayout :=
    eqControlLayout_eqConst root register accumulator flag scratches hlayout
  have hcompute := computeEqConstAdaptive_coherent
    register value flag scratches heqLayout
  have hfirstGate := interval_coherent_seq_circuits hcompute
    (Quantum.CoherentlyImplementsOn.unitary gate (fun _ ↦ True))
    (computeEqConst_HPFree register value flag scratches)
    (fun _ _ ↦ trivial)
  have hflagNotScratch := eqConstLayout_flag_not_scratch
    register flag scratches heqLayout
  have haccNotScratch : accumulator ∉ scratches := by
    have haccTail := (List.nodup_cons.mp (List.nodup_cons.mp hlayout.2).2).1
    intro hmem
    exact haccTail (by simp [hmem])
  have hprefixClean : ∀ state, Clean scratches state →
      Clean scratches (run (compute ++ gate) state) := by
    intro state hclean wire hwire
    rw [Classical.run_append,
      run_computeEqConst register value flag scratches state heqLayout hclean]
    have hwireFlag : wire ≠ flag := by
      intro equality
      subst wire
      exact hflagNotScratch hwire
    have hwireAccumulator : wire ≠ accumulator := by
      intro equality
      subst wire
      exact haccNotScratch hwire
    simpa [gate, Classical.run, Classical.applyGate, upd,
      hwireFlag, hwireAccumulator] using hclean wire hwire
  have hall := interval_coherent_seq_circuits hfirstGate hcompute
    (by simp [compute, gate]) hprefixClean
  rw [intervalAdaptive_seq_assoc] at hall
  simpa [toggleEqConstUnderControlAdaptive, toggleEqConstUnderControl,
    adaptiveCompute, compute, gate, Quantum.AdaptiveCircuit.seq,
    List.append_assoc] using hall

theorem toggleEqConstUnderControlAdaptive_wellFormed
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (hlayout : EqControlLayout root register accumulator flag scratches) :
    (toggleEqConstUnderControlAdaptive root register value
      accumulator flag scratches).WellFormed := by
  have hcompute := computeEqConstAdaptive_wellFormed register value flag scratches
    (eqControlLayout_eqConst root register accumulator flag scratches hlayout)
  have hroles := eqControlLayout_root_flag_accumulator
    root register accumulator flag scratches hlayout
  have hroles' : (root ≠ flag ∧ root ≠ accumulator) ∧
      flag ≠ accumulator := by
    simpa [List.nodup_cons] using hroles
  obtain ⟨⟨hrootFlag, hrootAccumulator⟩, hflagAccumulator⟩ := hroles'
  have hgate : CircuitWellFormed [.CCX root flag accumulator] := by
    simp [CircuitWellFormed, Gate.WellFormed, hrootFlag,
      hrootAccumulator, hflagAccumulator]
  exact Quantum.AdaptiveCircuit.WellFormed.seq hcompute ⟨hgate, hcompute⟩

@[simp]
theorem toggleEqConstUnderControlAdaptive_measurementCount
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (henough : register.length - 2 ≤ scratches.length) :
    (toggleEqConstUnderControlAdaptive root register value
      accumulator flag scratches).measurementCount =
      2 * mcxVChainMeasurementCost register.length := by
  simp [toggleEqConstUnderControlAdaptive,
    intervalAdaptive_measurementCount_seq,
    Quantum.AdaptiveCircuit.measurementCount,
    computeEqConstAdaptive_measurementCount register value flag scratches henough]
  omega

@[simp]
theorem toggleEqConstUnderControlAdaptive_tCount
    (root : Wire) (register : List Wire) (value : Nat)
    (accumulator flag : Wire) (scratches : List Wire)
    (henough : register.length - 2 ≤ scratches.length) :
    (toggleEqConstUnderControlAdaptive root register value
      accumulator flag scratches).tCount =
      14 * mcxVChainAdaptiveToffoliCost register.length + 7 := by
  rw [toggleEqConstUnderControlAdaptive, intervalAdaptive_tCount_seq,
    computeEqConstAdaptive_tCount register value flag scratches henough]
  simp [Quantum.AdaptiveCircuit.tCount, ShorECDLP.tCount,
    ShorECDLP.tCost,
    computeEqConstAdaptive_tCount register value flag scratches henough]
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

/-! ## Measurement-uncomputed ripple cells -/

/-- The adaptive source realization of the one-clean-wire three-controlled X. -/
def cleanC3XAdaptive
    (first second third target scratch : Wire) : Quantum.AdaptiveCircuit :=
  mcxVChainAdaptive ([first, second, third] : List Wire) target
    ([scratch] : List Wire)

def controlledMajAdaptive
    (control target addend carry scratch : Wire) : Quantum.AdaptiveCircuit :=
  .unitary [.CX carry target, .CX carry addend]
    (cleanC3XAdaptive control target addend carry scratch)

def controlledUmaAdaptive
    (control target addend carry scratch : Wire) : Quantum.AdaptiveCircuit :=
  (cleanC3XAdaptive control target addend carry scratch).seq
    (.unitary [.CCX control addend target, .CX carry addend, .CX carry target] .done)

def controlledMajInvAdaptive
    (control target addend carry scratch : Wire) : Quantum.AdaptiveCircuit :=
  (cleanC3XAdaptive control target addend carry scratch).seq
    (.unitary [.CX carry addend, .CX carry target] .done)

def controlledUmaInvAdaptive
    (control target addend carry scratch : Wire) : Quantum.AdaptiveCircuit :=
  .unitary [.CX carry target, .CX carry addend, .CCX control addend target]
    (cleanC3XAdaptive control target addend carry scratch)

def rippleFirstCellAdaptive (mode : RippleMode)
    (control target addend carry scratch : Wire) : Quantum.AdaptiveCircuit :=
  match mode with
  | .add => controlledMajAdaptive control target addend carry scratch
  | .sub => controlledUmaInvAdaptive control target addend carry scratch

def rippleSecondCellAdaptive (mode : RippleMode)
    (control target addend carry scratch : Wire) : Quantum.AdaptiveCircuit :=
  match mode with
  | .add => controlledUmaAdaptive control target addend carry scratch
  | .sub => controlledMajInvAdaptive control target addend carry scratch

theorem cleanC3XAdaptive_coherent
    (first second third target scratch : Wire)
    (hlayout : [first, second, third, target, scratch].Nodup) :
    Quantum.CoherentlyImplementsOn
      (cleanC3XAdaptive first second third target scratch)
      (Quantum.run (cleanC3X first second third target scratch))
      (fun state ↦ Clean [scratch] state) := by
  simpa [cleanC3XAdaptive, cleanC3X, McxVChainLayout] using
    mcxVChainAdaptive_coherent ([first, second, third] : List Wire) target
      ([scratch] : List Wire)
      (by simp) hlayout

theorem cleanC3XAdaptive_wellFormed
    (first second third target scratch : Wire)
    (hlayout : [first, second, third, target, scratch].Nodup) :
    (cleanC3XAdaptive first second third target scratch).WellFormed := by
  simpa [cleanC3XAdaptive, McxVChainLayout] using
    mcxVChainAdaptive_wellFormed ([first, second, third] : List Wire) target
      ([scratch] : List Wire)
      (by simp) hlayout

@[simp]
theorem cleanC3XAdaptive_measurementCount
    (first second third target scratch : Wire) :
    (cleanC3XAdaptive first second third target scratch).measurementCount = 1 := by
  rfl

@[simp]
theorem cleanC3XAdaptive_tCount
    (first second third target scratch : Wire) :
    (cleanC3XAdaptive first second third target scratch).tCount = 14 := by
  rfl

private theorem intervalCellScratch_preserved
    (circuit : Circuit) (support : List Wire) (scratch : Wire)
    (huses : PaperCircuitUsesOnly support circuit)
    (houtside : scratch ∉ support) :
    ∀ state, Clean [scratch] state → Clean [scratch] (run circuit state) := by
  intro state hclean wire hwire
  have hwireEq : wire = scratch := by simpa using hwire
  subst wire
  rw [huses.preservesOutside state houtside]
  exact hclean scratch (by simp)

theorem rippleFirstCellAdaptive_coherent
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (hlayout : [control, target, addend, carry, scratch].Nodup) :
    Quantum.CoherentlyImplementsOn
      (rippleFirstCellAdaptive mode control target addend carry scratch)
      (Quantum.run (rippleFirstCell mode control target addend carry scratch))
      (fun state ↦ Clean [scratch] state) := by
  cases mode with
  | add =>
      let headCircuit : Circuit := [.CX carry target, .CX carry addend]
      have hseq := interval_coherent_seq_circuits
        (Quantum.CoherentlyImplementsOn.unitary headCircuit
          (fun state ↦ Clean [scratch] state))
        (cleanC3XAdaptive_coherent control target addend carry scratch hlayout)
        (by simp [headCircuit])
        (intervalCellScratch_preserved headCircuit
          ([control, target, addend, carry] : List Wire)
          scratch (by
            simp [headCircuit, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]) (by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              or_false, not_or] at hlayout
            aesop))
      simpa [rippleFirstCellAdaptive, controlledMajAdaptive,
        rippleFirstCell, controlledMaj, headCircuit] using hseq
  | sub =>
      let headCircuit : Circuit :=
        [.CX carry target, .CX carry addend, .CCX control addend target]
      have hseq := interval_coherent_seq_circuits
        (Quantum.CoherentlyImplementsOn.unitary headCircuit
          (fun state ↦ Clean [scratch] state))
        (cleanC3XAdaptive_coherent control target addend carry scratch hlayout)
        (by simp [headCircuit])
        (intervalCellScratch_preserved headCircuit
          ([control, target, addend, carry] : List Wire)
          scratch (by
            simp [headCircuit, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]) (by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              or_false, not_or] at hlayout
            aesop))
      simpa [rippleFirstCellAdaptive, controlledUmaInvAdaptive,
        rippleFirstCell, controlledUmaInv, headCircuit] using hseq

theorem rippleSecondCellAdaptive_coherent
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (hlayout : [control, target, addend, carry, scratch].Nodup) :
    Quantum.CoherentlyImplementsOn
      (rippleSecondCellAdaptive mode control target addend carry scratch)
      (Quantum.run (rippleSecondCell mode control target addend carry scratch))
      (fun state ↦ Clean [scratch] state) := by
  cases mode with
  | add =>
      let tailCircuit : Circuit :=
        [.CCX control addend target, .CX carry addend, .CX carry target]
      have hseq := interval_coherent_seq_circuits
        (cleanC3XAdaptive_coherent control target addend carry scratch hlayout)
        (Quantum.CoherentlyImplementsOn.unitary tailCircuit (fun _ ↦ True))
        (by simp)
        (fun _ _ ↦ trivial)
      simpa [rippleSecondCellAdaptive, controlledUmaAdaptive,
        rippleSecondCell, controlledUma, tailCircuit] using hseq
  | sub =>
      let tailCircuit : Circuit := [.CX carry addend, .CX carry target]
      have hseq := interval_coherent_seq_circuits
        (cleanC3XAdaptive_coherent control target addend carry scratch hlayout)
        (Quantum.CoherentlyImplementsOn.unitary tailCircuit (fun _ ↦ True))
        (by simp)
        (fun _ _ ↦ trivial)
      simpa [rippleSecondCellAdaptive, controlledMajInvAdaptive,
        rippleSecondCell, controlledMajInv, tailCircuit] using hseq

theorem rippleFirstCellAdaptive_wellFormed
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (hlayout : [control, target, addend, carry, scratch].Nodup) :
    (rippleFirstCellAdaptive mode control target addend carry scratch).WellFormed := by
  cases mode with
  | add =>
      rw [rippleFirstCellAdaptive, controlledMajAdaptive]
      have hparts := controlledMaj_wellFormed control target addend carry scratch hlayout
      rw [controlledMaj, circuitWellFormed_append] at hparts
      exact ⟨hparts.1,
        cleanC3XAdaptive_wellFormed control target addend carry scratch hlayout⟩
  | sub =>
      rw [rippleFirstCellAdaptive, controlledUmaInvAdaptive]
      have hparts := controlledUmaInv_wellFormed control target addend carry scratch hlayout
      rw [controlledUmaInv, circuitWellFormed_append] at hparts
      exact ⟨hparts.1,
        cleanC3XAdaptive_wellFormed control target addend carry scratch hlayout⟩

theorem rippleSecondCellAdaptive_wellFormed
    (mode : RippleMode) (control target addend carry scratch : Wire)
    (hlayout : [control, target, addend, carry, scratch].Nodup) :
    (rippleSecondCellAdaptive mode control target addend carry scratch).WellFormed := by
  cases mode with
  | add =>
      rw [rippleSecondCellAdaptive, controlledUmaAdaptive]
      have hparts := controlledUma_wellFormed control target addend carry scratch hlayout
      rw [controlledUma, circuitWellFormed_append] at hparts
      exact Quantum.AdaptiveCircuit.WellFormed.seq
        (cleanC3XAdaptive_wellFormed control target addend carry scratch hlayout)
        ⟨hparts.2, trivial⟩
  | sub =>
      rw [rippleSecondCellAdaptive, controlledMajInvAdaptive]
      have hparts := controlledMajInv_wellFormed control target addend carry scratch hlayout
      rw [controlledMajInv, circuitWellFormed_append] at hparts
      exact Quantum.AdaptiveCircuit.WellFormed.seq
        (cleanC3XAdaptive_wellFormed control target addend carry scratch hlayout)
        ⟨hparts.2, trivial⟩

@[simp]
theorem rippleFirstCellAdaptive_measurementCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleFirstCellAdaptive mode control target addend carry scratch).measurementCount = 1 := by
  cases mode <;> simp [rippleFirstCellAdaptive, controlledMajAdaptive,
    controlledUmaInvAdaptive, intervalAdaptive_measurementCount_seq,
    Quantum.AdaptiveCircuit.measurementCount]

@[simp]
theorem rippleSecondCellAdaptive_measurementCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleSecondCellAdaptive mode control target addend carry scratch).measurementCount = 1 := by
  cases mode <;> simp [rippleSecondCellAdaptive, controlledUmaAdaptive,
    controlledMajInvAdaptive, intervalAdaptive_measurementCount_seq,
    Quantum.AdaptiveCircuit.measurementCount]

@[simp]
theorem rippleFirstCellAdaptive_tCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleFirstCellAdaptive mode control target addend carry scratch).tCount =
      7 * (rippleFirstCellToffoliCost mode - 1) := by
  cases mode <;> simp [rippleFirstCellAdaptive, controlledMajAdaptive,
    controlledUmaInvAdaptive, intervalAdaptive_tCount_seq,
    Quantum.AdaptiveCircuit.tCount, ShorECDLP.tCount, ShorECDLP.tCost,
    rippleFirstCellToffoliCost]

@[simp]
theorem rippleSecondCellAdaptive_tCount
    (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleSecondCellAdaptive mode control target addend carry scratch).tCount =
      7 * (rippleSecondCellToffoliCost mode - 1) := by
  cases mode <;> simp [rippleSecondCellAdaptive, controlledUmaAdaptive,
    controlledMajInvAdaptive, intervalAdaptive_tCount_seq,
    Quantum.AdaptiveCircuit.tCount, ShorECDLP.tCount, ShorECDLP.tCost,
    rippleSecondCellToffoliCost]

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

/-- Adaptive first leaf under the source's global measurement-uncompute switch. -/
def intervalFirstLeafAdaptive
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) : Quantum.AdaptiveCircuit :=
  .unitary (endpointLeafToggle topSpecial label rightTop rightControl accumulator)
    ((rippleFirstCellAdaptive mode accumulator target addend carry scratch).seq
      (.unitary (endpointLeafToggle topSpecial label leftTop leftControl accumulator) .done))

/-- Adaptive second leaf under the same global switch. -/
def intervalSecondLeafAdaptive
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) : Quantum.AdaptiveCircuit :=
  .unitary (endpointLeafToggle topSpecial label leftTop leftControl accumulator)
    ((rippleSecondCellAdaptive mode accumulator target addend carry scratch).seq
      (.unitary (endpointLeafToggle topSpecial label rightTop rightControl accumulator) .done))

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

theorem intervalFirstLeafAdaptive_coherent
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    Quantum.CoherentlyImplementsOn
      (intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl)
      (Quantum.run (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl))
      (fun state ↦ Clean [scratch] state) := by
  obtain ⟨hright, hleft, hcell⟩ := intervalLeafLayout_parts
    rightControl leftControl rightTop leftTop accumulator target addend carry scratch
      hlayout
  let rightCircuit := endpointLeafToggle topSpecial label
    rightTop rightControl accumulator
  let leftCircuit := endpointLeafToggle topSpecial label
    leftTop leftControl accumulator
  have hrightClean := intervalCellScratch_preserved rightCircuit
    ([rightControl, rightTop, accumulator] : List Wire) scratch
    (endpointLeafToggle_usesOnly topSpecial label rightTop rightControl accumulator) (by
      simp only [IntervalLeafLayout, intervalLeafSupport, List.nodup_append,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hlayout
      aesop)
  have hheadCell := interval_coherent_seq_circuits
    (Quantum.CoherentlyImplementsOn.unitary rightCircuit
      (fun state ↦ Clean [scratch] state))
    (rippleFirstCellAdaptive_coherent mode accumulator target addend carry scratch hcell)
    (endpointLeafToggle_HPFree topSpecial label rightTop rightControl accumulator)
    hrightClean
  have hall := interval_coherent_seq_circuits hheadCell
    (Quantum.CoherentlyImplementsOn.unitary leftCircuit (fun _ ↦ True))
    (by simp [rightCircuit]) (fun _ _ ↦ trivial)
  simpa [intervalFirstLeafAdaptive, intervalFirstLeaf,
    rightCircuit, leftCircuit, List.append_assoc] using hall

theorem intervalSecondLeafAdaptive_coherent
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    Quantum.CoherentlyImplementsOn
      (intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl)
      (Quantum.run (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl))
      (fun state ↦ Clean [scratch] state) := by
  obtain ⟨hright, hleft, hcell⟩ := intervalLeafLayout_parts
    rightControl leftControl rightTop leftTop accumulator target addend carry scratch
      hlayout
  let leftCircuit := endpointLeafToggle topSpecial label
    leftTop leftControl accumulator
  let rightCircuit := endpointLeafToggle topSpecial label
    rightTop rightControl accumulator
  have hleftClean := intervalCellScratch_preserved leftCircuit
    ([leftControl, leftTop, accumulator] : List Wire) scratch
    (endpointLeafToggle_usesOnly topSpecial label leftTop leftControl accumulator) (by
      simp only [IntervalLeafLayout, intervalLeafSupport, List.nodup_append,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hlayout
      aesop)
  have hheadCell := interval_coherent_seq_circuits
    (Quantum.CoherentlyImplementsOn.unitary leftCircuit
      (fun state ↦ Clean [scratch] state))
    (rippleSecondCellAdaptive_coherent mode accumulator target addend carry scratch hcell)
    (endpointLeafToggle_HPFree topSpecial label leftTop leftControl accumulator)
    hleftClean
  have hall := interval_coherent_seq_circuits hheadCell
    (Quantum.CoherentlyImplementsOn.unitary rightCircuit (fun _ ↦ True))
    (by simp [leftCircuit]) (fun _ _ ↦ trivial)
  simpa [intervalSecondLeafAdaptive, intervalSecondLeaf,
    rightCircuit, leftCircuit, List.append_assoc] using hall

theorem intervalFirstLeafAdaptive_wellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    (intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl).WellFormed := by
  obtain ⟨hright, hleft, hcell⟩ := intervalLeafLayout_parts
    rightControl leftControl rightTop leftTop accumulator target addend carry scratch
      hlayout
  exact ⟨endpointLeafToggle_wellFormed topSpecial label rightTop
      rightControl accumulator hright,
    Quantum.AdaptiveCircuit.WellFormed.seq
      (rippleFirstCellAdaptive_wellFormed mode accumulator target addend carry scratch hcell)
      ⟨endpointLeafToggle_wellFormed topSpecial label leftTop
        leftControl accumulator hleft, trivial⟩⟩

theorem intervalSecondLeafAdaptive_wellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    (intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl).WellFormed := by
  obtain ⟨hright, hleft, hcell⟩ := intervalLeafLayout_parts
    rightControl leftControl rightTop leftTop accumulator target addend carry scratch
      hlayout
  exact ⟨endpointLeafToggle_wellFormed topSpecial label leftTop
      leftControl accumulator hleft,
    Quantum.AdaptiveCircuit.WellFormed.seq
      (rippleSecondCellAdaptive_wellFormed mode accumulator target addend carry scratch hcell)
      ⟨endpointLeafToggle_wellFormed topSpecial label rightTop
        rightControl accumulator hright, trivial⟩⟩

@[simp]
theorem intervalFirstLeafAdaptive_measurementCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    (intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl).measurementCount = 1 := by
  simp [intervalFirstLeafAdaptive, intervalAdaptive_measurementCount_seq,
    Quantum.AdaptiveCircuit.measurementCount]

@[simp]
theorem intervalSecondLeafAdaptive_measurementCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    (intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl).measurementCount = 1 := by
  simp [intervalSecondLeafAdaptive, intervalAdaptive_measurementCount_seq,
    Quantum.AdaptiveCircuit.measurementCount]

@[simp]
theorem intervalFirstLeafAdaptive_tCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    (intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl).tCount =
      7 * (rippleFirstCellToffoliCost mode - 1 +
        if maskedZeroLeaf topSpecial label then 2 else 0) := by
  simp [intervalFirstLeafAdaptive, intervalAdaptive_tCount_seq,
    Quantum.AdaptiveCircuit.tCount, endpointLeafToggle_tCount]
  split <;> cases mode <;> simp [rippleFirstCellToffoliCost]

@[simp]
theorem intervalSecondLeafAdaptive_tCount
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire) :
    (intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl).tCount =
      7 * (rippleSecondCellToffoliCost mode - 1 +
        if maskedZeroLeaf topSpecial label then 2 else 0) := by
  simp [intervalSecondLeafAdaptive, intervalAdaptive_tCount_seq,
    Quantum.AdaptiveCircuit.tCount, endpointLeafToggle_tCount]
  split <;> cases mode <;> simp [rippleSecondCellToffoliCost]

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

private theorem intervalLeaf_scratch_outside_toggles
    (rightControl leftControl rightTop leftTop accumulator target addend carry scratch : Wire)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    scratch ∉ [rightControl, rightTop, accumulator] ∧
      scratch ∉ [leftControl, leftTop, accumulator] := by
  obtain ⟨_, hroles, hcross⟩ := List.nodup_append.mp hlayout
  have hrightControlScratch : rightControl ≠ scratch := by
    intro equality
    exact hcross rightControl (by simp) scratch (by simp) equality
  have hleftControlScratch : leftControl ≠ scratch := by
    intro equality
    exact hcross leftControl (by simp) scratch (by simp) equality
  have hrightTopScratch : rightTop ≠ scratch := by
    intro equality
    exact (List.nodup_cons.mp hroles).1 (by simp [equality])
  have hleftTopScratch : leftTop ≠ scratch := by
    intro equality
    exact (List.nodup_cons.mp (List.nodup_cons.mp hroles).2).1
      (by simp [equality])
  have haccumulatorScratch : accumulator ≠ scratch := by
    intro equality
    exact (List.nodup_cons.mp (List.nodup_cons.mp
      (List.nodup_cons.mp hroles).2).2).1 (by simp [equality])
  constructor <;> simp [Ne.symm hrightControlScratch, Ne.symm hleftControlScratch,
    Ne.symm hrightTopScratch, Ne.symm hleftTopScratch,
    Ne.symm haccumulatorScratch]

/-- A complete first leaf always restores the shared clean-v-chain cell wire. -/
theorem intervalFirstLeaf_preservesScratch
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    run (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) state scratch =
      state scratch := by
  obtain ⟨_, _, hcell⟩ := intervalLeafLayout_parts rightControl leftControl
    rightTop leftTop accumulator target addend carry scratch hlayout
  obtain ⟨hrightOutside, hleftOutside⟩ :=
    intervalLeaf_scratch_outside_toggles rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch hlayout
  let afterRight := run
    (endpointLeafToggle topSpecial label rightTop rightControl accumulator) state
  let afterCell := run
    (rippleFirstCell mode accumulator target addend carry scratch) afterRight
  rw [intervalFirstLeaf, run_append, run_append]
  change run (endpointLeafToggle topSpecial label leftTop leftControl accumulator)
      afterCell scratch = state scratch
  rw [(endpointLeafToggle_usesOnly topSpecial label leftTop leftControl accumulator).preservesOutside
      afterCell hleftOutside]
  change run (rippleFirstCell mode accumulator target addend carry scratch)
      afterRight scratch = state scratch
  rw [rippleFirstCell_preservesScratch mode accumulator target addend carry scratch
      afterRight hcell]
  change run (endpointLeafToggle topSpecial label rightTop rightControl accumulator)
      state scratch = state scratch
  exact (endpointLeafToggle_usesOnly topSpecial label rightTop rightControl accumulator).preservesOutside
    state hrightOutside

/-- A complete second leaf always restores the same cell wire. -/
theorem intervalSecondLeaf_preservesScratch
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState)
    (hlayout : IntervalLeafLayout rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch) :
    run (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) state scratch =
      state scratch := by
  obtain ⟨_, _, hcell⟩ := intervalLeafLayout_parts rightControl leftControl
    rightTop leftTop accumulator target addend carry scratch hlayout
  obtain ⟨hrightOutside, hleftOutside⟩ :=
    intervalLeaf_scratch_outside_toggles rightControl leftControl rightTop leftTop
      accumulator target addend carry scratch hlayout
  let afterLeft := run
    (endpointLeafToggle topSpecial label leftTop leftControl accumulator) state
  let afterCell := run
    (rippleSecondCell mode accumulator target addend carry scratch) afterLeft
  rw [intervalSecondLeaf, run_append, run_append]
  change run (endpointLeafToggle topSpecial label rightTop rightControl accumulator)
      afterCell scratch = state scratch
  rw [(endpointLeafToggle_usesOnly topSpecial label rightTop rightControl accumulator).preservesOutside
      afterCell hrightOutside]
  change run (rippleSecondCell mode accumulator target addend carry scratch)
      afterLeft scratch = state scratch
  rw [rippleSecondCell_preservesScratch mode accumulator target addend carry scratch
      afterLeft hcell]
  change run (endpointLeafToggle topSpecial label leftTop leftControl accumulator)
      state scratch = state scratch
  exact (endpointLeafToggle_usesOnly topSpecial label leftTop leftControl accumulator).preservesOutside
    state hleftOutside

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

/-- Measurement-uncomputed realization of the separately handled first top lane. -/
def topSpecialFirstLeafAdaptive
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) : Quantum.AdaptiveCircuit :=
  (toggleEqConstUnderControlAdaptive rightRoot rightRegister topValue accumulator
      eqFlag eqScratches).seq
    ((rippleFirstCellAdaptive mode accumulator target addend carry rippleScratch).seq
      (toggleEqConstUnderControlAdaptive leftRoot leftRegister topValue accumulator
        eqFlag eqScratches))

/-- Measurement-uncomputed realization of the separately handled second top lane. -/
def topSpecialSecondLeafAdaptive
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire) : Quantum.AdaptiveCircuit :=
  (toggleEqConstUnderControlAdaptive leftRoot leftRegister topValue accumulator
      eqFlag eqScratches).seq
    ((rippleSecondCellAdaptive mode accumulator target addend carry rippleScratch).seq
      (toggleEqConstUnderControlAdaptive rightRoot rightRegister topValue accumulator
        eqFlag eqScratches))

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

private theorem topSpecialFirstLeafState_clean
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry scratch : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (state : BasisState)
    (hcell : [accumulator, target, addend, carry, scratch].Nodup)
    (hdisjoint : List.Disjoint eqScratches
      (accumulator :: target :: addend :: carry :: scratch :: []))
    (hclean : Clean (scratch :: eqScratches) state) :
    Clean (scratch :: eqScratches)
      (topSpecialFirstLeafState mode topValue rightRegister leftRegister
        accumulator target addend carry rightRoot leftRoot state) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hcell
  obtain ⟨⟨haccTarget, haccAddend, haccCarry, haccScratch⟩,
    ⟨⟨htargetAddend, htargetCarry, htargetScratch⟩,
      ⟨⟨haddendCarry, haddendScratch⟩, ⟨hcarryScratch, _⟩⟩⟩⟩ := hcell
  rw [List.disjoint_left] at hdisjoint
  intro wire hwire
  rcases List.mem_cons.mp hwire with hwire | hwire
  · subst wire
    simpa [topSpecialFirstLeafState, writeRippleCell, upd,
      Ne.symm haccScratch, Ne.symm htargetScratch,
      Ne.symm haddendScratch, Ne.symm hcarryScratch] using
      hclean scratch (by simp)
  · have houtside := hdisjoint hwire
    have hacc : wire ≠ accumulator := by
      intro equality
      exact houtside (by simp [equality])
    have htarget : wire ≠ target := by
      intro equality
      exact houtside (by simp [equality])
    have haddend : wire ≠ addend := by
      intro equality
      exact houtside (by simp [equality])
    have hcarry : wire ≠ carry := by
      intro equality
      exact houtside (by simp [equality])
    simpa [topSpecialFirstLeafState, writeRippleCell, upd,
      hacc, htarget, haddend, hcarry] using hclean wire (by simp [hwire])

private theorem topSpecialSecondLeafState_clean
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry scratch : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (state : BasisState)
    (hcell : [accumulator, target, addend, carry, scratch].Nodup)
    (hdisjoint : List.Disjoint eqScratches
      (accumulator :: target :: addend :: carry :: scratch :: []))
    (hclean : Clean (scratch :: eqScratches) state) :
    Clean (scratch :: eqScratches)
      (topSpecialSecondLeafState mode topValue rightRegister leftRegister
        accumulator target addend carry rightRoot leftRoot state) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hcell
  obtain ⟨⟨haccTarget, haccAddend, haccCarry, haccScratch⟩,
    ⟨⟨htargetAddend, htargetCarry, htargetScratch⟩,
      ⟨⟨haddendCarry, haddendScratch⟩, ⟨hcarryScratch, _⟩⟩⟩⟩ := hcell
  rw [List.disjoint_left] at hdisjoint
  intro wire hwire
  rcases List.mem_cons.mp hwire with hwire | hwire
  · subst wire
    simpa [topSpecialSecondLeafState, writeRippleCell, upd,
      Ne.symm haccScratch, Ne.symm htargetScratch,
      Ne.symm haddendScratch, Ne.symm hcarryScratch] using
      hclean scratch (by simp)
  · have houtside := hdisjoint hwire
    have hacc : wire ≠ accumulator := by
      intro equality
      exact houtside (by simp [equality])
    have htarget : wire ≠ target := by
      intro equality
      exact houtside (by simp [equality])
    have haddend : wire ≠ addend := by
      intro equality
      exact houtside (by simp [equality])
    have hcarry : wire ≠ carry := by
      intro equality
      exact houtside (by simp [equality])
    simpa [topSpecialSecondLeafState, writeRippleCell, upd,
      hacc, htarget, haddend, hcarry] using hclean wire (by simp [hwire])

/-- The separately handled first top lane restores its equality/ripple scratch bank. -/
theorem topSpecialFirstLeaf_clean
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (state : BasisState)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches)
    (hclean : Clean (eqFlag :: eqScratches) state) :
    Clean (eqFlag :: eqScratches)
      (run (topSpecialFirstLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot) state) := by
  have heq : eqFlag = rippleScratch := hlayout.2.2.2.1
  subst eqFlag
  rw [run_topSpecialFirstLeaf mode topValue rightRegister leftRegister
    accumulator target addend carry rippleScratch rippleScratch eqScratches
    rightRoot leftRoot state hlayout hclean]
  exact topSpecialFirstLeafState_clean mode topValue rightRegister leftRegister
    accumulator target addend carry rippleScratch eqScratches rightRoot leftRoot state
    hlayout.2.2.1 hlayout.2.2.2.2 hclean

/-- The fully measurement-uncomputed first top lane coherently implements the literal source
unitary on the shared equality/ripple work domain. -/
theorem topSpecialFirstLeafAdaptive_coherent
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches) :
    Quantum.CoherentlyImplementsOn
      (topSpecialFirstLeafAdaptive mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot)
      (Quantum.run (topSpecialFirstLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot))
      (fun state ↦ Clean (eqFlag :: eqScratches) state) := by
  have heqFlag : eqFlag = rippleScratch := hlayout.2.2.2.1
  subst eqFlag
  let rightCircuit := toggleEqConstUnderControl rightRoot rightRegister topValue
    accumulator rippleScratch eqScratches
  let cellCircuit := rippleFirstCell mode accumulator target addend carry rippleScratch
  let leftCircuit := toggleEqConstUnderControl leftRoot leftRegister topValue
    accumulator rippleScratch eqScratches
  have hright : Quantum.CoherentlyImplementsOn
      (toggleEqConstUnderControlAdaptive rightRoot rightRegister topValue
        accumulator rippleScratch eqScratches)
      (Quantum.run (toggleEqConstUnderControl rightRoot rightRegister topValue
        accumulator rippleScratch eqScratches))
      (fun state ↦ Clean (rippleScratch :: eqScratches) state) :=
    interval_coherent_mono
    (toggleEqConstUnderControlAdaptive_coherent rightRoot rightRegister topValue
      accumulator rippleScratch eqScratches hlayout.1)
    (fun state hclean wire hwire ↦ hclean wire (by simp [hwire]))
  have hrightClean : ∀ state, Clean (rippleScratch :: eqScratches) state →
      Clean (rippleScratch :: eqScratches) (run rightCircuit state) := by
    intro state hclean
    exact toggleEqConstUnderControl_clean rightRoot rightRegister topValue
      accumulator rippleScratch eqScratches state hlayout.1 hclean
  have hhead := interval_coherent_seq_circuits hright
    (rippleFirstCellAdaptive_coherent mode accumulator target addend carry
      rippleScratch hlayout.2.2.1)
    (toggleEqConstUnderControl_HPFree rightRoot rightRegister topValue
      accumulator rippleScratch eqScratches)
    (fun state hclean wire hwire ↦
      hrightClean state hclean wire (by simp_all))
  have hprefixClean : ∀ state, Clean (rippleScratch :: eqScratches) state →
      Clean (rippleScratch :: eqScratches)
        (run (rightCircuit ++ cellCircuit) state) := by
    intro state hclean
    rw [Classical.run_append]
    exact topSpecial_eqClean_after_cell mode false accumulator target addend carry
      rippleScratch eqScratches (run rightCircuit state) hlayout.2.2.1
      (hrightClean state hclean) hlayout.2.2.2.2
  have hall := interval_coherent_seq_circuits hhead
    (toggleEqConstUnderControlAdaptive_coherent leftRoot leftRegister topValue
      accumulator rippleScratch eqScratches hlayout.2.1)
    (by simp [rightCircuit, cellCircuit])
    (fun state hclean wire hwire ↦
      hprefixClean state hclean wire (by simp [hwire]))
  rw [intervalAdaptive_seq_assoc] at hall
  simpa [topSpecialFirstLeafAdaptive, topSpecialFirstLeaf,
    rightCircuit, cellCircuit, leftCircuit, List.append_assoc] using hall

/-- The fully measurement-uncomputed second top lane coherently implements the literal source
unitary on the shared equality/ripple work domain. -/
theorem topSpecialSecondLeafAdaptive_coherent
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches) :
    Quantum.CoherentlyImplementsOn
      (topSpecialSecondLeafAdaptive mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot)
      (Quantum.run (topSpecialSecondLeaf mode topValue rightRegister leftRegister
        accumulator target addend carry rippleScratch eqFlag eqScratches
        rightRoot leftRoot))
      (fun state ↦ Clean (eqFlag :: eqScratches) state) := by
  have heqFlag : eqFlag = rippleScratch := hlayout.2.2.2.1
  subst eqFlag
  let leftCircuit := toggleEqConstUnderControl leftRoot leftRegister topValue
    accumulator rippleScratch eqScratches
  let cellCircuit := rippleSecondCell mode accumulator target addend carry rippleScratch
  let rightCircuit := toggleEqConstUnderControl rightRoot rightRegister topValue
    accumulator rippleScratch eqScratches
  have hleft : Quantum.CoherentlyImplementsOn
      (toggleEqConstUnderControlAdaptive leftRoot leftRegister topValue
        accumulator rippleScratch eqScratches)
      (Quantum.run (toggleEqConstUnderControl leftRoot leftRegister topValue
        accumulator rippleScratch eqScratches))
      (fun state ↦ Clean (rippleScratch :: eqScratches) state) :=
    interval_coherent_mono
    (toggleEqConstUnderControlAdaptive_coherent leftRoot leftRegister topValue
      accumulator rippleScratch eqScratches hlayout.2.1)
    (fun state hclean wire hwire ↦ hclean wire (by simp [hwire]))
  have hleftClean : ∀ state, Clean (rippleScratch :: eqScratches) state →
      Clean (rippleScratch :: eqScratches) (run leftCircuit state) := by
    intro state hclean
    exact toggleEqConstUnderControl_clean leftRoot leftRegister topValue
      accumulator rippleScratch eqScratches state hlayout.2.1 hclean
  have hhead := interval_coherent_seq_circuits hleft
    (rippleSecondCellAdaptive_coherent mode accumulator target addend carry
      rippleScratch hlayout.2.2.1)
    (toggleEqConstUnderControl_HPFree leftRoot leftRegister topValue
      accumulator rippleScratch eqScratches)
    (fun state hclean wire hwire ↦
      hleftClean state hclean wire (by simp_all))
  have hprefixClean : ∀ state, Clean (rippleScratch :: eqScratches) state →
      Clean (rippleScratch :: eqScratches)
        (run (leftCircuit ++ cellCircuit) state) := by
    intro state hclean
    rw [Classical.run_append]
    exact topSpecial_eqClean_after_cell mode true accumulator target addend carry
      rippleScratch eqScratches (run leftCircuit state) hlayout.2.2.1
      (hleftClean state hclean) hlayout.2.2.2.2
  have hall := interval_coherent_seq_circuits hhead
    (toggleEqConstUnderControlAdaptive_coherent rightRoot rightRegister topValue
      accumulator rippleScratch eqScratches hlayout.1)
    (by simp [leftCircuit, cellCircuit])
    (fun state hclean wire hwire ↦
      hprefixClean state hclean wire (by simp [hwire]))
  rw [intervalAdaptive_seq_assoc] at hall
  simpa [topSpecialSecondLeafAdaptive, topSpecialSecondLeaf,
    leftCircuit, cellCircuit, rightCircuit, List.append_assoc] using hall

theorem topSpecialFirstLeafAdaptive_wellFormed
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches) :
    (topSpecialFirstLeafAdaptive mode topValue rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches
      rightRoot leftRoot).WellFormed := by
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (toggleEqConstUnderControlAdaptive_wellFormed rightRoot rightRegister topValue
      accumulator eqFlag eqScratches hlayout.1)
    (Quantum.AdaptiveCircuit.WellFormed.seq
      (rippleFirstCellAdaptive_wellFormed mode accumulator target addend carry
        rippleScratch hlayout.2.2.1)
      (toggleEqConstUnderControlAdaptive_wellFormed leftRoot leftRegister topValue
        accumulator eqFlag eqScratches hlayout.2.1))

theorem topSpecialSecondLeafAdaptive_wellFormed
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hlayout : TopSpecialLeafLayout rightRoot leftRoot rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches) :
    (topSpecialSecondLeafAdaptive mode topValue rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches
      rightRoot leftRoot).WellFormed := by
  exact Quantum.AdaptiveCircuit.WellFormed.seq
    (toggleEqConstUnderControlAdaptive_wellFormed leftRoot leftRegister topValue
      accumulator eqFlag eqScratches hlayout.2.1)
    (Quantum.AdaptiveCircuit.WellFormed.seq
      (rippleSecondCellAdaptive_wellFormed mode accumulator target addend carry
        rippleScratch hlayout.2.2.1)
      (toggleEqConstUnderControlAdaptive_wellFormed rightRoot rightRegister topValue
        accumulator eqFlag eqScratches hlayout.1))

@[simp]
theorem topSpecialFirstLeafAdaptive_measurementCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hrightEnough : rightRegister.length - 2 ≤ eqScratches.length)
    (hleftEnough : leftRegister.length - 2 ≤ eqScratches.length) :
    (topSpecialFirstLeafAdaptive mode topValue rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches
      rightRoot leftRoot).measurementCount =
      2 * mcxVChainMeasurementCost rightRegister.length + 1 +
        2 * mcxVChainMeasurementCost leftRegister.length := by
  rw [topSpecialFirstLeafAdaptive, intervalAdaptive_measurementCount_seq,
    intervalAdaptive_measurementCount_seq,
    toggleEqConstUnderControlAdaptive_measurementCount rightRoot rightRegister
      topValue accumulator eqFlag eqScratches hrightEnough,
    rippleFirstCellAdaptive_measurementCount,
    toggleEqConstUnderControlAdaptive_measurementCount leftRoot leftRegister
      topValue accumulator eqFlag eqScratches hleftEnough]
  omega

@[simp]
theorem topSpecialSecondLeafAdaptive_measurementCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hrightEnough : rightRegister.length - 2 ≤ eqScratches.length)
    (hleftEnough : leftRegister.length - 2 ≤ eqScratches.length) :
    (topSpecialSecondLeafAdaptive mode topValue rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches
      rightRoot leftRoot).measurementCount =
      2 * mcxVChainMeasurementCost leftRegister.length + 1 +
        2 * mcxVChainMeasurementCost rightRegister.length := by
  rw [topSpecialSecondLeafAdaptive, intervalAdaptive_measurementCount_seq,
    intervalAdaptive_measurementCount_seq,
    toggleEqConstUnderControlAdaptive_measurementCount leftRoot leftRegister
      topValue accumulator eqFlag eqScratches hleftEnough,
    rippleSecondCellAdaptive_measurementCount,
    toggleEqConstUnderControlAdaptive_measurementCount rightRoot rightRegister
      topValue accumulator eqFlag eqScratches hrightEnough]
  omega

@[simp]
theorem topSpecialFirstLeafAdaptive_tCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hrightEnough : rightRegister.length - 2 ≤ eqScratches.length)
    (hleftEnough : leftRegister.length - 2 ≤ eqScratches.length) :
    (topSpecialFirstLeafAdaptive mode topValue rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches
      rightRoot leftRoot).tCount =
      (14 * mcxVChainAdaptiveToffoliCost rightRegister.length + 7) +
        7 * (rippleFirstCellToffoliCost mode - 1) +
        (14 * mcxVChainAdaptiveToffoliCost leftRegister.length + 7) := by
  rw [topSpecialFirstLeafAdaptive, intervalAdaptive_tCount_seq,
    intervalAdaptive_tCount_seq,
    toggleEqConstUnderControlAdaptive_tCount rightRoot rightRegister topValue
      accumulator eqFlag eqScratches hrightEnough,
    rippleFirstCellAdaptive_tCount,
    toggleEqConstUnderControlAdaptive_tCount leftRoot leftRegister topValue
      accumulator eqFlag eqScratches hleftEnough]
  omega

@[simp]
theorem topSpecialSecondLeafAdaptive_tCount
    (mode : RippleMode) (topValue : Nat)
    (rightRegister leftRegister : List Wire)
    (accumulator target addend carry rippleScratch eqFlag : Wire)
    (eqScratches : List Wire) (rightRoot leftRoot : Wire)
    (hrightEnough : rightRegister.length - 2 ≤ eqScratches.length)
    (hleftEnough : leftRegister.length - 2 ≤ eqScratches.length) :
    (topSpecialSecondLeafAdaptive mode topValue rightRegister leftRegister
      accumulator target addend carry rippleScratch eqFlag eqScratches
      rightRoot leftRoot).tCount =
      (14 * mcxVChainAdaptiveToffoliCost leftRegister.length + 7) +
        7 * (rippleSecondCellToffoliCost mode - 1) +
        (14 * mcxVChainAdaptiveToffoliCost rightRegister.length + 7) := by
  rw [topSpecialSecondLeafAdaptive, intervalAdaptive_tCount_seq,
    intervalAdaptive_tCount_seq,
    toggleEqConstUnderControlAdaptive_tCount leftRoot leftRegister topValue
      accumulator eqFlag eqScratches hleftEnough,
    rippleSecondCellAdaptive_tCount,
    toggleEqConstUnderControlAdaptive_tCount rightRoot rightRegister topValue
      accumulator eqFlag eqScratches hrightEnough]
  omega

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
  dualUnaryAdaptiveAction .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
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
  dualUnaryAdaptiveAction .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
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
    ∀ label, label ∈ tree.labels →
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles
        (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
        rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch

private theorem intervalTraversalLayout_decoderScratch
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt) :
    (tree.decoderWires rightRoot leftRoot rightPaths leftPaths ++ [scratch]).Nodup := by
  refine List.nodup_append.mpr
    ⟨hlayout.1.decoderNodup, by simp, ?_⟩
  obtain ⟨label, hlabel⟩ := tree.labels_nonempty
  have houtside := (hlayout.2 label hlabel).2
  rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
  intro decoder hdecoder extra hextra equality
  have hextraEq : extra = scratch := by simpa using hextra
  subst extra
  subst decoder
  exact (houtside hdecoder (by simp)).elim

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

/-- Decoder-facing form of first-leaf cell-scratch restoration. -/
theorem intervalFirstLeaf_preservesScratch_of_decoder
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (protectedWires : List Wire) (state : BasisState)
    (hroles : [rightTop, leftTop, accumulator, target, addend, carry, scratch].Nodup)
    (houtside : DecoderOutsideIntervalRoles protectedWires rightTop leftTop
      accumulator target addend carry scratch)
    (hright : rightControl ∈ protectedWires)
    (hleft : leftControl ∈ protectedWires) :
    run (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) state scratch =
      state scratch := by
  exact intervalFirstLeaf_preservesScratch mode topSpecial rightTop leftTop accumulator
    target addend carry scratch label rightControl leftControl state
    (intervalLeafLayout_of_decoder protectedWires rightControl leftControl
      rightTop leftTop accumulator target addend carry scratch hroles houtside
      hright hleft)

/-- Decoder-facing form of second-leaf cell-scratch restoration. -/
theorem intervalSecondLeaf_preservesScratch_of_decoder
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (protectedWires : List Wire) (state : BasisState)
    (hroles : [rightTop, leftTop, accumulator, target, addend, carry, scratch].Nodup)
    (houtside : DecoderOutsideIntervalRoles protectedWires rightTop leftTop
      accumulator target addend carry scratch)
    (hright : rightControl ∈ protectedWires)
    (hleft : leftControl ∈ protectedWires) :
    run (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        target addend carry scratch label rightControl leftControl) state scratch =
      state scratch := by
  exact intervalSecondLeaf_preservesScratch mode topSpecial rightTop leftTop accumulator
    target addend carry scratch label rightControl leftControl state
    (intervalLeafLayout_of_decoder protectedWires rightControl leftControl
      rightTop leftTop accumulator target addend carry scratch hroles houtside
      hright hleft)

private theorem intervalFirstLeaf_dualWellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (protectedWires : List Wire)
    (hfamily : ∀ label, label ∈ tree.labels →
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafWellFormed
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) tree protectedWires := by
  intro label hlabel rightControl hright leftControl hleft
  exact intervalFirstLeaf_wellFormed mode topSpecial rightTop leftTop accumulator
    (targetAt label) (addendAt label) carry scratch label rightControl leftControl
      (intervalLeafLayout_of_decoder protectedWires rightControl leftControl
        rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch
        (hfamily label hlabel).1 (hfamily label hlabel).2 hright hleft)

private theorem intervalSecondLeaf_dualWellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (protectedWires : List Wire)
    (hfamily : ∀ label, label ∈ tree.labels →
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafWellFormed
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) tree protectedWires := by
  intro label hlabel rightControl hright leftControl hleft
  exact intervalSecondLeaf_wellFormed mode topSpecial rightTop leftTop accumulator
    (targetAt label) (addendAt label) carry scratch label rightControl leftControl
      (intervalLeafLayout_of_decoder protectedWires rightControl leftControl
        rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch
        (hfamily label hlabel).1 (hfamily label hlabel).2 hright hleft)

private theorem intervalFirstLeaf_dualAdaptiveWellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (protectedWires : List Wire)
    (hfamily : ∀ label, label ∈ tree.labels →
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryAdaptiveLeafWellFormed
      (fun label rightControl leftControl ↦
        intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) tree protectedWires := by
  intro label hlabel rightControl hright leftControl hleft
  exact intervalFirstLeafAdaptive_wellFormed mode topSpecial rightTop leftTop
    accumulator (targetAt label) (addendAt label) carry scratch label
    rightControl leftControl
    (intervalLeafLayout_of_decoder protectedWires rightControl leftControl
      rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch
      (hfamily label hlabel).1 (hfamily label hlabel).2 hright hleft)

private theorem intervalSecondLeaf_dualAdaptiveWellFormed
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (protectedWires : List Wire)
    (hfamily : ∀ label, label ∈ tree.labels →
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryAdaptiveLeafWellFormed
      (fun label rightControl leftControl ↦
        intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) tree protectedWires := by
  intro label hlabel rightControl hright leftControl hleft
  exact intervalSecondLeafAdaptive_wellFormed mode topSpecial rightTop leftTop
    accumulator (targetAt label) (addendAt label) carry scratch label
    rightControl leftControl
    (intervalLeafLayout_of_decoder protectedWires rightControl leftControl
      rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch
      (hfamily label hlabel).1 (hfamily label hlabel).2 hright hleft)

private theorem intervalFirstLeafFamily_dualPreserves
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire) (labels : List Nat)
    (protectedWires : List Wire)
    (hfamily : ∀ label, label ∈ labels →
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafPreservesOn
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) labels protectedWires protectedWires := by
  intro label hlabel rightControl leftControl hright hleft state wire hwire
  have houtside := hfamily label hlabel
  rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
  exact intervalFirstLeaf_preservesOutside mode topSpecial rightTop leftTop
    accumulator (targetAt label) (addendAt label) carry scratch
    label rightControl leftControl state wire (houtside hwire)

private theorem intervalSecondLeafFamily_dualPreserves
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire) (labels : List Nat)
    (protectedWires : List Wire)
    (hfamily : ∀ label, label ∈ labels →
      DecoderOutsideIntervalRoles protectedWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafPreservesOn
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl) labels protectedWires protectedWires := by
  intro label hlabel rightControl leftControl hright hleft state wire hwire
  have houtside := hfamily label hlabel
  rw [DecoderOutsideIntervalRoles, List.disjoint_left] at houtside
  exact intervalSecondLeaf_preservesOutside mode topSpecial rightTop leftTop
    accumulator (targetAt label) (addendAt label) carry scratch
    label rightControl leftControl state wire (houtside hwire)

private theorem intervalFirstLeafFamily_dualPreservesWithScratch
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire) (labels : List Nat)
    (decoderWires : List Wire)
    (hfamily : ∀ label, label ∈ labels →
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles decoderWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafPreservesOn
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      labels decoderWires (decoderWires ++ [scratch]) := by
  intro label hlabel rightControl leftControl hright hleft state wire hwire
  rcases List.mem_append.mp hwire with hwire | hwire
  · exact intervalFirstLeafFamily_dualPreserves mode topSpecial rightTop leftTop
      accumulator carry scratch targetAt addendAt labels decoderWires
      (fun label hlabel ↦ (hfamily label hlabel).2)
      label hlabel rightControl leftControl hright hleft state wire hwire
  · have hwireEq : wire = scratch := by simpa using hwire
    subst wire
    exact intervalFirstLeaf_preservesScratch_of_decoder mode topSpecial rightTop
      leftTop accumulator (targetAt label) (addendAt label) carry scratch label
      rightControl leftControl decoderWires state (hfamily label hlabel).1
      (hfamily label hlabel).2 hright hleft

private theorem intervalSecondLeafFamily_dualPreservesWithScratch
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire) (labels : List Nat)
    (decoderWires : List Wire)
    (hfamily : ∀ label, label ∈ labels →
      [rightTop, leftTop, accumulator, targetAt label, addendAt label,
        carry, scratch].Nodup ∧
      DecoderOutsideIntervalRoles decoderWires rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch) :
    DualUnaryLeafPreservesOn
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      labels decoderWires (decoderWires ++ [scratch]) := by
  intro label hlabel rightControl leftControl hright hleft state wire hwire
  rcases List.mem_append.mp hwire with hwire | hwire
  · exact intervalSecondLeafFamily_dualPreserves mode topSpecial rightTop leftTop
      accumulator carry scratch targetAt addendAt labels decoderWires
      (fun label hlabel ↦ (hfamily label hlabel).2)
      label hlabel rightControl leftControl hright hleft state wire hwire
  · have hwireEq : wire = scratch := by simpa using hwire
    subst wire
    exact intervalSecondLeaf_preservesScratch_of_decoder mode topSpecial rightTop
      leftTop accumulator (targetAt label) (addendAt label) carry scratch label
      rightControl leftControl decoderWires state (hfamily label hlabel).1
      (hfamily label hlabel).2 hright hleft

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
  exact dualUnaryAdaptiveAction_wellFormed .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths htree
    (intervalFirstLeaf_dualAdaptiveWellFormed mode topSpecial rightTop leftTop accumulator
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
  exact dualUnaryAdaptiveAction_wellFormed .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths htree
    (intervalSecondLeaf_dualAdaptiveWellFormed mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths) hfamily)

/-! ## Direct ordered traversal semantics -/

/-- Total direct semantics of a first-pass leaf.  On the public clean-cell domain it is the
gate-independent Boolean action; the fallback makes the state transformer total outside that
domain without imposing a fictional behavior on dirty scratch. -/
def intervalFirstLeafTotalState
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState) : BasisState :=
  if state scratch = false then
    intervalFirstLeafState mode topSpecial rightTop leftTop accumulator
      target addend carry label rightControl leftControl state
  else
    run (intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl) state

/-- Total direct semantics of a second-pass leaf, with the same clean-cell boundary. -/
def intervalSecondLeafTotalState
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator target addend carry scratch : Wire)
    (label : Nat) (rightControl leftControl : Wire)
    (state : BasisState) : BasisState :=
  if state scratch = false then
    intervalSecondLeafState mode topSpecial rightTop leftTop accumulator
      target addend carry label rightControl leftControl state
  else
    run (intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
      target addend carry scratch label rightControl leftControl) state

/-- Gate-independent source-order state action of the first (decreasing) synchronized scan. -/
def intervalFirstTraversalState
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState) : BasisState :=
  tree.runLeafState .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeafTotalState mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch label
        rightControl leftControl)
    rightRoot leftRoot rightPaths leftPaths state

/-- Gate-independent source-order state action of the second (increasing) synchronized scan. -/
def intervalSecondTraversalState
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState) : BasisState :=
  tree.runLeafState .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeafTotalState mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch label
        rightControl leftControl)
    rightRoot leftRoot rightPaths leftPaths state

/-- Direct whole-state semantics of the first source-ordered traversal. -/
theorem run_intervalFirstTraversal_state
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt)
    (hcleanRight : Clean rightPaths state) (hcleanLeft : Clean leftPaths state) :
    run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state =
      intervalFirstTraversalState mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths state := by
  let decoderSupport := tree.decoderWires rightRoot leftRoot rightPaths leftPaths
  have hruns : DualUnaryLeafRunsAsOn
      (fun label rightControl leftControl ↦
        intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch label rightControl leftControl)
      (fun label rightControl leftControl ↦
        intervalFirstLeafTotalState mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch label rightControl leftControl)
      tree.labels decoderSupport := by
    intro label hlabel rightControl leftControl hright hleft next
    by_cases hclean : next scratch = false
    · simp only [intervalFirstLeafTotalState, hclean, if_pos]
      exact run_intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch label rightControl leftControl
        next (intervalLeafLayout_of_decoder decoderSupport rightControl leftControl
          rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch
          (hlayout.2 label hlabel).1 (hlayout.2 label hlabel).2 hright hleft) hclean
    · simp_all [intervalFirstLeafTotalState]
  rw [intervalFirstTraversal, intervalFirstTraversalState]
  exact run_dualUnaryActionUnitary_as_runLeafState_on .dec _ _ tree rightRoot leftRoot
    rightPaths leftPaths decoderSupport state hlayout.1 hruns
    (intervalFirstLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree.labels decoderSupport
      (fun label hlabel ↦ (hlayout.2 label hlabel).2))
    (fun _ hwire ↦ hwire) hcleanRight hcleanLeft

/-- Direct whole-state semantics of the second source-ordered traversal. -/
theorem run_intervalSecondTraversal_state
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt)
    (hcleanRight : Clean rightPaths state) (hcleanLeft : Clean leftPaths state) :
    run (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state =
      intervalSecondTraversalState mode topSpecial rightTop leftTop accumulator
        carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths state := by
  let decoderSupport := tree.decoderWires rightRoot leftRoot rightPaths leftPaths
  have hruns : DualUnaryLeafRunsAsOn
      (fun label rightControl leftControl ↦
        intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch label rightControl leftControl)
      (fun label rightControl leftControl ↦
        intervalSecondLeafTotalState mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch label rightControl leftControl)
      tree.labels decoderSupport := by
    intro label hlabel rightControl leftControl hright hleft next
    by_cases hclean : next scratch = false
    · simp only [intervalSecondLeafTotalState, hclean, if_pos]
      exact run_intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch label rightControl leftControl
        next (intervalLeafLayout_of_decoder decoderSupport rightControl leftControl
          rightTop leftTop accumulator (targetAt label) (addendAt label) carry scratch
          (hlayout.2 label hlabel).1 (hlayout.2 label hlabel).2 hright hleft) hclean
    · simp_all [intervalSecondLeafTotalState]
  rw [intervalSecondTraversal, intervalSecondTraversalState]
  exact run_dualUnaryActionUnitary_as_runLeafState_on .inc _ _ tree rightRoot leftRoot
    rightPaths leftPaths decoderSupport state hlayout.1 hruns
    (intervalSecondLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree.labels decoderSupport
      (fun label hlabel ↦ (hlayout.2 label hlabel).2))
    (fun _ hwire ↦ hwire) hcleanRight hcleanLeft

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
  exact dualUnaryActionUnitary_preservesDecoder_on .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths state htree
    (intervalFirstLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree.labels
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label hlabel ↦ (hfamily label hlabel).2))
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
  exact dualUnaryActionUnitary_preservesDecoder_on .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths state htree
    (intervalSecondLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree.labels
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label hlabel ↦ (hfamily label hlabel).2))
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
  exact dualUnaryActionUnitary_clean_on .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths state htree
    (intervalFirstLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree.labels
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label hlabel ↦ (hfamily label hlabel).2))
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
  exact dualUnaryActionUnitary_clean_on .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths state htree
    (intervalSecondLeafFamily_dualPreserves mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree.labels
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      (fun label hlabel ↦ (hfamily label hlabel).2))
    hcleanRight hcleanLeft

/-- The first coherent traversal restores both decoder stacks and its clean leaf scratch. -/
theorem intervalFirstTraversal_cleanWithScratch
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt)
    (hcleanRight : Clean rightPaths state) (hcleanLeft : Clean leftPaths state)
    (hcleanScratch : Clean [scratch] state) :
    Clean rightPaths
        (run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) ∧
      Clean leftPaths
        (run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) ∧
      Clean [scratch]
        (run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) := by
  let decoder := tree.decoderWires rightRoot leftRoot rightPaths leftPaths
  let leafAction := fun label rightControl leftControl ↦
    intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
      (targetAt label) (addendAt label) carry scratch label rightControl leftControl
  have hpaths := intervalFirstTraversal_clean mode topSpecial rightTop leftTop
    accumulator carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths
    leftPaths state hlayout hcleanRight hcleanLeft
  have hpreserves := dualUnaryActionUnitary_preservesOn .dec leafAction tree
    rightRoot leftRoot rightPaths leftPaths decoder (decoder ++ [scratch]) state
    hlayout.1
    (intervalFirstLeafFamily_dualPreservesWithScratch mode topSpecial rightTop leftTop
      accumulator carry scratch targetAt addendAt tree.labels decoder hlayout.2)
    (fun _ hwire ↦ hwire) (fun _ hwire ↦ List.mem_append_left [scratch] hwire)
    hcleanRight hcleanLeft
  refine ⟨hpaths.1, hpaths.2, ?_⟩
  intro wire hwire
  rw [show run (intervalFirstTraversal mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths)
      state wire = state wire by
    simpa [intervalFirstTraversal, leafAction, decoder] using
      hpreserves wire (List.mem_append_right decoder hwire)]
  exact hcleanScratch wire hwire

/-- The second coherent traversal restores both decoder stacks and its clean leaf scratch. -/
theorem intervalSecondTraversal_cleanWithScratch
    (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop accumulator carry scratch : Wire)
    (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire)
    (rightPaths leftPaths : List Wire) (state : BasisState)
    (hlayout : IntervalTraversalLayout tree rightRoot leftRoot rightPaths leftPaths
      rightTop leftTop accumulator carry scratch targetAt addendAt)
    (hcleanRight : Clean rightPaths state) (hcleanLeft : Clean leftPaths state)
    (hcleanScratch : Clean [scratch] state) :
    Clean rightPaths
        (run (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) ∧
      Clean leftPaths
        (run (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) ∧
      Clean [scratch]
        (run (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
          carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths) state) := by
  let decoder := tree.decoderWires rightRoot leftRoot rightPaths leftPaths
  let leafAction := fun label rightControl leftControl ↦
    intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
      (targetAt label) (addendAt label) carry scratch label rightControl leftControl
  have hpaths := intervalSecondTraversal_clean mode topSpecial rightTop leftTop
    accumulator carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths
    leftPaths state hlayout hcleanRight hcleanLeft
  have hpreserves := dualUnaryActionUnitary_preservesOn .inc leafAction tree
    rightRoot leftRoot rightPaths leftPaths decoder (decoder ++ [scratch]) state
    hlayout.1
    (intervalSecondLeafFamily_dualPreservesWithScratch mode topSpecial rightTop leftTop
      accumulator carry scratch targetAt addendAt tree.labels decoder hlayout.2)
    (fun _ hwire ↦ hwire) (fun _ hwire ↦ List.mem_append_left [scratch] hwire)
    hcleanRight hcleanLeft
  refine ⟨hpaths.1, hpaths.2, ?_⟩
  intro wire hwire
  rw [show run (intervalSecondTraversal mode topSpecial rightTop leftTop accumulator
      carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths)
      state wire = state wire by
    simpa [intervalSecondTraversal, leafAction, decoder] using
      hpreserves wire (List.mem_append_right decoder hwire)]
  exact hcleanScratch wire hwire

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
      (fun state ↦ Clean rightPaths state ∧ Clean leftPaths state ∧
        Clean [scratch] state) := by
  have hfull := intervalTraversalLayout_decoderScratch tree rightRoot leftRoot
    rightPaths leftPaths rightTop leftTop accumulator carry scratch targetAt
    addendAt hlayout
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalFirstTraversalAdaptive, intervalFirstTraversal]
  exact dualUnaryAdaptiveAction_coherent_on .dec
    (fun label rightControl leftControl ↦
      intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    (fun label rightControl leftControl ↦
      intervalFirstLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths ([scratch] : List Wire) htree hfull
    (intervalFirstLeafFamily_dualPreservesWithScratch mode topSpecial rightTop
      leftTop accumulator carry scratch targetAt addendAt tree.labels
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      hfamily)
    (by
      intro label hlabel rightControl leftControl hright hleft
      exact intervalFirstLeafAdaptive_coherent mode topSpecial rightTop leftTop
        accumulator (targetAt label) (addendAt label) carry scratch label
        rightControl leftControl
        (intervalLeafLayout_of_decoder
          (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
          rightControl leftControl rightTop leftTop accumulator (targetAt label)
          (addendAt label) carry scratch (hfamily label hlabel).1
          (hfamily label hlabel).2 hright hleft))
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
      (fun state ↦ Clean rightPaths state ∧ Clean leftPaths state ∧
        Clean [scratch] state) := by
  have hfull := intervalTraversalLayout_decoderScratch tree rightRoot leftRoot
    rightPaths leftPaths rightTop leftTop accumulator carry scratch targetAt
    addendAt hlayout
  rcases hlayout with ⟨htree, hfamily⟩
  rw [intervalSecondTraversalAdaptive, intervalSecondTraversal]
  exact dualUnaryAdaptiveAction_coherent_on .inc
    (fun label rightControl leftControl ↦
      intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    (fun label rightControl leftControl ↦
      intervalSecondLeaf mode topSpecial rightTop leftTop accumulator
        (targetAt label) (addendAt label) carry scratch
        label rightControl leftControl)
    tree rightRoot leftRoot rightPaths leftPaths ([scratch] : List Wire) htree hfull
    (intervalSecondLeafFamily_dualPreservesWithScratch mode topSpecial rightTop
      leftTop accumulator carry scratch targetAt addendAt tree.labels
      (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
      hfamily)
    (by
      intro label hlabel rightControl leftControl hright hleft
      exact intervalSecondLeafAdaptive_coherent mode topSpecial rightTop leftTop
        accumulator (targetAt label) (addendAt label) carry scratch label
        rightControl leftControl
        (intervalLeafLayout_of_decoder
          (tree.decoderWires rightRoot leftRoot rightPaths leftPaths)
          rightControl leftControl rightTop leftTop accumulator (targetAt label)
          (addendAt label) carry scratch (hfamily label hlabel).1
          (hfamily label hlabel).2 hright hleft))
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
      tree.leafCostSum (fun _ _ _ ↦ 1)
          rightRoot leftRoot rightPaths leftPaths +
        2 * tree.internalNodes := by
  simpa only [intervalFirstTraversalAdaptive,
    intervalFirstLeafAdaptive_measurementCount] using
    dualUnaryAdaptiveAction_measurementCount .dec
      (fun label rightControl leftControl ↦
        intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
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
      tree.leafCostSum (fun _ _ _ ↦ 1)
          rightRoot leftRoot rightPaths leftPaths +
        2 * tree.internalNodes := by
  simpa only [intervalSecondTraversalAdaptive,
    intervalSecondLeafAdaptive_measurementCount] using
    dualUnaryAdaptiveAction_measurementCount .inc
      (fun label rightControl leftControl ↦
        intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
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
          (fun label _ _ ↦ 7 * (rippleFirstCellToffoliCost mode - 1 +
            if maskedZeroLeaf topSpecial label then 2 else 0))
          rightRoot leftRoot rightPaths leftPaths +
        14 * tree.internalNodes := by
  simpa only [intervalFirstTraversalAdaptive,
    intervalFirstLeafAdaptive_tCount] using
    dualUnaryAdaptiveAction_tCount .dec
      (fun label rightControl leftControl ↦
        intervalFirstLeafAdaptive mode topSpecial rightTop leftTop accumulator
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
          (fun label _ _ ↦ 7 * (rippleSecondCellToffoliCost mode - 1 +
            if maskedZeroLeaf topSpecial label then 2 else 0))
          rightRoot leftRoot rightPaths leftPaths +
        14 * tree.internalNodes := by
  simpa only [intervalSecondTraversalAdaptive,
    intervalSecondLeafAdaptive_tCount] using
    dualUnaryAdaptiveAction_tCount .inc
      (fun label rightControl leftControl ↦
        intervalSecondLeafAdaptive mode topSpecial rightTop leftTop accumulator
          (targetAt label) (addendAt label) carry scratch
          label rightControl leftControl)
      tree rightRoot leftRoot rightPaths leftPaths hlayout

end ShorECDLP.Paper2607_13816
