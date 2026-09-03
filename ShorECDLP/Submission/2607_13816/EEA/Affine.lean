import ShorECDLP.Submission.«2607_13816».EEA.Increment

/-!
# Scratch-clean affine endpoint primitives

This module implements the literal no-overflow Cuccaro adder, constant add/subtract,
uncontrolled increment, and `const - register` transform used by the pinned supplement's
interval and length blocks.  Registers are little-endian.  All executable definitions are
total; theorems that claim source fidelity and semantics carry the generator's width and clean
scratch premises explicitly.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

set_option linter.unusedSimpArgs false

/-! ## No-overflow Cuccaro addition -/

/-- Source MAJ gate order. -/
def cuccaroMaj (addend target carry : Wire) : Circuit :=
  [.CX addend target, .CX addend carry, .CCX carry target addend]

/-- Source UMA gate order. -/
def cuccaroUma (addend target carry : Wire) : Circuit :=
  [.CCX carry target addend, .CX addend carry, .CX carry target]

/-- Carry produced by the source MAJ cell.  This presentation mirrors the actual sequential
gate updates and is propositionally the usual majority bit. -/
def cuccaroCarry (addend target carry : Bool) : Bool :=
  Bool.xor addend
    (Bool.xor carry addend && Bool.xor target addend)

/-- Low-bit sum produced by the matching UMA cell. -/
def cuccaroSum (addend target carry : Bool) : Bool :=
  Bool.xor (Bool.xor target addend) carry

/-- Ripple addition on Boolean words, dropping the final overflow bit. -/
def cuccaroAddBits : Bool → List Bool → List Bool → List Bool
  | _, [], [] => []
  | carry, addend :: addends, target :: targets =>
      cuccaroSum addend target carry ::
        cuccaroAddBits (cuccaroCarry addend target carry) addends targets
  | _, _, _ => []

/-- Bit-word inverse of `cuccaroAddBits`, reconstructing the target word before addition
from the emitted sum bits and the same addend/input carry. -/
def cuccaroSubBits : Bool → List Bool → List Bool → List Bool
  | _, [], [] => []
  | carry, addend :: addends, sum :: sums =>
      let target := Bool.xor (Bool.xor sum addend) carry
      target :: cuccaroSubBits (cuccaroCarry addend target carry) addends sums
  | _, _, _ => []

@[simp]
theorem cuccaroSubBits_addBits
    (carry : Bool) (addends targets : List Bool)
    (hlength : addends.length = targets.length) :
    cuccaroSubBits carry addends
        (cuccaroAddBits carry addends targets) = targets := by
  induction addends generalizing targets carry with
  | nil =>
      have : targets = [] := List.length_eq_zero_iff.mp hlength.symm
      subst targets
      rfl
  | cons addend addends ih =>
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          have htail : addends.length = targets.length := by simpa using hlength
          cases carry <;> cases addend <;> cases target <;>
            simp [cuccaroAddBits, cuccaroSubBits, cuccaroSum,
              cuccaroCarry, ih _ _ htail]

@[simp]
theorem cuccaroAddBits_subBits
    (carry : Bool) (addends sums : List Bool)
    (hlength : addends.length = sums.length) :
    cuccaroAddBits carry addends
        (cuccaroSubBits carry addends sums) = sums := by
  induction addends generalizing sums carry with
  | nil =>
      have : sums = [] := List.length_eq_zero_iff.mp hlength.symm
      subst sums
      rfl
  | cons addend addends ih =>
      cases sums with
      | nil => simp at hlength
      | cons sum sums =>
          have htail : addends.length = sums.length := by simpa using hlength
          cases carry <;> cases addend <;> cases sum <;>
            simp [cuccaroAddBits, cuccaroSubBits, cuccaroSum,
              cuccaroCarry, ih _ _ htail]

/-- Exact recursive source stream: MAJ from low to high, then UMA from high to low. -/
def cuccaroAdd : List Wire → List Wire → Wire → Circuit
  | [], [], _ => []
  | addend :: addends, target :: targets, carry =>
      cuccaroMaj addend target carry ++
        cuccaroAdd addends targets addend ++
        cuccaroUma addend target carry
  | _, _, _ => []

/-- Literal inverse stream used for subtraction. -/
def cuccaroSub (addends targets : List Wire) (carry : Wire) : Circuit :=
  (cuccaroAdd addends targets carry).adjoint

private theorem cuccaro_three_parts
    (addend target carry : Wire)
    (hnd : [addend, target, carry].Nodup) :
    addend ≠ target ∧ addend ≠ carry ∧ target ≠ carry := by
  have haddend := (List.nodup_cons.mp hnd).1
  have htail := (List.nodup_cons.mp hnd).2
  have htarget := (List.nodup_cons.mp htail).1
  exact ⟨by
      intro equality
      exact haddend (by simp [equality]), by
      intro equality
      exact haddend (by simp [equality]), by
      intro equality
      exact htarget (by simp [equality])⟩

private theorem run_cuccaroMaj
    (addend target carry : Wire) (state : BasisState)
    (hnd : [addend, target, carry].Nodup) :
    run (cuccaroMaj addend target carry) state =
      state[target ↦ Bool.xor (state target) (state addend)]
        [carry ↦ Bool.xor (state carry) (state addend)]
        [addend ↦ cuccaroCarry (state addend) (state target) (state carry)] := by
  obtain ⟨hat, hac, htc⟩ := cuccaro_three_parts addend target carry hnd
  funext wire
  by_cases hwa : wire = addend
  · subst wire
    cases ha : state addend <;> cases ht : state target <;>
      cases hc : state carry <;>
      simp [cuccaroMaj, cuccaroCarry, run, applyGate, upd,
        hat, hac, htc, Ne.symm hat, Ne.symm hac, Ne.symm htc,
        ha, ht, hc]
  · by_cases hwt : wire = target
    · subst wire
      simp [cuccaroMaj, cuccaroCarry, run, applyGate, upd,
        hat, hac, htc, Ne.symm hat, Ne.symm hac, Ne.symm htc]
    · by_cases hwc : wire = carry
      · subst wire
        simp [cuccaroMaj, cuccaroCarry, run, applyGate, upd,
          hat, hac, htc, Ne.symm hat, Ne.symm hac, Ne.symm htc]
      · simp [cuccaroMaj, cuccaroCarry, run, applyGate, upd,
          hwa, hwt, hwc]

private theorem run_cuccaroUma_prepared
    (addend target carry : Wire) (state : BasisState)
    (oldAddend oldTarget oldCarry : Bool)
    (hnd : [addend, target, carry].Nodup)
    (ha : state addend = cuccaroCarry oldAddend oldTarget oldCarry)
    (ht : state target = Bool.xor oldTarget oldAddend)
    (hc : state carry = Bool.xor oldCarry oldAddend) :
    run (cuccaroUma addend target carry) state =
      state[addend ↦ oldAddend]
        [carry ↦ oldCarry]
        [target ↦ cuccaroSum oldAddend oldTarget oldCarry] := by
  obtain ⟨hat, hac, htc⟩ := cuccaro_three_parts addend target carry hnd
  funext wire
  by_cases hwa : wire = addend
  · subst wire
    cases oldAddend <;> cases oldTarget <;> cases oldCarry <;>
      simp [cuccaroUma, cuccaroCarry, cuccaroSum, run, applyGate, upd,
        hat, hac, htc, Ne.symm hat, Ne.symm hac, Ne.symm htc,
        ha, ht, hc]
  · by_cases hwt : wire = target
    · subst wire
      cases oldAddend <;> cases oldTarget <;> cases oldCarry <;>
        simp [cuccaroUma, cuccaroCarry, cuccaroSum, run, applyGate, upd,
          hat, hac, htc, Ne.symm hat, Ne.symm hac, Ne.symm htc,
          ha, ht, hc]
    · by_cases hwc : wire = carry
      · subst wire
        cases oldAddend <;> cases oldTarget <;> cases oldCarry <;>
          simp [cuccaroUma, cuccaroCarry, cuccaroSum, run, applyGate, upd,
            hat, hac, htc, Ne.symm hat, Ne.symm hac, Ne.symm htc,
            ha, ht, hc]
      · simp [cuccaroUma, run, applyGate, upd, hwa, hwt, hwc]

private theorem wireValues_congr_on
    (wires : List Wire) (left right : BasisState)
    (h : ∀ wire ∈ wires, left wire = right wire) :
    wireValues wires left = wireValues wires right := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq]
      exact ⟨h wire (by simp), ih (fun next hnext ↦
        h next (by simp [hnext]))⟩

private theorem cuccaro_child_nodup
    (carry addend target : Wire) (addends targets : List Wire)
    (hnd : (carry :: (addend :: addends) ++ target :: targets).Nodup) :
    (addend :: addends ++ targets).Nodup := by
  have htail := (List.nodup_cons.mp hnd).2
  have haddendsTargets :
      ((addend :: addends) ++ target :: targets).Nodup := htail
  obtain ⟨haddends, htargets, hcross⟩ :=
    List.nodup_append.mp haddendsTargets
  have htargetTail := (List.nodup_cons.mp htargets).2
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact (List.nodup_cons.mp haddends).1 hmem
    · exact hcross addend (by simp) addend (by simp [hmem]) rfl
  · exact List.nodup_append.mpr ⟨(List.nodup_cons.mp haddends).2,
      htargetTail, by
        intro left hleft right hright
        exact hcross left (by simp [hleft]) right (by simp [hright])⟩

private theorem cuccaro_head_nodup
    (carry addend target : Wire) (addends targets : List Wire)
    (hnd : (carry :: (addend :: addends) ++ target :: targets).Nodup) :
    [addend, target, carry].Nodup := by
  have hcarry := (List.nodup_cons.mp hnd).1
  have htail := (List.nodup_cons.mp hnd).2
  obtain ⟨haddends, _, hcross⟩ := List.nodup_append.mp htail
  have hat : addend ≠ target := by
    intro equality
    exact hcross addend (by simp) addend (by simp [equality]) rfl
  have hac : addend ≠ carry := by
    intro equality
    exact hcarry (by simp [equality])
  have htc : target ≠ carry := by
    intro equality
    exact hcarry (by simp [equality])
  exact List.nodup_cons.mpr ⟨by simp [hat, hac],
    List.nodup_cons.mpr ⟨by simp [htc], by simp⟩⟩

/-- Direct basis-state semantics of the no-overflow Cuccaro adder.  The addend word, input
carry, and every wire outside the target word are restored; the target receives the ripple sum. -/
theorem cuccaroAdd_correct
    (addends targets : List Wire) (carry : Wire) (state : BasisState)
    (hlength : addends.length = targets.length)
    (hnd : (carry :: addends ++ targets).Nodup) :
    let after := run (cuccaroAdd addends targets carry) state
    wireValues addends after = wireValues addends state ∧
      wireValues targets after =
        cuccaroAddBits (state carry)
          (wireValues addends state) (wireValues targets state) ∧
      ∀ wire, wire ∉ targets → after wire = state wire := by
  induction addends generalizing targets carry state with
  | nil =>
      have htargets : targets = [] := List.length_eq_zero_iff.mp hlength.symm
      subst targets
      simp [cuccaroAdd, cuccaroAddBits, wireValues]
  | cons addend addends ih =>
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          have htailLength : addends.length = targets.length := by
            simpa using hlength
          have hheadNodup :=
            cuccaro_head_nodup carry addend target addends targets (by
              simpa [List.cons_append] using hnd)
          have hchildNodup :=
            cuccaro_child_nodup carry addend target addends targets (by
              simpa [List.cons_append] using hnd)
          obtain ⟨hat, hac, htc⟩ :=
            cuccaro_three_parts addend target carry hheadNodup
          let first := run (cuccaroMaj addend target carry) state
          have hfirst := run_cuccaroMaj addend target carry state hheadNodup
          have hfirstAddends :
              wireValues addends first = wireValues addends state := by
            apply wireValues_congr_on
            intro wire hwire
            dsimp only [first]
            rw [hfirst]
            have hwAddend : wire ≠ addend := by
              intro equality
              subst wire
              exact (List.nodup_cons.mp hchildNodup).1
                (List.mem_append_left targets hwire)
            have hwTarget : wire ≠ target := by
              intro equality
              subst wire
              have htail := (List.nodup_cons.mp hnd).2
              obtain ⟨_, _, hcross⟩ := List.nodup_append.mp htail
              exact hcross target (by simp [hwire]) target (by simp) rfl
            have hwCarry : wire ≠ carry := by
              intro equality
              subst wire
              exact (List.nodup_cons.mp hnd).1 (by simp [hwire])
            simp [upd, hwAddend, hwTarget, hwCarry]
          have hfirstTargets :
              wireValues targets first = wireValues targets state := by
            apply wireValues_congr_on
            intro wire hwire
            dsimp only [first]
            rw [hfirst]
            have hwAddend : wire ≠ addend := by
              intro equality
              subst wire
              exact (List.nodup_cons.mp hchildNodup).1
                (List.mem_append_right addends hwire)
            have hwTarget : wire ≠ target := by
              intro equality
              subst wire
              exact (List.nodup_cons.mp (List.nodup_append.mp
                (List.nodup_cons.mp hnd).2).2.1).1 hwire
            have hwCarry : wire ≠ carry := by
              intro equality
              subst wire
              exact (List.nodup_cons.mp hnd).1 (by simp [hwire])
            simp [upd, hwAddend, hwTarget, hwCarry]
          have hrecursive := ih targets addend first htailLength hchildNodup
          let middle := run (cuccaroAdd addends targets addend) first
          have hmiddleAddends :
              wireValues addends middle = wireValues addends first := by
            simpa only [middle] using hrecursive.1
          have hmiddleTargets :
              wireValues targets middle =
                cuccaroAddBits (first addend)
                  (wireValues addends first) (wireValues targets first) := by
            simpa only [middle] using hrecursive.2.1
          have hmiddleOutside :
              ∀ wire, wire ∉ targets → middle wire = first wire := by
            simpa only [middle] using hrecursive.2.2
          have hfirstAddend :
              first addend =
                cuccaroCarry (state addend) (state target) (state carry) := by
            dsimp only [first]
            rw [hfirst]
            simp [upd]
          have hmiddleAddend :
              middle addend =
                cuccaroCarry (state addend) (state target) (state carry) := by
            rw [hmiddleOutside addend]
            · exact hfirstAddend
            · intro hmem
              exact (List.nodup_cons.mp hchildNodup).1
                (List.mem_append_right addends hmem)
          have hmiddleTarget :
              middle target = Bool.xor (state target) (state addend) := by
            rw [hmiddleOutside target]
            · dsimp only [first]
              rw [hfirst]
              simp [upd, hat, htc, Ne.symm hat, Ne.symm htc]
            · exact (List.nodup_cons.mp (List.nodup_append.mp
                (List.nodup_cons.mp hnd).2).2.1).1
          have hmiddleCarry :
              middle carry = Bool.xor (state carry) (state addend) := by
            rw [hmiddleOutside carry]
            · dsimp only [first]
              rw [hfirst]
              simp [upd, hac, htc, Ne.symm hac, Ne.symm htc]
            · intro hmem
              exact (List.nodup_cons.mp hnd).1 (by simp [hmem])
          have huma := run_cuccaroUma_prepared addend target carry middle
            (state addend) (state target) (state carry) hheadNodup
            hmiddleAddend hmiddleTarget hmiddleCarry
          rw [cuccaroAdd, run_append, run_append]
          change
            wireValues (addend :: addends)
                (run (cuccaroUma addend target carry) middle) =
                  wireValues (addend :: addends) state ∧
              wireValues (target :: targets)
                (run (cuccaroUma addend target carry) middle) =
                  cuccaroAddBits (state carry)
                    (wireValues (addend :: addends) state)
                    (wireValues (target :: targets) state) ∧
              ∀ wire, wire ∉ target :: targets →
                run (cuccaroUma addend target carry) middle wire = state wire
          rw [huma]
          constructor
          · simp only [wireValues, List.map_cons, List.cons.injEq]
            constructor
            · simp [upd, hat, hac, htc, Ne.symm hat, Ne.symm hac,
                Ne.symm htc]
            · change wireValues addends
                  (middle[addend ↦ state addend]
                    [carry ↦ state carry]
                    [target ↦ cuccaroSum (state addend)
                      (state target) (state carry)]) =
                    wireValues addends state
              rw [wireValues_congr_on addends _ middle]
              · rw [hmiddleAddends, hfirstAddends]
              · intro wire hwire
                have hwa : wire ≠ addend := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hchildNodup).1
                    (List.mem_append_left targets hwire)
                have hwt : wire ≠ target := by
                  intro equality
                  subst wire
                  have htail := (List.nodup_cons.mp hnd).2
                  obtain ⟨_, _, hcross⟩ := List.nodup_append.mp htail
                  exact hcross target (by simp [hwire]) target (by simp) rfl
                have hwc : wire ≠ carry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hnd).1 (by simp [hwire])
                simp [upd, hwa, hwt, hwc]
          · constructor
            · simp only [wireValues, List.map_cons, cuccaroAddBits,
                List.cons.injEq]
              constructor
              · simp [upd, hat, hac, htc, Ne.symm hat, Ne.symm hac,
                  Ne.symm htc]
              · change wireValues targets
                    (middle[addend ↦ state addend]
                      [carry ↦ state carry]
                      [target ↦ cuccaroSum (state addend)
                        (state target) (state carry)]) =
                    cuccaroAddBits
                      (cuccaroCarry (state addend) (state target) (state carry))
                      (wireValues addends state) (wireValues targets state)
                rw [wireValues_congr_on targets _ middle]
                · rw [hmiddleTargets, hfirstAddend, hfirstAddends,
                    hfirstTargets]
                · intro wire hwire
                  have hwa : wire ≠ addend := by
                    intro equality
                    subst wire
                    exact (List.nodup_cons.mp hchildNodup).1
                      (List.mem_append_right addends hwire)
                  have hwt : wire ≠ target := by
                    intro equality
                    subst wire
                    exact (List.nodup_cons.mp (List.nodup_append.mp
                      (List.nodup_cons.mp hnd).2).2.1).1 hwire
                  have hwc : wire ≠ carry := by
                    intro equality
                    subst wire
                    exact (List.nodup_cons.mp hnd).1 (by simp [hwire])
                  simp [upd, hwa, hwt, hwc]
            · intro wire hwire
              simp only [List.mem_cons, not_or] at hwire
              by_cases hwa : wire = addend
              · subst wire
                simp [upd, hat, hac, htc, Ne.symm hat, Ne.symm hac,
                  Ne.symm htc]
              · by_cases hwc : wire = carry
                · subst wire
                  simp [upd, hat, hac, htc, Ne.symm hat, Ne.symm hac,
                    Ne.symm htc]
                · have hmiddleWire := hmiddleOutside wire hwire.2
                  rw [show
                    middle[addend ↦ state addend]
                        [carry ↦ state carry]
                        [target ↦ cuccaroSum (state addend)
                          (state target) (state carry)] wire = middle wire by
                    simp [upd, hwa, hwc, hwire.1],
                    hmiddleWire]
                  dsimp only [first]
                  rw [hfirst]
                  simp [upd, hwa, hwc, hwire.1]

/-- Exact named support of the no-overflow adder. -/
theorem cuccaroAdd_usesOnly
    (addends targets : List Wire) (carry : Wire) :
    PaperCircuitUsesOnly (carry :: addends ++ targets)
      (cuccaroAdd addends targets carry) := by
  induction addends generalizing targets carry with
  | nil => cases targets <;> simp [cuccaroAdd, PaperCircuitUsesOnly]
  | cons addend addends ih =>
      cases targets with
      | nil => simp [cuccaroAdd, PaperCircuitUsesOnly]
      | cons target targets =>
          rw [cuccaroAdd]
          apply PaperCircuitUsesOnly.append
          · apply PaperCircuitUsesOnly.append
            · intro gate hgate
              simp only [cuccaroMaj, List.mem_cons, List.not_mem_nil,
                or_false] at hgate
              rcases hgate with rfl | rfl | rfl
              all_goals simp [PaperGateUsesOnly, gateWires]
            · apply (ih targets addend).mono
              intro wire hwire
              rcases List.mem_cons.mp hwire with rfl | hwire
              · simp
              · rcases List.mem_append.mp hwire with hwire | hwire
                · simp [hwire]
                · simp [hwire]
          · intro gate hgate
            simp only [cuccaroUma, List.mem_cons, List.not_mem_nil,
              or_false] at hgate
            rcases hgate with rfl | rfl | rfl
            all_goals simp [PaperGateUsesOnly, gateWires]

theorem cuccaroSub_usesOnly
    (addends targets : List Wire) (carry : Wire) :
    PaperCircuitUsesOnly (carry :: addends ++ targets)
      (cuccaroSub addends targets carry) := by
  exact (cuccaroAdd_usesOnly addends targets carry).adjoint

@[simp]
theorem cuccaroAdd_HPFree (addends targets : List Wire) (carry : Wire) :
    HPFree (cuccaroAdd addends targets carry) := by
  induction addends generalizing targets carry with
  | nil => cases targets <;> simp [cuccaroAdd]
  | cons addend addends ih =>
      cases targets <;> simp [cuccaroAdd, cuccaroMaj, cuccaroUma, ih]

private theorem hpFree_adjoint_local
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

@[simp]
theorem cuccaroSub_HPFree (addends targets : List Wire) (carry : Wire) :
    HPFree (cuccaroSub addends targets carry) := by
  exact hpFree_adjoint_local (cuccaroAdd_HPFree addends targets carry)

/-- Physical well-formedness under pairwise-distinct register roles. -/
theorem cuccaroAdd_wellFormed
    (addends targets : List Wire) (carry : Wire)
    (hlength : addends.length = targets.length)
    (hnd : (carry :: addends ++ targets).Nodup) :
    CircuitWellFormed (cuccaroAdd addends targets carry) := by
  induction addends generalizing targets carry with
  | nil =>
      have : targets = [] := List.length_eq_zero_iff.mp hlength.symm
      subst targets
      simp [cuccaroAdd]
  | cons addend addends ih =>
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          have htailLength : addends.length = targets.length := by simpa using hlength
          have hhead := cuccaro_head_nodup carry addend target addends targets (by
            simpa [List.cons_append] using hnd)
          have hchild := cuccaro_child_nodup carry addend target addends targets (by
            simpa [List.cons_append] using hnd)
          obtain ⟨hat, hac, htc⟩ := cuccaro_three_parts _ _ _ hhead
          rw [cuccaroAdd, circuitWellFormed_append, circuitWellFormed_append]
          exact ⟨⟨by simp [cuccaroMaj, CircuitWellFormed, Gate.WellFormed,
              hat, hac, htc, Ne.symm hat, Ne.symm hac, Ne.symm htc],
              ih targets addend htailLength hchild⟩,
            by simp [cuccaroUma, CircuitWellFormed, Gate.WellFormed,
              hat, hac, htc, Ne.symm hat, Ne.symm hac, Ne.symm htc]⟩

theorem cuccaroSub_wellFormed
    (addends targets : List Wire) (carry : Wire)
    (hlength : addends.length = targets.length)
    (hnd : (carry :: addends ++ targets).Nodup) :
    CircuitWellFormed (cuccaroSub addends targets carry) := by
  exact (circuitWellFormed_adjoint _).mpr
    (cuccaroAdd_wellFormed addends targets carry hlength hnd)

/-- The literal subtraction stream reverses the addition stream on every basis state. -/
theorem run_cuccaroSub_after_add
    (addends targets : List Wire) (carry : Wire) (state : BasisState)
    (hlength : addends.length = targets.length)
    (hnd : (carry :: addends ++ targets).Nodup) :
    run (cuccaroSub addends targets carry)
        (run (cuccaroAdd addends targets carry) state) = state := by
  exact run_adjoint_run_classical _
    (cuccaroAdd_wellFormed addends targets carry hlength hnd) state

/-- Classical execution of a circuit adjoint followed by the original well-formed circuit also
restores the complete basis state. -/
theorem run_run_adjoint_classical
    (circuit : Circuit) (hwellFormed : CircuitWellFormed circuit)
    (state : BasisState) :
    run circuit (run circuit.adjoint state) = state := by
  have hadjoint : CircuitWellFormed circuit.adjoint :=
    (circuitWellFormed_adjoint circuit).mpr hwellFormed
  have hinverse := run_adjoint_run_classical circuit.adjoint hadjoint state
  simpa [circuit_adjoint_adjoint] using hinverse

/-- The forward Cuccaro stream restores a state produced by its literal subtraction stream. -/
theorem run_cuccaroAdd_after_sub
    (addends targets : List Wire) (carry : Wire) (state : BasisState)
    (hlength : addends.length = targets.length)
    (hnd : (carry :: addends ++ targets).Nodup) :
    run (cuccaroAdd addends targets carry)
        (run (cuccaroSub addends targets carry) state) = state := by
  exact run_run_adjoint_classical
    (cuccaroAdd addends targets carry)
    (cuccaroAdd_wellFormed addends targets carry hlength hnd) state

/-- Direct basis-state semantics of literal Cuccaro subtraction. -/
theorem cuccaroSub_correct
    (addends targets : List Wire) (carry : Wire) (state : BasisState)
    (hlength : addends.length = targets.length)
    (hnd : (carry :: addends ++ targets).Nodup) :
    let after := run (cuccaroSub addends targets carry) state
    wireValues addends after = wireValues addends state ∧
      wireValues targets after =
        cuccaroSubBits (state carry)
          (wireValues addends state) (wireValues targets state) ∧
      ∀ wire, wire ∉ targets → after wire = state wire := by
  let after := run (cuccaroSub addends targets carry) state
  have hinverse :
      run (cuccaroAdd addends targets carry) after = state := by
    simpa only [after] using
      run_cuccaroAdd_after_sub addends targets carry state hlength hnd
  have hadd := cuccaroAdd_correct addends targets carry after hlength hnd
  have haddends : wireValues addends after = wireValues addends state := by
    rw [← hinverse]
    exact hadd.1.symm
  have hcarryNotTarget : carry ∉ targets := by
    intro hmem
    exact (List.nodup_cons.mp hnd).1 (List.mem_append_right addends hmem)
  have hcarry : after carry = state carry := by
    rw [← hinverse]
    exact (hadd.2.2 carry hcarryNotTarget).symm
  have hsum :
      wireValues targets state =
        cuccaroAddBits (state carry) (wireValues addends state)
          (wireValues targets after) := by
    calc
      wireValues targets state =
          wireValues targets
            (run (cuccaroAdd addends targets carry) after) := by
        rw [hinverse]
      _ = cuccaroAddBits (after carry) (wireValues addends after)
          (wireValues targets after) := hadd.2.1
      _ = cuccaroAddBits (state carry) (wireValues addends state)
          (wireValues targets after) := by rw [hcarry, haddends]
  have htarget :
      wireValues targets after =
        cuccaroSubBits (state carry)
          (wireValues addends state) (wireValues targets state) := by
    have hmapped := congrArg
      (cuccaroSubBits (state carry) (wireValues addends state)) hsum
    have hwordLength :
        (wireValues addends state).length =
          (wireValues targets after).length := by
      simpa [wireValues] using hlength
    rw [cuccaroSubBits_addBits _ _ _ hwordLength] at hmapped
    exact hmapped.symm
  change wireValues addends after = wireValues addends state ∧
    wireValues targets after =
      cuccaroSubBits (state carry)
        (wireValues addends state) (wireValues targets state) ∧
    ∀ wire, wire ∉ targets → after wire = state wire
  refine ⟨haddends, htarget, ?_⟩
  intro wire hwire
  rw [← hinverse]
  exact (hadd.2.2 wire hwire).symm

/-- Exact source count: two Toffolis per bit. -/
theorem cuccaroAdd_toffoliCount
    (addends targets : List Wire) (carry : Wire)
    (hlength : addends.length = targets.length) :
    eeaToffoliCount (cuccaroAdd addends targets carry) =
      2 * addends.length := by
  induction addends generalizing targets carry with
  | nil =>
      have : targets = [] := List.length_eq_zero_iff.mp hlength.symm
      subst targets
      rfl
  | cons addend addends ih =>
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          have htail : addends.length = targets.length := by simpa using hlength
          rw [cuccaroAdd, eeaToffoliCount_append, eeaToffoliCount_append,
            ih targets addend htail]
          simp [cuccaroMaj, cuccaroUma, eeaToffoliCount]
          omega

/-- Exact source count: four CNOTs per bit. -/
theorem cuccaroAdd_cnotCount
    (addends targets : List Wire) (carry : Wire)
    (hlength : addends.length = targets.length) :
    eeaCnotCount (cuccaroAdd addends targets carry) =
      4 * addends.length := by
  induction addends generalizing targets carry with
  | nil =>
      have : targets = [] := List.length_eq_zero_iff.mp hlength.symm
      subst targets
      rfl
  | cons addend addends ih =>
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          have htail : addends.length = targets.length := by simpa using hlength
          rw [cuccaroAdd, eeaCnotCount_append, eeaCnotCount_append,
            ih targets addend htail]
          simp [cuccaroMaj, cuccaroUma, eeaCnotCount]
          omega

theorem cuccaroAdd_tCount
    (addends targets : List Wire) (carry : Wire)
    (hlength : addends.length = targets.length) :
    ShorECDLP.tCount (cuccaroAdd addends targets carry) =
      14 * addends.length := by
  induction addends generalizing targets carry with
  | nil =>
      have : targets = [] := List.length_eq_zero_iff.mp hlength.symm
      subst targets
      rfl
  | cons addend addends ih =>
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          have htail : addends.length = targets.length := by simpa using hlength
          rw [cuccaroAdd, tCount_append, tCount_append,
            ih targets addend htail]
          simp [cuccaroMaj, cuccaroUma, tCost]
          omega

theorem cuccaroSub_toffoliCount
    (addends targets : List Wire) (carry : Wire)
    (hlength : addends.length = targets.length) :
    eeaToffoliCount (cuccaroSub addends targets carry) =
      2 * addends.length := by
  rw [cuccaroSub, eeaToffoliCount_adjoint,
    cuccaroAdd_toffoliCount addends targets carry hlength]

theorem cuccaroSub_cnotCount
    (addends targets : List Wire) (carry : Wire)
    (hlength : addends.length = targets.length) :
    eeaCnotCount (cuccaroSub addends targets carry) =
      4 * addends.length := by
  rw [cuccaroSub, eeaCnotCount_adjoint,
    cuccaroAdd_cnotCount addends targets carry hlength]

theorem cuccaroSub_tCount
    (addends targets : List Wire) (carry : Wire)
    (hlength : addends.length = targets.length) :
    ShorECDLP.tCount (cuccaroSub addends targets carry) =
      14 * addends.length := by
  rw [cuccaroSub, tCount_adjoint,
    cuccaroAdd_tCount addends targets carry hlength]

/-! ## Constant loading and scratch-clean constant addition -/

/-- XOR the low `register.length` bits of a natural into a register, in increasing source order. -/
def xorConstant : List Wire → Nat → Circuit
  | [], _ => []
  | wire :: wires, value =>
      (if value.testBit 0 then [.X wire] else []) ++
        xorConstant wires (value / 2)

/-- Gate-independent word action of `xorConstant`. -/
def xorConstantBits : List Bool → Nat → List Bool
  | [], _ => []
  | bit :: bits, value =>
      (if value.testBit 0 then !bit else bit) ::
        xorConstantBits bits (value / 2)

/-- Low constant word emitted into an initially zero register. -/
def constantBits (width value : Nat) : List Bool :=
  xorConstantBits (List.replicate width false) value

private theorem xorConstantBits_twice
    (bits : List Bool) (value : Nat) :
    xorConstantBits (xorConstantBits bits value) value = bits := by
  induction bits generalizing value with
  | nil => rfl
  | cons bit bits ih =>
      by_cases hbit : value.testBit 0 <;>
        simp [xorConstantBits, hbit, ih]

private theorem wireValues_eq_at
    (wires : List Wire) (left right : BasisState)
    (hvalues : wireValues wires left = wireValues wires right)
    (wire : Wire) (hwire : wire ∈ wires) :
    left wire = right wire := by
  induction wires with
  | nil => simp at hwire
  | cons head tail ih =>
      simp only [List.mem_cons] at hwire
      simp only [wireValues, List.map_cons, List.cons.injEq] at hvalues
      rcases hwire with rfl | hwire
      · exact hvalues.1
      · exact ih hvalues.2 hwire

private theorem wireValues_falseState (wires : List Wire) :
    wireValues wires (fun _ ↦ false) =
      List.replicate wires.length false := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      rw [show (wire :: wires).length = wires.length + 1 by rfl,
        List.replicate_succ, ← ih]
      rfl

/-- Direct word semantics and locality of the exact constant-XOR stream. -/
theorem xorConstant_correct
    (register : List Wire) (value : Nat) (state : BasisState)
    (hnd : register.Nodup) :
    let after := run (xorConstant register value) state
    wireValues register after =
        xorConstantBits (wireValues register state) value ∧
      ∀ wire, wire ∉ register → after wire = state wire := by
  induction register generalizing value state with
  | nil => simp [xorConstant, xorConstantBits, wireValues]
  | cons head tail ih =>
      have hhead := (List.nodup_cons.mp hnd).1
      have htail := (List.nodup_cons.mp hnd).2
      by_cases hbit : value.testBit 0
      · rw [xorConstant, if_pos hbit, run_append]
        let first := run [.X head] state
        have hfirstHead : first head = !state head := by
          simp [first, run, applyGate]
        have hfirstTail : wireValues tail first = wireValues tail state := by
          apply wireValues_congr_on
          intro wire hwire
          have hw : wire ≠ head := by
            intro equality
            exact hhead (by simpa [equality] using hwire)
          simp [first, run, applyGate, upd, hw]
        have hrecursive := ih (value / 2) first htail
        constructor
        · have hheadValue :
              run (xorConstant tail (value / 2)) first head =
                Bool.not (state head) := by
            rw [hrecursive.2 head hhead, hfirstHead]
          have htailValues := hrecursive.1
          rw [hfirstTail] at htailValues
          simpa only [wireValues, List.map_cons, xorConstantBits,
            hbit, if_true] using
              congrArg₂ List.cons hheadValue htailValues
        · intro wire hwire
          simp only [List.mem_cons, not_or] at hwire
          rw [hrecursive.2 wire hwire.2]
          simp [first, run, applyGate, upd, hwire.1]
      · rw [xorConstant, if_neg hbit, List.nil_append]
        have hrecursive := ih (value / 2) state htail
        constructor
        · have hheadValue :
              run (xorConstant tail (value / 2)) state head = state head :=
            hrecursive.2 head hhead
          simpa only [wireValues, List.map_cons, xorConstantBits,
            hbit, if_false] using
              congrArg₂ List.cons hheadValue hrecursive.1
        · intro wire hwire
          exact hrecursive.2 wire (by
            simp only [List.mem_cons, not_or] at hwire
            exact hwire.2)

/-- Applying the same constant XOR twice restores the whole state. -/
theorem run_xorConstant_twice
    (register : List Wire) (value : Nat) (state : BasisState)
    (hnd : register.Nodup) :
    run (xorConstant register value)
        (run (xorConstant register value) state) = state := by
  have hfirst := xorConstant_correct register value state hnd
  have hsecond := xorConstant_correct register value
    (run (xorConstant register value) state) hnd
  funext wire
  by_cases hwire : wire ∈ register
  · apply wireValues_eq_at register _ _ ?_ wire hwire
    rw [hsecond.1, hfirst.1, xorConstantBits_twice]
  · rw [hsecond.2 wire hwire, hfirst.2 wire hwire]

@[simp]
theorem xorConstant_HPFree (register : List Wire) (value : Nat) :
    HPFree (xorConstant register value) := by
  induction register generalizing value with
  | nil => simp [xorConstant]
  | cons head tail ih =>
      by_cases hbit : value.testBit 0 <;>
        simp [xorConstant, hbit, ih]

theorem xorConstant_wellFormed (register : List Wire) (value : Nat) :
    CircuitWellFormed (xorConstant register value) := by
  induction register generalizing value with
  | nil => simp [xorConstant]
  | cons head tail ih =>
      by_cases hbit : value.testBit 0
      · rw [xorConstant, if_pos hbit, circuitWellFormed_append]
        exact ⟨by simp [CircuitWellFormed, Gate.WellFormed], ih (value / 2)⟩
      · rw [xorConstant, if_neg hbit]
        exact ih (value / 2)

theorem xorConstant_usesOnly (register : List Wire) (value : Nat) :
    PaperCircuitUsesOnly register (xorConstant register value) := by
  induction register generalizing value with
  | nil => simp [xorConstant, PaperCircuitUsesOnly]
  | cons head tail ih =>
      by_cases hbit : value.testBit 0
      · rw [xorConstant, if_pos hbit]
        apply PaperCircuitUsesOnly.append
        · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
        · exact (ih (value / 2)).mono (by
            intro wire hwire
            simp [hwire])
      · rw [xorConstant, if_neg hbit]
        exact (ih (value / 2)).mono (by
          intro wire hwire
          simp [hwire])

/-- Number of selected low bits in an uncontrolled constant load. -/
def constantBitCount : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, value =>
      (if value.testBit 0 then 1 else 0) +
        constantBitCount width (value / 2)

theorem xorConstant_gateCount
    (register : List Wire) (value : Nat) :
    (xorConstant register value).length =
      constantBitCount register.length value := by
  induction register generalizing value with
  | nil => rfl
  | cons head tail ih =>
      by_cases hbit : value.testBit 0
      · rw [xorConstant, if_pos hbit]
        simp [constantBitCount, hbit, ih, Nat.add_comm]
      · rw [xorConstant, if_neg hbit]
        simp [constantBitCount, hbit, ih]

@[simp]
theorem xorConstant_toffoliCount (register : List Wire) (value : Nat) :
    eeaToffoliCount (xorConstant register value) = 0 := by
  induction register generalizing value with
  | nil => rfl
  | cons head tail ih =>
      by_cases hbit : value.testBit 0
      · rw [xorConstant, if_pos hbit]
        simpa [eeaToffoliCount] using ih (value / 2)
      · rw [xorConstant, if_neg hbit]
        exact ih (value / 2)

@[simp]
theorem xorConstant_cnotCount (register : List Wire) (value : Nat) :
    eeaCnotCount (xorConstant register value) = 0 := by
  induction register generalizing value with
  | nil => rfl
  | cons head tail ih =>
      by_cases hbit : value.testBit 0
      · rw [xorConstant, if_pos hbit]
        simpa [eeaCnotCount] using ih (value / 2)
      · rw [xorConstant, if_neg hbit]
        exact ih (value / 2)

@[simp]
theorem xorConstant_tCount (register : List Wire) (value : Nat) :
    ShorECDLP.tCount (xorConstant register value) = 0 := by
  induction register generalizing value with
  | nil => rfl
  | cons head tail ih =>
      by_cases hbit : value.testBit 0
      · rw [xorConstant, if_pos hbit]
        simpa [tCost] using ih (value / 2)
      · rw [xorConstant, if_neg hbit]
        exact ih (value / 2)

/-- Scratch-clean source constant addition: load, no-overflow Cuccaro add, unload. -/
def addConstant
    (register constants : List Wire) (carry : Wire) (value : Nat) : Circuit :=
  xorConstant constants value ++
    cuccaroAdd constants register carry ++
    xorConstant constants value

/-- Literal constant subtraction with the same increasing-order loads around the inverse
Cuccaro stream. -/
def subConstant
    (register constants : List Wire) (carry : Wire) (value : Nat) : Circuit :=
  xorConstant constants value ++
    cuccaroSub constants register carry ++
    xorConstant constants value

/-- Physical role separation for a constant affine primitive. -/
def ConstantLayout
    (register constants : List Wire) (carry : Wire) : Prop :=
  (carry :: constants ++ register).Nodup

private theorem constantLayout_parts
    (register constants : List Wire) (carry : Wire)
    (hlayout : ConstantLayout register constants carry) :
    constants.Nodup ∧ register.Nodup ∧
      carry ∉ constants ∧ carry ∉ register ∧
      (∀ constant ∈ constants, constant ∉ register) := by
  have hcarry := (List.nodup_cons.mp hlayout).1
  obtain ⟨hconstants, hregister, hcross⟩ :=
    List.nodup_append.mp (List.nodup_cons.mp hlayout).2
  exact ⟨hconstants, hregister, by
      intro hmem
      exact hcarry (List.mem_append_left register hmem), by
      intro hmem
      exact hcarry (List.mem_append_right constants hmem), by
      intro constant hconstant hmem
      exact hcross constant hconstant constant hmem rfl⟩

/-- Direct word semantics and scratch restoration of constant addition. -/
theorem addConstant_correct
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (state : BasisState)
    (hlength : constants.length = register.length)
    (hlayout : ConstantLayout register constants carry)
    (hclean : Clean (constants ++ [carry]) state) :
    let after := run (addConstant register constants carry value) state
    wireValues register after =
        cuccaroAddBits false (constantBits constants.length value)
          (wireValues register state) ∧
      Clean (constants ++ [carry]) after ∧
      ∀ wire, wire ∉ register → after wire = state wire := by
  obtain ⟨hconstants, hregister, hcarryConstants, hcarryRegister,
    hcross⟩ := constantLayout_parts register constants carry hlayout
  let loaded := run (xorConstant constants value) state
  have hload := xorConstant_correct constants value state hconstants
  have hloadedConstants :
      wireValues constants loaded = constantBits constants.length value := by
    rw [hload.1]
    have hzeros : wireValues constants state =
        List.replicate constants.length false := by
      rw [← wireValues_falseState constants]
      apply wireValues_congr_on
      intro wire hwire
      exact hclean wire (by simp [hwire])
    rw [hzeros]
    rfl
  have hloadedRegister :
      wireValues register loaded = wireValues register state := by
    apply wireValues_congr_on
    intro wire hwire
    exact hload.2 wire (by
      intro hmem
      exact hcross wire hmem hwire)
  have hloadedCarry : loaded carry = false := by
    dsimp only [loaded]
    rw [hload.2 carry hcarryConstants]
    exact hclean carry (by simp)
  let added := run (cuccaroAdd constants register carry) loaded
  have hadd := cuccaroAdd_correct constants register carry loaded
    hlength hlayout
  have haddedRegister :
      wireValues register added =
        cuccaroAddBits false (constantBits constants.length value)
          (wireValues register state) := by
    rw [show wireValues register added =
        cuccaroAddBits (loaded carry) (wireValues constants loaded)
          (wireValues register loaded) by simpa only [added] using hadd.2.1,
      hloadedCarry, hloadedConstants, hloadedRegister]
  have haddedConstants :
      wireValues constants added = wireValues constants loaded := by
    simpa only [added] using hadd.1
  have haddedCarry : added carry = loaded carry := by
    exact hadd.2.2 carry hcarryRegister
  let after := run (xorConstant constants value) added
  have hunload := xorConstant_correct constants value added hconstants
  rw [addConstant, run_append, run_append]
  change
    wireValues register after =
        cuccaroAddBits false (constantBits constants.length value)
          (wireValues register state) ∧
      Clean (constants ++ [carry]) after ∧
      ∀ wire, wire ∉ register → after wire = state wire
  constructor
  · rw [show wireValues register after = wireValues register added by
      apply wireValues_congr_on
      intro wire hwire
      exact hunload.2 wire (by
        intro hmem
        exact hcross wire hmem hwire), haddedRegister]
  · constructor
    · intro wire hwire
      rcases List.mem_append.mp hwire with hconstant | hcarry
      · have hafterValues : wireValues constants after =
            List.replicate constants.length false := by
          rw [show wireValues constants after =
              xorConstantBits (wireValues constants added) value by
                simpa only [after] using hunload.1,
            haddedConstants, hloadedConstants]
          exact xorConstantBits_twice
            (List.replicate constants.length false) value
        have hzeroAt := wireValues_eq_at constants after
          (fun _ ↦ false) (by
            rw [wireValues_falseState]
            exact hafterValues) wire hconstant
        exact hzeroAt
      · simp only [List.mem_singleton] at hcarry
        subst wire
        rw [show after carry = added carry by
          exact hunload.2 carry hcarryConstants,
          haddedCarry, hloadedCarry]
    · intro wire hwire
      by_cases hconstant : wire ∈ constants
      · have hfinalClean : after wire = false := by
          exact (show Clean (constants ++ [carry]) after from by
            intro next hnext
            rcases List.mem_append.mp hnext with hnext | hnext
            · have hafterValues : wireValues constants after =
                  List.replicate constants.length false := by
                rw [show wireValues constants after =
                    xorConstantBits (wireValues constants added) value by
                      simpa only [after] using hunload.1,
                  haddedConstants, hloadedConstants]
                exact xorConstantBits_twice
                  (List.replicate constants.length false) value
              exact wireValues_eq_at constants after (fun _ ↦ false)
                (by
                  rw [wireValues_falseState]
                  exact hafterValues) next hnext
            · simp only [List.mem_singleton] at hnext
              subst next
              rw [show after carry = added carry by
                exact hunload.2 carry hcarryConstants,
                haddedCarry, hloadedCarry]) wire (by simp [hconstant])
        rw [hfinalClean, hclean wire (by simp [hconstant])]
      · rw [show after wire = added wire by
          exact hunload.2 wire hconstant,
          show added wire = loaded wire by
            exact hadd.2.2 wire hwire,
          show loaded wire = state wire by
            exact hload.2 wire hconstant]

/-- Direct word semantics and scratch restoration of constant subtraction. -/
theorem subConstant_correct
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (state : BasisState)
    (hlength : constants.length = register.length)
    (hlayout : ConstantLayout register constants carry)
    (hclean : Clean (constants ++ [carry]) state) :
    let after := run (subConstant register constants carry value) state
    wireValues register after =
        cuccaroSubBits false (constantBits constants.length value)
          (wireValues register state) ∧
      Clean (constants ++ [carry]) after ∧
      ∀ wire, wire ∉ register → after wire = state wire := by
  obtain ⟨hconstants, hregister, hcarryConstants, hcarryRegister,
    hcross⟩ := constantLayout_parts register constants carry hlayout
  let loaded := run (xorConstant constants value) state
  have hload := xorConstant_correct constants value state hconstants
  have hloadedConstants :
      wireValues constants loaded = constantBits constants.length value := by
    rw [hload.1]
    have hzeros : wireValues constants state =
        List.replicate constants.length false := by
      rw [← wireValues_falseState constants]
      apply wireValues_congr_on
      intro wire hwire
      exact hclean wire (by simp [hwire])
    rw [hzeros]
    rfl
  have hloadedRegister :
      wireValues register loaded = wireValues register state := by
    apply wireValues_congr_on
    intro wire hwire
    exact hload.2 wire (by
      intro hmem
      exact hcross wire hmem hwire)
  have hloadedCarry : loaded carry = false := by
    dsimp only [loaded]
    rw [hload.2 carry hcarryConstants]
    exact hclean carry (by simp)
  let subtracted := run (cuccaroSub constants register carry) loaded
  have hsub := cuccaroSub_correct constants register carry loaded
    hlength hlayout
  have hsubtractedRegister :
      wireValues register subtracted =
        cuccaroSubBits false (constantBits constants.length value)
          (wireValues register state) := by
    rw [show wireValues register subtracted =
        cuccaroSubBits (loaded carry) (wireValues constants loaded)
          (wireValues register loaded) by simpa only [subtracted] using hsub.2.1,
      hloadedCarry, hloadedConstants, hloadedRegister]
  have hsubtractedConstants :
      wireValues constants subtracted = wireValues constants loaded := by
    simpa only [subtracted] using hsub.1
  have hsubtractedCarry : subtracted carry = loaded carry := by
    exact hsub.2.2 carry hcarryRegister
  let after := run (xorConstant constants value) subtracted
  have hunload := xorConstant_correct constants value subtracted hconstants
  rw [subConstant, run_append, run_append]
  change
    wireValues register after =
        cuccaroSubBits false (constantBits constants.length value)
          (wireValues register state) ∧
      Clean (constants ++ [carry]) after ∧
      ∀ wire, wire ∉ register → after wire = state wire
  constructor
  · rw [show wireValues register after = wireValues register subtracted by
      apply wireValues_congr_on
      intro wire hwire
      exact hunload.2 wire (by
        intro hmem
        exact hcross wire hmem hwire), hsubtractedRegister]
  · constructor
    · intro wire hwire
      rcases List.mem_append.mp hwire with hconstant | hcarry
      · have hafterValues : wireValues constants after =
            List.replicate constants.length false := by
          rw [show wireValues constants after =
              xorConstantBits (wireValues constants subtracted) value by
                simpa only [after] using hunload.1,
            hsubtractedConstants, hloadedConstants]
          exact xorConstantBits_twice
            (List.replicate constants.length false) value
        exact wireValues_eq_at constants after (fun _ ↦ false) (by
          rw [wireValues_falseState]
          exact hafterValues) wire hconstant
      · simp only [List.mem_singleton] at hcarry
        subst wire
        rw [show after carry = subtracted carry by
          exact hunload.2 carry hcarryConstants,
          hsubtractedCarry, hloadedCarry]
    · intro wire hwire
      by_cases hconstant : wire ∈ constants
      · have hfinalClean : after wire = false := by
          exact (show Clean (constants ++ [carry]) after from by
            intro next hnext
            rcases List.mem_append.mp hnext with hnext | hnext
            · have hafterValues : wireValues constants after =
                  List.replicate constants.length false := by
                rw [show wireValues constants after =
                    xorConstantBits (wireValues constants subtracted) value by
                      simpa only [after] using hunload.1,
                  hsubtractedConstants, hloadedConstants]
                exact xorConstantBits_twice
                  (List.replicate constants.length false) value
              exact wireValues_eq_at constants after (fun _ ↦ false)
                (by
                  rw [wireValues_falseState]
                  exact hafterValues) next hnext
            · simp only [List.mem_singleton] at hnext
              subst next
              rw [show after carry = subtracted carry by
                exact hunload.2 carry hcarryConstants,
                hsubtractedCarry, hloadedCarry]) wire (by simp [hconstant])
        rw [hfinalClean, hclean wire (by simp [hconstant])]
      · rw [show after wire = subtracted wire by
          exact hunload.2 wire hconstant,
          show subtracted wire = loaded wire by
            exact hsub.2.2 wire hwire,
          show loaded wire = state wire by
            exact hload.2 wire hconstant]

/-- The source constant subtraction is the semantic inverse of source constant addition. -/
theorem run_subConstant_after_add
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (state : BasisState)
    (hlength : constants.length = register.length)
    (hlayout : ConstantLayout register constants carry) :
    run (subConstant register constants carry value)
        (run (addConstant register constants carry value) state) = state := by
  have hconstants := (constantLayout_parts register constants carry hlayout).1
  have hcuccaro := cuccaroAdd_wellFormed constants register carry hlength hlayout
  rw [addConstant, subConstant]
  simp only [run_append]
  rw [run_xorConstant_twice constants value]
  · rw [run_cuccaroSub_after_add constants register carry]
    · exact run_xorConstant_twice constants value state hconstants
    · exact hlength
    · exact hlayout
  · exact hconstants

@[simp]
theorem addConstant_HPFree
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    HPFree (addConstant register constants carry value) := by
  simp [addConstant]

@[simp]
theorem subConstant_HPFree
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    HPFree (subConstant register constants carry value) := by
  simp [subConstant]

/-- Complete named support of a source constant-addition block. -/
theorem addConstant_usesOnly
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    PaperCircuitUsesOnly (constants ++ register ++ [carry])
      (addConstant register constants carry value) := by
  rw [addConstant]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply (xorConstant_usesOnly constants value).mono
      intro wire hwire
      simp [hwire]
    · apply (cuccaroAdd_usesOnly constants register carry).mono
      intro wire hwire
      simp only [List.mem_cons, List.mem_append] at hwire
      rcases hwire with (rfl | hwire) | hwire
      · simp
      · simp [hwire]
      · simp [hwire]
  · apply (xorConstant_usesOnly constants value).mono
    intro wire hwire
    simp [hwire]

/-- Complete named support of a source constant-subtraction block. -/
theorem subConstant_usesOnly
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    PaperCircuitUsesOnly (constants ++ register ++ [carry])
      (subConstant register constants carry value) := by
  rw [subConstant]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply (xorConstant_usesOnly constants value).mono
      intro wire hwire
      simp [hwire]
    · apply (cuccaroSub_usesOnly constants register carry).mono
      intro wire hwire
      simp only [List.mem_cons, List.mem_append] at hwire
      rcases hwire with (rfl | hwire) | hwire
      · simp
      · simp [hwire]
      · simp [hwire]
  · apply (xorConstant_usesOnly constants value).mono
    intro wire hwire
    simp [hwire]

theorem addConstant_wellFormed
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hlength : constants.length = register.length)
    (hlayout : ConstantLayout register constants carry) :
    CircuitWellFormed (addConstant register constants carry value) := by
  simp only [addConstant, circuitWellFormed_append]
  exact ⟨⟨xorConstant_wellFormed constants value,
    cuccaroAdd_wellFormed constants register carry hlength hlayout⟩,
    xorConstant_wellFormed constants value⟩

theorem subConstant_wellFormed
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hlength : constants.length = register.length)
    (hlayout : ConstantLayout register constants carry) :
    CircuitWellFormed (subConstant register constants carry value) := by
  simp only [subConstant, circuitWellFormed_append]
  exact ⟨⟨xorConstant_wellFormed constants value,
    cuccaroSub_wellFormed constants register carry hlength hlayout⟩,
    xorConstant_wellFormed constants value⟩

theorem addConstant_toffoliCount
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hlength : constants.length = register.length) :
    eeaToffoliCount (addConstant register constants carry value) =
      2 * register.length := by
  simp [addConstant, eeaToffoliCount_append,
    cuccaroAdd_toffoliCount constants register carry hlength, hlength]

theorem addConstant_cnotCount
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hlength : constants.length = register.length) :
    eeaCnotCount (addConstant register constants carry value) =
      4 * register.length := by
  simp [addConstant, eeaCnotCount_append,
    cuccaroAdd_cnotCount constants register carry hlength, hlength]

theorem addConstant_tCount
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hlength : constants.length = register.length) :
    ShorECDLP.tCount (addConstant register constants carry value) =
      14 * register.length := by
  simp [addConstant, tCount_append,
    cuccaroAdd_tCount constants register carry hlength, hlength]

theorem subConstant_toffoliCount
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hlength : constants.length = register.length) :
    eeaToffoliCount (subConstant register constants carry value) =
      2 * register.length := by
  simp [subConstant, eeaToffoliCount_append,
    cuccaroSub_toffoliCount constants register carry hlength, hlength]

theorem subConstant_cnotCount
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hlength : constants.length = register.length) :
    eeaCnotCount (subConstant register constants carry value) =
      4 * register.length := by
  simp [subConstant, eeaCnotCount_append,
    cuccaroSub_cnotCount constants register carry hlength, hlength]

theorem subConstant_tCount
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hlength : constants.length = register.length) :
    ShorECDLP.tCount (subConstant register constants carry value) =
      14 * register.length := by
  simp [subConstant, tCount_append,
    cuccaroSub_tCount constants register carry hlength, hlength]

/-! ## Two's-complement affine involution -/

/-- Bitwise complement in increasing register order. -/
def notRegister : List Wire → Circuit
  | [] => []
  | wire :: wires => .X wire :: notRegister wires

theorem notRegister_correct
    (register : List Wire) (state : BasisState)
    (hnd : register.Nodup) :
    let after := run (notRegister register) state
    wireValues register after = (wireValues register state).map Bool.not ∧
      ∀ wire, wire ∉ register → after wire = state wire := by
  induction register generalizing state with
  | nil => simp [notRegister, wireValues]
  | cons head tail ih =>
      have hhead := (List.nodup_cons.mp hnd).1
      have htail := (List.nodup_cons.mp hnd).2
      rw [notRegister, run_cons]
      let first := applyGate (.X head) state
      have hrecursive := ih first htail
      constructor
      · have hheadValue :
            run (notRegister tail) first head = !(state head) := by
          rw [hrecursive.2 head hhead]
          simp [first, applyGate]
        have htailValues := hrecursive.1
        have hfirstTail : wireValues tail first = wireValues tail state := by
          apply wireValues_congr_on
          intro wire hwire
          have hw : wire ≠ head := by
            intro equality
            exact hhead (by simpa [equality] using hwire)
          simp [first, applyGate, upd, hw]
        rw [hfirstTail] at htailValues
        simpa only [wireValues, List.map_cons] using
          congrArg₂ List.cons hheadValue htailValues
      · intro wire hwire
        simp only [List.mem_cons, not_or] at hwire
        change run (notRegister tail) first wire = state wire
        rw [hrecursive.2 wire hwire.2]
        simp [first, applyGate, upd, hwire.1]

@[simp]
theorem notRegister_HPFree (register : List Wire) :
    HPFree (notRegister register) := by
  induction register with
  | nil => simp [notRegister]
  | cons head tail ih => simp [notRegister, ih]

theorem notRegister_wellFormed (register : List Wire) :
    CircuitWellFormed (notRegister register) := by
  induction register with
  | nil => simp [notRegister]
  | cons head tail ih =>
      rw [notRegister, circuitWellFormed_cons]
      exact ⟨by simp [Gate.WellFormed], ih⟩

theorem notRegister_usesOnly (register : List Wire) :
    PaperCircuitUsesOnly register (notRegister register) := by
  induction register with
  | nil => simp [notRegister, PaperCircuitUsesOnly]
  | cons head tail ih =>
      intro gate hgate
      simp only [notRegister, List.mem_cons] at hgate
      rcases hgate with rfl | hgate
      · simp [PaperGateUsesOnly, gateWires]
      · intro wire hwire
        exact List.mem_cons_of_mem head (ih gate hgate wire hwire)

@[simp]
theorem notRegister_toffoliCount (register : List Wire) :
    eeaToffoliCount (notRegister register) = 0 := by
  induction register with
  | nil => rfl
  | cons head tail ih =>
      rw [notRegister]
      change 0 + eeaToffoliCount (notRegister tail) = 0
      simp [ih]

@[simp]
theorem notRegister_cnotCount (register : List Wire) :
    eeaCnotCount (notRegister register) = 0 := by
  induction register with
  | nil => rfl
  | cons head tail ih =>
      rw [notRegister]
      change 0 + eeaCnotCount (notRegister tail) = 0
      simp [ih]

@[simp]
theorem notRegister_tCount (register : List Wire) :
    ShorECDLP.tCount (notRegister register) = 0 := by
  induction register with
  | nil => rfl
  | cons head tail ih =>
      rw [notRegister]
      change 0 + ShorECDLP.tCount (notRegister tail) = 0
      simp [ih]

/-- Gate-independent bit-word meaning of `const - register` modulo the register width. -/
def constMinusBits (bits : List Bool) (value : Nat) : List Bool :=
  cuccaroAddBits false (constantBits bits.length value)
    (incrementBits true (bits.map Bool.not))

/-- Exact source stream `(~x) + 1 + const`, reusing the first `n-1` constant-load wires for
the increment chain. -/
def constMinus
    (register constants : List Wire) (carry : Wire) (value : Nat) : Circuit :=
  notRegister register ++
    uncontrolledIncrement register
      (constants.take (register.length - 1)) ++
    addConstant register constants carry value

/-- Direct word semantics and complete clean-scratch restoration of the source affine map. -/
theorem constMinus_correct
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (state : BasisState)
    (hpositive : 0 < register.length)
    (hlength : constants.length = register.length)
    (hlayout : ConstantLayout register constants carry)
    (hclean : Clean (constants ++ [carry]) state) :
    let after := run (constMinus register constants carry value) state
    wireValues register after =
        constMinusBits (wireValues register state) value ∧
      Clean (constants ++ [carry]) after ∧
      ∀ wire, wire ∉ register → after wire = state wire := by
  obtain ⟨hconstants, hregister, _, _, hcross⟩ :=
    constantLayout_parts register constants carry hlayout
  let complemented := run (notRegister register) state
  have hnot := notRegister_correct register state hregister
  have hcomplementedClean : Clean (constants ++ [carry]) complemented := by
    intro wire hwire
    dsimp only [complemented]
    rw [hnot.2 wire]
    · exact hclean wire hwire
    · intro hmem
      rcases List.mem_append.mp hwire with hconstant | hcarry
      · exact hcross wire hconstant hmem
      · simp only [List.mem_singleton] at hcarry
        subst wire
        exact (constantLayout_parts register constants carry hlayout).2.2.2.1 hmem
  have htakeLength :
      register.length =
        (constants.take (register.length - 1)).length + 1 := by
    rw [List.length_take, hlength]
    omega
  have htakeNodup :
      (register ++ constants.take (register.length - 1)).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨hregister, hconstants.take, by
      intro left hleft right hright equality
      apply hcross right (List.mem_of_mem_take hright)
      simpa [equality] using hleft⟩
  have htakeClean :
      Clean (constants.take (register.length - 1)) complemented := by
    intro wire hwire
    exact hcomplementedClean wire (by
      simp [List.mem_of_mem_take hwire])
  let incremented := run
    (uncontrolledIncrement register
      (constants.take (register.length - 1))) complemented
  have hinc := uncontrolledIncrement_correct register
    (constants.take (register.length - 1)) complemented
    htakeLength htakeNodup htakeClean
  have hincrementedValues :
      wireValues register incremented =
        incrementBits true ((wireValues register state).map Bool.not) := by
    rw [show wireValues register incremented =
        incrementBits true (wireValues register complemented) by
          simpa only [incremented] using hinc.1,
      hnot.1]
  have hincrementedClean : Clean (constants ++ [carry]) incremented := by
    intro wire hwire
    rw [show incremented wire = complemented wire by
      exact hinc.2 wire (by
        intro hmem
        rcases List.mem_append.mp hwire with hconstant | hcarry
        · exact hcross wire hconstant hmem
        · simp only [List.mem_singleton] at hcarry
          subst wire
          exact (constantLayout_parts register constants carry hlayout).2.2.2.1 hmem)]
    exact hcomplementedClean wire hwire
  let after := run (addConstant register constants carry value) incremented
  have hadd := addConstant_correct register constants carry value incremented
    hlength hlayout hincrementedClean
  rw [constMinus, run_append, run_append]
  change
    wireValues register after =
        constMinusBits (wireValues register state) value ∧
      Clean (constants ++ [carry]) after ∧
      ∀ wire, wire ∉ register → after wire = state wire
  constructor
  · rw [show wireValues register after =
        cuccaroAddBits false (constantBits constants.length value)
          (wireValues register incremented) by
        simpa only [after] using hadd.1,
      hincrementedValues, hlength]
    simp [constMinusBits, wireValues]
  · constructor
    · exact hadd.2.1
    · intro wire hwire
      rw [show after wire = incremented wire by
          exact hadd.2.2 wire hwire,
        show incremented wire = complemented wire by
          exact hinc.2 wire hwire,
        show complemented wire = state wire by
          exact hnot.2 wire hwire]

@[simp]
theorem constMinus_HPFree
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    HPFree (constMinus register constants carry value) := by
  simp [constMinus]

/-- Complete named support of the source `const - register` block. -/
theorem constMinus_usesOnly
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    PaperCircuitUsesOnly (constants ++ register ++ [carry])
      (constMinus register constants carry value) := by
  rw [constMinus]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply (notRegister_usesOnly register).mono
      intro wire hwire
      simp [hwire]
    · apply (uncontrolledIncrement_usesOnly register
          (constants.take (register.length - 1))).mono
      intro wire hwire
      rcases List.mem_append.mp hwire with hwire | hwire
      · simp [hwire]
      · simp [List.mem_of_mem_take hwire]
  · exact addConstant_usesOnly register constants carry value

theorem constMinus_wellFormed
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hlength : constants.length = register.length)
    (hlayout : ConstantLayout register constants carry) :
    CircuitWellFormed (constMinus register constants carry value) := by
  obtain ⟨hconstants, hregister, _, _, hcross⟩ :=
    constantLayout_parts register constants carry hlayout
  have htakeNodup :
      (register ++ constants.take (register.length - 1)).Nodup := by
    exact List.nodup_append.mpr ⟨hregister, hconstants.take, by
      intro left hleft right hright equality
      apply hcross right (List.mem_of_mem_take hright)
      simpa [equality] using hleft⟩
  simp only [constMinus, circuitWellFormed_append]
  exact ⟨⟨notRegister_wellFormed register,
      uncontrolledIncrement_wellFormed _ _ htakeNodup⟩,
    addConstant_wellFormed register constants carry value hlength hlayout⟩

/-- Constructor-derived exact coherent counts of the source affine map. -/
theorem constMinus_toffoliCount
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hpositive : 0 < register.length)
    (hlength : constants.length = register.length) :
    eeaToffoliCount (constMinus register constants carry value) =
      2 * (register.length - 2) + 2 * register.length := by
  have htakeLength : register.length =
      (constants.take (register.length - 1)).length + 1 := by
    rw [List.length_take, hlength]
    omega
  simp [constMinus, eeaToffoliCount_append,
    uncontrolledIncrement_toffoliCount _ _ htakeLength,
    addConstant_toffoliCount register constants carry value hlength]

theorem constMinus_cnotCount
    (low next : Wire) (rest constants : List Wire)
    (carry : Wire) (value : Nat)
    (hlength : constants.length = (low :: next :: rest).length) :
    eeaCnotCount
        (constMinus (low :: next :: rest) constants carry value) =
      (low :: next :: rest).length + 1 +
        4 * (low :: next :: rest).length := by
  have htakeLength : (low :: next :: rest).length =
      (constants.take ((low :: next :: rest).length - 1)).length + 1 := by
    rw [List.length_take, hlength,
      Nat.min_eq_left (Nat.sub_le _ _)]
    simp only [List.length_cons]
    omega
  rw [constMinus, eeaCnotCount_append, eeaCnotCount_append,
    uncontrolledIncrement_cnotCount low next rest _ htakeLength,
    addConstant_cnotCount (low :: next :: rest) constants carry value hlength]
  simp

theorem constMinus_tCount
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hpositive : 0 < register.length)
    (hlength : constants.length = register.length) :
    ShorECDLP.tCount (constMinus register constants carry value) =
      14 * (register.length - 2) + 14 * register.length := by
  have htakeLength : register.length =
      (constants.take (register.length - 1)).length + 1 := by
    rw [List.length_take, hlength]
    omega
  simp [constMinus, tCount_append,
    uncontrolledIncrement_tCount _ _ htakeLength,
    addConstant_tCount register constants carry value hlength]

end ShorECDLP.Paper2607_13816
