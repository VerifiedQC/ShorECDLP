import ShorECDLP.Submission.«2607_13816».EEA.WordNat
import Mathlib.Data.Nat.ModEq

/-!
# Phase-dependent coefficient boundary

This module implements the pinned supplement's
`_prepare_latest_paper_t_boundary` / `_restore_latest_paper_t_boundary` pair.  The stored
truth-minus-one coefficient length is shifted to the absolute endpoint `ell_t + 1`; the right
length is reflected and reduced to `n + 3 - ell_r' - ell_s`; and Phase 4 selects the latter word
with a bitwise controlled swap.  The restore block follows the generator's explicit source order,
rather than replacing it by an opaque adjoint.

The coefficient-prefix arithmetic itself is proved in `CoefficientPrefix.lean`.  Its explicit
inverse and the surrounding indexed four-phase step remain separate composition boundaries.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

noncomputable section

/-- Physical registers used by the latest-paper coefficient-boundary pair.  Only the low
`lengthT.length` bits of `lengthS` and the first `lengthT.length + 1` scratch wires are touched,
exactly as in the pinned Python helpers. -/
structure TBoundaryRegisters where
  phase2 : Wire
  lengthT : List Wire
  lengthRP : List Wire
  lengthS : List Wire
  scratch : List Wire
deriving Repr

def TBoundaryRegisters.width (registers : TBoundaryRegisters) : Nat :=
  registers.lengthT.length

def TBoundaryRegisters.lengthSLow
    (registers : TBoundaryRegisters) : List Wire :=
  registers.lengthS.take registers.width

def TBoundaryRegisters.constants
    (registers : TBoundaryRegisters) : List Wire :=
  registers.scratch.take registers.width

def TBoundaryRegisters.carry (registers : TBoundaryRegisters) : Wire :=
  registers.scratch.getD registers.width 0

def TBoundaryRegisters.usedScratch
    (registers : TBoundaryRegisters) : List Wire :=
  registers.constants ++ [registers.carry]

/-- Exact physical footprint of the two source helpers; surplus high `lengthS` and scratch wires
are intentionally excluded because the Python implementation never touches them. -/
def TBoundaryRegisters.allWires
    (registers : TBoundaryRegisters) : List Wire :=
  [registers.phase2, registers.carry] ++ registers.constants ++
    registers.lengthSLow ++ registers.lengthT ++ registers.lengthRP

/-- Source-domain width, capacity, and physical-separation obligations. -/
structure TBoundaryLayout (registers : TBoundaryRegisters) : Prop where
  positive : 0 < registers.width
  lengthRP_length : registers.lengthRP.length = registers.width
  lengthS_capacity : registers.width ≤ registers.lengthS.length
  scratch_capacity : registers.width < registers.scratch.length
  physical : registers.allWires.Nodup

/-- The source pair borrows only the constant word and carry wire, and returns both clean. -/
def TBoundaryReady
    (registers : TBoundaryRegisters) (state : BasisState) : Prop :=
  Clean registers.usedScratch state

/-! ## Literal source circuits -/

/-- Bitwise version of the source's `for a,b in zip(...): cswap_toffoli(...)`. -/
private def controlledSwapWords (control : Wire) : List Wire → List Wire → Circuit
  | left :: lefts, right :: rights =>
      controlledSwap control left right ++
        controlledSwapWords control lefts rights
  | _, _ => []

private theorem controlledSwapWords_usesOnly
    (control : Wire) : ∀ (left right : List Wire),
    PaperCircuitUsesOnly (control :: left ++ right)
      (controlledSwapWords control left right) := by
  intro left
  induction left with
  | nil => intro right; simp [controlledSwapWords, PaperCircuitUsesOnly]
  | cons left lefts ih =>
      intro right
      cases right with
      | nil => simp [controlledSwapWords, PaperCircuitUsesOnly]
      | cons right rights =>
          rw [controlledSwapWords]
          apply PaperCircuitUsesOnly.append
          · apply (controlledSwap_usesOnly control left right).mono
            intro wire hwire
            simp only [List.mem_cons, List.mem_append] at hwire ⊢
            rcases hwire with rfl | rfl | (rfl | hfalse)
            · simp
            · simp
            · simp
            · contradiction
          · apply (ih rights).mono
            intro wire hwire
            simp only [List.mem_cons, List.mem_append] at hwire ⊢
            rcases hwire with (rfl | hwire) | hwire
            · simp
            · exact Or.inl (Or.inr (Or.inr hwire))
            · exact Or.inr (Or.inr hwire)

@[simp]
private theorem controlledSwapWords_HPFree
    (control : Wire) : ∀ (left right : List Wire),
    HPFree (controlledSwapWords control left right) := by
  intro left
  induction left with
  | nil => intro right; simp [controlledSwapWords]
  | cons left lefts ih =>
      intro right
      cases right with
      | nil => simp [controlledSwapWords]
      | cons right rights => simp [controlledSwapWords, ih]

private theorem controlledSwapWords_wellFormed
    (control : Wire) : ∀ (left right : List Wire),
    left.length = right.length →
    (control :: left ++ right).Nodup →
    CircuitWellFormed (controlledSwapWords control left right) := by
  intro left
  induction left with
  | nil =>
      intro right hlength
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      simp [controlledSwapWords]
  | cons left lefts ih =>
      intro right hlength hnd
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htailLength : lefts.length = rights.length := by simpa using hlength
          have hcontrol : control ∉ left :: lefts ++ right :: rights :=
            (List.nodup_cons.mp hnd).1
          have hrest : (left :: lefts ++ right :: rights).Nodup :=
            (List.nodup_cons.mp hnd).2
          have hleft : left ∉ lefts ++ right :: rights :=
            (List.nodup_cons.mp hrest).1
          have htailNodup : (control :: lefts ++ rights).Nodup :=
            hnd.sublist
              (List.Sublist.cons₂ control
                (List.Sublist.cons left
                  ((List.Sublist.refl lefts).append
                    (List.Sublist.cons right (List.Sublist.refl rights)))))
          have hcl : control ≠ left := by
            intro h; subst left; exact hcontrol (by simp)
          have hcr : control ≠ right := by
            intro h; subst right; exact hcontrol (by simp)
          have hlr : left ≠ right := by
            intro h; subst right; exact hleft (by simp)
          rw [controlledSwapWords, circuitWellFormed_append]
          exact ⟨controlledSwap_wellFormed control left right hcl hcr hlr,
            ih rights htailLength htailNodup⟩

private theorem controlledSwapWords_toffoliCount
    (control : Wire) : ∀ (left right : List Wire),
    left.length = right.length →
    eeaToffoliCount (controlledSwapWords control left right) = left.length := by
  intro left
  induction left with
  | nil =>
      intro right hlength
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons left lefts ih =>
      intro right hlength
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          rw [controlledSwapWords, eeaToffoliCount_append,
            controlledSwap_toffoliCount, ih rights (by simpa using hlength)]
          simp
          omega

private theorem controlledSwapWords_cnotCount
    (control : Wire) : ∀ (left right : List Wire),
    left.length = right.length →
    eeaCnotCount (controlledSwapWords control left right) = 2 * left.length := by
  intro left
  induction left with
  | nil =>
      intro right hlength
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons left lefts ih =>
      intro right hlength
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          rw [controlledSwapWords, eeaCnotCount_append,
            controlledSwap_cnotCount, ih rights (by simpa using hlength)]
          simp
          omega

@[simp]
private theorem controlledSwapWords_xCount
    (control : Wire) : ∀ (left right : List Wire),
    eeaXCount (controlledSwapWords control left right) = 0 := by
  intro left
  induction left with
  | nil => intro right; rfl
  | cons left lefts ih =>
      intro right
      cases right with
      | nil => rfl
      | cons right rights =>
          rw [controlledSwapWords, eeaXCount_append,
            controlledSwap_xCount, ih rights]

private theorem controlledSwapWords_tCount
    (control : Wire) : ∀ (left right : List Wire),
    left.length = right.length →
    tCount (controlledSwapWords control left right) = 7 * left.length := by
  intro left
  induction left with
  | nil =>
      intro right hlength
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons left lefts ih =>
      intro right hlength
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          rw [controlledSwapWords, tCount_append,
            controlledSwap_tCount, ih rights (by simpa using hlength)]
          simp
          omega

private theorem wireValues_congr_local
    (wires : List Wire) (left right : BasisState)
    (hagree : ∀ wire, wire ∈ wires → left wire = right wire) :
    wireValues wires left = wireValues wires right := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq]
      exact ⟨hagree wire (by simp), ih (fun next hnext ↦
        hagree next (by simp [hnext]))⟩

private theorem wireValues_eq_at_local
    (wires : List Wire) (left right : BasisState)
    (hvalues : wireValues wires left = wireValues wires right)
    {wire : Wire} (hwire : wire ∈ wires) : left wire = right wire := by
  induction wires with
  | nil => simp at hwire
  | cons head tail ih =>
      simp only [List.mem_cons] at hwire
      simp only [wireValues, List.map_cons, List.cons.injEq] at hvalues
      rcases hwire with rfl | hwire
      · exact hvalues.1
      · exact ih hvalues.2 hwire

/-- Exact pointwise action of the source's bitwise Fredkin loop. -/
private theorem controlledSwapWords_correct
    (control : Wire) : ∀ (left right : List Wire) (state : BasisState),
    left.length = right.length →
    (control :: left ++ right).Nodup →
    let after := run (controlledSwapWords control left right) state
    wireValues left after =
        (if state control then wireValues right state else wireValues left state) ∧
      wireValues right after =
        (if state control then wireValues left state else wireValues right state) := by
  intro left
  induction left with
  | nil =>
      intro right state hlength
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      simp [controlledSwapWords, wireValues]
  | cons left lefts ih =>
      intro right state hlength hnd
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htailLength : lefts.length = rights.length := by simpa using hlength
          simp only [List.cons_append, List.nodup_cons, List.mem_append,
            List.mem_cons, not_or] at hnd
          have htailParts := List.nodup_append.mp hnd.2.2
          have hright : right ∉ rights :=
            (List.nodup_cons.mp htailParts.2.1).1
          have hrightLefts : right ∉ lefts := by
            intro hmem
            exact htailParts.2.2 right hmem right List.mem_cons_self rfl
          have htailNodup : (control :: lefts ++ rights).Nodup := by
            apply List.nodup_cons.mpr
            refine ⟨?_, List.nodup_append.mpr ⟨htailParts.1,
              (List.nodup_cons.mp htailParts.2.1).2, ?_⟩⟩
            · intro hmem
              rcases List.mem_append.mp hmem with hmem | hmem
              · exact hnd.1.2.1 hmem
              · exact hnd.1.2.2.2 hmem
            · intro a ha b hb hab
              subst b
              exact htailParts.2.2 a ha a (List.mem_cons_of_mem right hb) rfl
          let firstState := run (controlledSwap control left right) state
          have hswap := run_controlledSwap control left right state
            hnd.1.1 hnd.1.2.2.1 hnd.2.1.2.1
          have hcontrolFirst : firstState control = state control := by
            dsimp only [firstState]
            rw [hswap]
            split <;> simp [upd, hnd.1.1, hnd.1.2.2.1]
          have hleftsFirst :
              wireValues lefts firstState = wireValues lefts state := by
            apply wireValues_congr_local
            intro wire hwire
            dsimp only [firstState]
            apply (controlledSwap_usesOnly control left right).preservesOutside
            intro hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with h | h | (h | hfalse)
            · subst wire; exact hnd.1.2.1 hwire
            · subst wire; exact hnd.2.1.1 hwire
            · subst wire; exact hrightLefts hwire
            · contradiction
          have hrightsFirst :
              wireValues rights firstState = wireValues rights state := by
            apply wireValues_congr_local
            intro wire hwire
            dsimp only [firstState]
            apply (controlledSwap_usesOnly control left right).preservesOutside
            intro hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with h | h | (h | hfalse)
            · subst wire; exact hnd.1.2.2.2 hwire
            · subst wire; exact hnd.2.1.2.2 hwire
            · subst wire; exact hright hwire
            · contradiction
          have hrecursive := ih rights firstState htailLength htailNodup
          have hleftFinal :
              run (controlledSwapWords control lefts rights) firstState left =
                firstState left := by
            apply (controlledSwapWords_usesOnly control lefts rights).preservesOutside
            intro hmem
            simp only [List.mem_cons, List.mem_append] at hmem
            rcases hmem with (h | hmem) | hmem
            · exact hnd.1.1 h.symm
            · exact hnd.2.1.1 hmem
            · exact hnd.2.1.2.2 hmem
          have hrightFinal :
              run (controlledSwapWords control lefts rights) firstState right =
                firstState right := by
            apply (controlledSwapWords_usesOnly control lefts rights).preservesOutside
            intro hmem
            simp only [List.mem_cons, List.mem_append] at hmem
            rcases hmem with (h | hmem) | hmem
            · exact hnd.1.2.2.1 h.symm
            · exact hrightLefts hmem
            · exact hright hmem
          rw [controlledSwapWords, run_append]
          change
            (run (controlledSwapWords control lefts rights) firstState left ::
                wireValues lefts
                  (run (controlledSwapWords control lefts rights) firstState) =
              if state control then
                state right :: wireValues rights state
              else state left :: wireValues lefts state) ∧
            (run (controlledSwapWords control lefts rights) firstState right ::
                wireValues rights
                  (run (controlledSwapWords control lefts rights) firstState) =
              if state control then
                state left :: wireValues lefts state
              else state right :: wireValues rights state)
          rw [hleftFinal, hrightFinal, hrecursive.1, hrecursive.2,
            hcontrolFirst, hleftsFirst, hrightsFirst]
          dsimp only [firstState]
          rw [hswap]
          cases hc : state control <;>
            simp [upd, hnd.2.1.2.1]

private theorem controlledSwapWords_control
    (control : Wire) : ∀ (left right : List Wire) (state : BasisState),
    control ∉ left → control ∉ right →
    run (controlledSwapWords control left right) state control = state control := by
  intro left
  induction left with
  | nil => intro right state _ _; simp [controlledSwapWords]
  | cons left lefts ih =>
      intro right state hleft hright
      cases right with
      | nil => simp [controlledSwapWords]
      | cons right rights =>
          simp only [List.mem_cons, not_or] at hleft hright
          rw [controlledSwapWords, run_append,
            ih rights _ hleft.2 hright.2]
          simp [controlledSwap, run, applyGate, upd, hleft.1, hright.1]

private theorem controlledSwapWords_preservesOutsideWords
    (control : Wire) (left right : List Wire) (state : BasisState)
    (hcontrolLeft : control ∉ left) (hcontrolRight : control ∉ right) :
    ∀ wire, wire ∉ left → wire ∉ right →
      run (controlledSwapWords control left right) state wire = state wire := by
  intro wire hleft hright
  by_cases hwire : wire = control
  · subst wire
    exact controlledSwapWords_control control left right state
      hcontrolLeft hcontrolRight
  · apply (controlledSwapWords_usesOnly control left right).preservesOutside
    simp only [List.mem_cons, List.mem_append, not_or]
    exact ⟨⟨hwire, hleft⟩, hright⟩

/-- Literal `_prepare_latest_paper_t_boundary`: add two to the stored `ell_t-1`, reflect the
right length, subtract the low shift word, then select that right endpoint in Phase 4. -/
def prepareLatestPaperTBoundary
    (registers : TBoundaryRegisters) (n : Nat) : Circuit :=
  addConstant registers.lengthT registers.constants registers.carry 2 ++
    constMinus registers.lengthRP registers.constants registers.carry (n + 1) ++
    cuccaroSub registers.lengthSLow registers.lengthRP registers.carry ++
    controlledSwapWords registers.phase2 registers.lengthT registers.lengthRP

/-- Literal `_restore_latest_paper_t_boundary`: undo the Phase-4 selection, repeat the source
reflection/subtraction identity on the right word, then subtract two from the left word. -/
def restoreLatestPaperTBoundary
    (registers : TBoundaryRegisters) (n : Nat) : Circuit :=
  controlledSwapWords registers.phase2 registers.lengthT registers.lengthRP ++
    constMinus registers.lengthRP registers.constants registers.carry (n + 1) ++
    cuccaroSub registers.lengthSLow registers.lengthRP registers.carry ++
    subConstant registers.lengthT registers.constants registers.carry 2

/-! ## Physical and structural contract -/

private theorem TBoundaryLayout.constants_length
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    registers.constants.length = registers.width := by
  simp only [TBoundaryRegisters.constants, List.length_take]
  rw [Nat.min_eq_left (Nat.le_of_lt layout.scratch_capacity)]

private theorem TBoundaryLayout.lengthSLow_length
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    registers.lengthSLow.length = registers.width := by
  simp only [TBoundaryRegisters.lengthSLow, List.length_take]
  rw [Nat.min_eq_left layout.lengthS_capacity]

private theorem TBoundaryLayout.constantT
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    ConstantLayout registers.lengthT registers.constants registers.carry := by
  apply List.Nodup.sublist ?_ layout.physical
  unfold TBoundaryRegisters.allWires
  simpa only [List.nil_append, List.cons_append, List.append_assoc] using
    List.Sublist.cons registers.phase2
      (List.Sublist.cons₂ registers.carry
        ((List.Sublist.refl registers.constants).append
          ((List.sublist_append_left registers.lengthT registers.lengthRP).trans
            (List.sublist_append_right registers.lengthSLow
              (registers.lengthT ++ registers.lengthRP)))))

private theorem TBoundaryLayout.constantRP
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    ConstantLayout registers.lengthRP registers.constants registers.carry := by
  apply List.Nodup.sublist ?_ layout.physical
  unfold TBoundaryRegisters.allWires
  simpa only [List.nil_append, List.cons_append, List.append_assoc] using
    List.Sublist.cons registers.phase2
      (List.Sublist.cons₂ registers.carry
        ((List.Sublist.refl registers.constants).append
          (List.sublist_append_right
            (registers.lengthSLow ++ registers.lengthT) registers.lengthRP)))

private theorem TBoundaryLayout.subtractRP
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    (registers.carry :: registers.lengthSLow ++ registers.lengthRP).Nodup := by
  apply List.Nodup.sublist ?_ layout.physical
  unfold TBoundaryRegisters.allWires
  have htail : (registers.lengthSLow ++ registers.lengthRP).Sublist
      (registers.constants ++ registers.lengthSLow ++ registers.lengthT ++
        registers.lengthRP) := by
    simpa only [List.append_assoc] using
      (((List.Sublist.refl registers.lengthSLow).append
        (List.sublist_append_right registers.lengthT registers.lengthRP)).trans
          (List.sublist_append_right registers.constants
            (registers.lengthSLow ++ (registers.lengthT ++ registers.lengthRP))))
  simpa only [List.nil_append, List.cons_append, List.append_assoc] using
    List.Sublist.cons registers.phase2
      (List.Sublist.cons₂ registers.carry htail)

private theorem TBoundaryLayout.swap
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    (registers.phase2 :: registers.lengthT ++ registers.lengthRP).Nodup := by
  apply List.Nodup.sublist ?_ layout.physical
  unfold TBoundaryRegisters.allWires
  simpa only [List.nil_append, List.cons_append, List.append_assoc] using
    List.Sublist.cons₂ registers.phase2
      (List.Sublist.cons registers.carry
        (List.sublist_append_right
          (registers.constants ++ registers.lengthSLow)
          (registers.lengthT ++ registers.lengthRP)))

private theorem TBoundaryLayout.dataWords
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    (registers.lengthSLow ++ registers.lengthT ++ registers.lengthRP).Nodup := by
  apply List.Nodup.sublist ?_ layout.physical
  unfold TBoundaryRegisters.allWires
  simpa only [List.nil_append, List.cons_append, List.append_assoc] using
    List.Sublist.cons registers.phase2
      (List.Sublist.cons registers.carry
        (List.sublist_append_right registers.constants
          (registers.lengthSLow ++ registers.lengthT ++ registers.lengthRP)))

private theorem TBoundaryLayout.phase_outside_words
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    registers.phase2 ∉ registers.lengthT ∧
      registers.phase2 ∉ registers.lengthRP := by
  have hphase := (List.nodup_cons.mp layout.swap).1
  exact ⟨fun ht ↦ hphase (List.mem_append_left registers.lengthRP ht),
    fun hrp ↦ hphase (List.mem_append_right registers.lengthT hrp)⟩

private theorem TBoundaryLayout.t_outside_rp
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    ∀ wire, wire ∈ registers.lengthT → wire ∉ registers.lengthRP := by
  have hparts := List.nodup_append.mp (List.nodup_cons.mp layout.swap).2
  intro wire ht hrp
  exact hparts.2.2 wire ht wire hrp rfl

private theorem TBoundaryLayout.rp_outside_t
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    ∀ wire, wire ∈ registers.lengthRP → wire ∉ registers.lengthT := by
  intro wire hrp ht
  exact layout.t_outside_rp wire ht hrp

private theorem TBoundaryLayout.s_outside_words
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    ∀ wire, wire ∈ registers.lengthSLow →
      wire ∉ registers.lengthT ∧ wire ∉ registers.lengthRP := by
  have hst : (registers.lengthSLow ++ registers.lengthT).Nodup :=
    List.Nodup.sublist
      (List.sublist_append_left
        (registers.lengthSLow ++ registers.lengthT) registers.lengthRP)
      layout.dataWords
  have hsr : (registers.lengthSLow ++ registers.lengthRP).Nodup := by
    apply List.Nodup.sublist ?_ layout.dataWords
    simpa only [List.append_assoc] using
      (List.Sublist.refl registers.lengthSLow).append
        (List.sublist_append_right registers.lengthT registers.lengthRP)
  have hstParts := List.nodup_append.mp hst
  have hsrParts := List.nodup_append.mp hsr
  intro wire hs
  exact ⟨fun ht ↦ hstParts.2.2 wire hs wire ht rfl,
    fun hrp ↦ hsrParts.2.2 wire hs wire hrp rfl⟩

private theorem TBoundaryLayout.scratch_outside_words
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    ∀ wire, wire ∈ registers.usedScratch →
      wire ∉ registers.lengthT ∧ wire ∉ registers.lengthRP := by
  intro wire hwire
  rcases List.mem_append.mp hwire with hconstant | hcarry
  · have ht := List.nodup_append.mp
        (List.nodup_cons.mp layout.constantT).2
    have hr := List.nodup_append.mp
        (List.nodup_cons.mp layout.constantRP).2
    exact ⟨fun h ↦ ht.2.2 wire hconstant wire h rfl,
      fun h ↦ hr.2.2 wire hconstant wire h rfl⟩
  · simp only [List.mem_singleton] at hcarry
    subst wire
    have ht := (List.nodup_cons.mp layout.constantT).1
    have hr := (List.nodup_cons.mp layout.constantRP).1
    exact ⟨fun h ↦ ht (List.mem_append_right registers.constants h),
      fun h ↦ hr (List.mem_append_right registers.constants h)⟩

private theorem TBoundaryRegisters.mem_allWires_constants
    {registers : TBoundaryRegisters} {wire : Wire}
    (hwire : wire ∈ registers.constants) :
    wire ∈ registers.allWires := by
  simp [TBoundaryRegisters.allWires, hwire]

private theorem TBoundaryRegisters.mem_allWires_carry
    (registers : TBoundaryRegisters) : registers.carry ∈ registers.allWires := by
  simp [TBoundaryRegisters.allWires]

private theorem TBoundaryRegisters.mem_allWires_s
    {registers : TBoundaryRegisters} {wire : Wire}
    (hwire : wire ∈ registers.lengthSLow) :
    wire ∈ registers.allWires := by
  simp [TBoundaryRegisters.allWires, hwire]

private theorem TBoundaryRegisters.mem_allWires_t
    {registers : TBoundaryRegisters} {wire : Wire}
    (hwire : wire ∈ registers.lengthT) :
    wire ∈ registers.allWires := by
  simp [TBoundaryRegisters.allWires, hwire]

private theorem TBoundaryRegisters.mem_allWires_rp
    {registers : TBoundaryRegisters} {wire : Wire}
    (hwire : wire ∈ registers.lengthRP) :
    wire ∈ registers.allWires := by
  simp [TBoundaryRegisters.allWires, hwire]

private theorem TBoundaryRegisters.mem_allWires_phase
    (registers : TBoundaryRegisters) : registers.phase2 ∈ registers.allWires := by
  simp [TBoundaryRegisters.allWires]

/-- The prepare helper touches only the declared boundary footprint. -/
theorem prepareLatestPaperTBoundary_usesOnly
    (registers : TBoundaryRegisters) (n : Nat) :
    PaperCircuitUsesOnly registers.allWires
      (prepareLatestPaperTBoundary registers n) := by
  unfold prepareLatestPaperTBoundary
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply PaperCircuitUsesOnly.append
      · apply (addConstant_usesOnly registers.lengthT registers.constants
          registers.carry 2).mono
        intro wire hwire
        simp only [List.mem_append, List.mem_singleton] at hwire
        rcases hwire with (hconstant | ht) | hcarry
        · exact registers.mem_allWires_constants hconstant
        · exact registers.mem_allWires_t ht
        · exact hcarry ▸ registers.mem_allWires_carry
      · apply (constMinus_usesOnly registers.lengthRP registers.constants
          registers.carry (n + 1)).mono
        intro wire hwire
        simp only [List.mem_append, List.mem_singleton] at hwire
        rcases hwire with (hconstant | hrp) | hcarry
        · exact registers.mem_allWires_constants hconstant
        · exact registers.mem_allWires_rp hrp
        · exact hcarry ▸ registers.mem_allWires_carry
    · apply (cuccaroSub_usesOnly registers.lengthSLow registers.lengthRP
        registers.carry).mono
      intro wire hwire
      rcases List.mem_cons.mp hwire with hcarry | hwire
      · exact hcarry ▸ registers.mem_allWires_carry
      · rcases List.mem_append.mp hwire with hs | hrp
        · exact registers.mem_allWires_s hs
        · exact registers.mem_allWires_rp hrp
  · apply (controlledSwapWords_usesOnly registers.phase2 registers.lengthT
        registers.lengthRP).mono
    intro wire hwire
    rcases List.mem_cons.mp hwire with hphase | hwire
    · exact hphase ▸ registers.mem_allWires_phase
    · rcases List.mem_append.mp hwire with ht | hrp
      · exact registers.mem_allWires_t ht
      · exact registers.mem_allWires_rp hrp

/-- The explicit restore helper has the same declared physical support. -/
theorem restoreLatestPaperTBoundary_usesOnly
    (registers : TBoundaryRegisters) (n : Nat) :
    PaperCircuitUsesOnly registers.allWires
      (restoreLatestPaperTBoundary registers n) := by
  unfold restoreLatestPaperTBoundary
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply PaperCircuitUsesOnly.append
      · apply (controlledSwapWords_usesOnly registers.phase2 registers.lengthT
            registers.lengthRP).mono
        intro wire hwire
        rcases List.mem_cons.mp hwire with hphase | hwire
        · exact hphase ▸ registers.mem_allWires_phase
        · rcases List.mem_append.mp hwire with ht | hrp
          · exact registers.mem_allWires_t ht
          · exact registers.mem_allWires_rp hrp
      · apply (constMinus_usesOnly registers.lengthRP registers.constants
          registers.carry (n + 1)).mono
        intro wire hwire
        simp only [List.mem_append, List.mem_singleton] at hwire
        rcases hwire with (hconstant | hrp) | hcarry
        · exact registers.mem_allWires_constants hconstant
        · exact registers.mem_allWires_rp hrp
        · exact hcarry ▸ registers.mem_allWires_carry
    · apply (cuccaroSub_usesOnly registers.lengthSLow registers.lengthRP
        registers.carry).mono
      intro wire hwire
      rcases List.mem_cons.mp hwire with hcarry | hwire
      · exact hcarry ▸ registers.mem_allWires_carry
      · rcases List.mem_append.mp hwire with hs | hrp
        · exact registers.mem_allWires_s hs
        · exact registers.mem_allWires_rp hrp
  · apply (subConstant_usesOnly registers.lengthT registers.constants
        registers.carry 2).mono
    intro wire hwire
    simp only [List.mem_append, List.mem_singleton] at hwire
    rcases hwire with (hconstant | ht) | hcarry
    · exact registers.mem_allWires_constants hconstant
    · exact registers.mem_allWires_t ht
    · exact hcarry ▸ registers.mem_allWires_carry

@[simp]
theorem prepareLatestPaperTBoundary_HPFree
    (registers : TBoundaryRegisters) (n : Nat) :
    HPFree (prepareLatestPaperTBoundary registers n) := by
  simp [prepareLatestPaperTBoundary]

@[simp]
theorem restoreLatestPaperTBoundary_HPFree
    (registers : TBoundaryRegisters) (n : Nat) :
    HPFree (restoreLatestPaperTBoundary registers n) := by
  simp [restoreLatestPaperTBoundary]

theorem prepareLatestPaperTBoundary_wellFormed
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers) :
    CircuitWellFormed (prepareLatestPaperTBoundary registers n) := by
  simp only [prepareLatestPaperTBoundary, circuitWellFormed_append]
  exact ⟨⟨⟨
    addConstant_wellFormed registers.lengthT registers.constants registers.carry 2
      (layout.constants_length.trans rfl) layout.constantT,
    constMinus_wellFormed registers.lengthRP registers.constants registers.carry (n + 1)
      (layout.constants_length.trans layout.lengthRP_length.symm) layout.constantRP⟩,
    cuccaroSub_wellFormed registers.lengthSLow registers.lengthRP registers.carry
      (layout.lengthSLow_length.trans layout.lengthRP_length.symm) layout.subtractRP⟩,
    controlledSwapWords_wellFormed registers.phase2 registers.lengthT registers.lengthRP
      layout.lengthRP_length.symm layout.swap⟩

theorem restoreLatestPaperTBoundary_wellFormed
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers) :
    CircuitWellFormed (restoreLatestPaperTBoundary registers n) := by
  simp only [restoreLatestPaperTBoundary, circuitWellFormed_append]
  exact ⟨⟨⟨
    controlledSwapWords_wellFormed registers.phase2 registers.lengthT registers.lengthRP
      layout.lengthRP_length.symm layout.swap,
    constMinus_wellFormed registers.lengthRP registers.constants registers.carry (n + 1)
      (layout.constants_length.trans layout.lengthRP_length.symm) layout.constantRP⟩,
    cuccaroSub_wellFormed registers.lengthSLow registers.lengthRP registers.carry
      (layout.lengthSLow_length.trans layout.lengthRP_length.symm) layout.subtractRP⟩,
    subConstant_wellFormed registers.lengthT registers.constants registers.carry 2
      (layout.constants_length.trans rfl) layout.constantT⟩

/-! ## Gate-independent word semantics -/

/-- Pure little-endian recurrence of the prepared boundary pair. -/
def prepareLatestPaperTBoundaryWords
    (phase2 : Bool) (lengthT lengthRP lengthS : List Bool) (n : Nat) :
    List Bool × List Bool :=
  let preparedT := cuccaroAddBits false (constantBits lengthT.length 2) lengthT
  let preparedRP := cuccaroSubBits false lengthS (constMinusBits lengthRP (n + 1))
  if phase2 then (preparedRP, preparedT) else (preparedT, preparedRP)

/-- Pure little-endian recurrence of the explicit restore helper. -/
def restoreLatestPaperTBoundaryWords
    (phase2 : Bool) (lengthT lengthRP lengthS : List Bool) (n : Nat) :
    List Bool × List Bool :=
  let unswapped := if phase2 then (lengthRP, lengthT) else (lengthT, lengthRP)
  let restoredT :=
    cuccaroSubBits false (constantBits unswapped.1.length 2) unswapped.1
  let restoredRP :=
    cuccaroSubBits false lengthS (constMinusBits unswapped.2 (n + 1))
  (restoredT, restoredRP)

/-! ## Word-level reversibility -/

/-- Natural interpretation of the inverse Cuccaro recurrence at zero input carry. -/
private theorem boolWordToNat_cuccaroSubBits_false
    (addends sums : List Bool) (hlength : addends.length = sums.length) :
    boolWordToNat (cuccaroSubBits false addends sums) =
      (boolWordToNat sums + 2 ^ addends.length - boolWordToNat addends) %
        2 ^ addends.length := by
  let difference := cuccaroSubBits false addends sums
  have hdifferenceLength : difference.length = addends.length := by
    dsimp only [difference]
    exact cuccaroSubBits_length false addends sums hlength
  have hinverse := congrArg boolWordToNat
    (cuccaroAddBits_subBits false addends sums hlength)
  have haddLength : addends.length = difference.length := hdifferenceLength.symm
  rw [boolWordToNat_cuccaroAddBits false addends difference haddLength] at hinverse
  simp only [Bool.toNat_false, Nat.zero_add] at hinverse
  have haddendBound := boolWordToNat_lt_pow_two addends
  have hdifferenceBound := boolWordToNat_lt_pow_two difference
  rw [hdifferenceLength] at hdifferenceBound
  have hsumBound := boolWordToNat_lt_pow_two sums
  rw [← hlength] at hsumBound
  change boolWordToNat difference =
    (boolWordToNat sums + 2 ^ addends.length - boolWordToNat addends) %
      2 ^ addends.length
  by_cases hsmall :
      boolWordToNat addends + boolWordToNat difference < 2 ^ addends.length
  · rw [Nat.mod_eq_of_lt hsmall] at hinverse
    rw [← hinverse]
    have heq :
        boolWordToNat addends + boolWordToNat difference + 2 ^ addends.length -
            boolWordToNat addends =
          2 ^ addends.length + boolWordToNat difference := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt hdifferenceBound]
    exact (Nat.mod_eq_of_lt hdifferenceBound).symm
  · have hlarge : 2 ^ addends.length ≤
        boolWordToNat addends + boolWordToNat difference := by omega
    rw [Nat.mod_eq_sub_mod hlarge,
      Nat.mod_eq_of_lt (by omega)] at hinverse
    rw [← hinverse]
    have heq :
        (boolWordToNat addends + boolWordToNat difference - 2 ^ addends.length) +
            2 ^ addends.length - boolWordToNat addends =
          boolWordToNat difference := by omega
    rw [heq, Nat.mod_eq_of_lt hdifferenceBound]

private theorem modSub_add_modEq
    (modulus subtrahend minuend : Nat)
    (hsub : subtrahend ≤ minuend + modulus) :
    ((minuend + modulus - subtrahend) % modulus) + subtrahend ≡
      minuend [MOD modulus] := by
  calc
    ((minuend + modulus - subtrahend) % modulus) + subtrahend ≡
        (minuend + modulus - subtrahend) + subtrahend [MOD modulus] :=
      (Nat.mod_modEq _ _).add_right subtrahend
    _ = minuend + modulus := Nat.sub_add_cancel hsub
    _ ≡ minuend [MOD modulus] := by simp

/-- The right-endpoint map `r ↦ (n+1-r)-s` is an involution modulo the word width. -/
private theorem modularRightBoundary_involutive
    (modulus constant shift current : Nat)
    (hmodulus : 0 < modulus) (hshift : shift < modulus)
    (hcurrent : current < modulus) :
    let reflected := (constant + modulus - current) % modulus
    let shifted := (reflected + modulus - shift) % modulus
    let reflectedAgain := (constant + modulus - shifted) % modulus
    (reflectedAgain + modulus - shift) % modulus = current := by
  dsimp
  let reflected := (constant + modulus - current) % modulus
  let shifted := (reflected + modulus - shift) % modulus
  let reflectedAgain := (constant + modulus - shifted) % modulus
  let final := (reflectedAgain + modulus - shift) % modulus
  have hreflected : reflected < modulus := Nat.mod_lt _ hmodulus
  have hshifted : shifted < modulus := Nat.mod_lt _ hmodulus
  have hreflectedAgain : reflectedAgain < modulus := Nat.mod_lt _ hmodulus
  have hfinal : final < modulus := Nat.mod_lt _ hmodulus
  have hfinalShift : final + shift ≡ reflectedAgain [MOD modulus] := by
    exact modSub_add_modEq modulus shift reflectedAgain (by omega)
  have hreflectedShifted : reflectedAgain + shifted ≡ constant [MOD modulus] := by
    exact modSub_add_modEq modulus shifted constant (by omega)
  have hshiftedShift : shifted + shift ≡ reflected [MOD modulus] := by
    exact modSub_add_modEq modulus shift reflected (by omega)
  have hreflectedCurrent : reflected + current ≡ constant [MOD modulus] := by
    exact modSub_add_modEq modulus current constant (by omega)
  have hfinalShiftShifted : final + (shift + shifted) ≡ constant [MOD modulus] := by
    calc
      final + (shift + shifted) = (final + shift) + shifted := by omega
      _ ≡ reflectedAgain + shifted [MOD modulus] :=
        hfinalShift.add_right shifted
      _ ≡ constant [MOD modulus] := hreflectedShifted
  have hfinalReflected : final + reflected ≡ constant [MOD modulus] := by
    calc
      final + reflected ≡ final + (shifted + shift) [MOD modulus] :=
        (Nat.ModEq.refl final).add hshiftedShift.symm
      _ = final + (shift + shifted) := by omega
      _ ≡ constant [MOD modulus] := hfinalShiftShifted
  have hcancel : final + reflected ≡ current + reflected [MOD modulus] := by
    exact hfinalReflected.trans (by
      rw [Nat.add_comm current reflected]
      exact hreflectedCurrent.symm)
  have hmodeq : final ≡ current [MOD modulus] :=
    Nat.ModEq.add_right_cancel' reflected hcancel
  exact hmodeq.eq_of_lt_of_lt hfinal hcurrent

private def rightBoundaryWords
    (lengthS lengthRP : List Bool) (n : Nat) : List Bool :=
  cuccaroSubBits false lengthS (constMinusBits lengthRP (n + 1))

private theorem boolWordToNat_rightBoundaryWords
    (lengthS lengthRP : List Bool) (n : Nat)
    (hlength : lengthS.length = lengthRP.length) :
    boolWordToNat (rightBoundaryWords lengthS lengthRP n) =
      (((n + 1) + 2 ^ lengthS.length - boolWordToNat lengthRP) %
          2 ^ lengthS.length + 2 ^ lengthS.length - boolWordToNat lengthS) %
        2 ^ lengthS.length := by
  unfold rightBoundaryWords
  rw [boolWordToNat_cuccaroSubBits_false]
  · rw [boolWordToNat_constMinusBits]
    simp [hlength]
  · rw [constMinusBits_length]
    exact hlength

@[simp]
private theorem rightBoundaryWords_length
    (lengthS lengthRP : List Bool) (n : Nat)
    (hlength : lengthS.length = lengthRP.length) :
    (rightBoundaryWords lengthS lengthRP n).length = lengthRP.length := by
  unfold rightBoundaryWords
  rw [cuccaroSubBits_length]
  · exact hlength
  · simpa using hlength

@[simp]
private theorem rightBoundaryWords_involutive
    (lengthS lengthRP : List Bool) (n : Nat)
    (hlength : lengthS.length = lengthRP.length) :
    rightBoundaryWords lengthS (rightBoundaryWords lengthS lengthRP n) n =
      lengthRP := by
  apply boolWordToNat_injective_of_length
  · simp [rightBoundaryWords_length, hlength]
  · have hfirstLength := rightBoundaryWords_length lengthS lengthRP n hlength
    have houter : lengthS.length =
        (rightBoundaryWords lengthS lengthRP n).length :=
      hlength.trans hfirstLength.symm
    rw [boolWordToNat_rightBoundaryWords _ _ _ houter,
      boolWordToNat_rightBoundaryWords lengthS lengthRP n hlength]
    exact modularRightBoundary_involutive
      (2 ^ lengthS.length) (n + 1) (boolWordToNat lengthS)
      (boolWordToNat lengthRP) (Nat.two_pow_pos _)
      (boolWordToNat_lt_pow_two lengthS)
      (by simpa [hlength] using boolWordToNat_lt_pow_two lengthRP)

/-- Preparing and then applying the explicit restore recurrence returns both words exactly. -/
theorem restore_prepareLatestPaperTBoundaryWords
    (phase2 : Bool) (lengthT lengthRP lengthS : List Bool) (n : Nat)
    (hrp : lengthS.length = lengthRP.length) :
    restoreLatestPaperTBoundaryWords phase2
      (prepareLatestPaperTBoundaryWords phase2 lengthT lengthRP lengthS n).1
      (prepareLatestPaperTBoundaryWords phase2 lengthT lengthRP lengthS n).2
      lengthS n = (lengthT, lengthRP) := by
  have hconstant : (constantBits lengthT.length 2).length = lengthT.length := by simp
  let preparedT := cuccaroAddBits false (constantBits lengthT.length 2) lengthT
  have hpreparedTLength : preparedT.length = lengthT.length := by
    dsimp only [preparedT]
    exact (cuccaroAddBits_length false _ _ hconstant).trans hconstant
  have htRestore :
      cuccaroSubBits false (constantBits preparedT.length 2) preparedT = lengthT := by
    rw [hpreparedTLength]
    exact cuccaroSubBits_addBits false _ _ hconstant
  have hrpRestore := rightBoundaryWords_involutive lengthS lengthRP n hrp
  cases phase2 <;>
    change
      (cuccaroSubBits false (constantBits preparedT.length 2) preparedT,
        rightBoundaryWords lengthS (rightBoundaryWords lengthS lengthRP n) n) =
        (lengthT, lengthRP)
  all_goals exact Prod.ext htRestore hrpRestore

private theorem add_subConstantBits
    (bits : List Bool) (value : Nat) :
    let subtracted :=
      cuccaroSubBits false (constantBits bits.length value) bits
    cuccaroAddBits false (constantBits subtracted.length value) subtracted = bits := by
  dsimp
  have hconstant : (constantBits bits.length value).length = bits.length := by simp
  have hsubtracted :
      (cuccaroSubBits false (constantBits bits.length value) bits).length =
        bits.length :=
    (cuccaroSubBits_length false _ _ hconstant).trans hconstant
  rw [hsubtracted]
  exact cuccaroAddBits_subBits false _ _ hconstant

/-- Applying prepare after the explicit restore recurrence also returns both words exactly. -/
theorem prepare_restoreLatestPaperTBoundaryWords
    (phase2 : Bool) (lengthT lengthRP lengthS : List Bool) (n : Nat)
    (ht : lengthS.length = lengthT.length)
    (hrp : lengthS.length = lengthRP.length) :
    prepareLatestPaperTBoundaryWords phase2
      (restoreLatestPaperTBoundaryWords phase2 lengthT lengthRP lengthS n).1
      (restoreLatestPaperTBoundaryWords phase2 lengthT lengthRP lengthS n).2
      lengthS n = (lengthT, lengthRP) := by
  have htRight := rightBoundaryWords_involutive lengthS lengthT n ht
  have hrpRight := rightBoundaryWords_involutive lengthS lengthRP n hrp
  cases phase2 with
  | false =>
      change
        (cuccaroAddBits false
            (constantBits
              (cuccaroSubBits false (constantBits lengthT.length 2) lengthT).length 2)
            (cuccaroSubBits false (constantBits lengthT.length 2) lengthT),
          rightBoundaryWords lengthS (rightBoundaryWords lengthS lengthRP n) n) =
          (lengthT, lengthRP)
      exact Prod.ext (add_subConstantBits lengthT 2) hrpRight
  | true =>
      change
        (rightBoundaryWords lengthS (rightBoundaryWords lengthS lengthT n) n,
          cuccaroAddBits false
            (constantBits
              (cuccaroSubBits false (constantBits lengthRP.length 2) lengthRP).length 2)
            (cuccaroSubBits false (constantBits lengthRP.length 2) lengthRP)) =
          (lengthT, lengthRP)
      exact Prod.ext htRight (add_subConstantBits lengthRP 2)

/-! ## Direct whole-state semantics -/

/-- The literal prepare block realizes the phase-dependent word recurrence, restores every
borrowed scratch wire, and changes no wire outside the two boundary words. -/
theorem prepareLatestPaperTBoundary_correct
    (registers : TBoundaryRegisters) (n : Nat) (state : BasisState)
    (layout : TBoundaryLayout registers)
    (ready : TBoundaryReady registers state) :
    let after := run (prepareLatestPaperTBoundary registers n) state
    (wireValues registers.lengthT after,
        wireValues registers.lengthRP after) =
      prepareLatestPaperTBoundaryWords (state registers.phase2)
        (wireValues registers.lengthT state)
        (wireValues registers.lengthRP state)
        (wireValues registers.lengthSLow state) n ∧
      TBoundaryReady registers after ∧
      ∀ wire, wire ∉ registers.lengthT → wire ∉ registers.lengthRP →
        after wire = state wire := by
  have hconstantT : registers.constants.length = registers.lengthT.length := by
    simpa [TBoundaryRegisters.width] using layout.constants_length
  have hconstantRP : registers.constants.length = registers.lengthRP.length :=
    layout.constants_length.trans layout.lengthRP_length.symm
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact layout.positive
  have hsubLength : registers.lengthSLow.length = registers.lengthRP.length :=
    layout.lengthSLow_length.trans layout.lengthRP_length.symm
  have hswapLength : registers.lengthT.length = registers.lengthRP.length :=
    layout.lengthRP_length.symm
  have hready : Clean (registers.constants ++ [registers.carry]) state := by
    simpa [TBoundaryReady, TBoundaryRegisters.usedScratch] using ready
  let afterAdd := run
    (addConstant registers.lengthT registers.constants registers.carry 2) state
  have hadd := addConstant_correct registers.lengthT registers.constants
    registers.carry 2 state hconstantT layout.constantT hready
  let afterReflect := run
    (constMinus registers.lengthRP registers.constants registers.carry (n + 1))
      afterAdd
  have hreflect := constMinus_correct registers.lengthRP registers.constants
    registers.carry (n + 1) afterAdd hpositiveRP hconstantRP
    layout.constantRP hadd.2.1
  let afterSub := run
    (cuccaroSub registers.lengthSLow registers.lengthRP registers.carry)
      afterReflect
  have hsub := cuccaroSub_correct registers.lengthSLow registers.lengthRP
    registers.carry afterReflect hsubLength layout.subtractRP
  let after := run
    (controlledSwapWords registers.phase2 registers.lengthT registers.lengthRP)
      afterSub
  have hswap := controlledSwapWords_correct registers.phase2 registers.lengthT
    registers.lengthRP afterSub hswapLength layout.swap
  have hfull : run (prepareLatestPaperTBoundary registers n) state = after := by
    simp [prepareLatestPaperTBoundary, after, afterSub, afterReflect, afterAdd,
      run_append]
  have hbeforeOutside
      (wire : Wire) (ht : wire ∉ registers.lengthT)
      (hrp : wire ∉ registers.lengthRP) : afterSub wire = state wire := by
    calc
      afterSub wire = afterReflect wire := hsub.2.2 wire hrp
      _ = afterAdd wire := hreflect.2.2 wire hrp
      _ = state wire := hadd.2.2 wire ht
  have hsValues :
      wireValues registers.lengthSLow afterReflect =
        wireValues registers.lengthSLow state := by
    calc
      wireValues registers.lengthSLow afterReflect =
          wireValues registers.lengthSLow afterAdd := by
        apply wireValues_congr_local
        intro wire hwire
        exact hreflect.2.2 wire (layout.s_outside_words wire hwire).2
      _ = wireValues registers.lengthSLow state := by
        apply wireValues_congr_local
        intro wire hwire
        exact hadd.2.2 wire (layout.s_outside_words wire hwire).1
  have htValues :
      wireValues registers.lengthT afterSub =
        cuccaroAddBits false (constantBits registers.constants.length 2)
          (wireValues registers.lengthT state) := by
    calc
      wireValues registers.lengthT afterSub =
          wireValues registers.lengthT afterReflect := by
        apply wireValues_congr_local
        intro wire hwire
        exact hsub.2.2 wire (layout.t_outside_rp wire hwire)
      _ = wireValues registers.lengthT afterAdd := by
        apply wireValues_congr_local
        intro wire hwire
        exact hreflect.2.2 wire (layout.t_outside_rp wire hwire)
      _ = cuccaroAddBits false (constantBits registers.constants.length 2)
          (wireValues registers.lengthT state) := hadd.1
  have hrpAfterAdd :
      wireValues registers.lengthRP afterAdd =
        wireValues registers.lengthRP state := by
    apply wireValues_congr_local
    intro wire hwire
    exact hadd.2.2 wire (layout.rp_outside_t wire hwire)
  have hrpAfterReflect :
      wireValues registers.lengthRP afterReflect =
        constMinusBits (wireValues registers.lengthRP state) (n + 1) := by
    rw [hreflect.1, hrpAfterAdd]
  have hcarryReflect : afterReflect registers.carry = false := by
    exact hreflect.2.1 registers.carry (by
      simp)
  have hrpValues :
      wireValues registers.lengthRP afterSub =
        cuccaroSubBits false (wireValues registers.lengthSLow state)
          (constMinusBits (wireValues registers.lengthRP state) (n + 1)) := by
    rw [hsub.2.1, hcarryReflect, hsValues, hrpAfterReflect]
  have hphaseBefore : afterSub registers.phase2 = state registers.phase2 :=
    hbeforeOutside registers.phase2 layout.phase_outside_words.1
      layout.phase_outside_words.2
  have hwords :
      (wireValues registers.lengthT after,
          wireValues registers.lengthRP after) =
        prepareLatestPaperTBoundaryWords (state registers.phase2)
          (wireValues registers.lengthT state)
          (wireValues registers.lengthRP state)
          (wireValues registers.lengthSLow state) n := by
    dsimp only [after]
    rw [hswap.1, hswap.2, hphaseBefore, htValues, hrpValues, hconstantT]
    unfold prepareLatestPaperTBoundaryWords
    cases hphase : state registers.phase2 <;> simp [wireValues]
  have hcontrolLeft := layout.phase_outside_words.1
  have hcontrolRight := layout.phase_outside_words.2
  have houtside (wire : Wire)
      (ht : wire ∉ registers.lengthT)
      (hrp : wire ∉ registers.lengthRP) : after wire = state wire := by
    calc
      after wire = afterSub wire :=
        controlledSwapWords_preservesOutsideWords registers.phase2
          registers.lengthT registers.lengthRP afterSub hcontrolLeft hcontrolRight
          wire ht hrp
      _ = state wire := hbeforeOutside wire ht hrp
  have hclean : TBoundaryReady registers after := by
    intro wire hwire
    have hout := layout.scratch_outside_words wire hwire
    rw [houtside wire hout.1 hout.2]
    exact ready wire hwire
  rw [hfull]
  exact ⟨hwords, hclean, houtside⟩

/-- The generator's explicit restore order realizes its stated word recurrence, returns every
borrowed wire clean, and changes no wire outside the two boundary words. -/
theorem restoreLatestPaperTBoundary_correct
    (registers : TBoundaryRegisters) (n : Nat) (state : BasisState)
    (layout : TBoundaryLayout registers)
    (ready : TBoundaryReady registers state) :
    let after := run (restoreLatestPaperTBoundary registers n) state
    (wireValues registers.lengthT after,
        wireValues registers.lengthRP after) =
      restoreLatestPaperTBoundaryWords (state registers.phase2)
        (wireValues registers.lengthT state)
        (wireValues registers.lengthRP state)
        (wireValues registers.lengthSLow state) n ∧
      TBoundaryReady registers after ∧
      ∀ wire, wire ∉ registers.lengthT → wire ∉ registers.lengthRP →
        after wire = state wire := by
  have hconstantT : registers.constants.length = registers.lengthT.length := by
    simpa [TBoundaryRegisters.width] using layout.constants_length
  have hconstantRP : registers.constants.length = registers.lengthRP.length :=
    layout.constants_length.trans layout.lengthRP_length.symm
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact layout.positive
  have hsubLength : registers.lengthSLow.length = registers.lengthRP.length :=
    layout.lengthSLow_length.trans layout.lengthRP_length.symm
  have hswapLength : registers.lengthT.length = registers.lengthRP.length :=
    layout.lengthRP_length.symm
  let afterSwap := run
    (controlledSwapWords registers.phase2 registers.lengthT registers.lengthRP) state
  have hswap := controlledSwapWords_correct registers.phase2 registers.lengthT
    registers.lengthRP state hswapLength layout.swap
  have hcontrolLeft := layout.phase_outside_words.1
  have hcontrolRight := layout.phase_outside_words.2
  have hswapOutside (wire : Wire)
      (ht : wire ∉ registers.lengthT)
      (hrp : wire ∉ registers.lengthRP) : afterSwap wire = state wire := by
    exact controlledSwapWords_preservesOutsideWords registers.phase2
      registers.lengthT registers.lengthRP state hcontrolLeft hcontrolRight
      wire ht hrp
  have hswapReady : TBoundaryReady registers afterSwap := by
    intro wire hwire
    have hout := layout.scratch_outside_words wire hwire
    rw [hswapOutside wire hout.1 hout.2]
    exact ready wire hwire
  have hswapClean : Clean (registers.constants ++ [registers.carry]) afterSwap := by
    simpa [TBoundaryReady, TBoundaryRegisters.usedScratch] using hswapReady
  let afterReflect := run
    (constMinus registers.lengthRP registers.constants registers.carry (n + 1))
      afterSwap
  have hreflect := constMinus_correct registers.lengthRP registers.constants
    registers.carry (n + 1) afterSwap hpositiveRP hconstantRP
    layout.constantRP hswapClean
  let afterSub := run
    (cuccaroSub registers.lengthSLow registers.lengthRP registers.carry)
      afterReflect
  have hsub := cuccaroSub_correct registers.lengthSLow registers.lengthRP
    registers.carry afterReflect hsubLength layout.subtractRP
  have hsubClean : Clean (registers.constants ++ [registers.carry]) afterSub := by
    intro wire hwire
    have hout := layout.scratch_outside_words wire hwire
    calc
      afterSub wire = afterReflect wire := hsub.2.2 wire hout.2
      _ = false := hreflect.2.1 wire hwire
  let after := run
    (subConstant registers.lengthT registers.constants registers.carry 2) afterSub
  have hfinal := subConstant_correct registers.lengthT registers.constants
    registers.carry 2 afterSub hconstantT layout.constantT hsubClean
  have hfull : run (restoreLatestPaperTBoundary registers n) state = after := by
    simp [restoreLatestPaperTBoundary, after, afterSub, afterReflect, afterSwap,
      run_append]
  have hsSwap :
      wireValues registers.lengthSLow afterSwap =
        wireValues registers.lengthSLow state := by
    apply wireValues_congr_local
    intro wire hwire
    have hout := layout.s_outside_words wire hwire
    exact hswapOutside wire hout.1 hout.2
  have hsReflect :
      wireValues registers.lengthSLow afterReflect =
        wireValues registers.lengthSLow state := by
    calc
      wireValues registers.lengthSLow afterReflect =
          wireValues registers.lengthSLow afterSwap := by
        apply wireValues_congr_local
        intro wire hwire
        exact hreflect.2.2 wire (layout.s_outside_words wire hwire).2
      _ = wireValues registers.lengthSLow state := hsSwap
  have hcarryReflect : afterReflect registers.carry = false :=
    hreflect.2.1 registers.carry (by simp)
  have hrpReflect :
      wireValues registers.lengthRP afterReflect =
        constMinusBits (wireValues registers.lengthRP afterSwap) (n + 1) :=
    hreflect.1
  have hrpSub :
      wireValues registers.lengthRP afterSub =
        cuccaroSubBits false (wireValues registers.lengthSLow state)
          (constMinusBits (wireValues registers.lengthRP afterSwap) (n + 1)) := by
    rw [hsub.2.1, hcarryReflect, hsReflect, hrpReflect]
  have htSub :
      wireValues registers.lengthT afterSub =
        wireValues registers.lengthT afterSwap := by
    calc
      wireValues registers.lengthT afterSub =
          wireValues registers.lengthT afterReflect := by
        apply wireValues_congr_local
        intro wire hwire
        exact hsub.2.2 wire (layout.t_outside_rp wire hwire)
      _ = wireValues registers.lengthT afterSwap := by
        apply wireValues_congr_local
        intro wire hwire
        exact hreflect.2.2 wire (layout.t_outside_rp wire hwire)
  have htFinal :
      wireValues registers.lengthT after =
        cuccaroSubBits false (constantBits registers.lengthT.length 2)
          (wireValues registers.lengthT afterSwap) := by
    rw [hfinal.1, hconstantT, htSub]
  have hrpFinal :
      wireValues registers.lengthRP after =
        cuccaroSubBits false (wireValues registers.lengthSLow state)
          (constMinusBits (wireValues registers.lengthRP afterSwap) (n + 1)) := by
    calc
      wireValues registers.lengthRP after =
          wireValues registers.lengthRP afterSub := by
        apply wireValues_congr_local
        intro wire hwire
        exact hfinal.2.2 wire (layout.rp_outside_t wire hwire)
      _ = _ := hrpSub
  have hwords :
      (wireValues registers.lengthT after,
          wireValues registers.lengthRP after) =
        restoreLatestPaperTBoundaryWords (state registers.phase2)
          (wireValues registers.lengthT state)
          (wireValues registers.lengthRP state)
          (wireValues registers.lengthSLow state) n := by
    rw [htFinal, hrpFinal, hswap.1, hswap.2]
    unfold restoreLatestPaperTBoundaryWords
    cases hphase : state registers.phase2 <;>
      simp [wireValues, hswapLength]
  have houtside (wire : Wire)
      (ht : wire ∉ registers.lengthT)
      (hrp : wire ∉ registers.lengthRP) : after wire = state wire := by
    calc
      after wire = afterSub wire := hfinal.2.2 wire ht
      _ = afterReflect wire := hsub.2.2 wire hrp
      _ = afterSwap wire := hreflect.2.2 wire hrp
      _ = state wire := hswapOutside wire ht hrp
  rw [hfull]
  exact ⟨hwords, by
    simpa [TBoundaryReady, TBoundaryRegisters.usedScratch] using hfinal.2.1,
    houtside⟩

/-- The generator's explicit restoration block reverses boundary preparation on the complete
basis state, including all borrowed scratch wires. -/
theorem run_restoreLatestPaperTBoundary_after_prepare
    (registers : TBoundaryRegisters) (n : Nat) (state : BasisState)
    (layout : TBoundaryLayout registers)
    (ready : TBoundaryReady registers state) :
    run (restoreLatestPaperTBoundary registers n)
      (run (prepareLatestPaperTBoundary registers n) state) = state := by
  let prepared := run (prepareLatestPaperTBoundary registers n) state
  have hprepare :=
    prepareLatestPaperTBoundary_correct registers n state layout ready
  let restored := run (restoreLatestPaperTBoundary registers n) prepared
  have hrestore :=
    restoreLatestPaperTBoundary_correct registers n prepared layout hprepare.2.1
  have hphase : prepared registers.phase2 = state registers.phase2 := by
    exact hprepare.2.2 registers.phase2 layout.phase_outside_words.1
      layout.phase_outside_words.2
  have hs :
      wireValues registers.lengthSLow prepared =
        wireValues registers.lengthSLow state := by
    apply wireValues_congr_local
    intro wire hwire
    have hout := layout.s_outside_words wire hwire
    exact hprepare.2.2 wire hout.1 hout.2
  have hrps :
      (wireValues registers.lengthSLow state).length =
        (wireValues registers.lengthRP state).length := by
    simp [wireValues, TBoundaryRegisters.width, layout.lengthSLow_length,
      layout.lengthRP_length]
  have htPrepared :
      wireValues registers.lengthT prepared =
        (prepareLatestPaperTBoundaryWords (state registers.phase2)
          (wireValues registers.lengthT state)
          (wireValues registers.lengthRP state)
          (wireValues registers.lengthSLow state) n).1 := by
    simpa only [prepared] using congrArg Prod.fst hprepare.1
  have hrpPrepared :
      wireValues registers.lengthRP prepared =
        (prepareLatestPaperTBoundaryWords (state registers.phase2)
          (wireValues registers.lengthT state)
          (wireValues registers.lengthRP state)
          (wireValues registers.lengthSLow state) n).2 := by
    simpa only [prepared] using congrArg Prod.snd hprepare.1
  have hwords :
      (wireValues registers.lengthT restored,
          wireValues registers.lengthRP restored) =
        (wireValues registers.lengthT state,
          wireValues registers.lengthRP state) := by
    rw [hrestore.1, hphase, hs, htPrepared, hrpPrepared]
    exact restore_prepareLatestPaperTBoundaryWords
      (state registers.phase2)
      (wireValues registers.lengthT state)
      (wireValues registers.lengthRP state)
      (wireValues registers.lengthSLow state) n hrps
  have ht :
      wireValues registers.lengthT restored =
        wireValues registers.lengthT state := congrArg Prod.fst hwords
  have hrp :
      wireValues registers.lengthRP restored =
        wireValues registers.lengthRP state := congrArg Prod.snd hwords
  change restored = state
  funext wire
  by_cases hwireT : wire ∈ registers.lengthT
  · exact wireValues_eq_at_local registers.lengthT restored state ht hwireT
  · by_cases hwireRP : wire ∈ registers.lengthRP
    · exact wireValues_eq_at_local registers.lengthRP restored state hrp hwireRP
    · have houtRestore := hrestore.2.2 wire hwireT hwireRP
      have houtPrepare := hprepare.2.2 wire hwireT hwireRP
      change restored wire = prepared wire at houtRestore
      change prepared wire = state wire at houtPrepare
      exact houtRestore.trans houtPrepare

/-- Preparation likewise reverses the generator's explicit restoration block on the complete
basis state. -/
theorem run_prepareLatestPaperTBoundary_after_restore
    (registers : TBoundaryRegisters) (n : Nat) (state : BasisState)
    (layout : TBoundaryLayout registers)
    (ready : TBoundaryReady registers state) :
    run (prepareLatestPaperTBoundary registers n)
      (run (restoreLatestPaperTBoundary registers n) state) = state := by
  let restored := run (restoreLatestPaperTBoundary registers n) state
  have hrestore :=
    restoreLatestPaperTBoundary_correct registers n state layout ready
  let prepared := run (prepareLatestPaperTBoundary registers n) restored
  have hprepare :=
    prepareLatestPaperTBoundary_correct registers n restored layout hrestore.2.1
  have hphase : restored registers.phase2 = state registers.phase2 := by
    exact hrestore.2.2 registers.phase2 layout.phase_outside_words.1
      layout.phase_outside_words.2
  have hs :
      wireValues registers.lengthSLow restored =
        wireValues registers.lengthSLow state := by
    apply wireValues_congr_local
    intro wire hwire
    have hout := layout.s_outside_words wire hwire
    exact hrestore.2.2 wire hout.1 hout.2
  have hts :
      (wireValues registers.lengthSLow state).length =
        (wireValues registers.lengthT state).length := by
    simp [wireValues, TBoundaryRegisters.width, layout.lengthSLow_length]
  have hrps :
      (wireValues registers.lengthSLow state).length =
        (wireValues registers.lengthRP state).length := by
    simp [wireValues, TBoundaryRegisters.width, layout.lengthSLow_length,
      layout.lengthRP_length]
  have htRestored :
      wireValues registers.lengthT restored =
        (restoreLatestPaperTBoundaryWords (state registers.phase2)
          (wireValues registers.lengthT state)
          (wireValues registers.lengthRP state)
          (wireValues registers.lengthSLow state) n).1 := by
    simpa only [restored] using congrArg Prod.fst hrestore.1
  have hrpRestored :
      wireValues registers.lengthRP restored =
        (restoreLatestPaperTBoundaryWords (state registers.phase2)
          (wireValues registers.lengthT state)
          (wireValues registers.lengthRP state)
          (wireValues registers.lengthSLow state) n).2 := by
    simpa only [restored] using congrArg Prod.snd hrestore.1
  have hwords :
      (wireValues registers.lengthT prepared,
          wireValues registers.lengthRP prepared) =
        (wireValues registers.lengthT state,
          wireValues registers.lengthRP state) := by
    rw [hprepare.1, hphase, hs, htRestored, hrpRestored]
    exact prepare_restoreLatestPaperTBoundaryWords
      (state registers.phase2)
      (wireValues registers.lengthT state)
      (wireValues registers.lengthRP state)
      (wireValues registers.lengthSLow state) n hts hrps
  have ht :
      wireValues registers.lengthT prepared =
        wireValues registers.lengthT state := congrArg Prod.fst hwords
  have hrp :
      wireValues registers.lengthRP prepared =
        wireValues registers.lengthRP state := congrArg Prod.snd hwords
  change prepared = state
  funext wire
  by_cases hwireT : wire ∈ registers.lengthT
  · exact wireValues_eq_at_local registers.lengthT prepared state ht hwireT
  · by_cases hwireRP : wire ∈ registers.lengthRP
    · exact wireValues_eq_at_local registers.lengthRP prepared state hrp hwireRP
    · have houtPrepare := hprepare.2.2 wire hwireT hwireRP
      have houtRestore := hrestore.2.2 wire hwireT hwireRP
      change prepared wire = restored wire at houtPrepare
      change restored wire = state wire at houtRestore
      exact houtPrepare.trans houtRestore

/-! ## Constructor-derived resources -/

private theorem cuccaroAdd_xCount_local :
    ∀ (addends targets : List Wire) (carry : Wire),
      eeaXCount (cuccaroAdd addends targets carry) = 0 := by
  intro addends
  induction addends with
  | nil => intro targets carry; cases targets <;> rfl
  | cons addend addends ih =>
      intro targets carry
      cases targets with
      | nil => rfl
      | cons target targets =>
          rw [cuccaroAdd, eeaXCount_append, eeaXCount_append,
            ih targets addend]
          rfl

private theorem cuccaroSub_xCount_local
    (addends targets : List Wire) (carry : Wire) :
    eeaXCount (cuccaroSub addends targets carry) = 0 := by
  rw [cuccaroSub, eeaXCount_adjoint, cuccaroAdd_xCount_local]

private theorem xorConstant_xCount_local :
    ∀ (register : List Wire) (value : Nat),
      eeaXCount (xorConstant register value) =
        (constantBits register.length value).count true := by
  intro register
  induction register with
  | nil => intro value; rfl
  | cons wire wires ih =>
      intro value
      rw [xorConstant, eeaXCount_append, ih (value / 2)]
      change
        eeaXCount (if value.testBit 0 then [.X wire] else []) +
            (constantBits wires.length (value / 2)).count true =
          (xorConstantBits (List.replicate (wires.length + 1) false) value).count true
      rw [show wires.length + 1 = Nat.succ wires.length by omega,
        List.replicate_succ]
      by_cases hbit : value.testBit 0
      · simp [constantBits, xorConstantBits, hbit, eeaXCount]
        omega
      · simp [constantBits, xorConstantBits, hbit, eeaXCount]

private theorem notRegister_xCount_local (register : List Wire) :
    eeaXCount (notRegister register) = register.length := by
  induction register with
  | nil => rfl
  | cons wire wires ih =>
      rw [notRegister]
      change 1 + eeaXCount (notRegister wires) = wires.length + 1
      omega

private theorem incrementTail_xCount_local :
    ∀ (bits : List Wire) (carry : Wire) (carries : List Wire),
      eeaXCount (incrementTail bits carry carries) = 0 := by
  intro bits
  induction bits with
  | nil => intro carry carries; rfl
  | cons bit bits ih =>
      intro carry carries
      cases bits with
      | nil => cases carries <;> rfl
      | cons next rest =>
          cases carries with
          | nil => rfl
          | cons nextCarry carries =>
              rw [incrementTail, eeaXCount_append, eeaXCount_append,
                ih nextCarry carries]
              rfl

private theorem uncontrolledIncrement_xCount_local
    (register carries : List Wire)
    (hpositive : 0 < register.length)
    (hlength : register.length = carries.length + 1) :
    eeaXCount (uncontrolledIncrement register carries) = 1 := by
  cases register with
  | nil => simp at hpositive
  | cons low tail =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons firstCarry carries =>
              rw [uncontrolledIncrement, eeaXCount_append, eeaXCount_append,
                incrementTail_xCount_local]
              rfl

private theorem addConstant_xCount_local
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    eeaXCount (addConstant register constants carry value) =
      2 * (constantBits constants.length value).count true := by
  simp [addConstant, eeaXCount_append, xorConstant_xCount_local,
    cuccaroAdd_xCount_local]
  omega

private theorem subConstant_xCount_local
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    eeaXCount (subConstant register constants carry value) =
      2 * (constantBits constants.length value).count true := by
  simp [subConstant, eeaXCount_append, xorConstant_xCount_local,
    cuccaroSub_xCount_local]
  omega

private theorem constMinus_xCount_local
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hpositive : 0 < register.length)
    (hlength : constants.length = register.length) :
    eeaXCount (constMinus register constants carry value) =
      register.length + 1 +
        2 * (constantBits constants.length value).count true := by
  have htakeLength : register.length =
      (constants.take (register.length - 1)).length + 1 := by
    rw [List.length_take, hlength]
    omega
  simp [constMinus, eeaXCount_append, notRegister_xCount_local,
    uncontrolledIncrement_xCount_local register _ hpositive htakeLength,
    addConstant_xCount_local]
  omega

private theorem constMinus_cnotCount_of_two_le
    (register constants : List Wire) (carry : Wire) (value : Nat)
    (hwidth : 2 ≤ register.length)
    (hlength : constants.length = register.length) :
    eeaCnotCount (constMinus register constants carry value) =
      register.length + 1 + 4 * register.length := by
  cases register with
  | nil => simp at hwidth
  | cons low tail =>
      cases tail with
      | nil => simp at hwidth
      | cons next rest =>
          exact constMinus_cnotCount low next rest constants carry value hlength

private theorem TBoundaryLayout.lengthRP_lengthT
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    registers.lengthRP.length = registers.lengthT.length :=
  layout.lengthRP_length

private theorem TBoundaryLayout.lengthSLow_lengthT
    {registers : TBoundaryRegisters} (layout : TBoundaryLayout registers) :
    registers.lengthSLow.length = registers.lengthT.length :=
  layout.lengthSLow_length

/-- Closed coherent Toffoli formula for either literal coefficient-boundary stream. -/
def latestPaperTBoundaryToffoliFormula (width : Nat) : Nat :=
  9 * width - 4

/-- Closed coherent CNOT formula for either literal coefficient-boundary stream. -/
def latestPaperTBoundaryCnotFormula (width : Nat) : Nat :=
  15 * width + 1

/-- Exact standalone-X formula.  The two `constantBits` weights expose the actual low-bit
constant loads used by the source, including the `n + 1` reflection constant. -/
def latestPaperTBoundaryXFormula (width n : Nat) : Nat :=
  2 * (constantBits width 2).count true + width + 1 +
    2 * (constantBits width (n + 1)).count true

/-- Framework-derived coherent T formula for either literal coefficient-boundary stream. -/
def latestPaperTBoundaryTFormula (width : Nat) : Nat :=
  63 * width - 28

theorem prepareLatestPaperTBoundary_toffoliCount
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers)
    (hwidth : 2 ≤ registers.width) :
    eeaToffoliCount (prepareLatestPaperTBoundary registers n) =
      latestPaperTBoundaryToffoliFormula registers.width := by
  change 2 ≤ registers.lengthT.length at hwidth
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact layout.positive
  simp only [prepareLatestPaperTBoundary, eeaToffoliCount_append]
  rw [addConstant_toffoliCount registers.lengthT registers.constants
      registers.carry 2 (layout.constants_length.trans rfl),
    constMinus_toffoliCount registers.lengthRP registers.constants
      registers.carry (n + 1) hpositiveRP
      (layout.constants_length.trans layout.lengthRP_length.symm),
    cuccaroSub_toffoliCount registers.lengthSLow registers.lengthRP
      registers.carry
      (layout.lengthSLow_length.trans layout.lengthRP_length.symm),
    controlledSwapWords_toffoliCount registers.phase2 registers.lengthT
      registers.lengthRP layout.lengthRP_length.symm]
  rw [layout.lengthRP_lengthT, layout.lengthSLow_lengthT]
  simp [latestPaperTBoundaryToffoliFormula, TBoundaryRegisters.width]
  omega

theorem restoreLatestPaperTBoundary_toffoliCount
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers)
    (hwidth : 2 ≤ registers.width) :
    eeaToffoliCount (restoreLatestPaperTBoundary registers n) =
      latestPaperTBoundaryToffoliFormula registers.width := by
  change 2 ≤ registers.lengthT.length at hwidth
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact layout.positive
  simp only [restoreLatestPaperTBoundary, eeaToffoliCount_append]
  rw [controlledSwapWords_toffoliCount registers.phase2 registers.lengthT
      registers.lengthRP layout.lengthRP_length.symm,
    constMinus_toffoliCount registers.lengthRP registers.constants
      registers.carry (n + 1) hpositiveRP
      (layout.constants_length.trans layout.lengthRP_length.symm),
    cuccaroSub_toffoliCount registers.lengthSLow registers.lengthRP
      registers.carry
      (layout.lengthSLow_length.trans layout.lengthRP_length.symm),
    subConstant_toffoliCount registers.lengthT registers.constants
      registers.carry 2 (layout.constants_length.trans rfl)]
  rw [layout.lengthRP_lengthT, layout.lengthSLow_lengthT]
  simp [latestPaperTBoundaryToffoliFormula, TBoundaryRegisters.width]
  omega

theorem prepareLatestPaperTBoundary_cnotCount
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers)
    (hwidth : 2 ≤ registers.width) :
    eeaCnotCount (prepareLatestPaperTBoundary registers n) =
      latestPaperTBoundaryCnotFormula registers.width := by
  have hwidthRP : 2 ≤ registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact hwidth
  simp only [prepareLatestPaperTBoundary, eeaCnotCount_append]
  rw [addConstant_cnotCount registers.lengthT registers.constants
      registers.carry 2 (layout.constants_length.trans rfl),
    constMinus_cnotCount_of_two_le registers.lengthRP registers.constants
      registers.carry (n + 1) hwidthRP
      (layout.constants_length.trans layout.lengthRP_length.symm),
    cuccaroSub_cnotCount registers.lengthSLow registers.lengthRP
      registers.carry
      (layout.lengthSLow_length.trans layout.lengthRP_length.symm),
    controlledSwapWords_cnotCount registers.phase2 registers.lengthT
      registers.lengthRP layout.lengthRP_length.symm]
  rw [layout.lengthRP_lengthT, layout.lengthSLow_lengthT]
  simp [latestPaperTBoundaryCnotFormula, TBoundaryRegisters.width]
  omega

theorem restoreLatestPaperTBoundary_cnotCount
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers)
    (hwidth : 2 ≤ registers.width) :
    eeaCnotCount (restoreLatestPaperTBoundary registers n) =
      latestPaperTBoundaryCnotFormula registers.width := by
  have hwidthRP : 2 ≤ registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact hwidth
  simp only [restoreLatestPaperTBoundary, eeaCnotCount_append]
  rw [controlledSwapWords_cnotCount registers.phase2 registers.lengthT
      registers.lengthRP layout.lengthRP_length.symm,
    constMinus_cnotCount_of_two_le registers.lengthRP registers.constants
      registers.carry (n + 1) hwidthRP
      (layout.constants_length.trans layout.lengthRP_length.symm),
    cuccaroSub_cnotCount registers.lengthSLow registers.lengthRP
      registers.carry
      (layout.lengthSLow_length.trans layout.lengthRP_length.symm),
    subConstant_cnotCount registers.lengthT registers.constants
      registers.carry 2 (layout.constants_length.trans rfl)]
  rw [layout.lengthRP_lengthT, layout.lengthSLow_lengthT]
  simp [latestPaperTBoundaryCnotFormula, TBoundaryRegisters.width]
  omega

theorem prepareLatestPaperTBoundary_xCount
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers) :
    eeaXCount (prepareLatestPaperTBoundary registers n) =
      latestPaperTBoundaryXFormula registers.width n := by
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact layout.positive
  simp only [prepareLatestPaperTBoundary, eeaXCount_append]
  rw [addConstant_xCount_local registers.lengthT registers.constants
      registers.carry 2,
    constMinus_xCount_local registers.lengthRP registers.constants
      registers.carry (n + 1) hpositiveRP
      (layout.constants_length.trans layout.lengthRP_length.symm),
    cuccaroSub_xCount_local, controlledSwapWords_xCount]
  simp [latestPaperTBoundaryXFormula, TBoundaryRegisters.width,
    layout.constants_length, layout.lengthRP_length]
  omega

theorem restoreLatestPaperTBoundary_xCount
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers) :
    eeaXCount (restoreLatestPaperTBoundary registers n) =
      latestPaperTBoundaryXFormula registers.width n := by
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact layout.positive
  simp only [restoreLatestPaperTBoundary, eeaXCount_append]
  rw [controlledSwapWords_xCount,
    constMinus_xCount_local registers.lengthRP registers.constants
      registers.carry (n + 1) hpositiveRP
      (layout.constants_length.trans layout.lengthRP_length.symm),
    cuccaroSub_xCount_local,
    subConstant_xCount_local registers.lengthT registers.constants
      registers.carry 2]
  simp [latestPaperTBoundaryXFormula, TBoundaryRegisters.width,
    layout.constants_length, layout.lengthRP_length]
  omega

theorem prepareLatestPaperTBoundary_tCount
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers)
    (hwidth : 2 ≤ registers.width) :
    tCount (prepareLatestPaperTBoundary registers n) =
      latestPaperTBoundaryTFormula registers.width := by
  change 2 ≤ registers.lengthT.length at hwidth
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact layout.positive
  simp only [prepareLatestPaperTBoundary, tCount_append]
  rw [addConstant_tCount registers.lengthT registers.constants
      registers.carry 2 (layout.constants_length.trans rfl),
    constMinus_tCount registers.lengthRP registers.constants
      registers.carry (n + 1) hpositiveRP
      (layout.constants_length.trans layout.lengthRP_length.symm),
    cuccaroSub_tCount registers.lengthSLow registers.lengthRP registers.carry
      (layout.lengthSLow_length.trans layout.lengthRP_length.symm),
    controlledSwapWords_tCount registers.phase2 registers.lengthT
      registers.lengthRP layout.lengthRP_length.symm]
  rw [layout.lengthRP_lengthT, layout.lengthSLow_lengthT]
  simp [latestPaperTBoundaryTFormula, TBoundaryRegisters.width]
  omega

theorem restoreLatestPaperTBoundary_tCount
    (registers : TBoundaryRegisters) (n : Nat)
    (layout : TBoundaryLayout registers)
    (hwidth : 2 ≤ registers.width) :
    tCount (restoreLatestPaperTBoundary registers n) =
      latestPaperTBoundaryTFormula registers.width := by
  change 2 ≤ registers.lengthT.length at hwidth
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [layout.lengthRP_length]
    exact layout.positive
  simp only [restoreLatestPaperTBoundary, tCount_append]
  rw [controlledSwapWords_tCount registers.phase2 registers.lengthT
      registers.lengthRP layout.lengthRP_length.symm,
    constMinus_tCount registers.lengthRP registers.constants
      registers.carry (n + 1) hpositiveRP
      (layout.constants_length.trans layout.lengthRP_length.symm),
    cuccaroSub_tCount registers.lengthSLow registers.lengthRP registers.carry
      (layout.lengthSLow_length.trans layout.lengthRP_length.symm),
    subConstant_tCount registers.lengthT registers.constants registers.carry 2
      (layout.constants_length.trans rfl)]
  rw [layout.lengthRP_lengthT, layout.lengthSLow_lengthT]
  simp [latestPaperTBoundaryTFormula, TBoundaryRegisters.width]
  omega

/-! ## Closed secp256k1 witness -/

private def latestPaperTBoundaryWidthTwoRegisters : TBoundaryRegisters where
  phase2 := 0
  lengthT := [1, 2]
  lengthRP := [3, 4]
  lengthS := [5, 6]
  scratch := [7, 8, 9]

/-- Exact flattened width-two streams.  This regression fixes the pinned helper ordering:
prepare performs add/reflect/subtract/swap, while restore performs swap/reflect/subtract/subtract. -/
theorem latestPaperTBoundary_widthTwo_source_regression :
    prepareLatestPaperTBoundary latestPaperTBoundaryWidthTwoRegisters 4 =
      [.X 8,
       .CX 7 1, .CX 7 9, .CCX 9 1 7,
       .CX 8 2, .CX 8 7, .CCX 7 2 8,
       .CCX 7 2 8, .CX 8 7, .CX 7 2,
       .CCX 9 1 7, .CX 7 9, .CX 9 1, .X 8,
       .X 3, .X 4,
       .CX 3 7, .CX 7 4, .CX 3 7, .X 3,
       .X 7,
       .CX 7 3, .CX 7 9, .CCX 9 3 7,
       .CX 8 4, .CX 8 7, .CCX 7 4 8,
       .CCX 7 4 8, .CX 8 7, .CX 7 4,
       .CCX 9 3 7, .CX 7 9, .CX 9 3, .X 7,
       .CX 9 3, .CX 5 9, .CCX 9 3 5,
       .CX 5 4, .CX 6 5, .CCX 5 4 6,
       .CCX 5 4 6, .CX 6 5, .CX 6 4,
       .CCX 9 3 5, .CX 5 9, .CX 5 3,
       .CX 3 1, .CCX 0 1 3, .CX 3 1,
       .CX 4 2, .CCX 0 2 4, .CX 4 2] ∧
    restoreLatestPaperTBoundary latestPaperTBoundaryWidthTwoRegisters 4 =
      [.CX 3 1, .CCX 0 1 3, .CX 3 1,
       .CX 4 2, .CCX 0 2 4, .CX 4 2,
       .X 3, .X 4,
       .CX 3 7, .CX 7 4, .CX 3 7, .X 3,
       .X 7,
       .CX 7 3, .CX 7 9, .CCX 9 3 7,
       .CX 8 4, .CX 8 7, .CCX 7 4 8,
       .CCX 7 4 8, .CX 8 7, .CX 7 4,
       .CCX 9 3 7, .CX 7 9, .CX 9 3, .X 7,
       .CX 9 3, .CX 5 9, .CCX 9 3 5,
       .CX 5 4, .CX 6 5, .CCX 5 4 6,
       .CCX 5 4 6, .CX 6 5, .CX 6 4,
       .CCX 9 3 5, .CX 5 9, .CX 5 3,
       .X 8,
       .CX 9 1, .CX 7 9, .CCX 9 1 7,
       .CX 7 2, .CX 8 7, .CCX 7 2 8,
       .CCX 7 2 8, .CX 8 7, .CX 8 2,
       .CCX 9 1 7, .CX 7 9, .CX 7 1, .X 8] := by
  constructor <;> rfl

/-- Isolated 38-role allocation for the production `(n, boundary width) = (256, 9)` source
block.  The later whole-step composition may shift these roles without changing this local
certificate. -/
private def latestPaperTBoundarySecp256k1Registers : TBoundaryRegisters where
  phase2 := 0
  lengthT := List.range' 1 9
  lengthRP := List.range' 10 9
  lengthS := List.range' 19 9
  scratch := List.range' 28 10

set_option maxRecDepth 100000 in
private theorem latestPaperTBoundarySecp256k1Layout :
    TBoundaryLayout latestPaperTBoundarySecp256k1Registers := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  decide

set_option maxRecDepth 100000 in
private theorem prepareLatestPaperTBoundary_secp256k1_qubitCount :
    qubitCount
      (prepareLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 38 := by
  decide

set_option maxRecDepth 100000 in
private theorem restoreLatestPaperTBoundary_secp256k1_qubitCount :
    qubitCount
      (restoreLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 38 := by
  decide

/-- Closed production witness for both pinned source blocks.  Each block borrows ten clean
scratch roles, touches exactly 38 wires, and has the same constructor-derived resource count. -/
theorem latestPaperTBoundary_secp256k1_resources :
    latestPaperTBoundarySecp256k1Registers.width = 9 ∧
      latestPaperTBoundarySecp256k1Registers.usedScratch.length = 10 ∧
      latestPaperTBoundarySecp256k1Registers.allWires.length = 38 ∧
      qubitCount
          (prepareLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 38 ∧
      eeaToffoliCount
          (prepareLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 77 ∧
      eeaCnotCount
          (prepareLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 136 ∧
      eeaXCount
          (prepareLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 16 ∧
      tCount
          (prepareLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 539 ∧
      qubitCount
          (restoreLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 38 ∧
      eeaToffoliCount
          (restoreLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 77 ∧
      eeaCnotCount
          (restoreLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 136 ∧
      eeaXCount
          (restoreLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 16 ∧
      tCount
          (restoreLatestPaperTBoundary latestPaperTBoundarySecp256k1Registers 256) = 539 := by
  have hwidth : latestPaperTBoundarySecp256k1Registers.width = 9 := by decide
  have htwo : 2 ≤ latestPaperTBoundarySecp256k1Registers.width := by decide
  have hprepareToffoli := prepareLatestPaperTBoundary_toffoliCount
    latestPaperTBoundarySecp256k1Registers 256
      latestPaperTBoundarySecp256k1Layout htwo
  have hprepareCnot := prepareLatestPaperTBoundary_cnotCount
    latestPaperTBoundarySecp256k1Registers 256
      latestPaperTBoundarySecp256k1Layout htwo
  have hprepareX := prepareLatestPaperTBoundary_xCount
    latestPaperTBoundarySecp256k1Registers 256
      latestPaperTBoundarySecp256k1Layout
  have hprepareT := prepareLatestPaperTBoundary_tCount
    latestPaperTBoundarySecp256k1Registers 256
      latestPaperTBoundarySecp256k1Layout htwo
  have hrestoreToffoli := restoreLatestPaperTBoundary_toffoliCount
    latestPaperTBoundarySecp256k1Registers 256
      latestPaperTBoundarySecp256k1Layout htwo
  have hrestoreCnot := restoreLatestPaperTBoundary_cnotCount
    latestPaperTBoundarySecp256k1Registers 256
      latestPaperTBoundarySecp256k1Layout htwo
  have hrestoreX := restoreLatestPaperTBoundary_xCount
    latestPaperTBoundarySecp256k1Registers 256
      latestPaperTBoundarySecp256k1Layout
  have hrestoreT := restoreLatestPaperTBoundary_tCount
    latestPaperTBoundarySecp256k1Registers 256
      latestPaperTBoundarySecp256k1Layout htwo
  rw [hwidth] at hprepareToffoli hprepareCnot hprepareX hprepareT hrestoreToffoli hrestoreCnot hrestoreX hrestoreT
  have htoffoliFormula : latestPaperTBoundaryToffoliFormula 9 = 77 := by decide
  have hcnotFormula : latestPaperTBoundaryCnotFormula 9 = 136 := by decide
  have hxFormula : latestPaperTBoundaryXFormula 9 256 = 16 := by decide
  have htFormula : latestPaperTBoundaryTFormula 9 = 539 := by decide
  rw [htoffoliFormula] at hprepareToffoli hrestoreToffoli
  rw [hcnotFormula] at hprepareCnot hrestoreCnot
  rw [hxFormula] at hprepareX hrestoreX
  rw [htFormula] at hprepareT hrestoreT
  exact ⟨hwidth, by decide, by decide,
    prepareLatestPaperTBoundary_secp256k1_qubitCount,
    hprepareToffoli, hprepareCnot, hprepareX, hprepareT,
    restoreLatestPaperTBoundary_secp256k1_qubitCount,
    hrestoreToffoli, hrestoreCnot, hrestoreX, hrestoreT⟩

end

end ShorECDLP.Paper2607_13816
