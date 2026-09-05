import ShorECDLP.Submission.«2607_13816».EEA.LengthBlocks
import ShorECDLP.Submission.«2607_13816».EEA.QuotientSwap
import ShorECDLP.Submission.«2607_13816».EEA.Windows

/-!
# Source-exact end-of-iteration Work/length aggregate

This module implements the pinned supplement's
`swap_work_and_len_unary_shared_gate` and its explicit reverse.  The source first swaps the full
Work words under `Ctrl`, then runs the upper and lower length updates serially.  Both length blocks
reuse one low-aux scratch prefix: the constant-arithmetic word/carry and the unary decoder path are
allowed to alias because each block restores them before the next starts.

The surrounding four-step zero tests, `Iter` toggle, and complete indexed Algorithm-3 step remain
the next composition boundary.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

noncomputable section

/-! ## Full-word controlled swap -/

/-- Literal increasing `for i in range(work_size): cswap_toffoli(...)` stream. -/
def controlledWorkSwap (control : Wire) : List Wire → List Wire → Circuit
  | left :: lefts, right :: rights =>
      controlledSwap control left right ++ controlledWorkSwap control lefts rights
  | _, _ => []

/-- Literal reverse-loop stream used by the source inverse. -/
def controlledWorkSwapInverse (control : Wire) (left right : List Wire) : Circuit :=
  controlledWorkSwap control left.reverse right.reverse

theorem controlledWorkSwap_usesOnly
    (control : Wire) : ∀ (left right : List Wire),
    PaperCircuitUsesOnly (control :: left ++ right)
      (controlledWorkSwap control left right) := by
  intro left
  induction left with
  | nil => intro right; simp [controlledWorkSwap, PaperCircuitUsesOnly]
  | cons left lefts ih =>
      intro right
      cases right with
      | nil => simp [controlledWorkSwap, PaperCircuitUsesOnly]
      | cons right rights =>
          rw [controlledWorkSwap]
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

theorem controlledWorkSwapInverse_usesOnly
    (control : Wire) (left right : List Wire) :
    PaperCircuitUsesOnly (control :: left ++ right)
      (controlledWorkSwapInverse control left right) := by
  apply (controlledWorkSwap_usesOnly control left.reverse right.reverse).mono
  intro wire hwire
  simp only [List.mem_cons, List.mem_append, List.mem_reverse] at hwire ⊢
  exact hwire

@[simp]
theorem controlledWorkSwap_HPFree
    (control : Wire) : ∀ (left right : List Wire),
    HPFree (controlledWorkSwap control left right) := by
  intro left
  induction left with
  | nil => intro right; simp [controlledWorkSwap]
  | cons left lefts ih =>
      intro right
      cases right with
      | nil => simp [controlledWorkSwap]
      | cons right rights => simp [controlledWorkSwap, ih]

@[simp]
theorem controlledWorkSwapInverse_HPFree
    (control : Wire) (left right : List Wire) :
    HPFree (controlledWorkSwapInverse control left right) := by
  simp [controlledWorkSwapInverse]

theorem controlledWorkSwap_wellFormed
    (control : Wire) : ∀ (left right : List Wire),
    left.length = right.length →
    (control :: left ++ right).Nodup →
    CircuitWellFormed (controlledWorkSwap control left right) := by
  intro left
  induction left with
  | nil =>
      intro right hlength
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      simp [controlledWorkSwap]
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
          rw [controlledWorkSwap, circuitWellFormed_append]
          exact ⟨controlledSwap_wellFormed control left right hcl hcr hlr,
            ih rights htailLength htailNodup⟩

theorem controlledWorkSwapInverse_wellFormed
    (control : Wire) (left right : List Wire)
    (hlength : left.length = right.length)
    (hlayout : (control :: left ++ right).Nodup) :
    CircuitWellFormed (controlledWorkSwapInverse control left right) := by
  apply controlledWorkSwap_wellFormed
  · simpa using hlength
  · have hcontrol := (List.nodup_cons.mp hlayout).1
    obtain ⟨hleft, hright, hcross⟩ :=
      List.nodup_append.mp (List.nodup_cons.mp hlayout).2
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rcases List.mem_append.mp hmem with hleftMem | hrightMem
      · apply hcontrol
        exact List.mem_append_left right (by simpa using hleftMem)
      · apply hcontrol
        exact List.mem_append_right left (by simpa using hrightMem)
    · apply List.nodup_append.mpr
      refine ⟨List.nodup_reverse.mpr hleft,
        List.nodup_reverse.mpr hright, ?_⟩
      intro a ha b hb
      exact hcross a (by simpa using ha) b (by simpa using hb)

theorem controlledWorkSwap_toffoliCount
    (control : Wire) : ∀ (left right : List Wire),
    left.length = right.length →
    eeaToffoliCount (controlledWorkSwap control left right) = left.length := by
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
          rw [controlledWorkSwap, eeaToffoliCount_append,
            controlledSwap_toffoliCount, ih rights (by simpa using hlength)]
          simp
          omega

theorem controlledWorkSwap_cnotCount
    (control : Wire) : ∀ (left right : List Wire),
    left.length = right.length →
    eeaCnotCount (controlledWorkSwap control left right) = 2 * left.length := by
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
          rw [controlledWorkSwap, eeaCnotCount_append,
            controlledSwap_cnotCount, ih rights (by simpa using hlength)]
          simp
          omega

@[simp]
theorem controlledWorkSwap_xCount
    (control : Wire) : ∀ (left right : List Wire),
    eeaXCount (controlledWorkSwap control left right) = 0 := by
  intro left
  induction left with
  | nil => intro right; rfl
  | cons left lefts ih =>
      intro right
      cases right with
      | nil => rfl
      | cons right rights =>
          rw [controlledWorkSwap, eeaXCount_append,
            controlledSwap_xCount, ih rights]

theorem controlledWorkSwap_tCount
    (control : Wire) : ∀ (left right : List Wire),
    left.length = right.length →
    tCount (controlledWorkSwap control left right) = 7 * left.length := by
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
          rw [controlledWorkSwap, tCount_append,
            controlledSwap_tCount, ih rights (by simpa using hlength)]
          simp
          omega

theorem controlledWorkSwapInverse_toffoliCount
    (control : Wire) (left right : List Wire)
    (hlength : left.length = right.length) :
    eeaToffoliCount (controlledWorkSwapInverse control left right) = left.length := by
  rw [controlledWorkSwapInverse,
    controlledWorkSwap_toffoliCount control left.reverse right.reverse (by simpa)]
  simp

theorem controlledWorkSwapInverse_cnotCount
    (control : Wire) (left right : List Wire)
    (hlength : left.length = right.length) :
    eeaCnotCount (controlledWorkSwapInverse control left right) = 2 * left.length := by
  rw [controlledWorkSwapInverse,
    controlledWorkSwap_cnotCount control left.reverse right.reverse (by simpa)]
  simp

@[simp]
theorem controlledWorkSwapInverse_xCount
    (control : Wire) (left right : List Wire) :
    eeaXCount (controlledWorkSwapInverse control left right) = 0 := by
  simp [controlledWorkSwapInverse]

theorem controlledWorkSwapInverse_tCount
    (control : Wire) (left right : List Wire)
    (hlength : left.length = right.length) :
    tCount (controlledWorkSwapInverse control left right) = 7 * left.length := by
  rw [controlledWorkSwapInverse,
    controlledWorkSwap_tCount control left.reverse right.reverse (by simpa)]
  simp

private theorem endIteration_wireValues_congr
    (wires : List Wire) (left right : BasisState)
    (hagree : ∀ wire, wire ∈ wires → left wire = right wire) :
    wireValues wires left = wireValues wires right := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq]
      exact ⟨hagree wire (by simp), ih (fun next hnext ↦
        hagree next (by simp [hnext]))⟩

private theorem endIteration_wireValues_eq_at
    (wires : List Wire) (left right : BasisState)
    (hvalues : wireValues wires left = wireValues wires right)
    (wire : Wire) (hwire : wire ∈ wires) : left wire = right wire := by
  induction wires with
  | nil => simp at hwire
  | cons head tail ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq] at hvalues
      rcases List.mem_cons.mp hwire with rfl | hwire
      · exact hvalues.1
      · exact ih hvalues.2 hwire

/-- Exact pointwise action of the increasing source Fredkin loop. -/
theorem controlledWorkSwap_correct
    (control : Wire) : ∀ (left right : List Wire) (state : BasisState),
    left.length = right.length →
    (control :: left ++ right).Nodup →
    let after := run (controlledWorkSwap control left right) state
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
      simp [controlledWorkSwap, wireValues]
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
            apply endIteration_wireValues_congr
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
            apply endIteration_wireValues_congr
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
              run (controlledWorkSwap control lefts rights) firstState left =
                firstState left := by
            apply (controlledWorkSwap_usesOnly control lefts rights).preservesOutside
            intro hmem
            simp only [List.mem_cons, List.mem_append] at hmem
            rcases hmem with (h | hmem) | hmem
            · exact hnd.1.1 h.symm
            · exact hnd.2.1.1 hmem
            · exact hnd.2.1.2.2 hmem
          have hrightFinal :
              run (controlledWorkSwap control lefts rights) firstState right =
                firstState right := by
            apply (controlledWorkSwap_usesOnly control lefts rights).preservesOutside
            intro hmem
            simp only [List.mem_cons, List.mem_append] at hmem
            rcases hmem with (h | hmem) | hmem
            · exact hnd.1.2.2.1 h.symm
            · exact hrightLefts hmem
            · exact hright hmem
          rw [controlledWorkSwap, Classical.run_append]
          change
            (run (controlledWorkSwap control lefts rights) firstState left ::
                wireValues lefts
                  (run (controlledWorkSwap control lefts rights) firstState) =
              if state control then
                state right :: wireValues rights state
              else state left :: wireValues lefts state) ∧
            (run (controlledWorkSwap control lefts rights) firstState right ::
                wireValues rights
                  (run (controlledWorkSwap control lefts rights) firstState) =
              if state control then
                state left :: wireValues lefts state
              else state right :: wireValues rights state)
          rw [hleftFinal, hrightFinal, hrecursive.1, hrecursive.2,
            hcontrolFirst, hleftsFirst, hrightsFirst]
          dsimp only [firstState]
          rw [hswap]
          cases hc : state control <;>
            simp [upd, hnd.2.1.2.1]

/-- Reversing the disjoint source loop does not change its full-word swap action. -/
theorem controlledWorkSwapInverse_correct
    (control : Wire) (left right : List Wire) (state : BasisState)
    (hlength : left.length = right.length)
    (hlayout : (control :: left ++ right).Nodup) :
    let after := run (controlledWorkSwapInverse control left right) state
    wireValues left after =
        (if state control then wireValues right state else wireValues left state) ∧
      wireValues right after =
        (if state control then wireValues left state else wireValues right state) := by
  have hcontrol := (List.nodup_cons.mp hlayout).1
  obtain ⟨hleft, hright, hcross⟩ :=
    List.nodup_append.mp (List.nodup_cons.mp hlayout).2
  have hreverse : (control :: left.reverse ++ right.reverse).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rcases List.mem_append.mp hmem with hleftMem | hrightMem
      · exact hcontrol (List.mem_append_left right (by simpa using hleftMem))
      · exact hcontrol (List.mem_append_right left (by simpa using hrightMem))
    · apply List.nodup_append.mpr
      refine ⟨List.nodup_reverse.mpr hleft,
        List.nodup_reverse.mpr hright, ?_⟩
      intro a ha b hb
      exact hcross a (by simpa using ha) b (by simpa using hb)
  have hcorrect := controlledWorkSwap_correct control left.reverse right.reverse state
    (by simpa using hlength) hreverse
  have hfirst := congrArg List.reverse hcorrect.1
  have hsecond := congrArg List.reverse hcorrect.2
  cases hc : state control <;>
    simp [controlledWorkSwapInverse, wireValues, hc] at hfirst hsecond ⊢ <;>
    exact ⟨hfirst, hsecond⟩

theorem controlledWorkSwap_control
    (control : Wire) : ∀ (left right : List Wire) (state : BasisState),
    control ∉ left → control ∉ right →
    run (controlledWorkSwap control left right) state control = state control := by
  intro left
  induction left with
  | nil => intro right state _ _; simp [controlledWorkSwap]
  | cons left lefts ih =>
      intro right state hleft hright
      cases right with
      | nil => simp [controlledWorkSwap]
      | cons right rights =>
          simp only [List.mem_cons, not_or] at hleft hright
          rw [controlledWorkSwap, Classical.run_append,
            ih rights _ hleft.2 hright.2]
          simp [controlledSwap, run, applyGate, upd, hleft.1, hright.1]

theorem controlledWorkSwapInverse_control
    (control : Wire) (left right : List Wire) (state : BasisState)
    (hleft : control ∉ left) (hright : control ∉ right) :
    run (controlledWorkSwapInverse control left right) state control = state control := by
  apply controlledWorkSwap_control control left.reverse right.reverse state
  · simpa using hleft
  · simpa using hright

theorem controlledWorkSwap_preservesOutsideWords
    (control : Wire) (left right : List Wire) (state : BasisState)
    (hcontrolLeft : control ∉ left) (hcontrolRight : control ∉ right) :
    ∀ wire, wire ∉ left → wire ∉ right →
      run (controlledWorkSwap control left right) state wire = state wire := by
  intro wire hleft hright
  by_cases hwire : wire = control
  · subst wire
    exact controlledWorkSwap_control control left right state
      hcontrolLeft hcontrolRight
  · apply (controlledWorkSwap_usesOnly control left right).preservesOutside
    simp only [List.mem_cons, List.mem_append, not_or]
    exact ⟨⟨hwire, hleft⟩, hright⟩

theorem controlledWorkSwapInverse_preservesOutsideWords
    (control : Wire) (left right : List Wire) (state : BasisState)
    (hcontrolLeft : control ∉ left) (hcontrolRight : control ∉ right) :
    ∀ wire, wire ∉ left → wire ∉ right →
      run (controlledWorkSwapInverse control left right) state wire = state wire := by
  intro wire hleft hright
  by_cases hwire : wire = control
  · subst wire
    exact controlledWorkSwapInverse_control control left right state
      hcontrolLeft hcontrolRight
  · apply (controlledWorkSwapInverse_usesOnly control left right).preservesOutside
    simp only [List.mem_cons, List.mem_append, not_or]
    exact ⟨⟨hwire, hleft⟩, hright⟩

/-! ## Source register and scratch projections -/

structure EndIterationRegisters where
  control : Wire
  work1 : List Wire
  work2 : List Wire
  lengthT : List Wire
  lengthRP : List Wire
  scratch : List Wire
deriving Repr

structure EndIterationWindows where
  k4 : Nat
  K4 : Nat
  k5 : Nat
  K5 : Nat
deriving DecidableEq, Repr

/-- The two source windows selected by the indexed paper scheduler. -/
def endIterationWindowsAt (n T : Nat) : EndIterationWindows :=
  let windows := certifiedActiveWindows n T
  ⟨windows.lengthT.start, windows.lengthT.stop,
    windows.lengthRPrime.start, windows.lengthRPrime.stop⟩

def EndIterationWindows.K5Decode
    (windows : EndIterationWindows) (n : Nat) : Nat :=
  min (windows.K5 + 1) (n + 3)

def EndIterationRegisters.width (registers : EndIterationRegisters) : Nat :=
  registers.lengthT.length

def EndIterationRegisters.work1At
    (registers : EndIterationRegisters) (label : Nat) : Wire :=
  registers.work1.getD (label - 1) 0

def EndIterationRegisters.work2At
    (registers : EndIterationRegisters) (label : Nat) : Wire :=
  registers.work2.getD (label - 1) 0

private def EndIterationRegisters.treeRegisters
    (index : List Wire) : QuotientSwapRegisters where
  control := 0
  sign := 0
  work1 := []
  lengthT := []
  lengthQ := index
  scratch := []

/-- Exact highest-varying-bit tree constructed by the pinned upper writer. -/
def EndIterationRegisters.upperTree
    (registers : EndIterationRegisters) (windows : EndIterationWindows) :
    UnaryActionTree :=
  quotientSwapTree (EndIterationRegisters.treeRegisters registers.lengthRP)
    windows.k4 windows.K4

/-- Exact highest-varying-bit tree constructed by the pinned lower writer. -/
def EndIterationRegisters.lowerTree
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) : UnaryActionTree :=
  quotientSwapTree (EndIterationRegisters.treeRegisters registers.lengthT)
    windows.k5 (windows.K5Decode n)

private theorem sourceRangeTree_visitLabels
    (index : List Wire) {k K : Nat} (hkK : k ≤ K) :
    (quotientSwapTree (EndIterationRegisters.treeRegisters index) k K).visitLabels .inc =
      zeroMapLabels k K := by
  rw [UnaryActionTree.visitLabels_inc,
    quotientSwapTree_labels (EndIterationRegisters.treeRegisters index) hkK,
    zeroMapLabels_eq_range', quotientSwapLabels]
  exact (List.toFinset_sort (r := (· ≤ ·)) List.nodup_range').2
    (List.pairwise_le_range' 1)

theorem EndIterationRegisters.upperTree_visitLabels
    (registers : EndIterationRegisters) (windows : EndIterationWindows)
    (hkK : windows.k4 ≤ windows.K4) :
    (registers.upperTree windows).visitLabels .inc =
      zeroMapLabels windows.k4 windows.K4 := by
  exact sourceRangeTree_visitLabels registers.lengthRP hkK

theorem EndIterationRegisters.lowerTree_visitLabels
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hkK : windows.k5 ≤ windows.K5Decode n) :
    (registers.lowerTree n windows).visitLabels .inc =
      zeroMapLabels windows.k5 (windows.K5Decode n) := by
  exact sourceRangeTree_visitLabels registers.lengthT hkK

private theorem sourceRangeTree_routeLabel_eq
    (index : List Wire) {k K : Nat} (state : BasisState)
    (hkK : k ≤ K)
    (hwidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels k K).toFinset ≤ index.length)
    (hvalue : boolWordToNat (wireValues index state) ∈ zeroMapLabels k K) :
    (quotientSwapTree (EndIterationRegisters.treeRegisters index) k K).routeLabel state =
      boolWordToNat (wireValues index state) := by
  apply quotientSwapTree_routeLabel_eq_of_width
    (EndIterationRegisters.treeRegisters index) state hkK hwidth
  simpa [zeroMapLabels_eq_range', quotientSwapLabels] using hvalue

/-- The exact upper source tree decodes the transformed right boundary whenever its value lies
in the certified active window. -/
theorem EndIterationRegisters.upperTree_routeLabel_eq
    (registers : EndIterationRegisters) (windows : EndIterationWindows)
    (state : BasisState) (hkK : windows.k4 ≤ windows.K4)
    (hwidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels windows.k4 windows.K4).toFinset ≤
        registers.lengthRP.length)
    (hvalue : boolWordToNat (wireValues registers.lengthRP state) ∈
      zeroMapLabels windows.k4 windows.K4) :
    (registers.upperTree windows).routeLabel state =
      boolWordToNat (wireValues registers.lengthRP state) :=
  sourceRangeTree_routeLabel_eq registers.lengthRP state hkK hwidth hvalue

/-- The exact lower source tree decodes the transformed left boundary whenever its value lies
in the certified active window. -/
theorem EndIterationRegisters.lowerTree_routeLabel_eq
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) (state : BasisState)
    (hkK : windows.k5 ≤ windows.K5Decode n)
    (hwidth : DualUnaryActionTree.sourceWidth
      (quotientSwapLabels windows.k5 (windows.K5Decode n)).toFinset ≤
        registers.lengthT.length)
    (hvalue : boolWordToNat (wireValues registers.lengthT state) ∈
      zeroMapLabels windows.k5 (windows.K5Decode n)) :
    (registers.lowerTree n windows).routeLabel state =
      boolWordToNat (wireValues registers.lengthT state) :=
  sourceRangeTree_routeLabel_eq registers.lengthT state hkK hwidth hvalue

def endIterationUnaryDepth (k K : Nat) : Nat :=
  quotientSwapUnaryDepth k K

def endIterationLengthScratchSize (width k K : Nat) : Nat :=
  max (width + 1) (endIterationUnaryDepth k K + 2)

def endIterationScratchSize
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) : Nat :=
  max
    (endIterationLengthScratchSize registers.width windows.k4 windows.K4)
    (endIterationLengthScratchSize registers.width windows.k5 (windows.K5Decode n))

def EndIterationRegisters.path
    (registers : EndIterationRegisters) (k K : Nat) : List Wire :=
  registers.scratch.take (endIterationUnaryDepth k K)

def EndIterationRegisters.rangeAccumulator
    (registers : EndIterationRegisters) (k K : Nat) : Wire :=
  registers.scratch.getD (endIterationUnaryDepth k K) 0

def EndIterationRegisters.temporary
    (registers : EndIterationRegisters) (k K : Nat) : Wire :=
  registers.scratch.getD (endIterationUnaryDepth k K + 1) 0

def EndIterationRegisters.constants
    (registers : EndIterationRegisters) : List Wire :=
  registers.scratch.take registers.width

def EndIterationRegisters.carry
    (registers : EndIterationRegisters) : Wire :=
  registers.scratch.getD registers.width 0

def EndIterationRegisters.allWires
    (registers : EndIterationRegisters) : List Wire :=
  registers.control :: registers.work1 ++ registers.work2 ++
    registers.lengthT ++ registers.lengthRP ++ registers.scratch

def EndIterationReady
    (registers : EndIterationRegisters) (state : BasisState) : Prop :=
  Clean registers.scratch state

/-! ## Gate-independent aggregate recurrence -/

/-- The source's full Work swap, stated only on the two Boolean words. -/
def endIterationSwappedWorkWords
    (registers : EndIterationRegisters) (state : BasisState) :
    List Bool × List Bool :=
  if state registers.control then
    (wireValues registers.work2 state, wireValues registers.work1 state)
  else
    (wireValues registers.work1 state, wireValues registers.work2 state)

/-- Upper-writer range bits read from an already selected Work word.  Labels are one-based in
the pinned Python source. -/
def endIterationUpperRangeBits
    (enabled : Bool) (boundary : Nat) (labels : List Nat)
    (work : List Bool) : List Bool :=
  labels.map fun label =>
    enabled && decide (label ≤ boundary) && work.getD (label - 1) false

/-- Lower-writer range bits read from an already selected Work word. -/
def endIterationLowerRangeBits
    (enabled : Bool) (boundary : Nat) (labels : List Nat)
    (work : List Bool) : List Bool :=
  labels.map fun label =>
    enabled && decide (boundary ≤ label) && work.getD (label - 1) false

/-- Pure Boolean-word recurrence of `swap_work_and_len_unary_shared_gate`. -/
def endIterationLengthWords
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) (boundary4 boundary5 : Nat)
    (state : BasisState) : List Bool × List Bool :=
  let work := endIterationSwappedWorkWords registers state
  let lengthT :=
    highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
      (state registers.control)
      (endIterationUpperRangeBits (state registers.control) boundary4
        (zeroMapLabels windows.k4 windows.K4) work.1)
      (highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
        (state registers.control)
        (endIterationUpperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) work.2)
        (wireValues registers.lengthT state))
  let lengthRP :=
    rightLengthWordAction n registers.lengthRP.length windows.k5
      (windows.K5Decode n) (state registers.control)
      (endIterationLowerRangeBits (state registers.control) boundary5
        (zeroMapLabels windows.k5 (windows.K5Decode n)) work.2)
      (rightLengthWordAction n registers.lengthRP.length windows.k5
        (windows.K5Decode n) (state registers.control)
        (endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) work.1)
        (wireValues registers.lengthRP state))
  (lengthT, lengthRP)

/-- Pure recurrence of the pinned explicit reverse before its final full-Work swap. -/
def endIterationInverseLengthWords
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) (boundary4 boundary5 : Nat)
    (state : BasisState) : List Bool × List Bool :=
  let lengthT :=
    highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
      (state registers.control)
      (endIterationUpperRangeBits (state registers.control) boundary4
        (zeroMapLabels windows.k4 windows.K4) (wireValues registers.work1 state))
      (highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
        (state registers.control)
        (endIterationUpperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) (wireValues registers.work2 state))
        (wireValues registers.lengthT state))
  let lengthRP :=
    rightLengthWordAction n registers.lengthRP.length windows.k5
      (windows.K5Decode n) (state registers.control)
      (endIterationLowerRangeBits (state registers.control) boundary5
        (zeroMapLabels windows.k5 (windows.K5Decode n))
        (wireValues registers.work2 state))
      (rightLengthWordAction n registers.lengthRP.length windows.k5
        (windows.K5Decode n) (state registers.control)
        (endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (wireValues registers.work1 state))
        (wireValues registers.lengthRP state))
  (lengthT, lengthRP)

/-- Complete source-domain contract.  The two `SharedLengthBlockLayout` fields are the exact
serial-aliasing boundary: they permit `constants`/`carry` to be the same wires as the decoder
scratch while keeping live data registers separated. -/
structure EndIterationLayout
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) : Prop where
  k4_positive : 0 < windows.k4
  k4_le_K4 : windows.k4 ≤ windows.K4
  K4_le_work : windows.K4 ≤ n + 3
  k5_positive : 0 < windows.k5
  k5_le_decode : windows.k5 ≤ windows.K5Decode n
  work1_length : registers.work1.length = n + 3
  work2_length : registers.work2.length = n + 3
  width_positive : 0 < registers.width
  lengthRP_length : registers.lengthRP.length = registers.width
  scratch_capacity : endIterationScratchSize registers n windows ≤ registers.scratch.length
  physical : registers.allWires.Nodup
  upper : SharedLengthBlockLayout windows.k4 windows.K4 (registers.upperTree windows) registers.control
    (registers.rangeAccumulator windows.k4 windows.K4)
    (registers.temporary windows.k4 windows.K4) registers.carry
    (registers.path windows.k4 windows.K4)
    registers.work1At registers.work2At registers.lengthRP registers.lengthT
    registers.constants
  lower : SharedLengthBlockLayout windows.k5 (windows.K5Decode n) (registers.lowerTree n windows) registers.control
    (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
    (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
    (registers.path windows.k5 (windows.K5Decode n))
    registers.work1At registers.work2At registers.lengthT registers.lengthRP
    registers.constants

private theorem endIteration_full_split
    {registers : EndIterationRegisters}
    (hphysical : registers.allWires.Nodup) :
    ((registers.control :: registers.work1 ++ registers.work2) ++
      (registers.lengthT ++ registers.lengthRP ++ registers.scratch)).Nodup := by
  simpa [EndIterationRegisters.allWires, List.append_assoc] using hphysical

private theorem EndIterationLayout.work_nodup
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows) :
    (registers.control :: registers.work1 ++ registers.work2).Nodup :=
  (List.nodup_append.mp (endIteration_full_split hlayout.physical)).1

private theorem EndIterationLayout.work_not_rest
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {work rest : Wire}
    (hwork : work ∈ registers.control :: registers.work1 ++ registers.work2)
    (hrest : rest ∈ registers.lengthT ++ registers.lengthRP ++ registers.scratch) :
    work ≠ rest :=
  (List.nodup_append.mp (endIteration_full_split hlayout.physical)).2.2
    work hwork rest hrest

private theorem EndIterationLayout.lengthT_not_tail
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {left right : Wire} (hleft : left ∈ registers.lengthT)
    (hright : right ∈ registers.lengthRP ++ registers.scratch) :
    left ≠ right := by
  have hrest := (List.nodup_append.mp
    (endIteration_full_split hlayout.physical)).2.1
  obtain ⟨hlengths, hscratch, hcrossScratch⟩ := List.nodup_append.mp hrest
  obtain ⟨hlengthT, hlengthRP, hcrossRP⟩ := List.nodup_append.mp hlengths
  rcases List.mem_append.mp hright with hrightRP | hrightScratch
  · exact hcrossRP left hleft right hrightRP
  · exact hcrossScratch left (List.mem_append_left _ hleft)
      right hrightScratch

private theorem EndIterationLayout.lengthRP_not_scratch
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {left right : Wire} (hleft : left ∈ registers.lengthRP)
    (hright : right ∈ registers.scratch) : left ≠ right := by
  have hrest := (List.nodup_append.mp
    (endIteration_full_split hlayout.physical)).2.1
  obtain ⟨hlengths, hscratch, hcrossScratch⟩ := List.nodup_append.mp hrest
  exact hcrossScratch left (List.mem_append_right _ hleft) right hright

private theorem endIteration_list_getD_mem
    (wires : List Wire) (index : Nat) (hindex : index < wires.length) :
    wires.getD index 0 ∈ wires := by
  rw [List.getD_eq_getElem wires 0 hindex]
  exact List.getElem_mem hindex

private theorem EndIterationLayout.work1At_mem
    {registers : EndIterationRegisters} {n label : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    (hpositive : 0 < label) (hupper : label ≤ n + 3) :
    registers.work1At label ∈ registers.work1 := by
  apply endIteration_list_getD_mem
  rw [hlayout.work1_length]
  omega

private theorem EndIterationLayout.work2At_mem
    {registers : EndIterationRegisters} {n label : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    (hpositive : 0 < label) (hupper : label ≤ n + 3) :
    registers.work2At label ∈ registers.work2 := by
  apply endIteration_list_getD_mem
  rw [hlayout.work2_length]
  omega

private theorem EndIterationLayout.workWire_not_lengthT
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire}
    (hwire : wire ∈ registers.control :: registers.work1 ++ registers.work2) :
    wire ∉ registers.lengthT := by
  intro htarget
  exact hlayout.work_not_rest hwire (by simp [htarget]) rfl

private theorem EndIterationLayout.workWire_not_lengthRP
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire}
    (hwire : wire ∈ registers.control :: registers.work1 ++ registers.work2) :
    wire ∉ registers.lengthRP := by
  intro htarget
  exact hlayout.work_not_rest hwire (by simp [htarget]) rfl

private theorem EndIterationLayout.scratch_not_lengthT
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire} (hwire : wire ∈ registers.scratch) :
    wire ∉ registers.lengthT := by
  intro htarget
  exact hlayout.lengthT_not_tail htarget (by simp [hwire]) rfl

private theorem EndIterationLayout.scratch_not_lengthRP
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire} (hwire : wire ∈ registers.scratch) :
    wire ∉ registers.lengthRP := by
  intro htarget
  exact hlayout.lengthRP_not_scratch htarget hwire rfl

private theorem EndIterationLayout.scratch_not_work1
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire} (hwire : wire ∈ registers.scratch) :
    wire ∉ registers.work1 := by
  intro htarget
  have hwork : wire ∈ registers.control :: registers.work1 ++ registers.work2 := by
    exact List.mem_append_left registers.work2
      (List.mem_cons_of_mem registers.control htarget)
  have hrest : wire ∈ registers.lengthT ++ registers.lengthRP ++ registers.scratch := by
    exact List.mem_append_right (registers.lengthT ++ registers.lengthRP) hwire
  exact hlayout.work_not_rest hwork hrest rfl

private theorem EndIterationLayout.scratch_not_work2
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire} (hwire : wire ∈ registers.scratch) :
    wire ∉ registers.work2 := by
  intro htarget
  have hwork : wire ∈ registers.control :: registers.work1 ++ registers.work2 := by
    exact List.mem_append_right (registers.control :: registers.work1) htarget
  have hrest : wire ∈ registers.lengthT ++ registers.lengthRP ++ registers.scratch := by
    exact List.mem_append_right (registers.lengthT ++ registers.lengthRP) hwire
  exact hlayout.work_not_rest hwork hrest rfl

private theorem EndIterationLayout.lengthT_not_work1
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire} (hwire : wire ∈ registers.lengthT) :
    wire ∉ registers.work1 := by
  intro htarget
  have hwork : wire ∈ registers.control :: registers.work1 ++ registers.work2 :=
    List.mem_append_left registers.work2
      (List.mem_cons_of_mem registers.control htarget)
  have hrest : wire ∈ registers.lengthT ++ registers.lengthRP ++ registers.scratch :=
    List.mem_append_left registers.scratch
      (List.mem_append_left registers.lengthRP hwire)
  exact hlayout.work_not_rest hwork hrest rfl

private theorem EndIterationLayout.lengthT_not_work2
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire} (hwire : wire ∈ registers.lengthT) :
    wire ∉ registers.work2 := by
  intro htarget
  have hwork : wire ∈ registers.control :: registers.work1 ++ registers.work2 :=
    List.mem_append_right (registers.control :: registers.work1) htarget
  have hrest : wire ∈ registers.lengthT ++ registers.lengthRP ++ registers.scratch :=
    List.mem_append_left registers.scratch
      (List.mem_append_left registers.lengthRP hwire)
  exact hlayout.work_not_rest hwork hrest rfl

private theorem EndIterationLayout.lengthRP_not_work1
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire} (hwire : wire ∈ registers.lengthRP) :
    wire ∉ registers.work1 := by
  intro htarget
  have hwork : wire ∈ registers.control :: registers.work1 ++ registers.work2 :=
    List.mem_append_left registers.work2
      (List.mem_cons_of_mem registers.control htarget)
  have hrest : wire ∈ registers.lengthT ++ registers.lengthRP ++ registers.scratch :=
    List.mem_append_left registers.scratch
      (List.mem_append_right registers.lengthT hwire)
  exact hlayout.work_not_rest hwork hrest rfl

private theorem EndIterationLayout.lengthRP_not_work2
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire} (hwire : wire ∈ registers.lengthRP) :
    wire ∉ registers.work2 := by
  intro htarget
  have hwork : wire ∈ registers.control :: registers.work1 ++ registers.work2 :=
    List.mem_append_right (registers.control :: registers.work1) htarget
  have hrest : wire ∈ registers.lengthT ++ registers.lengthRP ++ registers.scratch :=
    List.mem_append_left registers.scratch
      (List.mem_append_right registers.lengthT hwire)
  exact hlayout.work_not_rest hwork hrest rfl

private theorem EndIterationLayout.lengthT_not_lengthRP
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {wire : Wire} (hwire : wire ∈ registers.lengthT) :
    wire ∉ registers.lengthRP := by
  intro htarget
  exact hlayout.lengthT_not_tail hwire (by simp [htarget]) rfl

private theorem EndIterationLayout.width_lt_scratch
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows) :
    registers.width < registers.scratch.length := by
  have hupper : registers.width + 1 ≤
      endIterationLengthScratchSize registers.width windows.k4 windows.K4 := by
    simp [endIterationLengthScratchSize]
  have hmax : endIterationLengthScratchSize registers.width windows.k4 windows.K4 ≤
      endIterationScratchSize registers n windows := by
    simp [endIterationScratchSize]
  have hcapacity := hlayout.scratch_capacity
  omega

private theorem EndIterationLayout.depth_succ_lt_scratch4
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows) :
    endIterationUnaryDepth windows.k4 windows.K4 + 1 < registers.scratch.length := by
  have hupper : endIterationUnaryDepth windows.k4 windows.K4 + 2 ≤
      endIterationLengthScratchSize registers.width windows.k4 windows.K4 := by
    simp [endIterationLengthScratchSize]
  have hmax : endIterationLengthScratchSize registers.width windows.k4 windows.K4 ≤
      endIterationScratchSize registers n windows := by
    simp [endIterationScratchSize]
  have hcapacity := hlayout.scratch_capacity
  omega

private theorem EndIterationLayout.depth_succ_lt_scratch5
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows) :
    endIterationUnaryDepth windows.k5 (windows.K5Decode n) + 1 <
      registers.scratch.length := by
  have hupper : endIterationUnaryDepth windows.k5 (windows.K5Decode n) + 2 ≤
      endIterationLengthScratchSize registers.width windows.k5 (windows.K5Decode n) := by
    simp [endIterationLengthScratchSize]
  have hmax : endIterationLengthScratchSize registers.width windows.k5
      (windows.K5Decode n) ≤ endIterationScratchSize registers n windows := by
    simp [endIterationScratchSize]
  have hcapacity := hlayout.scratch_capacity
  omega

private theorem EndIterationLayout.constants_length
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows) :
    registers.constants.length = registers.width := by
  simp [EndIterationRegisters.constants, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hlayout.width_lt_scratch)]

private theorem EndIterationLayout.clean_components4
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {state : BasisState} (hready : EndIterationReady registers state) :
    Clean (registers.constants ++ [registers.carry]) state ∧
      Clean (registers.path windows.k4 windows.K4) state ∧
      state (registers.rangeAccumulator windows.k4 windows.K4) = false ∧
      state (registers.temporary windows.k4 windows.K4) = false := by
  have hcarry : registers.carry ∈ registers.scratch := by
    exact endIteration_list_getD_mem registers.scratch registers.width
      hlayout.width_lt_scratch
  have hrange : registers.rangeAccumulator windows.k4 windows.K4 ∈
      registers.scratch := by
    exact endIteration_list_getD_mem registers.scratch
      (endIterationUnaryDepth windows.k4 windows.K4) (by
        have hbound := hlayout.depth_succ_lt_scratch4
        omega)
  have htemporary : registers.temporary windows.k4 windows.K4 ∈
      registers.scratch := by
    exact endIteration_list_getD_mem registers.scratch
      (endIterationUnaryDepth windows.k4 windows.K4 + 1)
      hlayout.depth_succ_lt_scratch4
  refine ⟨?_, ?_, hready _ hrange, hready _ htemporary⟩
  · intro wire hwire
    rcases List.mem_append.mp hwire with hconstant | hcarryMem
    · exact hready wire (List.mem_of_mem_take hconstant)
    · simp only [List.mem_singleton] at hcarryMem
      subst wire
      exact hready _ hcarry
  · intro wire hwire
    exact hready wire (List.mem_of_mem_take hwire)

private theorem EndIterationLayout.clean_components5
    {registers : EndIterationRegisters} {n : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    {state : BasisState} (hready : EndIterationReady registers state) :
    Clean (registers.constants ++ [registers.carry]) state ∧
      Clean (registers.path windows.k5 (windows.K5Decode n)) state ∧
      state (registers.rangeAccumulator windows.k5 (windows.K5Decode n)) = false ∧
      state (registers.temporary windows.k5 (windows.K5Decode n)) = false := by
  have hcarry : registers.carry ∈ registers.scratch := by
    exact endIteration_list_getD_mem registers.scratch registers.width
      hlayout.width_lt_scratch
  have hrange : registers.rangeAccumulator windows.k5 (windows.K5Decode n) ∈
      registers.scratch := by
    exact endIteration_list_getD_mem registers.scratch
      (endIterationUnaryDepth windows.k5 (windows.K5Decode n)) (by
        have hbound := hlayout.depth_succ_lt_scratch5
        omega)
  have htemporary : registers.temporary windows.k5 (windows.K5Decode n) ∈
      registers.scratch := by
    exact endIteration_list_getD_mem registers.scratch
      (endIterationUnaryDepth windows.k5 (windows.K5Decode n) + 1)
      hlayout.depth_succ_lt_scratch5
  refine ⟨?_, ?_, hready _ hrange, hready _ htemporary⟩
  · intro wire hwire
    rcases List.mem_append.mp hwire with hconstant | hcarryMem
    · exact hready wire (List.mem_of_mem_take hconstant)
    · simp only [List.mem_singleton] at hcarryMem
      subst wire
      exact hready _ hcarry
  · intro wire hwire
    exact hready wire (List.mem_of_mem_take hwire)

private theorem endIteration_wireValues_getD
    (wires : List Wire) (state : BasisState) (index : Nat)
    (hindex : index < wires.length) :
    (wireValues wires state).getD index false = state (wires.getD index 0) := by
  have hvalues : index < (wireValues wires state).length := by
    simpa only [wireValues, List.length_map] using hindex
  rw [List.getD_eq_getElem _ _ hvalues,
    List.getD_eq_getElem _ _ hindex]
  simp only [wireValues, List.getElem_map]

private theorem endIteration_upperRangeBits_wireValues
    (enabled : Bool) (boundary : Nat) (labels : List Nat)
    (wires : List Wire) (state : BasisState)
    (hvalid : ∀ label, label ∈ labels → 0 < label ∧ label ≤ wires.length) :
    upperRangeBits enabled boundary labels
        (fun label ↦ wires.getD (label - 1) 0) state =
      endIterationUpperRangeBits enabled boundary labels (wireValues wires state) := by
  unfold upperRangeBits endIterationUpperRangeBits
  apply List.map_congr_left
  intro label hlabel
  have hbounds := hvalid label hlabel
  have hindex : label - 1 < wires.length := by omega
  rw [endIteration_wireValues_getD wires state (label - 1) hindex]

private theorem endIteration_lowerRangeBits_wireValues
    (enabled : Bool) (boundary : Nat) (labels : List Nat)
    (wires : List Wire) (state : BasisState)
    (hvalid : ∀ label, label ∈ labels → 0 < label ∧ label ≤ wires.length) :
    lowerRangeBits enabled boundary labels
        (fun label ↦ wires.getD (label - 1) 0) state =
      endIterationLowerRangeBits enabled boundary labels (wireValues wires state) := by
  unfold lowerRangeBits endIterationLowerRangeBits
  apply List.map_congr_left
  intro label hlabel
  have hbounds := hvalid label hlabel
  have hindex : label - 1 < wires.length := by omega
  rw [endIteration_wireValues_getD wires state (label - 1) hindex]

private theorem controlledWorkSwap_getD_left
    (control : Wire) (left right : List Wire) (state : BasisState)
    (hlength : left.length = right.length)
    (hlayout : (control :: left ++ right).Nodup)
    (index : Nat) (hindex : index < left.length) :
    run (controlledWorkSwap control left right) state (left.getD index 0) =
      (if state control then wireValues right state else wireValues left state).getD
        index false := by
  have hrightIndex : index < right.length := by simpa [hlength] using hindex
  have hcorrect := controlledWorkSwap_correct control left right state hlength hlayout
  calc
    run (controlledWorkSwap control left right) state (left.getD index 0) =
        (wireValues left (run (controlledWorkSwap control left right) state)).getD
          index false := (endIteration_wireValues_getD left _ index hindex).symm
    _ = (if state control then wireValues right state else wireValues left state).getD
          index false := congrArg (fun bits ↦ bits.getD index false) hcorrect.1

private theorem controlledWorkSwap_getD_right
    (control : Wire) (left right : List Wire) (state : BasisState)
    (hlength : left.length = right.length)
    (hlayout : (control :: left ++ right).Nodup)
    (index : Nat) (hindex : index < right.length) :
    run (controlledWorkSwap control left right) state (right.getD index 0) =
      (if state control then wireValues left state else wireValues right state).getD
        index false := by
  have hleftIndex : index < left.length := by simpa [hlength] using hindex
  have hcorrect := controlledWorkSwap_correct control left right state hlength hlayout
  calc
    run (controlledWorkSwap control left right) state (right.getD index 0) =
        (wireValues right (run (controlledWorkSwap control left right) state)).getD
          index false := (endIteration_wireValues_getD right _ index hindex).symm
    _ = (if state control then wireValues left state else wireValues right state).getD
          index false := congrArg (fun bits ↦ bits.getD index false) hcorrect.2

private theorem EndIterationLayout.upperBits_work1
    {registers : EndIterationRegisters} {n boundary : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    (state : BasisState) :
    let swapped := run
      (controlledWorkSwap registers.control registers.work1 registers.work2) state
    upperRangeBits (swapped registers.control) boundary
        (zeroMapLabels windows.k4 windows.K4) registers.work1At swapped =
      endIterationUpperRangeBits (state registers.control) boundary
        (zeroMapLabels windows.k4 windows.K4)
        (endIterationSwappedWorkWords registers state).1 := by
  intro swapped
  unfold upperRangeBits endIterationUpperRangeBits
  apply List.map_congr_left
  intro label hlabel
  obtain ⟨hlabelLow, hlabelHigh⟩ :=
    (mem_zeroMapLabels hlayout.k4_le_K4).mp hlabel
  have hkPositive := hlayout.k4_positive
  have hKWork := hlayout.K4_le_work
  have hindex : label - 1 < registers.work1.length := by
    rw [hlayout.work1_length]
    omega
  have hcontrol := controlledWorkSwap_control registers.control registers.work1
    registers.work2 state
  have hwork := controlledWorkSwap_getD_left registers.control registers.work1
    registers.work2 state (hlayout.work1_length.trans hlayout.work2_length.symm)
    hlayout.work_nodup (label - 1) hindex
  change
    (swapped registers.control && decide (label ≤ boundary) &&
        swapped (registers.work1.getD (label - 1) 0)) =
      (state registers.control && decide (label ≤ boundary) &&
        (endIterationSwappedWorkWords registers state).1.getD (label - 1) false)
  dsimp only [swapped]
  rw [hcontrol (by
      exact (List.nodup_cons.mp hlayout.work_nodup).1.imp fun h ↦
        List.mem_append_left registers.work2 h)
    (by
      exact (List.nodup_cons.mp hlayout.work_nodup).1.imp fun h ↦
        List.mem_append_right registers.work1 h), hwork]
  cases hc : state registers.control <;>
    simp [endIterationSwappedWorkWords, hc]

private theorem EndIterationLayout.upperBits_work2
    {registers : EndIterationRegisters} {n boundary : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    (state : BasisState) :
    let swapped := run
      (controlledWorkSwap registers.control registers.work1 registers.work2) state
    upperRangeBits (swapped registers.control) boundary
        (zeroMapLabels windows.k4 windows.K4) registers.work2At swapped =
      endIterationUpperRangeBits (state registers.control) boundary
        (zeroMapLabels windows.k4 windows.K4)
        (endIterationSwappedWorkWords registers state).2 := by
  intro swapped
  unfold upperRangeBits endIterationUpperRangeBits
  apply List.map_congr_left
  intro label hlabel
  obtain ⟨hlabelLow, hlabelHigh⟩ :=
    (mem_zeroMapLabels hlayout.k4_le_K4).mp hlabel
  have hkPositive := hlayout.k4_positive
  have hKWork := hlayout.K4_le_work
  have hindex : label - 1 < registers.work2.length := by
    rw [hlayout.work2_length]
    omega
  have hcontrol := controlledWorkSwap_control registers.control registers.work1
    registers.work2 state
  have hwork := controlledWorkSwap_getD_right registers.control registers.work1
    registers.work2 state (hlayout.work1_length.trans hlayout.work2_length.symm)
    hlayout.work_nodup (label - 1) hindex
  change
    (swapped registers.control && decide (label ≤ boundary) &&
        swapped (registers.work2.getD (label - 1) 0)) =
      (state registers.control && decide (label ≤ boundary) &&
        (endIterationSwappedWorkWords registers state).2.getD (label - 1) false)
  dsimp only [swapped]
  rw [hcontrol (by
      exact (List.nodup_cons.mp hlayout.work_nodup).1.imp fun h ↦
        List.mem_append_left registers.work2 h)
    (by
      exact (List.nodup_cons.mp hlayout.work_nodup).1.imp fun h ↦
        List.mem_append_right registers.work1 h), hwork]
  cases hc : state registers.control <;>
    simp [endIterationSwappedWorkWords, hc]

private theorem EndIterationLayout.lowerBits_work1
    {registers : EndIterationRegisters} {n boundary : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    (state : BasisState) :
    let swapped := run
      (controlledWorkSwap registers.control registers.work1 registers.work2) state
    lowerRangeBits (swapped registers.control) boundary
        (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work1At swapped =
      endIterationLowerRangeBits (state registers.control) boundary
        (zeroMapLabels windows.k5 (windows.K5Decode n))
        (endIterationSwappedWorkWords registers state).1 := by
  intro swapped
  unfold lowerRangeBits endIterationLowerRangeBits
  apply List.map_congr_left
  intro label hlabel
  obtain ⟨hlabelLow, hlabelHigh⟩ :=
    (mem_zeroMapLabels hlayout.k5_le_decode).mp hlabel
  have hkPositive := hlayout.k5_positive
  have hdecode : windows.K5Decode n ≤ n + 3 := by
    simp [EndIterationWindows.K5Decode]
  have hindex : label - 1 < registers.work1.length := by
    rw [hlayout.work1_length]
    omega
  have hcontrol := controlledWorkSwap_control registers.control registers.work1
    registers.work2 state
  have hwork := controlledWorkSwap_getD_left registers.control registers.work1
    registers.work2 state (hlayout.work1_length.trans hlayout.work2_length.symm)
    hlayout.work_nodup (label - 1) hindex
  change
    (swapped registers.control && decide (boundary ≤ label) &&
        swapped (registers.work1.getD (label - 1) 0)) =
      (state registers.control && decide (boundary ≤ label) &&
        (endIterationSwappedWorkWords registers state).1.getD (label - 1) false)
  dsimp only [swapped]
  rw [hcontrol (by
      exact (List.nodup_cons.mp hlayout.work_nodup).1.imp fun h ↦
        List.mem_append_left registers.work2 h)
    (by
      exact (List.nodup_cons.mp hlayout.work_nodup).1.imp fun h ↦
        List.mem_append_right registers.work1 h), hwork]
  cases hc : state registers.control <;>
    simp [endIterationSwappedWorkWords, hc]

private theorem EndIterationLayout.lowerBits_work2
    {registers : EndIterationRegisters} {n boundary : Nat}
    {windows : EndIterationWindows}
    (hlayout : EndIterationLayout registers n windows)
    (state : BasisState) :
    let swapped := run
      (controlledWorkSwap registers.control registers.work1 registers.work2) state
    lowerRangeBits (swapped registers.control) boundary
        (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work2At swapped =
      endIterationLowerRangeBits (state registers.control) boundary
        (zeroMapLabels windows.k5 (windows.K5Decode n))
        (endIterationSwappedWorkWords registers state).2 := by
  intro swapped
  unfold lowerRangeBits endIterationLowerRangeBits
  apply List.map_congr_left
  intro label hlabel
  obtain ⟨hlabelLow, hlabelHigh⟩ :=
    (mem_zeroMapLabels hlayout.k5_le_decode).mp hlabel
  have hkPositive := hlayout.k5_positive
  have hdecode : windows.K5Decode n ≤ n + 3 := by
    simp [EndIterationWindows.K5Decode]
  have hindex : label - 1 < registers.work2.length := by
    rw [hlayout.work2_length]
    omega
  have hcontrol := controlledWorkSwap_control registers.control registers.work1
    registers.work2 state
  have hwork := controlledWorkSwap_getD_right registers.control registers.work1
    registers.work2 state (hlayout.work1_length.trans hlayout.work2_length.symm)
    hlayout.work_nodup (label - 1) hindex
  change
    (swapped registers.control && decide (boundary ≤ label) &&
        swapped (registers.work2.getD (label - 1) 0)) =
      (state registers.control && decide (boundary ≤ label) &&
        (endIterationSwappedWorkWords registers state).2.getD (label - 1) false)
  dsimp only [swapped]
  rw [hcontrol (by
      exact (List.nodup_cons.mp hlayout.work_nodup).1.imp fun h ↦
        List.mem_append_left registers.work2 h)
    (by
      exact (List.nodup_cons.mp hlayout.work_nodup).1.imp fun h ↦
        List.mem_append_right registers.work1 h), hwork]
  cases hc : state registers.control <;>
    simp [endIterationSwappedWorkWords, hc]

/-! ## Literal aggregate and explicit reverse -/

/-- Exact `swap_work_and_len_unary_shared_gate`: full Work swap, upper length update, lower
length update, with the same physical scratch list supplied to both serial blocks. -/
def swapWorkAndLengthUnaryShared
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) : Circuit :=
  controlledWorkSwap registers.control registers.work1 registers.work2 ++
    lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows) registers.control
      (registers.rangeAccumulator windows.k4 windows.K4)
      (registers.temporary windows.k4 windows.K4) registers.carry
      (registers.path windows.k4 windows.K4)
      registers.work1At registers.work2At
      registers.lengthT registers.lengthRP registers.constants ++
    lenUpdateLrpUnary n windows.k5 (windows.K5Decode n) (registers.lowerTree n windows) registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At
      registers.lengthT registers.lengthRP registers.constants

/-- Exact dynamic inverse: lower writer first, upper writer second, then the reversed full-Work
Fredkin loop. -/
def swapWorkAndLengthUnarySharedInverse
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) : Circuit :=
  lenUpdateLrpUnary n windows.k5 (windows.K5Decode n) (registers.lowerTree n windows) registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At
      registers.lengthT registers.lengthRP registers.constants ++
    lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows) registers.control
      (registers.rangeAccumulator windows.k4 windows.K4)
      (registers.temporary windows.k4 windows.K4) registers.carry
      (registers.path windows.k4 windows.K4)
      registers.work1At registers.work2At
      registers.lengthT registers.lengthRP registers.constants ++
    controlledWorkSwapInverse registers.control registers.work1 registers.work2

/-! ## Structural and constructor-derived resource contracts -/

private theorem endIteration_cuccaroAdd_xCount :
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

private theorem endIteration_cuccaroSub_xCount
    (addends targets : List Wire) (carry : Wire) :
    eeaXCount (cuccaroSub addends targets carry) = 0 := by
  rw [cuccaroSub, eeaXCount_adjoint, endIteration_cuccaroAdd_xCount]

private theorem endIteration_xorConstant_xCount :
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

private theorem endIteration_notRegister_xCount (register : List Wire) :
    eeaXCount (notRegister register) = register.length := by
  induction register with
  | nil => rfl
  | cons wire wires ih =>
      rw [notRegister]
      change 1 + eeaXCount (notRegister wires) = wires.length + 1
      omega

private theorem endIteration_incrementTail_xCount :
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

private theorem endIteration_uncontrolledIncrement_xCount
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
                endIteration_incrementTail_xCount]
              rfl

private theorem endIteration_addConstant_xCount
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    eeaXCount (addConstant register constants carry value) =
      2 * (constantBits constants.length value).count true := by
  simp [addConstant, eeaXCount_append, endIteration_xorConstant_xCount,
    endIteration_cuccaroAdd_xCount]
  omega

private theorem endIteration_subConstant_xCount
    (register constants : List Wire) (carry : Wire) (value : Nat) :
    eeaXCount (subConstant register constants carry value) =
      2 * (constantBits constants.length value).count true := by
  simp [subConstant, eeaXCount_append, endIteration_xorConstant_xCount,
    endIteration_cuccaroSub_xCount]
  omega

private theorem endIteration_constMinus_xCount
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
  simp [constMinus, eeaXCount_append, endIteration_notRegister_xCount,
    endIteration_uncontrolledIncrement_xCount register _ hpositive htakeLength,
    endIteration_addConstant_xCount]
  omega

private theorem endIteration_controlledXorConstant_xCount :
    ∀ (control : Wire) (targets : List Wire) (value : Nat),
      eeaXCount (controlledXorConstant control targets value) = 0 := by
  intro control targets
  induction targets with
  | nil => intro value; rfl
  | cons target targets ih =>
      intro value
      by_cases hbit : value.testBit 0
      · rw [controlledXorConstant, if_pos hbit, eeaXCount_append,
          ih (value / 2)]
        rfl
      · rw [controlledXorConstant, if_neg hbit]
        exact ih (value / 2)

private theorem endIteration_dirtyConstantWrites_xCount
    (targets : List Wire) (dirtyAt : Nat → Wire) (valueAt : Nat → Nat) :
    ∀ labels : List Nat,
      eeaXCount (dirtyConstantWrites targets dirtyAt valueAt labels) = 0 := by
  intro labels
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      rw [dirtyConstantWrites, eeaXCount_append,
        endIteration_controlledXorConstant_xCount, ih]

private theorem endIteration_highestPositionXorWrite_xCount
    (k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    eeaXCount
        (highestPositionXorWrite k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) =
      2 * eeaXCount
        (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
          bitAt dirtyAt) := by
  simp [highestPositionXorWrite, highestPositionDirtyWrites,
    eeaXCount_append, endIteration_controlledXorConstant_xCount,
    endIteration_dirtyConstantWrites_xCount]
  omega

private theorem endIteration_rightLengthXorWrite_xCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) :
    eeaXCount
        (rightLengthXorWrite n k K tree control rangeAccumulator temporary path
          bitAt dirtyAt targets) =
      2 * eeaXCount
        (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
          bitAt dirtyAt) := by
  simp [rightLengthXorWrite, rightLengthDirtyWrites, eeaXCount_append,
    endIteration_controlledXorConstant_xCount,
    endIteration_dirtyConstantWrites_xCount]
  omega

private theorem endIteration_lenUpdateLtUnary_xCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire)
    (hpositive : 0 < lengthRP.length)
    (hlength : constants.length = lengthRP.length) :
    eeaXCount
        (lenUpdateLtUnary n k K tree control rangeAccumulator temporary carry path
          work1At work2At lengthT lengthRP constants) =
      2 * (lengthRP.length + 1 +
          2 * (constantBits constants.length (n + 2)).count true) +
        2 * eeaXCount
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
            work2At work1At) +
        2 * eeaXCount
          (upperZeroMapUnitary k K tree control rangeAccumulator temporary path
            work1At work2At) := by
  simp only [lenUpdateLtUnary, eeaXCount_append]
  rw [endIteration_constMinus_xCount lengthRP constants carry (n + 2)
      hpositive hlength,
    endIteration_highestPositionXorWrite_xCount k K tree control
      rangeAccumulator temporary path work2At work1At lengthT,
    endIteration_highestPositionXorWrite_xCount k K tree control
      rangeAccumulator temporary path work1At work2At lengthT]
  omega

private theorem endIteration_lenUpdateLrpUnary_xCount
    (n k K : Nat) (tree : UnaryActionTree)
    (control rangeAccumulator temporary carry : Wire) (path : List Wire)
    (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) :
    eeaXCount
        (lenUpdateLrpUnary n k K tree control rangeAccumulator temporary carry path
          work1At work2At lengthT lengthRP constants) =
      4 * (constantBits constants.length 3).count true +
        2 * eeaXCount
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
            work1At work2At) +
        2 * eeaXCount
          (lowerZeroMapUnitary k K tree control rangeAccumulator temporary path
            work2At work1At) := by
  simp only [lenUpdateLrpUnary, eeaXCount_append]
  rw [endIteration_addConstant_xCount lengthT constants carry 3,
    endIteration_rightLengthXorWrite_xCount n k K tree control
      rangeAccumulator temporary path work1At work2At lengthRP,
    endIteration_rightLengthXorWrite_xCount n k K tree control
      rangeAccumulator temporary path work2At work1At lengthRP,
    endIteration_subConstant_xCount lengthT constants carry 3]
  omega

/-- Closed Toffoli formula for the literal end-of-iteration source aggregate. -/
def endIterationToffoliFormula
    (workWidth lengthWidth n : Nat) (windows : EndIterationWindows) : Nat :=
  workWidth +
    2 * (2 * (lengthWidth - 2) + 2 * lengthWidth) +
    4 * (10 * (windows.K4 + 1 - windows.k4) - 7) +
    4 * lengthWidth +
    4 * (10 * (windows.K5Decode n + 1 - windows.k5) - 7)

/-- Closed CNOT formula, retaining the source constants' exact low-bit weights. -/
def endIterationCnotFormula
    (workWidth lengthWidth n : Nat) (windows : EndIterationWindows) : Nat :=
  2 * workWidth +
    2 * (lengthWidth + 1 + 4 * lengthWidth) +
    2 * lowBitCount lengthWidth
      (truthMinusOneValue lengthWidth windows.K4) +
    4 * ((zeroMapLabels windows.k4 windows.K4).reverse.map fun label ↦
      lowBitCount lengthWidth
        (highestPositionWriteValue lengthWidth windows.k4 label)).sum +
    4 * (6 * (windows.K4 + 1 - windows.k4) - 2) +
    8 * lengthWidth +
    2 * lowBitCount lengthWidth
      (rightLengthValue n lengthWidth windows.k5) +
    4 * ((zeroMapLabels windows.k5 (windows.K5Decode n)).map fun label ↦
      lowBitCount lengthWidth
        (rightLengthWriteValue n lengthWidth (windows.K5Decode n) label)).sum +
    4 * (6 * (windows.K5Decode n + 1 - windows.k5) - 2)

/-- Closed standalone-X formula for the literal end-of-iteration source aggregate. -/
def endIterationXFormula
    (lengthWidth n : Nat) (windows : EndIterationWindows) : Nat :=
  2 * (lengthWidth + 1 +
      2 * (constantBits lengthWidth (n + 2)).count true) +
    4 * (12 * (windows.K4 + 1 - windows.k4) - 10) +
    4 * (constantBits lengthWidth 3).count true +
    4 * (12 * (windows.K5Decode n + 1 - windows.k5) - 10)

/-- Framework-derived coherent T formula for the literal end-of-iteration source aggregate. -/
def endIterationTFormula
    (workWidth lengthWidth n : Nat) (windows : EndIterationWindows) : Nat :=
  7 * workWidth +
    2 * (14 * (lengthWidth - 2) + 14 * lengthWidth) +
    4 * (70 * (windows.K4 + 1 - windows.k4) - 49) +
    28 * lengthWidth +
    4 * (70 * (windows.K5Decode n + 1 - windows.k5) - 49)

/-- All four exact gate counts, reduced from the literal constructors and the two source trees.
The proof never evaluates the exponentially described aggregate circuit. -/
theorem swapWorkAndLengthUnaryShared_resourceCounts
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hwidth : 2 ≤ registers.width)
    (hlayout : EndIterationLayout registers n windows) :
    eeaToffoliCount (swapWorkAndLengthUnaryShared registers n windows) =
        endIterationToffoliFormula registers.work1.length registers.width n windows ∧
      eeaCnotCount (swapWorkAndLengthUnaryShared registers n windows) =
        endIterationCnotFormula registers.work1.length registers.width n windows ∧
      eeaXCount (swapWorkAndLengthUnaryShared registers n windows) =
        endIterationXFormula registers.width n windows ∧
      ShorECDLP.tCount (swapWorkAndLengthUnaryShared registers n windows) =
        endIterationTFormula registers.work1.length registers.width n windows := by
  have hwork : registers.work1.length = registers.work2.length :=
    hlayout.work1_length.trans hlayout.work2_length.symm
  have hlengthT : registers.lengthT.length = registers.width := rfl
  have hlengthRP : registers.lengthRP.length = registers.width :=
    hlayout.lengthRP_length
  have hconstants : registers.constants.length = registers.width := by
    have hwidthScratch : registers.width ≤ registers.scratch.length := by
      apply le_trans (b := endIterationScratchSize registers n windows)
      · unfold endIterationScratchSize
        apply le_trans (b := endIterationLengthScratchSize registers.width
            windows.k4 windows.K4)
        · unfold endIterationLengthScratchSize
          exact le_trans (by omega) (Nat.le_max_left _ _)
        · exact Nat.le_max_left _ _
      · exact hlayout.scratch_capacity
    simp [EndIterationRegisters.constants, List.length_take,
      Nat.min_eq_left hwidthScratch]
  have hpositive : 0 < registers.lengthRP.length := by
    rw [hlayout.lengthRP_length]
    exact hlayout.width_positive
  have hupper1 := upperZeroMapUnitary_resourceCounts windows.k4 windows.K4
    (registers.upperTree windows) registers.control
    (registers.rangeAccumulator windows.k4 windows.K4)
    (registers.temporary windows.k4 windows.K4)
    (registers.path windows.k4 windows.K4)
    registers.work1At registers.work2At hlayout.k4_le_K4
    hlayout.upper.work1Bits.decoder
    (registers.upperTree_visitLabels windows hlayout.k4_le_K4)
  have hupper2 := upperZeroMapUnitary_resourceCounts windows.k4 windows.K4
    (registers.upperTree windows) registers.control
    (registers.rangeAccumulator windows.k4 windows.K4)
    (registers.temporary windows.k4 windows.K4)
    (registers.path windows.k4 windows.K4)
    registers.work2At registers.work1At hlayout.k4_le_K4
    hlayout.upper.work2Bits.decoder
    (registers.upperTree_visitLabels windows hlayout.k4_le_K4)
  have hlower1 := lowerZeroMapUnitary_resourceCounts windows.k5
    (windows.K5Decode n) (registers.lowerTree n windows) registers.control
    (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
    (registers.temporary windows.k5 (windows.K5Decode n))
    (registers.path windows.k5 (windows.K5Decode n))
    registers.work1At registers.work2At hlayout.k5_le_decode
    hlayout.lower.work1Bits.decoder
    (registers.lowerTree_visitLabels n windows hlayout.k5_le_decode)
  have hlower2 := lowerZeroMapUnitary_resourceCounts windows.k5
    (windows.K5Decode n) (registers.lowerTree n windows) registers.control
    (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
    (registers.temporary windows.k5 (windows.K5Decode n))
    (registers.path windows.k5 (windows.K5Decode n))
    registers.work2At registers.work1At hlayout.k5_le_decode
    hlayout.lower.work2Bits.decoder
    (registers.lowerTree_visitLabels n windows hlayout.k5_le_decode)
  constructor
  · simp only [swapWorkAndLengthUnaryShared, eeaToffoliCount_append]
    rw [controlledWorkSwap_toffoliCount registers.control registers.work1
        registers.work2 hwork,
      lenUpdateLtUnary_toffoliCount n windows.k4 windows.K4
        (registers.upperTree windows) registers.control
        (registers.rangeAccumulator windows.k4 windows.K4)
        (registers.temporary windows.k4 windows.K4) registers.carry
        (registers.path windows.k4 windows.K4) registers.work1At
        registers.work2At registers.lengthT registers.lengthRP registers.constants
        hpositive (hconstants.trans hlengthRP.symm),
      lenUpdateLrpUnary_toffoliCount n windows.k5 (windows.K5Decode n)
        (registers.lowerTree n windows) registers.control
        (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
        (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
        (registers.path windows.k5 (windows.K5Decode n)) registers.work1At
        registers.work2At registers.lengthT registers.lengthRP registers.constants
        (hconstants.trans hlengthT.symm),
      hupper1.1, hupper2.1, hlower1.1, hlower2.1,
      hlengthRP, hlengthT]
    unfold endIterationToffoliFormula
    omega
  constructor
  · simp only [swapWorkAndLengthUnaryShared, eeaCnotCount_append]
    rw [controlledWorkSwap_cnotCount registers.control registers.work1
        registers.work2 hwork,
      lenUpdateLtUnary_cnotCount n windows.k4 windows.K4
        (registers.upperTree windows) registers.control
        (registers.rangeAccumulator windows.k4 windows.K4)
        (registers.temporary windows.k4 windows.K4) registers.carry
        (registers.path windows.k4 windows.K4) registers.work1At
        registers.work2At registers.lengthT registers.lengthRP registers.constants
        (by simpa only [hlengthRP] using hwidth) (hconstants.trans hlengthRP.symm),
      lenUpdateLrpUnary_cnotCount n windows.k5 (windows.K5Decode n)
        (registers.lowerTree n windows) registers.control
        (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
        (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
        (registers.path windows.k5 (windows.K5Decode n)) registers.work1At
        registers.work2At registers.lengthT registers.lengthRP registers.constants
        (hconstants.trans hlengthT.symm),
      hupper1.2.1, hupper2.2.1, hlower1.2.1, hlower2.2.1,
      hlengthRP, hlengthT]
    unfold endIterationCnotFormula
    omega
  constructor
  · simp only [swapWorkAndLengthUnaryShared, eeaXCount_append,
      controlledWorkSwap_xCount]
    rw [endIteration_lenUpdateLtUnary_xCount n windows.k4 windows.K4
        (registers.upperTree windows) registers.control
        (registers.rangeAccumulator windows.k4 windows.K4)
        (registers.temporary windows.k4 windows.K4) registers.carry
        (registers.path windows.k4 windows.K4) registers.work1At
        registers.work2At registers.lengthT registers.lengthRP registers.constants
        hpositive (hconstants.trans hlengthRP.symm),
      endIteration_lenUpdateLrpUnary_xCount n windows.k5 (windows.K5Decode n)
        (registers.lowerTree n windows) registers.control
        (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
        (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
        (registers.path windows.k5 (windows.K5Decode n)) registers.work1At
        registers.work2At registers.lengthT registers.lengthRP registers.constants,
      hupper1.2.2.1, hupper2.2.2.1, hlower1.2.2.1, hlower2.2.2.1,
      hlengthRP, hconstants]
    unfold endIterationXFormula
    omega
  · simp only [swapWorkAndLengthUnaryShared, ShorECDLP.tCount_append]
    rw [controlledWorkSwap_tCount registers.control registers.work1 registers.work2
        hwork,
      lenUpdateLtUnary_tCount n windows.k4 windows.K4
        (registers.upperTree windows) registers.control
        (registers.rangeAccumulator windows.k4 windows.K4)
        (registers.temporary windows.k4 windows.K4) registers.carry
        (registers.path windows.k4 windows.K4) registers.work1At
        registers.work2At registers.lengthT registers.lengthRP registers.constants
        hpositive (hconstants.trans hlengthRP.symm),
      lenUpdateLrpUnary_tCount n windows.k5 (windows.K5Decode n)
        (registers.lowerTree n windows) registers.control
        (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
        (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
        (registers.path windows.k5 (windows.K5Decode n)) registers.work1At
        registers.work2At registers.lengthT registers.lengthRP registers.constants
        (hconstants.trans hlengthT.symm),
      hupper1.2.2.2, hupper2.2.2.2, hlower1.2.2.2, hlower2.2.2.2,
      hlengthRP, hlengthT]
    unfold endIterationTFormula
    omega

/-- Complete named support obtained directly from the three emitted source blocks. -/
def endIterationSupport
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) : List Wire :=
  (registers.control :: registers.work1 ++ registers.work2) ++
    lengthBlockSupport windows.k4 windows.K4 (registers.upperTree windows) registers.control
      (registers.rangeAccumulator windows.k4 windows.K4)
      (registers.temporary windows.k4 windows.K4) registers.carry
      (registers.path windows.k4 windows.K4)
      registers.work1At registers.work2At registers.lengthRP registers.lengthT
      registers.constants ++
    lengthBlockSupport windows.k5 (windows.K5Decode n) (registers.lowerTree n windows) registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants

theorem swapWorkAndLengthUnaryShared_usesOnly
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hk4 : windows.k4 ≤ windows.K4)
    (hk5 : windows.k5 ≤ windows.K5Decode n) :
    PaperCircuitUsesOnly (endIterationSupport registers n windows)
      (swapWorkAndLengthUnaryShared registers n windows) := by
  rw [swapWorkAndLengthUnaryShared]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply (controlledWorkSwap_usesOnly registers.control registers.work1
        registers.work2).mono
      intro wire hwire
      exact List.mem_append_left _ (List.mem_append_left _ hwire)
    · apply (lenUpdateLtUnary_usesOnly n windows.k4 windows.K4 hk4 (registers.upperTree windows)
        registers.control (registers.rangeAccumulator windows.k4 windows.K4)
        (registers.temporary windows.k4 windows.K4) registers.carry
        (registers.path windows.k4 windows.K4)
        registers.work1At registers.work2At registers.lengthT registers.lengthRP
        registers.constants).mono
      intro wire hwire
      exact List.mem_append_left _ (List.mem_append_right _ hwire)
  · apply (lenUpdateLrpUnary_usesOnly n windows.k5 (windows.K5Decode n) hk5 (registers.lowerTree n windows)
      registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants).mono
    intro wire hwire
    exact List.mem_append_right _ hwire

theorem swapWorkAndLengthUnarySharedInverse_usesOnly
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hk4 : windows.k4 ≤ windows.K4)
    (hk5 : windows.k5 ≤ windows.K5Decode n) :
    PaperCircuitUsesOnly (endIterationSupport registers n windows)
      (swapWorkAndLengthUnarySharedInverse registers n windows) := by
  rw [swapWorkAndLengthUnarySharedInverse]
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · apply (lenUpdateLrpUnary_usesOnly n windows.k5 (windows.K5Decode n) hk5 (registers.lowerTree n windows)
        registers.control
        (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
        (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
        (registers.path windows.k5 (windows.K5Decode n))
        registers.work1At registers.work2At registers.lengthT registers.lengthRP
        registers.constants).mono
      intro wire hwire
      exact List.mem_append_right _ hwire
    · apply (lenUpdateLtUnary_usesOnly n windows.k4 windows.K4 hk4 (registers.upperTree windows)
        registers.control (registers.rangeAccumulator windows.k4 windows.K4)
        (registers.temporary windows.k4 windows.K4) registers.carry
        (registers.path windows.k4 windows.K4)
        registers.work1At registers.work2At registers.lengthT registers.lengthRP
        registers.constants).mono
      intro wire hwire
      exact List.mem_append_left _ (List.mem_append_right _ hwire)
  · apply (controlledWorkSwapInverse_usesOnly registers.control registers.work1
      registers.work2).mono
    intro wire hwire
    exact List.mem_append_left _ (List.mem_append_left _ hwire)

@[simp]
theorem swapWorkAndLengthUnaryShared_HPFree
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) :
    HPFree (swapWorkAndLengthUnaryShared registers n windows) := by
  simp [swapWorkAndLengthUnaryShared]

@[simp]
theorem swapWorkAndLengthUnarySharedInverse_HPFree
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) :
    HPFree (swapWorkAndLengthUnarySharedInverse registers n windows) := by
  simp [swapWorkAndLengthUnarySharedInverse]

theorem swapWorkAndLengthUnaryShared_wellFormed
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hlayout : EndIterationLayout registers n windows) :
    CircuitWellFormed
      (swapWorkAndLengthUnaryShared registers n windows) := by
  simp only [swapWorkAndLengthUnaryShared, circuitWellFormed_append]
  exact ⟨⟨controlledWorkSwap_wellFormed registers.control registers.work1 registers.work2
      (hlayout.work1_length.trans hlayout.work2_length.symm) hlayout.work_nodup,
    lenUpdateLtUnary_wellFormed_shared n windows.k4 windows.K4
      hlayout.k4_le_K4 (registers.upperTree windows) registers.control
      (registers.rangeAccumulator windows.k4 windows.K4)
      (registers.temporary windows.k4 windows.K4) registers.carry
      (registers.path windows.k4 windows.K4)
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants
      (hlayout.constants_length.trans hlayout.lengthRP_length.symm)
      hlayout.upper⟩,
    lenUpdateLrpUnary_wellFormed_shared n windows.k5 (windows.K5Decode n)
      hlayout.k5_le_decode (registers.lowerTree n windows) registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants
      (by simpa only [EndIterationRegisters.width] using hlayout.constants_length)
      hlayout.lower⟩

theorem swapWorkAndLengthUnarySharedInverse_wellFormed
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hlayout : EndIterationLayout registers n windows) :
    CircuitWellFormed
      (swapWorkAndLengthUnarySharedInverse registers n windows) := by
  simp only [swapWorkAndLengthUnarySharedInverse, circuitWellFormed_append]
  exact ⟨⟨
    lenUpdateLrpUnary_wellFormed_shared n windows.k5 (windows.K5Decode n)
      hlayout.k5_le_decode (registers.lowerTree n windows) registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants
      (by simpa only [EndIterationRegisters.width] using hlayout.constants_length)
      hlayout.lower,
    lenUpdateLtUnary_wellFormed_shared n windows.k4 windows.K4
      hlayout.k4_le_K4 (registers.upperTree windows) registers.control
      (registers.rangeAccumulator windows.k4 windows.K4)
      (registers.temporary windows.k4 windows.K4) registers.carry
      (registers.path windows.k4 windows.K4)
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants
      (hlayout.constants_length.trans hlayout.lengthRP_length.symm)
      hlayout.upper⟩,
    controlledWorkSwapInverse_wellFormed registers.control registers.work1 registers.work2
      (hlayout.work1_length.trans hlayout.work2_length.symm) hlayout.work_nodup⟩

/-- Exact constructor-level Toffoli sum, shared by the forward and inverse source orders. -/
theorem swapWorkAndLengthUnaryShared_toffoliCount
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hwork : registers.work1.length = registers.work2.length) :
    eeaToffoliCount
        (swapWorkAndLengthUnaryShared registers n windows) =
      registers.work1.length +
        eeaToffoliCount
          (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows) registers.control
            (registers.rangeAccumulator windows.k4 windows.K4)
            (registers.temporary windows.k4 windows.K4) registers.carry
            (registers.path windows.k4 windows.K4)
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants) +
        eeaToffoliCount
          (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n) (registers.lowerTree n windows) registers.control
            (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
            (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
            (registers.path windows.k5 (windows.K5Decode n))
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants) := by
  simp only [swapWorkAndLengthUnaryShared, eeaToffoliCount_append]
  rw [controlledWorkSwap_toffoliCount registers.control registers.work1 registers.work2
    hwork]

theorem swapWorkAndLengthUnaryShared_cnotCount
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hwork : registers.work1.length = registers.work2.length) :
    eeaCnotCount (swapWorkAndLengthUnaryShared registers n windows) =
      2 * registers.work1.length +
        eeaCnotCount
          (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows) registers.control
            (registers.rangeAccumulator windows.k4 windows.K4)
            (registers.temporary windows.k4 windows.K4) registers.carry
            (registers.path windows.k4 windows.K4)
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants) +
        eeaCnotCount
          (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n) (registers.lowerTree n windows) registers.control
            (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
            (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
            (registers.path windows.k5 (windows.K5Decode n))
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants) := by
  simp only [swapWorkAndLengthUnaryShared, eeaCnotCount_append]
  rw [controlledWorkSwap_cnotCount registers.control registers.work1 registers.work2
    hwork]

theorem swapWorkAndLengthUnaryShared_tCount
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hwork : registers.work1.length = registers.work2.length) :
    ShorECDLP.tCount (swapWorkAndLengthUnaryShared registers n windows) =
      7 * registers.work1.length +
        ShorECDLP.tCount
          (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows) registers.control
            (registers.rangeAccumulator windows.k4 windows.K4)
            (registers.temporary windows.k4 windows.K4) registers.carry
            (registers.path windows.k4 windows.K4)
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants) +
        ShorECDLP.tCount
          (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n) (registers.lowerTree n windows) registers.control
            (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
            (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
            (registers.path windows.k5 (windows.K5Decode n))
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants) := by
  simp only [swapWorkAndLengthUnaryShared, ShorECDLP.tCount_append]
  rw [controlledWorkSwap_tCount registers.control registers.work1 registers.work2 hwork]

theorem swapWorkAndLengthUnaryShared_xCount
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) :
    eeaXCount (swapWorkAndLengthUnaryShared registers n windows) =
      eeaXCount
        (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows)
          registers.control (registers.rangeAccumulator windows.k4 windows.K4)
          (registers.temporary windows.k4 windows.K4) registers.carry
          (registers.path windows.k4 windows.K4)
          registers.work1At registers.work2At registers.lengthT registers.lengthRP
          registers.constants) +
      eeaXCount
        (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n)
          (registers.lowerTree n windows) registers.control
          (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
          (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
          (registers.path windows.k5 (windows.K5Decode n))
          registers.work1At registers.work2At registers.lengthT registers.lengthRP
          registers.constants) := by
  simp [swapWorkAndLengthUnaryShared, eeaXCount_append]

theorem swapWorkAndLengthUnarySharedInverse_toffoliCount
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hwork : registers.work1.length = registers.work2.length) :
    eeaToffoliCount (swapWorkAndLengthUnarySharedInverse registers n windows) =
      eeaToffoliCount (swapWorkAndLengthUnaryShared registers n windows) := by
  simp only [swapWorkAndLengthUnarySharedInverse, swapWorkAndLengthUnaryShared,
    eeaToffoliCount_append]
  rw [controlledWorkSwap_toffoliCount registers.control registers.work1 registers.work2 hwork,
    controlledWorkSwapInverse_toffoliCount registers.control registers.work1 registers.work2
      hwork]
  omega

theorem swapWorkAndLengthUnarySharedInverse_cnotCount
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hwork : registers.work1.length = registers.work2.length) :
    eeaCnotCount (swapWorkAndLengthUnarySharedInverse registers n windows) =
      eeaCnotCount (swapWorkAndLengthUnaryShared registers n windows) := by
  simp only [swapWorkAndLengthUnarySharedInverse, swapWorkAndLengthUnaryShared,
    eeaCnotCount_append]
  rw [controlledWorkSwap_cnotCount registers.control registers.work1 registers.work2 hwork,
    controlledWorkSwapInverse_cnotCount registers.control registers.work1 registers.work2 hwork]
  omega

theorem swapWorkAndLengthUnarySharedInverse_xCount
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows) :
    eeaXCount (swapWorkAndLengthUnarySharedInverse registers n windows) =
      eeaXCount (swapWorkAndLengthUnaryShared registers n windows) := by
  simp [swapWorkAndLengthUnarySharedInverse, swapWorkAndLengthUnaryShared,
    eeaXCount_append]
  omega

theorem swapWorkAndLengthUnarySharedInverse_tCount
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (hwork : registers.work1.length = registers.work2.length) :
    tCount (swapWorkAndLengthUnarySharedInverse registers n windows) =
      tCount (swapWorkAndLengthUnaryShared registers n windows) := by
  simp only [swapWorkAndLengthUnarySharedInverse, swapWorkAndLengthUnaryShared,
    tCount_append]
  rw [controlledWorkSwap_tCount registers.control registers.work1 registers.work2 hwork,
    controlledWorkSwapInverse_tCount registers.control registers.work1 registers.work2 hwork]
  omega

/-! ## Direct aggregate semantics -/

/-- The literal shared-scratch aggregate realizes the pinned Boolean-word recurrence, restores
the complete physical scratch list, and changes no wire outside the four mutable words. -/
theorem swapWorkAndLengthUnaryShared_correct
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (boundary4 boundary5 : Nat)
    (hboundary4 : windows.k4 ≤ boundary4 ∧ boundary4 ≤ windows.K4)
    (hboundary5 : windows.k5 ≤ boundary5 ∧
      boundary5 ≤ windows.K5Decode n)
    (state : BasisState)
    (hlayout : EndIterationLayout registers n windows)
    (hroute4 : (registers.upperTree windows).routeLabel
      (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
        (run (controlledWorkSwap registers.control registers.work1 registers.work2)
          state)) = boundary4)
    (hroute5 : (registers.lowerTree n windows).routeLabel
      (run (addConstant registers.lengthT registers.constants registers.carry 3)
        (run
          (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows) registers.control
            (registers.rangeAccumulator windows.k4 windows.K4)
            (registers.temporary windows.k4 windows.K4) registers.carry
            (registers.path windows.k4 windows.K4)
            registers.work1At registers.work2At
            registers.lengthT registers.lengthRP registers.constants)
          (run (controlledWorkSwap registers.control registers.work1 registers.work2)
            state))) = boundary5)
    (hready : EndIterationReady registers state) :
    let after := run
      (swapWorkAndLengthUnaryShared registers n windows) state
    let work := endIterationSwappedWorkWords registers state
    let lengths := endIterationLengthWords registers n windows boundary4 boundary5 state
    wireValues registers.work1 after = work.1 ∧
      wireValues registers.work2 after = work.2 ∧
      (wireValues registers.lengthT after,
          wireValues registers.lengthRP after) = lengths ∧
      EndIterationReady registers after ∧
      ∀ wire, wire ∉ registers.work1 → wire ∉ registers.work2 →
        wire ∉ registers.lengthT → wire ∉ registers.lengthRP →
        after wire = state wire := by
  let swapped := run
    (controlledWorkSwap registers.control registers.work1 registers.work2) state
  let afterUpper := run
    (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows) registers.control
      (registers.rangeAccumulator windows.k4 windows.K4)
      (registers.temporary windows.k4 windows.K4) registers.carry
      (registers.path windows.k4 windows.K4)
      registers.work1At registers.work2At
      registers.lengthT registers.lengthRP registers.constants) swapped
  let after := run
    (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n) (registers.lowerTree n windows) registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At
      registers.lengthT registers.lengthRP registers.constants) afterUpper
  have hworkLength : registers.work1.length = registers.work2.length :=
    hlayout.work1_length.trans hlayout.work2_length.symm
  have hcontrolLeft : registers.control ∉ registers.work1 := by
    intro hmem
    exact (List.nodup_cons.mp hlayout.work_nodup).1
      (List.mem_append_left registers.work2 hmem)
  have hcontrolRight : registers.control ∉ registers.work2 := by
    intro hmem
    exact (List.nodup_cons.mp hlayout.work_nodup).1
      (List.mem_append_right registers.work1 hmem)
  have hswap := controlledWorkSwap_correct registers.control registers.work1
    registers.work2 state hworkLength hlayout.work_nodup
  have hswapOutside (wire : Wire)
      (hleft : wire ∉ registers.work1) (hright : wire ∉ registers.work2) :
      swapped wire = state wire := by
    exact controlledWorkSwap_preservesOutsideWords registers.control registers.work1
      registers.work2 state hcontrolLeft hcontrolRight wire hleft hright
  have hreadySwapped : EndIterationReady registers swapped := by
    intro wire hwire
    rw [hswapOutside wire (hlayout.scratch_not_work1 hwire)
      (hlayout.scratch_not_work2 hwire)]
    exact hready wire hwire
  obtain ⟨hconstants4, hpath4, hrange4, htemporary4⟩ :=
    hlayout.clean_components4 hreadySwapped
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [hlayout.lengthRP_length]
    exact hlayout.width_positive
  have hconstantsRP : registers.constants.length = registers.lengthRP.length :=
    hlayout.constants_length.trans hlayout.lengthRP_length.symm
  have hupper := lenUpdateLtUnary_correct_shared n windows.k4 windows.K4 boundary4
    hlayout.k4_le_K4 hboundary4 (registers.upperTree windows) registers.control
    (registers.rangeAccumulator windows.k4 windows.K4)
    (registers.temporary windows.k4 windows.K4) registers.carry
    (registers.path windows.k4 windows.K4)
    registers.work1At registers.work2At registers.lengthT registers.lengthRP
    registers.constants swapped hpositiveRP hconstantsRP hlayout.upper
    (registers.upperTree_visitLabels windows hlayout.k4_le_K4)
    (by simpa only [swapped] using hroute4)
    hconstants4 hpath4 hrange4 htemporary4
  have hupperTarget : wireValues registers.lengthT afterUpper =
      highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
        (swapped registers.control)
        (upperRangeBits (swapped registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work1At swapped)
        (highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
          (swapped registers.control)
          (upperRangeBits (swapped registers.control) boundary4
            (zeroMapLabels windows.k4 windows.K4) registers.work2At swapped)
          (wireValues registers.lengthT swapped)) := by
    simpa only [afterUpper] using hupper.1
  have hupperBoundary : wireValues registers.lengthRP afterUpper =
      wireValues registers.lengthRP swapped := by
    simpa only [afterUpper] using hupper.2.1
  have hupperOutside : ∀ wire, wire ∉ registers.lengthT →
      afterUpper wire = swapped wire := by
    simpa only [afterUpper] using hupper.2.2.2.2
  have hreadyUpper : EndIterationReady registers afterUpper := by
    intro wire hwire
    rw [hupperOutside wire (hlayout.scratch_not_lengthT hwire)]
    exact hreadySwapped wire hwire
  obtain ⟨hconstants5, hpath5, hrange5, htemporary5⟩ :=
    hlayout.clean_components5 hreadyUpper
  have hconstantsT : registers.constants.length = registers.lengthT.length := by
    simpa only [EndIterationRegisters.width] using hlayout.constants_length
  have hlower := lenUpdateLrpUnary_correct_shared n windows.k5
    (windows.K5Decode n) boundary5 hlayout.k5_le_decode hboundary5 (registers.lowerTree n windows)
    registers.control
    (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
    (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
    (registers.path windows.k5 (windows.K5Decode n))
    registers.work1At registers.work2At registers.lengthT registers.lengthRP
    registers.constants afterUpper hconstantsT hlayout.lower
    (registers.lowerTree_visitLabels n windows hlayout.k5_le_decode)
    (by simpa only [afterUpper, swapped] using hroute5)
    hconstants5 hpath5 hrange5 htemporary5
  have hlowerTarget : wireValues registers.lengthRP after =
      rightLengthWordAction n registers.lengthRP.length windows.k5
        (windows.K5Decode n) (afterUpper registers.control)
        (lowerRangeBits (afterUpper registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          registers.work2At afterUpper)
        (rightLengthWordAction n registers.lengthRP.length windows.k5
          (windows.K5Decode n) (afterUpper registers.control)
          (lowerRangeBits (afterUpper registers.control) boundary5
            (zeroMapLabels windows.k5 (windows.K5Decode n))
            registers.work1At afterUpper)
          (wireValues registers.lengthRP afterUpper)) := by
    simpa only [after] using hlower.1
  have hlowerBoundary : wireValues registers.lengthT after =
      wireValues registers.lengthT afterUpper := by
    simpa only [after] using hlower.2.1
  have hlowerOutside : ∀ wire, wire ∉ registers.lengthRP →
      after wire = afterUpper wire := by
    simpa only [after] using hlower.2.2.2.2
  have hcontrolSwapped : swapped registers.control = state registers.control :=
    hswapOutside registers.control hcontrolLeft hcontrolRight
  have hwork1Words : wireValues registers.work1 swapped =
      (endIterationSwappedWorkWords registers state).1 := by
    rw [hswap.1]
    cases hcontrol : state registers.control <;>
      simp [endIterationSwappedWorkWords, hcontrol]
  have hwork2Words : wireValues registers.work2 swapped =
      (endIterationSwappedWorkWords registers state).2 := by
    rw [hswap.2]
    cases hcontrol : state registers.control <;>
      simp [endIterationSwappedWorkWords, hcontrol]
  have hlengthTBefore : wireValues registers.lengthT swapped =
      wireValues registers.lengthT state := by
    apply endIteration_wireValues_congr
    intro wire hwire
    apply hswapOutside
    · exact hlayout.lengthT_not_work1 hwire
    · exact hlayout.lengthT_not_work2 hwire
  have hlengthRPBefore : wireValues registers.lengthRP swapped =
      wireValues registers.lengthRP state := by
    apply endIteration_wireValues_congr
    intro wire hwire
    apply hswapOutside
    · exact hlayout.lengthRP_not_work1 hwire
    · exact hlayout.lengthRP_not_work2 hwire
  have hupperBits1 :
      upperRangeBits (swapped registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work1At swapped =
        endIterationUpperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4)
          (endIterationSwappedWorkWords registers state).1 := by
    simpa only [swapped] using
      hlayout.upperBits_work1 (boundary := boundary4) state
  have hupperBits2 :
      upperRangeBits (swapped registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work2At swapped =
        endIterationUpperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4)
          (endIterationSwappedWorkWords registers state).2 := by
    simpa only [swapped] using
      hlayout.upperBits_work2 (boundary := boundary4) state
  have hlengthTUpper : wireValues registers.lengthT afterUpper =
      (endIterationLengthWords registers n windows boundary4 boundary5 state).1 := by
    rw [hupperTarget, hupperBits1, hupperBits2, hcontrolSwapped, hlengthTBefore]
    rfl
  have hupperControl : afterUpper registers.control = state registers.control := by
    calc
      afterUpper registers.control = swapped registers.control :=
        hupperOutside _
          (hlayout.workWire_not_lengthT (by simp))
      _ = state registers.control := hcontrolSwapped
  have hlowerBits1 :
      lowerRangeBits (afterUpper registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          registers.work1At afterUpper =
        endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (endIterationSwappedWorkWords registers state).1 := by
    calc
      lowerRangeBits (afterUpper registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          registers.work1At afterUpper =
        lowerRangeBits (swapped registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          registers.work1At swapped := by
            unfold lowerRangeBits
            apply List.map_congr_left
            intro label hlabel
            obtain ⟨hlabelLow, hlabelHigh⟩ :=
              (mem_zeroMapLabels hlayout.k5_le_decode).mp hlabel
            have hdecode : windows.K5Decode n ≤ n + 3 := by
              simp [EndIterationWindows.K5Decode]
            have hmem := hlayout.work1At_mem (label := label)
              (lt_of_lt_of_le hlayout.k5_positive hlabelLow)
              (hlabelHigh.trans hdecode)
            have hcontrolWork : registers.control ∈
                registers.control :: registers.work1 ++ registers.work2 := by
              exact List.mem_append_left registers.work2 List.mem_cons_self
            have hbitWork : registers.work1At label ∈
                registers.control :: registers.work1 ++ registers.work2 := by
              exact List.mem_append_left registers.work2
                (List.mem_cons_of_mem registers.control hmem)
            rw [hupperOutside registers.control
                (hlayout.workWire_not_lengthT hcontrolWork),
              hupperOutside (registers.work1At label)
                (hlayout.workWire_not_lengthT hbitWork)]
      _ = endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (endIterationSwappedWorkWords registers state).1 :=
        hlayout.lowerBits_work1 state
  have hlowerBits2 :
      lowerRangeBits (afterUpper registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          registers.work2At afterUpper =
        endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (endIterationSwappedWorkWords registers state).2 := by
    calc
      lowerRangeBits (afterUpper registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          registers.work2At afterUpper =
        lowerRangeBits (swapped registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          registers.work2At swapped := by
            unfold lowerRangeBits
            apply List.map_congr_left
            intro label hlabel
            obtain ⟨hlabelLow, hlabelHigh⟩ :=
              (mem_zeroMapLabels hlayout.k5_le_decode).mp hlabel
            have hdecode : windows.K5Decode n ≤ n + 3 := by
              simp [EndIterationWindows.K5Decode]
            have hmem := hlayout.work2At_mem (label := label)
              (lt_of_lt_of_le hlayout.k5_positive hlabelLow)
              (hlabelHigh.trans hdecode)
            have hcontrolWork : registers.control ∈
                registers.control :: registers.work1 ++ registers.work2 := by
              exact List.mem_append_left registers.work2 List.mem_cons_self
            have hbitWork : registers.work2At label ∈
                registers.control :: registers.work1 ++ registers.work2 := by
              exact List.mem_append_right (registers.control :: registers.work1) hmem
            rw [hupperOutside registers.control
                (hlayout.workWire_not_lengthT hcontrolWork),
              hupperOutside (registers.work2At label)
                (hlayout.workWire_not_lengthT hbitWork)]
      _ = endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (endIterationSwappedWorkWords registers state).2 :=
        hlayout.lowerBits_work2 state
  have hlengthRPUpper : wireValues registers.lengthRP afterUpper =
      wireValues registers.lengthRP state :=
    hupperBoundary.trans hlengthRPBefore
  have hlengthRPAfter : wireValues registers.lengthRP after =
      (endIterationLengthWords registers n windows boundary4 boundary5 state).2 := by
    rw [hlowerTarget, hlowerBits1, hlowerBits2, hupperControl, hlengthRPUpper]
    rfl
  have hlengthTAfter : wireValues registers.lengthT after =
      (endIterationLengthWords registers n windows boundary4 boundary5 state).1 := by
    calc
      wireValues registers.lengthT after =
          wireValues registers.lengthT afterUpper := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hlowerOutside wire (hlayout.lengthT_not_lengthRP hwire)
      _ = _ := hlengthTUpper
  have hwork1After : wireValues registers.work1 after =
      (endIterationSwappedWorkWords registers state).1 := by
    calc
      wireValues registers.work1 after = wireValues registers.work1 afterUpper := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hlowerOutside wire
          (hlayout.workWire_not_lengthRP (by simp [hwire]))
      _ = wireValues registers.work1 swapped := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hupperOutside wire
          (hlayout.workWire_not_lengthT (by simp [hwire]))
      _ = _ := hwork1Words
  have hwork2After : wireValues registers.work2 after =
      (endIterationSwappedWorkWords registers state).2 := by
    calc
      wireValues registers.work2 after = wireValues registers.work2 afterUpper := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hlowerOutside wire
          (hlayout.workWire_not_lengthRP (by simp [hwire]))
      _ = wireValues registers.work2 swapped := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hupperOutside wire
          (hlayout.workWire_not_lengthT (by simp [hwire]))
      _ = _ := hwork2Words
  have hreadyAfter : EndIterationReady registers after := by
    intro wire hwire
    rw [hlowerOutside wire (hlayout.scratch_not_lengthRP hwire)]
    exact hreadyUpper wire hwire
  have houtside (wire : Wire)
      (hwork1 : wire ∉ registers.work1) (hwork2 : wire ∉ registers.work2)
      (hlengthT : wire ∉ registers.lengthT)
      (hlengthRP : wire ∉ registers.lengthRP) :
      after wire = state wire := by
    calc
      after wire = afterUpper wire := hlowerOutside wire hlengthRP
      _ = swapped wire := hupperOutside wire hlengthT
      _ = state wire := hswapOutside wire hwork1 hwork2
  have hfull : run
      (swapWorkAndLengthUnaryShared registers n windows) state = after := by
    simp [swapWorkAndLengthUnaryShared, after, afterUpper, swapped, run_append]
  rw [hfull]
  exact ⟨hwork1After, hwork2After,
    Prod.ext hlengthTAfter hlengthRPAfter, hreadyAfter, houtside⟩

/-- Direct circuit-free whole-state semantics of the pinned explicit reverse order. -/
theorem swapWorkAndLengthUnarySharedInverse_correct
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (boundary4 boundary5 : Nat)
    (hboundary4 : windows.k4 ≤ boundary4 ∧ boundary4 ≤ windows.K4)
    (hboundary5 : windows.k5 ≤ boundary5 ∧
      boundary5 ≤ windows.K5Decode n)
    (state : BasisState)
    (hlayout : EndIterationLayout registers n windows)
    (hroute5 : (registers.lowerTree n windows).routeLabel
      (run (addConstant registers.lengthT registers.constants registers.carry 3)
        state) = boundary5)
    (hroute4 : (registers.upperTree windows).routeLabel
      (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
        (run
          (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n) (registers.lowerTree n windows)
            registers.control
            (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
            (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
            (registers.path windows.k5 (windows.K5Decode n))
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants) state)) = boundary4)
    (hready : EndIterationReady registers state) :
    let after := run
      (swapWorkAndLengthUnarySharedInverse registers n windows) state
    let work := endIterationSwappedWorkWords registers state
    let lengths :=
      endIterationInverseLengthWords registers n windows boundary4 boundary5 state
    wireValues registers.work1 after = work.1 ∧
      wireValues registers.work2 after = work.2 ∧
      (wireValues registers.lengthT after,
          wireValues registers.lengthRP after) = lengths ∧
      EndIterationReady registers after ∧
      ∀ wire, wire ∉ registers.work1 → wire ∉ registers.work2 →
        wire ∉ registers.lengthT → wire ∉ registers.lengthRP →
        after wire = state wire := by
  let afterLower := run
    (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n) (registers.lowerTree n windows) registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants) state
  let afterUpper := run
    (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows) registers.control
      (registers.rangeAccumulator windows.k4 windows.K4)
      (registers.temporary windows.k4 windows.K4) registers.carry
      (registers.path windows.k4 windows.K4)
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants) afterLower
  let after := run
    (controlledWorkSwapInverse registers.control registers.work1 registers.work2)
      afterUpper
  obtain ⟨hconstants5, hpath5, hrange5, htemporary5⟩ :=
    hlayout.clean_components5 hready
  have hconstantsT : registers.constants.length = registers.lengthT.length := by
    simpa only [EndIterationRegisters.width] using hlayout.constants_length
  have hlower := lenUpdateLrpUnary_correct_shared n windows.k5
    (windows.K5Decode n) boundary5 hlayout.k5_le_decode hboundary5 (registers.lowerTree n windows)
    registers.control
    (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
    (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
    (registers.path windows.k5 (windows.K5Decode n))
    registers.work1At registers.work2At registers.lengthT registers.lengthRP
    registers.constants state hconstantsT hlayout.lower
    (registers.lowerTree_visitLabels n windows hlayout.k5_le_decode)
    hroute5 hconstants5 hpath5 hrange5 htemporary5
  have hlowerTarget : wireValues registers.lengthRP afterLower =
      rightLengthWordAction n registers.lengthRP.length windows.k5
        (windows.K5Decode n) (state registers.control)
        (lowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work2At state)
        (rightLengthWordAction n registers.lengthRP.length windows.k5
          (windows.K5Decode n) (state registers.control)
          (lowerRangeBits (state registers.control) boundary5
            (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work1At state)
          (wireValues registers.lengthRP state)) := by
    simpa only [afterLower] using hlower.1
  have hlowerBoundary : wireValues registers.lengthT afterLower =
      wireValues registers.lengthT state := by
    simpa only [afterLower] using hlower.2.1
  have hlowerOutside : ∀ wire, wire ∉ registers.lengthRP →
      afterLower wire = state wire := by
    simpa only [afterLower] using hlower.2.2.2.2
  have hreadyLower : EndIterationReady registers afterLower := by
    intro wire hwire
    rw [hlowerOutside wire (hlayout.scratch_not_lengthRP hwire)]
    exact hready wire hwire
  obtain ⟨hconstants4, hpath4, hrange4, htemporary4⟩ :=
    hlayout.clean_components4 hreadyLower
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [hlayout.lengthRP_length]
    exact hlayout.width_positive
  have hconstantsRP : registers.constants.length = registers.lengthRP.length :=
    hlayout.constants_length.trans hlayout.lengthRP_length.symm
  have hupper := lenUpdateLtUnary_correct_shared n windows.k4 windows.K4 boundary4
    hlayout.k4_le_K4 hboundary4 (registers.upperTree windows) registers.control
    (registers.rangeAccumulator windows.k4 windows.K4)
    (registers.temporary windows.k4 windows.K4) registers.carry
    (registers.path windows.k4 windows.K4)
    registers.work1At registers.work2At registers.lengthT registers.lengthRP
    registers.constants afterLower hpositiveRP hconstantsRP hlayout.upper
    (registers.upperTree_visitLabels windows hlayout.k4_le_K4)
    (by simpa only [afterLower] using hroute4)
    hconstants4 hpath4 hrange4 htemporary4
  have hupperTarget : wireValues registers.lengthT afterUpper =
      highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
        (afterLower registers.control)
        (upperRangeBits (afterLower registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work1At afterLower)
        (highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
          (afterLower registers.control)
          (upperRangeBits (afterLower registers.control) boundary4
            (zeroMapLabels windows.k4 windows.K4) registers.work2At afterLower)
          (wireValues registers.lengthT afterLower)) := by
    simpa only [afterUpper] using hupper.1
  have hupperBoundary : wireValues registers.lengthRP afterUpper =
      wireValues registers.lengthRP afterLower := by
    simpa only [afterUpper] using hupper.2.1
  have hupperOutside : ∀ wire, wire ∉ registers.lengthT →
      afterUpper wire = afterLower wire := by
    simpa only [afterUpper] using hupper.2.2.2.2
  have hreadyUpper : EndIterationReady registers afterUpper := by
    intro wire hwire
    rw [hupperOutside wire (hlayout.scratch_not_lengthT hwire)]
    exact hreadyLower wire hwire
  have hdecode : windows.K5Decode n ≤ n + 3 := by
    simp [EndIterationWindows.K5Decode]
  have hlowerBits1 :
      lowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work1At state =
        endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (wireValues registers.work1 state) := by
    apply endIteration_lowerRangeBits_wireValues
    intro label hlabel
    obtain ⟨hlabelLow, hlabelHigh⟩ :=
      (mem_zeroMapLabels hlayout.k5_le_decode).mp hlabel
    constructor
    · exact lt_of_lt_of_le hlayout.k5_positive hlabelLow
    · rw [hlayout.work1_length]
      exact hlabelHigh.trans hdecode
  have hlowerBits2 :
      lowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work2At state =
        endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (wireValues registers.work2 state) := by
    apply endIteration_lowerRangeBits_wireValues
    intro label hlabel
    obtain ⟨hlabelLow, hlabelHigh⟩ :=
      (mem_zeroMapLabels hlayout.k5_le_decode).mp hlabel
    constructor
    · exact lt_of_lt_of_le hlayout.k5_positive hlabelLow
    · rw [hlayout.work2_length]
      exact hlabelHigh.trans hdecode
  have hlengthRPLower : wireValues registers.lengthRP afterLower =
      (endIterationInverseLengthWords registers n windows boundary4 boundary5 state).2 := by
    rw [hlowerTarget, hlowerBits1, hlowerBits2]
    rfl
  have hlowerControl : afterLower registers.control = state registers.control :=
    hlowerOutside registers.control
      (hlayout.workWire_not_lengthRP (by simp))
  have hupperBits1 :
      upperRangeBits (afterLower registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work1At afterLower =
        endIterationUpperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4)
          (wireValues registers.work1 state) := by
    calc
      upperRangeBits (afterLower registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work1At afterLower =
        upperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work1At state := by
            unfold upperRangeBits
            apply List.map_congr_left
            intro label hlabel
            obtain ⟨hlabelLow, hlabelHigh⟩ :=
              (mem_zeroMapLabels hlayout.k4_le_K4).mp hlabel
            have hmem := hlayout.work1At_mem (label := label)
              (lt_of_lt_of_le hlayout.k4_positive hlabelLow)
              (hlabelHigh.trans hlayout.K4_le_work)
            have hcontrolWork : registers.control ∈
                registers.control :: registers.work1 ++ registers.work2 :=
              List.mem_append_left registers.work2 List.mem_cons_self
            have hbitWork : registers.work1At label ∈
                registers.control :: registers.work1 ++ registers.work2 :=
              List.mem_append_left registers.work2
                (List.mem_cons_of_mem registers.control hmem)
            rw [hlowerOutside registers.control
                (hlayout.workWire_not_lengthRP hcontrolWork),
              hlowerOutside (registers.work1At label)
                (hlayout.workWire_not_lengthRP hbitWork)]
      _ = _ := by
        apply endIteration_upperRangeBits_wireValues
        intro label hlabel
        obtain ⟨hlabelLow, hlabelHigh⟩ :=
          (mem_zeroMapLabels hlayout.k4_le_K4).mp hlabel
        constructor
        · exact lt_of_lt_of_le hlayout.k4_positive hlabelLow
        · rw [hlayout.work1_length]
          exact hlabelHigh.trans hlayout.K4_le_work
  have hupperBits2 :
      upperRangeBits (afterLower registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work2At afterLower =
        endIterationUpperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4)
          (wireValues registers.work2 state) := by
    calc
      upperRangeBits (afterLower registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work2At afterLower =
        upperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4) registers.work2At state := by
            unfold upperRangeBits
            apply List.map_congr_left
            intro label hlabel
            obtain ⟨hlabelLow, hlabelHigh⟩ :=
              (mem_zeroMapLabels hlayout.k4_le_K4).mp hlabel
            have hmem := hlayout.work2At_mem (label := label)
              (lt_of_lt_of_le hlayout.k4_positive hlabelLow)
              (hlabelHigh.trans hlayout.K4_le_work)
            have hcontrolWork : registers.control ∈
                registers.control :: registers.work1 ++ registers.work2 :=
              List.mem_append_left registers.work2 List.mem_cons_self
            have hbitWork : registers.work2At label ∈
                registers.control :: registers.work1 ++ registers.work2 :=
              List.mem_append_right (registers.control :: registers.work1) hmem
            rw [hlowerOutside registers.control
                (hlayout.workWire_not_lengthRP hcontrolWork),
              hlowerOutside (registers.work2At label)
                (hlayout.workWire_not_lengthRP hbitWork)]
      _ = _ := by
        apply endIteration_upperRangeBits_wireValues
        intro label hlabel
        obtain ⟨hlabelLow, hlabelHigh⟩ :=
          (mem_zeroMapLabels hlayout.k4_le_K4).mp hlabel
        constructor
        · exact lt_of_lt_of_le hlayout.k4_positive hlabelLow
        · rw [hlayout.work2_length]
          exact hlabelHigh.trans hlayout.K4_le_work
  have hlengthTUpper : wireValues registers.lengthT afterUpper =
      (endIterationInverseLengthWords registers n windows boundary4 boundary5 state).1 := by
    rw [hupperTarget, hupperBits1, hupperBits2, hlowerControl, hlowerBoundary]
    rfl
  have hwork1Upper : wireValues registers.work1 afterUpper =
      wireValues registers.work1 state := by
    calc
      wireValues registers.work1 afterUpper = wireValues registers.work1 afterLower := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hupperOutside wire
          (hlayout.workWire_not_lengthT (by simp [hwire]))
      _ = wireValues registers.work1 state := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hlowerOutside wire
          (hlayout.workWire_not_lengthRP (by simp [hwire]))
  have hwork2Upper : wireValues registers.work2 afterUpper =
      wireValues registers.work2 state := by
    calc
      wireValues registers.work2 afterUpper = wireValues registers.work2 afterLower := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hupperOutside wire
          (hlayout.workWire_not_lengthT (by simp [hwire]))
      _ = wireValues registers.work2 state := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hlowerOutside wire
          (hlayout.workWire_not_lengthRP (by simp [hwire]))
  have hcontrolUpper : afterUpper registers.control = state registers.control := by
    calc
      afterUpper registers.control = afterLower registers.control :=
        hupperOutside _ (hlayout.workWire_not_lengthT (by simp))
      _ = state registers.control := hlowerControl
  have hswap := controlledWorkSwapInverse_correct registers.control registers.work1
    registers.work2 afterUpper
    (hlayout.work1_length.trans hlayout.work2_length.symm) hlayout.work_nodup
  have hwork1After : wireValues registers.work1 after =
      (endIterationSwappedWorkWords registers state).1 := by
    rw [show wireValues registers.work1 after =
        (if afterUpper registers.control then wireValues registers.work2 afterUpper
          else wireValues registers.work1 afterUpper) by
      simpa only [after] using hswap.1,
      hcontrolUpper, hwork1Upper, hwork2Upper]
    cases hcontrol : state registers.control <;>
      simp [endIterationSwappedWorkWords, hcontrol]
  have hwork2After : wireValues registers.work2 after =
      (endIterationSwappedWorkWords registers state).2 := by
    rw [show wireValues registers.work2 after =
        (if afterUpper registers.control then wireValues registers.work1 afterUpper
          else wireValues registers.work2 afterUpper) by
      simpa only [after] using hswap.2,
      hcontrolUpper, hwork1Upper, hwork2Upper]
    cases hcontrol : state registers.control <;>
      simp [endIterationSwappedWorkWords, hcontrol]
  have hcontrolLeft : registers.control ∉ registers.work1 := by
    intro hmem
    exact (List.nodup_cons.mp hlayout.work_nodup).1
      (List.mem_append_left registers.work2 hmem)
  have hcontrolRight : registers.control ∉ registers.work2 := by
    intro hmem
    exact (List.nodup_cons.mp hlayout.work_nodup).1
      (List.mem_append_right registers.work1 hmem)
  have hswapOutside (wire : Wire)
      (hleft : wire ∉ registers.work1) (hright : wire ∉ registers.work2) :
      after wire = afterUpper wire := by
    exact controlledWorkSwapInverse_preservesOutsideWords registers.control
      registers.work1 registers.work2 afterUpper hcontrolLeft hcontrolRight
      wire hleft hright
  have hlengthTAfter : wireValues registers.lengthT after =
      (endIterationInverseLengthWords registers n windows boundary4 boundary5 state).1 := by
    calc
      wireValues registers.lengthT after = wireValues registers.lengthT afterUpper := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hswapOutside wire (hlayout.lengthT_not_work1 hwire)
          (hlayout.lengthT_not_work2 hwire)
      _ = _ := hlengthTUpper
  have hlengthRPAfter : wireValues registers.lengthRP after =
      (endIterationInverseLengthWords registers n windows boundary4 boundary5 state).2 := by
    calc
      wireValues registers.lengthRP after = wireValues registers.lengthRP afterUpper := by
        apply endIteration_wireValues_congr
        intro wire hwire
        exact hswapOutside wire (hlayout.lengthRP_not_work1 hwire)
          (hlayout.lengthRP_not_work2 hwire)
      _ = wireValues registers.lengthRP afterLower := hupperBoundary
      _ = _ := hlengthRPLower
  have hreadyAfter : EndIterationReady registers after := by
    intro wire hwire
    rw [hswapOutside wire (hlayout.scratch_not_work1 hwire)
      (hlayout.scratch_not_work2 hwire)]
    exact hreadyUpper wire hwire
  have houtside (wire : Wire)
      (hwork1 : wire ∉ registers.work1) (hwork2 : wire ∉ registers.work2)
      (hlengthT : wire ∉ registers.lengthT)
      (hlengthRP : wire ∉ registers.lengthRP) :
      after wire = state wire := by
    calc
      after wire = afterUpper wire := hswapOutside wire hwork1 hwork2
      _ = afterLower wire := hupperOutside wire hlengthT
      _ = state wire := hlowerOutside wire hlengthRP
  have hfull : run
      (swapWorkAndLengthUnarySharedInverse registers n windows) state = after := by
    simp [swapWorkAndLengthUnarySharedInverse, after, afterUpper, afterLower, run_append]
  rw [hfull]
  exact ⟨hwork1After, hwork2After,
    Prod.ext hlengthTAfter hlengthRPAfter, hreadyAfter, houtside⟩

/-- The source forward aggregate followed by its explicit reverse restores the complete basis
state whenever both decoder calls select the same certified boundaries. -/
theorem swapWorkAndLengthUnaryShared_roundTrip
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (boundary4 boundary5 : Nat)
    (hboundary4 : windows.k4 ≤ boundary4 ∧ boundary4 ≤ windows.K4)
    (hboundary5 : windows.k5 ≤ boundary5 ∧
      boundary5 ≤ windows.K5Decode n)
    (state : BasisState)
    (hlayout : EndIterationLayout registers n windows)
    (hroute4Forward : (registers.upperTree windows).routeLabel
      (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
        (run (controlledWorkSwap registers.control registers.work1 registers.work2)
          state)) = boundary4)
    (hroute5Forward : (registers.lowerTree n windows).routeLabel
      (run (addConstant registers.lengthT registers.constants registers.carry 3)
        (run
          (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows) registers.control
            (registers.rangeAccumulator windows.k4 windows.K4)
            (registers.temporary windows.k4 windows.K4) registers.carry
            (registers.path windows.k4 windows.K4)
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants)
          (run (controlledWorkSwap registers.control registers.work1 registers.work2)
            state))) = boundary5)
    (hroute5Inverse : (registers.lowerTree n windows).routeLabel
      (run (addConstant registers.lengthT registers.constants registers.carry 3)
        (run (swapWorkAndLengthUnaryShared registers n windows) state)) =
      boundary5)
    (hroute4Inverse : (registers.upperTree windows).routeLabel
      (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
        (run
          (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n) (registers.lowerTree n windows)
            registers.control
            (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
            (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
            (registers.path windows.k5 (windows.K5Decode n))
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants)
          (run (swapWorkAndLengthUnaryShared registers n windows) state))) =
      boundary4)
    (hready : EndIterationReady registers state) :
    run (swapWorkAndLengthUnarySharedInverse registers n windows)
      (run (swapWorkAndLengthUnaryShared registers n windows) state) = state := by
  let middle := run
    (swapWorkAndLengthUnaryShared registers n windows) state
  let after := run
    (swapWorkAndLengthUnarySharedInverse registers n windows) middle
  have hforward := swapWorkAndLengthUnaryShared_correct registers n windows
    boundary4 boundary5 hboundary4 hboundary5 state hlayout hroute4Forward
    hroute5Forward hready
  have hmiddleWork1 : wireValues registers.work1 middle =
      (endIterationSwappedWorkWords registers state).1 := by
    simpa only [middle] using hforward.1
  have hmiddleWork2 : wireValues registers.work2 middle =
      (endIterationSwappedWorkWords registers state).2 := by
    simpa only [middle] using hforward.2.1
  have hmiddleLengths :
      (wireValues registers.lengthT middle, wireValues registers.lengthRP middle) =
        endIterationLengthWords registers n windows boundary4 boundary5 state := by
    simpa only [middle] using hforward.2.2.1
  have hmiddleReady : EndIterationReady registers middle := by
    simpa only [middle] using hforward.2.2.2.1
  have hmiddleOutside : ∀ wire, wire ∉ registers.work1 →
      wire ∉ registers.work2 → wire ∉ registers.lengthT →
      wire ∉ registers.lengthRP → middle wire = state wire := by
    simpa only [middle] using hforward.2.2.2.2
  have hinverse := swapWorkAndLengthUnarySharedInverse_correct registers n windows boundary4 boundary5 hboundary4 hboundary5 middle hlayout
    (by simpa only [middle] using hroute5Inverse)
    (by simpa only [middle] using hroute4Inverse) hmiddleReady
  have hafterWork1 : wireValues registers.work1 after =
      (endIterationSwappedWorkWords registers middle).1 := by
    simpa only [after] using hinverse.1
  have hafterWork2 : wireValues registers.work2 after =
      (endIterationSwappedWorkWords registers middle).2 := by
    simpa only [after] using hinverse.2.1
  have hafterLengths :
      (wireValues registers.lengthT after, wireValues registers.lengthRP after) =
        endIterationInverseLengthWords registers n windows boundary4 boundary5 middle := by
    simpa only [after] using hinverse.2.2.1
  have hafterOutside : ∀ wire, wire ∉ registers.work1 →
      wire ∉ registers.work2 → wire ∉ registers.lengthT →
      wire ∉ registers.lengthRP → after wire = middle wire := by
    simpa only [after] using hinverse.2.2.2.2
  have hcontrolLeft : registers.control ∉ registers.work1 := by
    intro hmem
    exact (List.nodup_cons.mp hlayout.work_nodup).1
      (List.mem_append_left registers.work2 hmem)
  have hcontrolRight : registers.control ∉ registers.work2 := by
    intro hmem
    exact (List.nodup_cons.mp hlayout.work_nodup).1
      (List.mem_append_right registers.work1 hmem)
  have hcontrolWork : registers.control ∈
      registers.control :: registers.work1 ++ registers.work2 :=
    List.mem_append_left registers.work2 List.mem_cons_self
  have hmiddleControl : middle registers.control = state registers.control :=
    hmiddleOutside registers.control hcontrolLeft hcontrolRight
      (hlayout.workWire_not_lengthT hcontrolWork)
      (hlayout.workWire_not_lengthRP hcontrolWork)
  have hdoubleWork : endIterationSwappedWorkWords registers middle =
      (wireValues registers.work1 state, wireValues registers.work2 state) := by
    cases hcontrol : state registers.control <;>
      simp [endIterationSwappedWorkWords, hmiddleControl, hmiddleWork1,
        hmiddleWork2, hcontrol]
  have hmiddleT : wireValues registers.lengthT middle =
      highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
        (state registers.control)
        (endIterationUpperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4)
          (endIterationSwappedWorkWords registers state).1)
        (highestPositionWordAction registers.lengthT.length windows.k4 windows.K4
          (state registers.control)
          (endIterationUpperRangeBits (state registers.control) boundary4
            (zeroMapLabels windows.k4 windows.K4)
            (endIterationSwappedWorkWords registers state).2)
          (wireValues registers.lengthT state)) := by
    have := congrArg Prod.fst hmiddleLengths
    simpa only [endIterationLengthWords] using this
  have hmiddleRP : wireValues registers.lengthRP middle =
      rightLengthWordAction n registers.lengthRP.length windows.k5
        (windows.K5Decode n) (state registers.control)
        (endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (endIterationSwappedWorkWords registers state).2)
        (rightLengthWordAction n registers.lengthRP.length windows.k5
          (windows.K5Decode n) (state registers.control)
          (endIterationLowerRangeBits (state registers.control) boundary5
            (zeroMapLabels windows.k5 (windows.K5Decode n))
            (endIterationSwappedWorkWords registers state).1)
          (wireValues registers.lengthRP state)) := by
    have := congrArg Prod.snd hmiddleLengths
    simpa only [endIterationLengthWords] using this
  have hinverseLengths :
      endIterationInverseLengthWords registers n windows boundary4 boundary5 middle =
        (wireValues registers.lengthT state, wireValues registers.lengthRP state) := by
    apply Prod.ext
    · dsimp only [endIterationInverseLengthWords]
      rw [hmiddleControl, hmiddleWork1, hmiddleWork2, hmiddleT]
      exact highestPositionWordActions_involutive registers.lengthT.length
        windows.k4 windows.K4 (state registers.control)
        (endIterationUpperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4)
          (endIterationSwappedWorkWords registers state).1)
        (endIterationUpperRangeBits (state registers.control) boundary4
          (zeroMapLabels windows.k4 windows.K4)
          (endIterationSwappedWorkWords registers state).2)
        (wireValues registers.lengthT state)
        (by simp [endIterationUpperRangeBits])
        (by simp [endIterationUpperRangeBits])
    · dsimp only [endIterationInverseLengthWords]
      rw [hmiddleControl, hmiddleWork1, hmiddleWork2, hmiddleRP]
      exact rightLengthWordActions_involutive n registers.lengthRP.length
        windows.k5 (windows.K5Decode n) (state registers.control)
        (endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (endIterationSwappedWorkWords registers state).2)
        (endIterationLowerRangeBits (state registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n))
          (endIterationSwappedWorkWords registers state).1)
        (wireValues registers.lengthRP state)
        (by simp [endIterationLowerRangeBits])
        (by simp [endIterationLowerRangeBits])
  have hwork1 : wireValues registers.work1 after = wireValues registers.work1 state :=
    hafterWork1.trans (congrArg Prod.fst hdoubleWork)
  have hwork2 : wireValues registers.work2 after = wireValues registers.work2 state :=
    hafterWork2.trans (congrArg Prod.snd hdoubleWork)
  have hlengthT : wireValues registers.lengthT after =
      wireValues registers.lengthT state :=
    (congrArg Prod.fst hafterLengths).trans (congrArg Prod.fst hinverseLengths)
  have hlengthRP : wireValues registers.lengthRP after =
      wireValues registers.lengthRP state :=
    (congrArg Prod.snd hafterLengths).trans (congrArg Prod.snd hinverseLengths)
  have hstate : after = state := by
    funext wire
    by_cases hwork1Mem : wire ∈ registers.work1
    · exact endIteration_wireValues_eq_at registers.work1 after state hwork1
        wire hwork1Mem
    by_cases hwork2Mem : wire ∈ registers.work2
    · exact endIteration_wireValues_eq_at registers.work2 after state hwork2
        wire hwork2Mem
    by_cases hlengthTMem : wire ∈ registers.lengthT
    · exact endIteration_wireValues_eq_at registers.lengthT after state hlengthT
        wire hlengthTMem
    by_cases hlengthRPMem : wire ∈ registers.lengthRP
    · exact endIteration_wireValues_eq_at registers.lengthRP after state hlengthRP
        wire hlengthRPMem
    exact (hafterOutside wire hwork1Mem hwork2Mem hlengthTMem hlengthRPMem).trans
      (hmiddleOutside wire hwork1Mem hwork2Mem hlengthTMem hlengthRPMem)
  simpa only [after, middle] using hstate

/-- The decoder routes required by the explicit reverse are consequences of the forward
routes.  The lower block leaves the left-boundary decoder word unchanged, and running that
block a second time cancels its two Boolean-word actions.  The upper inverse decoder therefore
sees the original reflected right boundary as well. -/
theorem swapWorkAndLengthUnaryShared_inverseRoutes
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (boundary4 boundary5 : Nat)
    (hboundary4 : windows.k4 ≤ boundary4 ∧ boundary4 ≤ windows.K4)
    (hboundary5 : windows.k5 ≤ boundary5 ∧
      boundary5 ≤ windows.K5Decode n)
    (state : BasisState)
    (hlayout : EndIterationLayout registers n windows)
    (hroute4Forward : (registers.upperTree windows).routeLabel
      (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
        (run (controlledWorkSwap registers.control registers.work1 registers.work2)
          state)) = boundary4)
    (hroute5Forward : (registers.lowerTree n windows).routeLabel
      (run (addConstant registers.lengthT registers.constants registers.carry 3)
        (run
          (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows)
            registers.control (registers.rangeAccumulator windows.k4 windows.K4)
            (registers.temporary windows.k4 windows.K4) registers.carry
            (registers.path windows.k4 windows.K4)
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants)
          (run (controlledWorkSwap registers.control registers.work1 registers.work2)
            state))) = boundary5)
    (hready : EndIterationReady registers state) :
    let middle := run (swapWorkAndLengthUnaryShared registers n windows) state
    let afterLower := run
      (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n)
        (registers.lowerTree n windows) registers.control
        (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
        (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
        (registers.path windows.k5 (windows.K5Decode n))
        registers.work1At registers.work2At registers.lengthT registers.lengthRP
        registers.constants) middle
    (registers.lowerTree n windows).routeLabel
        (run (addConstant registers.lengthT registers.constants registers.carry 3)
          middle) = boundary5 ∧
      (registers.upperTree windows).routeLabel
        (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
          afterLower) = boundary4 := by
  let swapped := run
    (controlledWorkSwap registers.control registers.work1 registers.work2) state
  let afterUpper := run
    (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows)
      registers.control (registers.rangeAccumulator windows.k4 windows.K4)
      (registers.temporary windows.k4 windows.K4) registers.carry
      (registers.path windows.k4 windows.K4)
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants) swapped
  let middle := run
    (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n)
      (registers.lowerTree n windows) registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants) afterUpper
  let afterLower := run
    (lenUpdateLrpUnary n windows.k5 (windows.K5Decode n)
      (registers.lowerTree n windows) registers.control
      (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
      (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
      (registers.path windows.k5 (windows.K5Decode n))
      registers.work1At registers.work2At registers.lengthT registers.lengthRP
      registers.constants) middle
  have hworkLength : registers.work1.length = registers.work2.length :=
    hlayout.work1_length.trans hlayout.work2_length.symm
  have hcontrolLeft : registers.control ∉ registers.work1 := by
    intro hmem
    exact (List.nodup_cons.mp hlayout.work_nodup).1
      (List.mem_append_left registers.work2 hmem)
  have hcontrolRight : registers.control ∉ registers.work2 := by
    intro hmem
    exact (List.nodup_cons.mp hlayout.work_nodup).1
      (List.mem_append_right registers.work1 hmem)
  have hswapOutside (wire : Wire)
      (hleft : wire ∉ registers.work1) (hright : wire ∉ registers.work2) :
      swapped wire = state wire := by
    exact controlledWorkSwap_preservesOutsideWords registers.control registers.work1
      registers.work2 state hcontrolLeft hcontrolRight wire hleft hright
  have hreadySwapped : EndIterationReady registers swapped := by
    intro wire hwire
    rw [hswapOutside wire (hlayout.scratch_not_work1 hwire)
      (hlayout.scratch_not_work2 hwire)]
    exact hready wire hwire
  obtain ⟨hconstants4, hpath4, hrange4, htemporary4⟩ :=
    hlayout.clean_components4 hreadySwapped
  have hpositiveRP : 0 < registers.lengthRP.length := by
    rw [hlayout.lengthRP_length]
    exact hlayout.width_positive
  have hconstantsRP : registers.constants.length = registers.lengthRP.length :=
    hlayout.constants_length.trans hlayout.lengthRP_length.symm
  have hupper := lenUpdateLtUnary_correct_shared n windows.k4 windows.K4 boundary4
    hlayout.k4_le_K4 hboundary4 (registers.upperTree windows) registers.control
    (registers.rangeAccumulator windows.k4 windows.K4)
    (registers.temporary windows.k4 windows.K4) registers.carry
    (registers.path windows.k4 windows.K4)
    registers.work1At registers.work2At registers.lengthT registers.lengthRP
    registers.constants swapped hpositiveRP hconstantsRP hlayout.upper
    (registers.upperTree_visitLabels windows hlayout.k4_le_K4)
    (by simpa only [swapped] using hroute4Forward)
    hconstants4 hpath4 hrange4 htemporary4
  have hupperBoundary : wireValues registers.lengthRP afterUpper =
      wireValues registers.lengthRP swapped := by
    simpa only [afterUpper] using hupper.2.1
  have hupperOutside : ∀ wire, wire ∉ registers.lengthT →
      afterUpper wire = swapped wire := by
    simpa only [afterUpper] using hupper.2.2.2.2
  have hreadyUpper : EndIterationReady registers afterUpper := by
    intro wire hwire
    rw [hupperOutside wire (hlayout.scratch_not_lengthT hwire)]
    exact hreadySwapped wire hwire
  obtain ⟨hconstants5, hpath5, hrange5, htemporary5⟩ :=
    hlayout.clean_components5 hreadyUpper
  have hconstantsT : registers.constants.length = registers.lengthT.length := by
    simpa only [EndIterationRegisters.width] using hlayout.constants_length
  have hlowerForward := lenUpdateLrpUnary_correct_shared n windows.k5
    (windows.K5Decode n) boundary5 hlayout.k5_le_decode hboundary5
    (registers.lowerTree n windows) registers.control
    (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
    (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
    (registers.path windows.k5 (windows.K5Decode n))
    registers.work1At registers.work2At registers.lengthT registers.lengthRP
    registers.constants afterUpper hconstantsT hlayout.lower
    (registers.lowerTree_visitLabels n windows hlayout.k5_le_decode)
    (by simpa only [afterUpper, swapped] using hroute5Forward)
    hconstants5 hpath5 hrange5 htemporary5
  have hlowerForwardOutside : ∀ wire, wire ∉ registers.lengthRP →
      middle wire = afterUpper wire := by
    simpa only [middle] using hlowerForward.2.2.2.2
  have hreadyMiddle : EndIterationReady registers middle := by
    intro wire hwire
    rw [hlowerForwardOutside wire (hlayout.scratch_not_lengthRP hwire)]
    exact hreadyUpper wire hwire
  have hroute5AtUpper : (registers.lowerTree n windows).routeLabel
      (run (addConstant registers.lengthT registers.constants registers.carry 3)
        afterUpper) = boundary5 := by
    simpa only [afterUpper, swapped] using hroute5Forward
  have hroute5Inverse : (registers.lowerTree n windows).routeLabel
      (run (addConstant registers.lengthT registers.constants registers.carry 3)
        middle) = boundary5 := by
    calc
      (registers.lowerTree n windows).routeLabel
          (run (addConstant registers.lengthT registers.constants registers.carry 3)
            middle) =
        (registers.lowerTree n windows).routeLabel
          (run (addConstant registers.lengthT registers.constants registers.carry 3)
            afterUpper) := by
              apply (registers.lowerTree n windows).routeLabel_congr
              intro wire hwire
              have hnotTarget : wire ∉ registers.lengthRP :=
                hlayout.lower.work1Bits.mapWire_not_target (by
                  simp [zeroMapWires, zeroMapProtectedWires, hwire])
              by_cases hsupport : wire ∈
                  registers.constants ++ registers.lengthT ++ [registers.carry]
              · apply (addConstant_usesOnly registers.lengthT registers.constants
                    registers.carry 3).run_congrOn
                  middle afterUpper _ wire hsupport
                intro next hnext
                apply hlowerForwardOutside
                rcases List.mem_append.mp hnext with hnext | hcarry
                · rcases List.mem_append.mp hnext with hconstant | hlengthT
                  · exact List.disjoint_left.mp
                      hlayout.lower.constantCarryDisjointTarget
                      (List.mem_append_left [registers.carry] hconstant)
                  · exact hlayout.lengthT_not_lengthRP hlengthT
                · exact List.disjoint_left.mp
                    hlayout.lower.constantCarryDisjointTarget
                    (List.mem_append_right registers.constants hcarry)
              · rw [(addConstant_usesOnly registers.lengthT registers.constants
                    registers.carry 3).preservesOutside middle hsupport,
                  (addConstant_usesOnly registers.lengthT registers.constants
                    registers.carry 3).preservesOutside afterUpper hsupport]
                exact hlowerForwardOutside wire hnotTarget
      _ = boundary5 := hroute5AtUpper
  obtain ⟨hconstants5Middle, hpath5Middle, hrange5Middle, htemporary5Middle⟩ :=
    hlayout.clean_components5 hreadyMiddle
  have hlowerInverse := lenUpdateLrpUnary_correct_shared n windows.k5
    (windows.K5Decode n) boundary5 hlayout.k5_le_decode hboundary5
    (registers.lowerTree n windows) registers.control
    (registers.rangeAccumulator windows.k5 (windows.K5Decode n))
    (registers.temporary windows.k5 (windows.K5Decode n)) registers.carry
    (registers.path windows.k5 (windows.K5Decode n))
    registers.work1At registers.work2At registers.lengthT registers.lengthRP
    registers.constants middle hconstantsT hlayout.lower
    (registers.lowerTree_visitLabels n windows hlayout.k5_le_decode)
    hroute5Inverse hconstants5Middle hpath5Middle hrange5Middle htemporary5Middle
  have hlowerInverseOutside : ∀ wire, wire ∉ registers.lengthRP →
      afterLower wire = middle wire := by
    simpa only [afterLower] using hlowerInverse.2.2.2.2
  have hcontrolMiddle : middle registers.control = afterUpper registers.control :=
    hlowerForwardOutside registers.control hlayout.lower.work1Bits.control_not_target
  have hwork1Middle :
      lowerRangeBits (middle registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work1At middle =
        lowerRangeBits (afterUpper registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work1At afterUpper := by
    unfold lowerRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hcontrolMiddle,
      hlowerForwardOutside (registers.work1At label)
        (hlayout.lower.work2Bits.dirty_not_target hlabel)]
  have hwork2Middle :
      lowerRangeBits (middle registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work2At middle =
        lowerRangeBits (afterUpper registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work2At afterUpper := by
    unfold lowerRangeBits
    apply List.map_congr_left
    intro label hlabel
    rw [hcontrolMiddle,
      hlowerForwardOutside (registers.work2At label)
        (hlayout.lower.work1Bits.dirty_not_target hlabel)]
  have hlowerForwardTarget : wireValues registers.lengthRP middle =
      rightLengthWordAction n registers.lengthRP.length windows.k5
        (windows.K5Decode n) (afterUpper registers.control)
        (lowerRangeBits (afterUpper registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work2At afterUpper)
        (rightLengthWordAction n registers.lengthRP.length windows.k5
          (windows.K5Decode n) (afterUpper registers.control)
          (lowerRangeBits (afterUpper registers.control) boundary5
            (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work1At afterUpper)
          (wireValues registers.lengthRP afterUpper)) := by
    simpa only [middle] using hlowerForward.1
  have hlowerInverseTarget : wireValues registers.lengthRP afterLower =
      rightLengthWordAction n registers.lengthRP.length windows.k5
        (windows.K5Decode n) (middle registers.control)
        (lowerRangeBits (middle registers.control) boundary5
          (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work2At middle)
        (rightLengthWordAction n registers.lengthRP.length windows.k5
          (windows.K5Decode n) (middle registers.control)
          (lowerRangeBits (middle registers.control) boundary5
            (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work1At middle)
          (wireValues registers.lengthRP middle)) := by
    simpa only [afterLower] using hlowerInverse.1
  have hafterLowerBoundary : wireValues registers.lengthRP afterLower =
      wireValues registers.lengthRP afterUpper := by
    rw [hlowerInverseTarget, hwork1Middle, hwork2Middle, hcontrolMiddle,
      hlowerForwardTarget]
    exact rightLengthWordActions_involutive n registers.lengthRP.length
      windows.k5 (windows.K5Decode n) (afterUpper registers.control)
      (lowerRangeBits (afterUpper registers.control) boundary5
        (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work2At afterUpper)
      (lowerRangeBits (afterUpper registers.control) boundary5
        (zeroMapLabels windows.k5 (windows.K5Decode n)) registers.work1At afterUpper)
      (wireValues registers.lengthRP afterUpper)
      (by simp [lowerRangeBits]) (by simp [lowerRangeBits])
  have hrightBoundary : wireValues registers.lengthRP afterLower =
      wireValues registers.lengthRP swapped :=
    hafterLowerBoundary.trans hupperBoundary
  have hconstantsAfterLower :
      Clean (registers.constants ++ [registers.carry]) afterLower := by
    simpa only [afterLower] using hlowerInverse.2.2.1
  have hroute4AtSwapped : (registers.upperTree windows).routeLabel
      (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
        swapped) = boundary4 := by
    simpa only [swapped] using hroute4Forward
  have hroute4Inverse : (registers.upperTree windows).routeLabel
      (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
        afterLower) = boundary4 := by
    calc
      (registers.upperTree windows).routeLabel
          (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
            afterLower) =
        (registers.upperTree windows).routeLabel
          (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
            swapped) := by
              apply (registers.upperTree windows).routeLabel_congr
              intro wire hwire
              have hnotTarget : wire ∉ registers.lengthT :=
                hlayout.upper.work1Bits.mapWire_not_target (by
                  simp [zeroMapWires, zeroMapProtectedWires, hwire])
              by_cases hsupport : wire ∈
                  registers.constants ++ registers.lengthRP ++ [registers.carry]
              · apply (constMinus_usesOnly registers.lengthRP registers.constants
                    registers.carry (n + 2)).run_congrOn
                  afterLower swapped _ wire hsupport
                intro next hnext
                by_cases hlengthRP : next ∈ registers.lengthRP
                · exact endIteration_wireValues_eq_at registers.lengthRP afterLower swapped
                    hrightBoundary next hlengthRP
                · have hconstantCarry : next ∈ registers.constants ++ [registers.carry] := by
                    rcases List.mem_append.mp hnext with hnext | hcarry
                    · rcases List.mem_append.mp hnext with hconstant | hfalse
                      · exact List.mem_append_left [registers.carry] hconstant
                      · exact (hlengthRP hfalse).elim
                    · exact List.mem_append_right registers.constants hcarry
                  rw [hconstantsAfterLower next hconstantCarry,
                    hconstants4 next hconstantCarry]
              · have hnotRP : wire ∉ registers.lengthRP := by
                  intro hmem
                  exact hsupport (by simp [hmem])
                calc
                  run (constMinus registers.lengthRP registers.constants registers.carry
                      (n + 2)) afterLower wire = afterLower wire :=
                    (constMinus_usesOnly registers.lengthRP registers.constants
                      registers.carry (n + 2)).preservesOutside afterLower hsupport
                  _ = middle wire := hlowerInverseOutside wire hnotRP
                  _ = afterUpper wire := hlowerForwardOutside wire hnotRP
                  _ = swapped wire := hupperOutside wire hnotTarget
                  _ = run (constMinus registers.lengthRP registers.constants registers.carry
                      (n + 2)) swapped wire :=
                    ((constMinus_usesOnly registers.lengthRP registers.constants
                      registers.carry (n + 2)).preservesOutside swapped hsupport).symm
      _ = boundary4 := hroute4AtSwapped
  simpa only [swapWorkAndLengthUnaryShared, Classical.run_append,
    middle, afterUpper, swapped, afterLower] using
      (And.intro hroute5Inverse hroute4Inverse)

/-- The source forward aggregate followed by its explicit reverse restores the complete basis
state using only the forward decoder certificates. -/
theorem swapWorkAndLengthUnaryShared_roundTrip_auto
    (registers : EndIterationRegisters) (n : Nat)
    (windows : EndIterationWindows)
    (boundary4 boundary5 : Nat)
    (hboundary4 : windows.k4 ≤ boundary4 ∧ boundary4 ≤ windows.K4)
    (hboundary5 : windows.k5 ≤ boundary5 ∧
      boundary5 ≤ windows.K5Decode n)
    (state : BasisState)
    (hlayout : EndIterationLayout registers n windows)
    (hroute4Forward : (registers.upperTree windows).routeLabel
      (run (constMinus registers.lengthRP registers.constants registers.carry (n + 2))
        (run (controlledWorkSwap registers.control registers.work1 registers.work2)
          state)) = boundary4)
    (hroute5Forward : (registers.lowerTree n windows).routeLabel
      (run (addConstant registers.lengthT registers.constants registers.carry 3)
        (run
          (lenUpdateLtUnary n windows.k4 windows.K4 (registers.upperTree windows)
            registers.control (registers.rangeAccumulator windows.k4 windows.K4)
            (registers.temporary windows.k4 windows.K4) registers.carry
            (registers.path windows.k4 windows.K4)
            registers.work1At registers.work2At registers.lengthT registers.lengthRP
            registers.constants)
          (run (controlledWorkSwap registers.control registers.work1 registers.work2)
            state))) = boundary5)
    (hready : EndIterationReady registers state) :
    run (swapWorkAndLengthUnarySharedInverse registers n windows)
      (run (swapWorkAndLengthUnaryShared registers n windows) state) = state := by
  obtain ⟨hroute5Inverse, hroute4Inverse⟩ :=
    swapWorkAndLengthUnaryShared_inverseRoutes registers n windows boundary4 boundary5
      hboundary4 hboundary5 state hlayout hroute4Forward hroute5Forward hready
  exact swapWorkAndLengthUnaryShared_roundTrip registers n windows boundary4 boundary5
    hboundary4 hboundary5 state hlayout hroute4Forward hroute5Forward
    hroute5Inverse hroute4Inverse hready

/-! ## Concrete secp256k1 production allocation -/

private def endIterationProductionTreeDepth : UnaryActionTree → Nat
  | .leaf _ => 0
  | .node _ zero one => 1 + max (endIterationProductionTreeDepth zero) (endIterationProductionTreeDepth one)

private theorem endIterationProductionTree_layout_of_separated
    (tree : UnaryActionTree) (control : Wire) (path : List Wire)
    (hdepth : endIterationProductionTreeDepth tree ≤ path.length)
    (hcontrolIndex : control ∉ tree.indexWires)
    (hcontrolPath : control ∉ path)
    (hpathNodup : path.Nodup)
    (hindexPath : ∀ wire ∈ tree.indexWires, wire ∉ path) :
    tree.Layout control path := by
  induction tree generalizing control path with
  | leaf label =>
      exact .leaf label control path (by
        simp only [List.nodup_cons]
        exact ⟨hcontrolPath, hpathNodup⟩)
  | node indexBit zero one ihZero ihOne =>
      cases path with
      | nil => simp [endIterationProductionTreeDepth] at hdepth
      | cons next rest =>
          have hrestNodup : rest.Nodup :=
            (List.nodup_cons.mp hpathNodup).2
          have hnextRest : next ∉ rest :=
            (List.nodup_cons.mp hpathNodup).1
          have hlocal :
              (control ::
                ((UnaryActionTree.node indexBit zero one).indexWires.dedup ++
                  (next :: rest))).Nodup := by
            rw [List.nodup_cons, List.nodup_append]
            refine ⟨?_, List.nodup_dedup _, hpathNodup, ?_⟩
            · intro hmem
              rw [List.mem_append] at hmem
              exact hmem.elim
                (fun h => hcontrolIndex (by simpa using h)) hcontrolPath
            · intro wire hwire pathWire hpathWire heq
              exact hindexPath wire (by simpa using hwire)
                (by simpa [← heq] using hpathWire)
          exact .node indexBit control next zero one rest hlocal
            (ihZero next rest
              (by simp [endIterationProductionTreeDepth] at hdepth; omega)
              (by
                intro hmem
                exact hindexPath next
                  (by simp [UnaryActionTree.indexWires, hmem]) (by simp))
              hnextRest hrestNodup
              (by
                intro wire hwire hrest
                exact hindexPath wire
                  (by simp [UnaryActionTree.indexWires, hwire]) (by simp [hrest])))
            (ihOne next rest
              (by simp [endIterationProductionTreeDepth] at hdepth; omega)
              (by
                intro hmem
                exact hindexPath next
                  (by simp [UnaryActionTree.indexWires, hmem]) (by simp))
              hnextRest hrestNodup
              (by
                intro wire hwire hrest
                exact hindexPath wire
                  (by simp [UnaryActionTree.indexWires, hwire]) (by simp [hrest])))

/-- Dense 549-role allocation for the pinned `n = 256`, `T = 1024` source call.  The same
12-wire scratch slice is reused serially by the upper and lower length blocks. -/
def endIterationProductionRegisters : EndIterationRegisters where
  control := 0
  work1 := List.range' 1 259
  work2 := List.range' 260 259
  lengthT := List.range' 519 9
  lengthRP := List.range' 528 9
  scratch := List.range' 537 12

private theorem endIterationProduction_work1At {label : Nat}
    (hlow : 0 < label) (hhigh : label ≤ 259) :
    endIterationProductionRegisters.work1At label = label := by
  change (List.range' 1 259).getD (label - 1) 0 = label
  rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'_1]
  omega

private theorem endIterationProduction_work2At {label : Nat}
    (hlow : 0 < label) (hhigh : label ≤ 259) :
    endIterationProductionRegisters.work2At label = 259 + label := by
  change (List.range' 260 259).getD (label - 1) 0 = 259 + label
  rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'_1]
  omega

private theorem endIterationProduction_cell12 {k K label : Nat} {range temporary guard : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hlabel : label ∈ zeroMapLabels k K)
    (hrangeLow : 519 ≤ range) (htemporaryLow : 519 ≤ temporary)
    (hrangeTemporary : range ≠ temporary)
    (hguard : guard = 0 ∨
      ∃ neighbour ∈ zeroMapLabels k K,
        neighbour ≠ label ∧ guard = endIterationProductionRegisters.work2At neighbour) :
    [range, endIterationProductionRegisters.work1At label, guard,
      endIterationProductionRegisters.work2At label, temporary].Nodup := by
  obtain ⟨hlabelLow, hlabelHigh⟩ := (mem_zeroMapLabels hkK).mp hlabel
  have hlabelPositive : 0 < label := lt_of_lt_of_le hkPositive hlabelLow
  have hlabelBound : label ≤ 259 := hlabelHigh.trans hK
  have hwork1 := endIterationProduction_work1At hlabelPositive hlabelBound
  have hwork2 := endIterationProduction_work2At hlabelPositive hlabelBound
  rcases hguard with rfl | ⟨neighbour, hneighbour, hne, rfl⟩
  · rw [hwork1, hwork2]
    have hwork2Bound : 259 + label ≤ 518 := by omega
    have hlabelRange : label < range :=
      lt_of_le_of_lt hlabelBound
        (lt_of_lt_of_le (by decide : 259 < 519) hrangeLow)
    have hwork2Range : 259 + label < range :=
      lt_of_le_of_lt hwork2Bound
        (lt_of_lt_of_le (by decide : 518 < 519) hrangeLow)
    have hlabelTemporary : label < temporary :=
      lt_of_le_of_lt hlabelBound
        (lt_of_lt_of_le (by decide : 259 < 519) htemporaryLow)
    have hwork2Temporary : 259 + label < temporary :=
      lt_of_le_of_lt hwork2Bound
        (lt_of_lt_of_le (by decide : 518 < 519) htemporaryLow)
    have hzeroRange : 0 < range := lt_of_lt_of_le (by decide) hrangeLow
    have hzeroTemporary : 0 < temporary :=
      lt_of_lt_of_le (by decide) htemporaryLow
    have hlabelWork2 : label < 259 + label := by omega
    have hzeroWork2 : 0 < 259 + label := by omega
    simp [hlabelRange.ne', hwork2Range.ne', hlabelPositive.ne',
      hlabelTemporary.ne, hwork2Temporary.ne, hzeroWork2.ne,
      hzeroRange.ne', hzeroTemporary.ne, hrangeTemporary]
  · obtain ⟨hneighbourLow, hneighbourHigh⟩ :=
      (mem_zeroMapLabels hkK).mp hneighbour
    have hneighbourPositive : 0 < neighbour :=
      lt_of_lt_of_le hkPositive hneighbourLow
    have hneighbourBound : neighbour ≤ 259 := hneighbourHigh.trans hK
    have hneighbourWork := endIterationProduction_work2At hneighbourPositive hneighbourBound
    rw [hwork1, hwork2, hneighbourWork]
    have hneighbourWorkBound : 259 + neighbour ≤ 518 := by omega
    have hwork2Bound : 259 + label ≤ 518 := by omega
    have hlabelRange : label < range :=
      lt_of_le_of_lt hlabelBound
        (lt_of_lt_of_le (by decide : 259 < 519) hrangeLow)
    have hneighbourRange : 259 + neighbour < range :=
      lt_of_le_of_lt hneighbourWorkBound
        (lt_of_lt_of_le (by decide : 518 < 519) hrangeLow)
    have hwork2Range : 259 + label < range :=
      lt_of_le_of_lt hwork2Bound
        (lt_of_lt_of_le (by decide : 518 < 519) hrangeLow)
    have hlabelNeighbour : label < 259 + neighbour := by omega
    have hlabelTemporary : label < temporary :=
      lt_of_le_of_lt hlabelBound
        (lt_of_lt_of_le (by decide : 259 < 519) htemporaryLow)
    have hneighbourTemporary : 259 + neighbour < temporary :=
      lt_of_le_of_lt hneighbourWorkBound
        (lt_of_lt_of_le (by decide : 518 < 519) htemporaryLow)
    have hwork2Temporary : 259 + label < temporary :=
      lt_of_le_of_lt hwork2Bound
        (lt_of_lt_of_le (by decide : 518 < 519) htemporaryLow)
    simp [hlabelRange.ne', hneighbourRange.ne', hwork2Range.ne',
      hlabelNeighbour.ne, hlabelTemporary.ne,
      hneighbourTemporary.ne, hwork2Temporary.ne, hrangeTemporary,
      Nat.add_left_cancel_iff, hne]

private theorem endIterationProduction_cell21 {k K label : Nat} {range temporary guard : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hlabel : label ∈ zeroMapLabels k K)
    (hrangeLow : 519 ≤ range) (htemporaryLow : 519 ≤ temporary)
    (hrangeTemporary : range ≠ temporary)
    (hguard : guard = 0 ∨
      ∃ neighbour ∈ zeroMapLabels k K,
        neighbour ≠ label ∧ guard = endIterationProductionRegisters.work1At neighbour) :
    [range, endIterationProductionRegisters.work2At label, guard,
      endIterationProductionRegisters.work1At label, temporary].Nodup := by
  obtain ⟨hlabelLow, hlabelHigh⟩ := (mem_zeroMapLabels hkK).mp hlabel
  have hlabelPositive : 0 < label := lt_of_lt_of_le hkPositive hlabelLow
  have hlabelBound : label ≤ 259 := hlabelHigh.trans hK
  have hwork1 := endIterationProduction_work1At hlabelPositive hlabelBound
  have hwork2 := endIterationProduction_work2At hlabelPositive hlabelBound
  rcases hguard with rfl | ⟨neighbour, hneighbour, hne, rfl⟩
  · rw [hwork1, hwork2]
    have hwork2Bound : 259 + label ≤ 518 := by omega
    have hwork2Range : 259 + label < range :=
      lt_of_le_of_lt hwork2Bound
        (lt_of_lt_of_le (by decide : 518 < 519) hrangeLow)
    have hlabelRange : label < range :=
      lt_of_le_of_lt hlabelBound
        (lt_of_lt_of_le (by decide : 259 < 519) hrangeLow)
    have hwork2Temporary : 259 + label < temporary :=
      lt_of_le_of_lt hwork2Bound
        (lt_of_lt_of_le (by decide : 518 < 519) htemporaryLow)
    have hlabelTemporary : label < temporary :=
      lt_of_le_of_lt hlabelBound
        (lt_of_lt_of_le (by decide : 259 < 519) htemporaryLow)
    have hzeroRange : 0 < range := lt_of_lt_of_le (by decide) hrangeLow
    have hzeroTemporary : 0 < temporary :=
      lt_of_lt_of_le (by decide) htemporaryLow
    simp [hwork2Range.ne', hlabelRange.ne', hwork2Temporary.ne,
      hlabelTemporary.ne, hzeroRange.ne', hzeroTemporary.ne,
      hlabelPositive.ne, hlabelPositive.ne',
      hrangeTemporary]
  · obtain ⟨hneighbourLow, hneighbourHigh⟩ :=
      (mem_zeroMapLabels hkK).mp hneighbour
    have hneighbourPositive : 0 < neighbour :=
      lt_of_lt_of_le hkPositive hneighbourLow
    have hneighbourBound : neighbour ≤ 259 := hneighbourHigh.trans hK
    have hneighbourWork := endIterationProduction_work1At hneighbourPositive hneighbourBound
    rw [hwork1, hwork2, hneighbourWork]
    have hwork2Bound : 259 + label ≤ 518 := by omega
    have hwork2Range : 259 + label < range :=
      lt_of_le_of_lt hwork2Bound
        (lt_of_lt_of_le (by decide : 518 < 519) hrangeLow)
    have hneighbourRange : neighbour < range :=
      lt_of_le_of_lt hneighbourBound
        (lt_of_lt_of_le (by decide : 259 < 519) hrangeLow)
    have hlabelRange : label < range :=
      lt_of_le_of_lt hlabelBound
        (lt_of_lt_of_le (by decide : 259 < 519) hrangeLow)
    have hwork2Neighbour : neighbour < 259 + label := by omega
    have hwork2Temporary : 259 + label < temporary :=
      lt_of_le_of_lt hwork2Bound
        (lt_of_lt_of_le (by decide : 518 < 519) htemporaryLow)
    have hneighbourTemporary : neighbour < temporary :=
      lt_of_le_of_lt hneighbourBound
        (lt_of_lt_of_le (by decide : 259 < 519) htemporaryLow)
    have hlabelTemporary : label < temporary :=
      lt_of_le_of_lt hlabelBound
        (lt_of_lt_of_le (by decide : 259 < 519) htemporaryLow)
    simp [hwork2Range.ne', hneighbourRange.ne', hlabelRange.ne',
      hwork2Neighbour.ne', hwork2Temporary.ne,
      hneighbourTemporary.ne, hlabelTemporary.ne, hrangeTemporary, hne]

private theorem endIterationProduction_work1_map_nodup {k K : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259) :
    ((zeroMapLabels k K).map endIterationProductionRegisters.work1At).Nodup := by
  apply (zeroMapLabels_nodup k K).map_on
  intro left hleft right hright heq
  obtain ⟨hleftLow, hleftHigh⟩ := (mem_zeroMapLabels hkK).mp hleft
  obtain ⟨hrightLow, hrightHigh⟩ := (mem_zeroMapLabels hkK).mp hright
  rw [endIterationProduction_work1At (lt_of_lt_of_le hkPositive hleftLow) (hleftHigh.trans hK),
    endIterationProduction_work1At (lt_of_lt_of_le hkPositive hrightLow) (hrightHigh.trans hK)] at heq
  exact heq

private theorem endIterationProduction_work2_map_nodup {k K : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259) :
    ((zeroMapLabels k K).map endIterationProductionRegisters.work2At).Nodup := by
  apply (zeroMapLabels_nodup k K).map_on
  intro left hleft right hright heq
  obtain ⟨hleftLow, hleftHigh⟩ := (mem_zeroMapLabels hkK).mp hleft
  obtain ⟨hrightLow, hrightHigh⟩ := (mem_zeroMapLabels hkK).mp hright
  rw [endIterationProduction_work2At (lt_of_lt_of_le hkPositive hleftLow) (hleftHigh.trans hK),
    endIterationProduction_work2At (lt_of_lt_of_le hkPositive hrightLow) (hrightHigh.trans hK)] at heq
  exact Nat.add_left_cancel heq

private theorem endIterationProduction_work_maps_disjoint {k K : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259) :
    List.Disjoint ((zeroMapLabels k K).map endIterationProductionRegisters.work1At)
      ((zeroMapLabels k K).map endIterationProductionRegisters.work2At) := by
  apply List.disjoint_left.mpr
  intro wire hwork1 hwork2
  obtain ⟨label1, hlabel1, heq1⟩ := List.mem_map.mp hwork1
  obtain ⟨label2, hlabel2, heq2⟩ := List.mem_map.mp hwork2
  obtain ⟨hlabel1Low, hlabel1High⟩ := (mem_zeroMapLabels hkK).mp hlabel1
  obtain ⟨hlabel2Low, hlabel2High⟩ := (mem_zeroMapLabels hkK).mp hlabel2
  rw [endIterationProduction_work1At (lt_of_lt_of_le hkPositive hlabel1Low)
      (hlabel1High.trans hK)] at heq1
  rw [endIterationProduction_work2At (lt_of_lt_of_le hkPositive hlabel2Low)
      (hlabel2High.trans hK)] at heq2
  subst wire
  have hlt : label1 < 259 + label2 := by omega
  exact hlt.ne heq2.symm

private theorem endIterationProduction_work_maps_nodup {k K : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259) :
    (((zeroMapLabels k K).map endIterationProductionRegisters.work1At) ++
      (zeroMapLabels k K).map endIterationProductionRegisters.work2At).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨endIterationProduction_work1_map_nodup hkPositive hkK hK,
    endIterationProduction_work2_map_nodup hkPositive hkK hK, ?_⟩
  intro left hleft right hright heq
  subst right
  exact List.disjoint_left.mp (endIterationProduction_work_maps_disjoint hkPositive hkK hK)
    hleft hright

private theorem endIterationProduction_work_map_bounds {k K wire : Nat}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hwire : wire ∈
      ((zeroMapLabels k K).map endIterationProductionRegisters.work1At) ++
        (zeroMapLabels k K).map endIterationProductionRegisters.work2At) :
    0 < wire ∧ wire ≤ 518 := by
  rcases List.mem_append.mp hwire with hwork1 | hwork2
  · obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp hwork1
    obtain ⟨hlabelLow, hlabelHigh⟩ := (mem_zeroMapLabels hkK).mp hlabel
    rw [endIterationProduction_work1At (lt_of_lt_of_le hkPositive hlabelLow)
      (hlabelHigh.trans hK)]
    omega
  · obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp hwork2
    obtain ⟨hlabelLow, hlabelHigh⟩ := (mem_zeroMapLabels hkK).mp hlabel
    rw [endIterationProduction_work2At (lt_of_lt_of_le hkPositive hlabelLow)
      (hlabelHigh.trans hK)]
    omega

private theorem endIterationProduction_zeroMap_tail_nodup {k K : Nat} {range temporary : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hrangeLow : 519 ≤ range) (htemporaryLow : 519 ≤ temporary)
    (hrangeTemporary : range ≠ temporary) :
    (range :: temporary ::
      (zeroMapLabels k K).map endIterationProductionRegisters.work1At ++
      (zeroMapLabels k K).map endIterationProductionRegisters.work2At).Nodup := by
  change (range :: temporary ::
    ((zeroMapLabels k K).map endIterationProductionRegisters.work1At ++
      (zeroMapLabels k K).map endIterationProductionRegisters.work2At)).Nodup
  rw [List.nodup_cons, List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with heq | hwork
    · exact hrangeTemporary heq
    · exact (not_lt_of_ge hrangeLow)
        ((endIterationProduction_work_map_bounds hkPositive hkK hK hwork).2.trans_lt (by decide))
  · constructor
    · intro hwork
      exact (not_lt_of_ge htemporaryLow)
        ((endIterationProduction_work_map_bounds hkPositive hkK hK hwork).2.trans_lt (by decide))
    · exact endIterationProduction_work_maps_nodup hkPositive hkK hK

private theorem endIterationProduction_zeroMap_tail_reverse_nodup {k K : Nat}
    {range temporary : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hrangeLow : 519 ≤ range) (htemporaryLow : 519 ≤ temporary)
    (hrangeTemporary : range ≠ temporary) :
    (range :: temporary ::
      (zeroMapLabels k K).map endIterationProductionRegisters.work2At ++
      (zeroMapLabels k K).map endIterationProductionRegisters.work1At).Nodup := by
  change (range :: temporary ::
    ((zeroMapLabels k K).map endIterationProductionRegisters.work2At ++
      (zeroMapLabels k K).map endIterationProductionRegisters.work1At)).Nodup
  rw [List.nodup_cons, List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with heq | hwork
    · exact hrangeTemporary heq
    · have hwork' : range ∈
          ((zeroMapLabels k K).map endIterationProductionRegisters.work1At) ++
            (zeroMapLabels k K).map endIterationProductionRegisters.work2At := by
          rcases List.mem_append.mp hwork with hwork2 | hwork1
          · exact List.mem_append.mpr (Or.inr hwork2)
          · exact List.mem_append.mpr (Or.inl hwork1)
      exact (not_lt_of_ge hrangeLow)
        ((endIterationProduction_work_map_bounds hkPositive hkK hK hwork').2.trans_lt (by decide))
  · constructor
    · intro hwork
      have hwork' : temporary ∈
          ((zeroMapLabels k K).map endIterationProductionRegisters.work1At) ++
            (zeroMapLabels k K).map endIterationProductionRegisters.work2At := by
        rcases List.mem_append.mp hwork with hwork2 | hwork1
        · exact List.mem_append.mpr (Or.inr hwork2)
        · exact List.mem_append.mpr (Or.inl hwork1)
      exact (not_lt_of_ge htemporaryLow)
        ((endIterationProduction_work_map_bounds hkPositive hkK hK hwork').2.trans_lt (by decide))
    · apply List.nodup_append.mpr
      refine ⟨endIterationProduction_work2_map_nodup hkPositive hkK hK,
        endIterationProduction_work1_map_nodup hkPositive hkK hK, ?_⟩
      intro left hleft right hright heq
      subst right
      exact (List.disjoint_left.mp
        (endIterationProduction_work_maps_disjoint hkPositive hkK hK) hright hleft)

private theorem endIterationProduction_protected_tail_disjoint
    {k K : Nat} {tree : UnaryActionTree} {path : List Wire}
    {range temporary : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hindex : ∀ wire ∈ tree.indexWires, 519 ≤ wire ∧ wire ≤ 536)
    (hpath : ∀ wire ∈ path, 537 ≤ wire ∧ wire < range)
    (hrangeLow : 537 ≤ range) (hrangeTemporary : range < temporary) :
    ∀ left ∈ zeroMapProtectedWires tree 0 path,
      ∀ right ∈ range :: temporary ::
        ((zeroMapLabels k K).map endIterationProductionRegisters.work1At ++
          (zeroMapLabels k K).map endIterationProductionRegisters.work2At),
        left ≠ right := by
  intro left hleft right hright
  have hleftClass : left = 0 ∨
      (519 ≤ left ∧ left ≤ 536) ∨
      (537 ≤ left ∧ left < range) := by
    rw [zeroMapProtectedWires] at hleft
    rcases List.mem_cons.mp hleft with rfl | hdecoder
    · exact Or.inl rfl
    rcases List.mem_append.mp hdecoder with hindexWire | hpathWire
    · exact Or.inr (Or.inl
        (hindex left (List.mem_dedup.mp hindexWire)))
    · exact Or.inr (Or.inr (hpath left hpathWire))
  have hrightClass : right = range ∨ right = temporary ∨
      (0 < right ∧ right ≤ 518) := by
    have hright' : right ∈ range :: temporary ::
        (((zeroMapLabels k K).map endIterationProductionRegisters.work1At) ++
          (zeroMapLabels k K).map endIterationProductionRegisters.work2At) := by
      simpa using hright
    rcases List.mem_cons.mp hright' with rfl | hright'
    · exact Or.inl rfl
    rcases List.mem_cons.mp hright' with rfl | hwork
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr
        (endIterationProduction_work_map_bounds hkPositive hkK hK hwork))
  intro heq
  subst right
  rcases hleftClass with hzero | hindexWire | hpathWire
  · subst left
    rcases hrightClass with hrange | htemporary | hwork
    · exact (lt_of_lt_of_le (by decide : 0 < 537) hrangeLow).ne hrange
    · have htemporaryPositive : 0 < temporary :=
          lt_trans (lt_of_lt_of_le (by decide : 0 < 537) hrangeLow)
            hrangeTemporary
      exact htemporaryPositive.ne htemporary
    · obtain ⟨hworkLow, hworkHigh⟩ := hwork
      exact (Nat.lt_irrefl 0) hworkLow
  · obtain ⟨hindexLow, hindexHigh⟩ := hindexWire
    rcases hrightClass with hrange | htemporary | hwork
    · have hlt : left < range :=
          lt_of_le_of_lt hindexHigh
            (lt_of_lt_of_le (by decide : 536 < 537) hrangeLow)
      exact hlt.ne hrange
    · have hlt : left < temporary :=
          lt_trans
            (lt_of_le_of_lt hindexHigh
              (lt_of_lt_of_le (by decide : 536 < 537) hrangeLow))
            hrangeTemporary
      exact hlt.ne htemporary
    · obtain ⟨hworkLow, hworkHigh⟩ := hwork
      exact (not_lt_of_ge hindexLow)
        (lt_of_le_of_lt hworkHigh (by decide))
  · obtain ⟨hpathLow, hpathHigh⟩ := hpathWire
    rcases hrightClass with hrange | htemporary | hwork
    · exact hpathHigh.ne hrange
    · exact (lt_trans hpathHigh hrangeTemporary).ne htemporary
    · obtain ⟨hworkLow, hworkHigh⟩ := hwork
      exact (not_lt_of_ge hpathLow)
        (lt_of_le_of_lt hworkHigh (by decide))

private theorem endIterationProduction_protected_tail_reverse_disjoint
    {k K : Nat} {tree : UnaryActionTree} {path : List Wire}
    {range temporary : Wire}
    (hkPositive : 0 < k) (hkK : k ≤ K) (hK : K ≤ 259)
    (hindex : ∀ wire ∈ tree.indexWires, 519 ≤ wire ∧ wire ≤ 536)
    (hpath : ∀ wire ∈ path, 537 ≤ wire ∧ wire < range)
    (hrangeLow : 537 ≤ range) (hrangeTemporary : range < temporary) :
    ∀ left ∈ zeroMapProtectedWires tree 0 path,
      ∀ right ∈ range :: temporary ::
        ((zeroMapLabels k K).map endIterationProductionRegisters.work2At ++
          (zeroMapLabels k K).map endIterationProductionRegisters.work1At),
        left ≠ right := by
  intro left hleft right hright
  apply endIterationProduction_protected_tail_disjoint hkPositive hkK hK hindex hpath
    hrangeLow hrangeTemporary left hleft right
  have hright' : right ∈ range :: temporary ::
      (((zeroMapLabels k K).map endIterationProductionRegisters.work2At) ++
        (zeroMapLabels k K).map endIterationProductionRegisters.work1At) := by
    simpa using hright
  rcases List.mem_cons.mp hright' with rfl | hright'
  · simp
  rcases List.mem_cons.mp hright' with rfl | hwork
  · simp
  have : right ∈ range :: temporary ::
      (((zeroMapLabels k K).map endIterationProductionRegisters.work1At) ++
        (zeroMapLabels k K).map endIterationProductionRegisters.work2At) := by
    simp only [List.mem_cons]
    apply Or.inr
    apply Or.inr
    rcases List.mem_append.mp hwork with hwork2 | hwork1
    · exact List.mem_append.mpr (Or.inr hwork2)
    · exact List.mem_append.mpr (Or.inl hwork1)
  simpa using this

private theorem endIterationProduction_target_disjoint
    {k K : Nat} {tree : UnaryActionTree} {path targets : List Wire}
    {range temporary : Wire} {firstAt secondAt : Nat → Wire}
    (htargetBounds : ∀ wire ∈ targets, 519 ≤ wire ∧ wire ≤ 536)
    (htargetIndex : ∀ wire ∈ targets, wire ∉ tree.indexWires)
    (hpathLow : ∀ wire ∈ path, 537 ≤ wire)
    (hrangeLow : 537 ≤ range) (htemporaryLow : 537 ≤ temporary)
    (hwork : ∀ wire ∈
      ((zeroMapLabels k K).map firstAt) ++
        (zeroMapLabels k K).map secondAt,
      0 < wire ∧ wire ≤ 518) :
    List.Disjoint targets
      (zeroMapWires k K tree 0 range temporary path firstAt secondAt) := by
  apply List.disjoint_left.mpr
  intro wire htarget hzeroMap
  obtain ⟨htargetLow, htargetHigh⟩ := htargetBounds wire htarget
  simp only [zeroMapWires, zeroMapProtectedWires, List.mem_append,
    List.mem_cons, List.mem_dedup, List.mem_map] at hzeroMap
  rcases hzeroMap with hmain | ⟨label, hlabel, heq⟩
  · rcases hmain with hprotected | hrange | htemporary |
        ⟨label, hlabel, heq⟩
    · rcases hprotected with hdecoder | hpath
      · rcases hdecoder with hcontrol | hindex
        · exact (not_lt_of_ge htargetLow) (by simp [hcontrol])
        · exact htargetIndex wire htarget hindex
      · have hpathRange := hpathLow wire hpath
        exact (not_lt_of_ge hpathRange)
          (lt_of_le_of_lt htargetHigh (by decide))
    · exact (not_lt_of_ge hrangeLow)
        (by simpa [hrange] using lt_of_le_of_lt htargetHigh (by decide : 536 < 537))
    · exact (not_lt_of_ge htemporaryLow)
        (by simpa [htemporary] using lt_of_le_of_lt htargetHigh (by decide : 536 < 537))
    · have hmaps : wire ∈
          ((zeroMapLabels k K).map firstAt) ++
            (zeroMapLabels k K).map secondAt := by
        apply List.mem_append.mpr
        exact Or.inl (List.mem_map.mpr ⟨label, hlabel, heq⟩)
      obtain ⟨hworkLow, hworkHigh⟩ := hwork wire hmaps
      exact (not_lt_of_ge htargetLow)
        (lt_of_le_of_lt hworkHigh (by decide))
  · have hmaps : wire ∈
        ((zeroMapLabels k K).map firstAt) ++
          (zeroMapLabels k K).map secondAt := by
      apply List.mem_append.mpr
      exact Or.inr (List.mem_map.mpr ⟨label, hlabel, heq⟩)
    obtain ⟨hworkLow, hworkHigh⟩ := hwork wire hmaps
    exact (not_lt_of_ge htargetLow)
      (lt_of_le_of_lt hworkHigh (by decide))

private theorem endIterationProduction_nonAffine_disjoint
    {k K : Nat} {path affineRegister target : List Wire}
    {range temporary : Wire}
    (haffineBounds : ∀ wire ∈ affineRegister,
      519 ≤ wire ∧ wire ≤ 536)
    (haffineTarget : List.Disjoint affineRegister target)
    (hpathLow : ∀ wire ∈ path, 537 ≤ wire)
    (hrangeLow : 537 ≤ range) (htemporaryLow : 537 ≤ temporary)
    (hwork : ∀ wire ∈
      ((zeroMapLabels k K).map endIterationProductionRegisters.work1At) ++
        (zeroMapLabels k K).map endIterationProductionRegisters.work2At,
      0 < wire ∧ wire ≤ 518) :
    List.Disjoint affineRegister
      (lengthBlockNonAffineSupport k K 0 range temporary path
        endIterationProductionRegisters.work1At endIterationProductionRegisters.work2At target) := by
  apply List.disjoint_left.mpr
  intro wire haffine hsupport
  obtain ⟨haffineLow, haffineHigh⟩ := haffineBounds wire haffine
  simp only [lengthBlockNonAffineSupport, List.mem_append, List.mem_cons,
    List.mem_map] at hsupport
  rcases hsupport with hmain | ⟨label, hlabel, heq⟩
  · rcases hmain with hprefix | hrange | htemporary |
        ⟨label, hlabel, heq⟩
    · rcases hprefix with htarget | hcontrol | hpath
      · exact List.disjoint_left.mp haffineTarget haffine htarget
      · exact (not_lt_of_ge haffineLow) (by simp [hcontrol])
      · have hpathRange := hpathLow wire hpath
        exact (not_lt_of_ge hpathRange)
          (lt_of_le_of_lt haffineHigh (by decide))
    · exact (not_lt_of_ge hrangeLow)
        (by simpa [hrange] using lt_of_le_of_lt haffineHigh (by decide : 536 < 537))
    · exact (not_lt_of_ge htemporaryLow)
        (by simpa [htemporary] using lt_of_le_of_lt haffineHigh (by decide : 536 < 537))
    · have hmaps : wire ∈
          ((zeroMapLabels k K).map endIterationProductionRegisters.work1At) ++
            (zeroMapLabels k K).map endIterationProductionRegisters.work2At := by
        apply List.mem_append.mpr
        exact Or.inl (List.mem_map.mpr ⟨label, hlabel, heq⟩)
      obtain ⟨hworkLow, hworkHigh⟩ := hwork wire hmaps
      exact (not_lt_of_ge haffineLow)
        (lt_of_le_of_lt hworkHigh (by decide))
  · have hmaps : wire ∈
        ((zeroMapLabels k K).map endIterationProductionRegisters.work1At) ++
          (zeroMapLabels k K).map endIterationProductionRegisters.work2At := by
      apply List.mem_append.mpr
      exact Or.inr (List.mem_map.mpr ⟨label, hlabel, heq⟩)
    obtain ⟨hworkLow, hworkHigh⟩ := hwork wire hmaps
    exact (not_lt_of_ge haffineLow)
      (lt_of_le_of_lt hworkHigh (by decide))

private theorem endIterationProduction_constantCarry_target_disjoint
    {target : List Wire}
    (htarget : ∀ wire ∈ target, wire ≤ 536) :
    List.Disjoint (endIterationProductionRegisters.constants ++ [endIterationProductionRegisters.carry]) target := by
  apply List.disjoint_left.mpr
  intro wire hscratch htargetMem
  have htargetBound := htarget wire htargetMem
  have hscratchLow : 537 ≤ wire := by
    simp only [EndIterationRegisters.constants, EndIterationRegisters.carry,
      EndIterationRegisters.width, endIterationProductionRegisters, List.length_range', List.mem_append,
      List.mem_singleton] at hscratch
    rcases hscratch with hconstant | rfl
    · exact (List.mem_range'_1.mp (List.mem_of_mem_take hconstant)).1
    · decide
  exact (not_lt_of_ge hscratchLow)
    (lt_of_le_of_lt htargetBound (by decide))

/-- The exact upper and lower paper windows selected at the pinned production index. -/
theorem endIterationProduction_windows :
    endIterationWindowsAt 256 1024 = ⟨1, 258, 164, 259⟩ := by
  decide

private def endIterationProductionTreeRegisters (index : List Wire) : QuotientSwapRegisters where
  control := 0
  sign := 0
  work1 := []
  lengthT := []
  lengthQ := index
  scratch := []

set_option maxRecDepth 100000 in
private theorem endIterationProduction_upper_index_bounds {wire : Wire}
    (hwire : wire ∈
      (endIterationProductionRegisters.upperTree ⟨1, 258, 164, 259⟩).indexWires) :
    528 ≤ wire ∧ wire ≤ 536 := by
  have htree : endIterationProductionRegisters.upperTree ⟨1, 258, 164, 259⟩ =
      quotientSwapTree (endIterationProductionTreeRegisters endIterationProductionRegisters.lengthRP) 1 258 := rfl
  rw [htree] at hwire
  have hmem := quotientSwapTree_indexWires_mem_lengthQ
    (endIterationProductionTreeRegisters endIterationProductionRegisters.lengthRP) (k := 1) (K := 258)
    (by decide) (by decide) wire hwire
  change wire ∈ List.range' 528 9 at hmem
  obtain ⟨hlow, hhigh⟩ := List.mem_range'_1.mp hmem
  norm_num at hhigh
  exact ⟨hlow, Nat.lt_succ_iff.mp hhigh⟩

set_option maxRecDepth 100000 in
private theorem endIterationProduction_lower_index_bounds {wire : Wire}
    (hwire : wire ∈
      (endIterationProductionRegisters.lowerTree 256 ⟨1, 258, 164, 259⟩).indexWires) :
    519 ≤ wire ∧ wire ≤ 527 := by
  have htree : endIterationProductionRegisters.lowerTree 256 ⟨1, 258, 164, 259⟩ =
      quotientSwapTree (endIterationProductionTreeRegisters endIterationProductionRegisters.lengthT) 164 259 := rfl
  rw [htree] at hwire
  have hmem := quotientSwapTree_indexWires_mem_lengthQ
    (endIterationProductionTreeRegisters endIterationProductionRegisters.lengthT) (k := 164) (K := 259)
    (by decide) (by decide) wire hwire
  change wire ∈ List.range' 519 9 at hmem
  obtain ⟨hlow, hhigh⟩ := List.mem_range'_1.mp hmem
  norm_num at hhigh
  exact ⟨hlow, Nat.lt_succ_iff.mp hhigh⟩

private theorem endIterationProduction_upper_path_bounds {wire : Wire}
    (hwire : wire ∈ endIterationProductionRegisters.path 1 258) :
    537 ≤ wire ∧ wire < 547 := by
  change wire ∈
    (List.range' 537 12).take (quotientSwapUnaryDepth 1 258) at hwire
  have hlength : quotientSwapUnaryDepth 1 258 = 10 := by decide
  have htaken : wire ∈ (List.range' 537 10) := by
    simpa [hlength] using hwire
  have hbounds := List.mem_range'_1.mp htaken
  exact ⟨hbounds.1, hbounds.2⟩

private theorem endIterationProduction_lower_path_bounds {wire : Wire}
    (hwire : wire ∈ endIterationProductionRegisters.path 164 259) :
    537 ≤ wire ∧ wire < 545 := by
  change wire ∈
    (List.range' 537 12).take (quotientSwapUnaryDepth 164 259) at hwire
  have hlength : quotientSwapUnaryDepth 164 259 = 8 := by decide
  have htaken : wire ∈ (List.range' 537 8) := by
    simpa [hlength] using hwire
  have hbounds := List.mem_range'_1.mp htaken
  exact ⟨hbounds.1, hbounds.2⟩

private theorem endIterationProduction_lengthT_bounds {wire : Wire}
    (hwire : wire ∈ endIterationProductionRegisters.lengthT) :
    519 ≤ wire ∧ wire ≤ 527 := by
  change wire ∈ List.range' 519 9 at hwire
  obtain ⟨hlow, hhigh⟩ := List.mem_range'_1.mp hwire
  norm_num at hhigh
  exact ⟨hlow, Nat.lt_succ_iff.mp hhigh⟩

private theorem endIterationProduction_lengthRP_bounds {wire : Wire}
    (hwire : wire ∈ endIterationProductionRegisters.lengthRP) :
    528 ≤ wire ∧ wire ≤ 536 := by
  change wire ∈ List.range' 528 9 at hwire
  obtain ⟨hlow, hhigh⟩ := List.mem_range'_1.mp hwire
  norm_num at hhigh
  exact ⟨hlow, Nat.lt_succ_iff.mp hhigh⟩

private theorem endIterationProduction_lengthRP_disjoint_lengthT :
    List.Disjoint endIterationProductionRegisters.lengthRP endIterationProductionRegisters.lengthT := by
  apply List.disjoint_left.mpr
  intro wire hrp ht
  obtain ⟨hrpLow, hrpHigh⟩ := endIterationProduction_lengthRP_bounds hrp
  obtain ⟨htLow, htHigh⟩ := endIterationProduction_lengthT_bounds ht
  exact (not_lt_of_ge hrpLow) (lt_of_le_of_lt htHigh (by decide))

private theorem endIterationProduction_upper_range : endIterationProductionRegisters.rangeAccumulator 1 258 = 547 := by
  decide

private theorem endIterationProduction_upper_temporary : endIterationProductionRegisters.temporary 1 258 = 548 := by
  decide

private theorem endIterationProduction_lower_range : endIterationProductionRegisters.rangeAccumulator 164 259 = 545 := by
  decide

private theorem endIterationProduction_lower_temporary : endIterationProductionRegisters.temporary 164 259 = 546 := by
  decide

private theorem endIterationProduction_K5Decode :
    (EndIterationWindows.K5Decode ⟨1, 258, 164, 259⟩ 256) = 259 := by
  decide

private theorem endIterationProduction_lengthT_disjoint_lengthRP :
    List.Disjoint endIterationProductionRegisters.lengthT endIterationProductionRegisters.lengthRP :=
  List.Disjoint.symm endIterationProduction_lengthRP_disjoint_lengthT

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3200000 in
/-- The dense production allocation satisfies the full shared-scratch physical contract. -/
theorem endIterationProduction_layout :
    EndIterationLayout endIterationProductionRegisters 256 (endIterationWindowsAt 256 1024) := by
  rw [endIterationProduction_windows]
  have hupperDecoder :
      (endIterationProductionRegisters.upperTree ⟨1, 258, 164, 259⟩).Layout
        endIterationProductionRegisters.control (endIterationProductionRegisters.path 1 258) := by
    apply endIterationProductionTree_layout_of_separated
    all_goals decide
  have hlowerDecoder :
      (endIterationProductionRegisters.lowerTree 256 ⟨1, 258, 164, 259⟩).Layout
        endIterationProductionRegisters.control (endIterationProductionRegisters.path 164 259) := by
    apply endIterationProductionTree_layout_of_separated
    all_goals decide
  refine {
    k4_positive := by decide
    k4_le_K4 := by decide
    K4_le_work := by decide
    k5_positive := by decide
    k5_le_decode := by decide
    work1_length := by decide
    work2_length := by decide
    width_positive := by decide
    lengthRP_length := by decide
    scratch_capacity := by decide
    physical := by decide
    upper := ?_
    lower := ?_ }
  · refine {
      affine := ?_
      work1Bits := ?_
      work2Bits := ?_
      affineRegisterDisjoint := ?_
      constantCarryDisjointTarget := ?_ }
    · simp [ConstantLayout, endIterationProductionRegisters, EndIterationRegisters.constants,
        EndIterationRegisters.carry, EndIterationRegisters.width]
      decide
    · refine {
        decoder := hupperDecoder
        wires := ?_
        cell := ?_
        targetNodup := List.nodup_range'
        targetDisjoint := ?_ }
      · apply List.nodup_append.mpr
        refine ⟨unaryLayout_decoderNodup hupperDecoder, ?_, ?_⟩
        · rw [endIterationProduction_upper_range, endIterationProduction_upper_temporary]
          exact endIterationProduction_zeroMap_tail_nodup (k := 1) (K := 258)
            (range := 547) (temporary := 548)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
        · rw [endIterationProduction_upper_range, endIterationProduction_upper_temporary]
          exact endIterationProduction_protected_tail_disjoint (k := 1) (K := 258)
              (tree := endIterationProductionRegisters.upperTree ⟨1, 258, 164, 259⟩)
              (path := endIterationProductionRegisters.path 1 258) (range := 547) (temporary := 548)
              (by decide) (by decide) (by decide)
              (fun wire hwire ↦ by
                obtain ⟨hlow, hhigh⟩ := endIterationProduction_upper_index_bounds hwire
                exact ⟨(by exact (by decide : 519 ≤ 528).trans hlow), hhigh⟩)
              (fun wire hwire ↦ endIterationProduction_upper_path_bounds hwire)
              (by decide) (by decide)
      · intro label hlabel guard hguard
        rw [endIterationProduction_upper_range, endIterationProduction_upper_temporary]
        apply endIterationProduction_cell12 (k := 1) (K := 258) (range := 547)
          (temporary := 548) (guard := guard)
          (by decide) (by decide) (by decide) hlabel
          (by decide) (by decide) (by decide)
        simpa only [endIterationProductionRegisters] using hguard
      · rw [endIterationProduction_upper_range, endIterationProduction_upper_temporary]
        apply endIterationProduction_target_disjoint
          (k := 1) (K := 258)
          (tree := endIterationProductionRegisters.upperTree ⟨1, 258, 164, 259⟩)
          (path := endIterationProductionRegisters.path 1 258) (targets := endIterationProductionRegisters.lengthT)
          (range := 547) (temporary := 548)
          (firstAt := endIterationProductionRegisters.work1At) (secondAt := endIterationProductionRegisters.work2At)
        · intro wire hwire
          obtain ⟨hlow, hhigh⟩ := endIterationProduction_lengthT_bounds hwire
          exact ⟨hlow, hhigh.trans (by decide)⟩
        · intro wire hwire hindex
          obtain ⟨htargetLow, htargetHigh⟩ := endIterationProduction_lengthT_bounds hwire
          obtain ⟨hsourceLow, hsourceHigh⟩ := endIterationProduction_upper_index_bounds hindex
          exact (not_lt_of_ge hsourceLow)
            (lt_of_le_of_lt htargetHigh (by decide))
        · intro wire hwire
          exact (endIterationProduction_upper_path_bounds hwire).1
        · decide
        · decide
        · intro wire hwire
          exact endIterationProduction_work_map_bounds (k := 1) (K := 258)
            (by decide) (by decide) (by decide) hwire
    · refine {
        decoder := hupperDecoder
        wires := ?_
        cell := ?_
        targetNodup := List.nodup_range'
        targetDisjoint := ?_ }
      · apply List.nodup_append.mpr
        refine ⟨unaryLayout_decoderNodup hupperDecoder, ?_, ?_⟩
        · rw [endIterationProduction_upper_range, endIterationProduction_upper_temporary]
          exact endIterationProduction_zeroMap_tail_reverse_nodup (k := 1) (K := 258)
            (range := 547) (temporary := 548)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
        · rw [endIterationProduction_upper_range, endIterationProduction_upper_temporary]
          exact endIterationProduction_protected_tail_reverse_disjoint (k := 1) (K := 258)
              (tree := endIterationProductionRegisters.upperTree ⟨1, 258, 164, 259⟩)
              (path := endIterationProductionRegisters.path 1 258) (range := 547) (temporary := 548)
              (by decide) (by decide) (by decide)
              (fun wire hwire ↦ by
                obtain ⟨hlow, hhigh⟩ := endIterationProduction_upper_index_bounds hwire
                exact ⟨(by exact (by decide : 519 ≤ 528).trans hlow), hhigh⟩)
              (fun wire hwire ↦ endIterationProduction_upper_path_bounds hwire)
              (by decide) (by decide)
      · intro label hlabel guard hguard
        rw [endIterationProduction_upper_range, endIterationProduction_upper_temporary]
        apply endIterationProduction_cell21 (k := 1) (K := 258) (range := 547)
          (temporary := 548) (guard := guard)
          (by decide) (by decide) (by decide) hlabel
          (by decide) (by decide) (by decide)
        simpa only [endIterationProductionRegisters] using hguard
      · rw [endIterationProduction_upper_range, endIterationProduction_upper_temporary]
        apply endIterationProduction_target_disjoint
          (k := 1) (K := 258)
          (tree := endIterationProductionRegisters.upperTree ⟨1, 258, 164, 259⟩)
          (path := endIterationProductionRegisters.path 1 258) (targets := endIterationProductionRegisters.lengthT)
          (range := 547) (temporary := 548)
          (firstAt := endIterationProductionRegisters.work2At) (secondAt := endIterationProductionRegisters.work1At)
        · intro wire hwire
          obtain ⟨hlow, hhigh⟩ := endIterationProduction_lengthT_bounds hwire
          exact ⟨hlow, hhigh.trans (by decide)⟩
        · intro wire hwire hindex
          obtain ⟨htargetLow, htargetHigh⟩ := endIterationProduction_lengthT_bounds hwire
          obtain ⟨hsourceLow, hsourceHigh⟩ := endIterationProduction_upper_index_bounds hindex
          exact (not_lt_of_ge hsourceLow)
            (lt_of_le_of_lt htargetHigh (by decide))
        · intro wire hwire
          exact (endIterationProduction_upper_path_bounds hwire).1
        · decide
        · decide
        · intro wire hwire
          apply endIterationProduction_work_map_bounds (k := 1) (K := 258)
            (by decide) (by decide) (by decide)
          rcases List.mem_append.mp hwire with hwork2 | hwork1
          · exact List.mem_append.mpr (Or.inr hwork2)
          · exact List.mem_append.mpr (Or.inl hwork1)
    · rw [endIterationProduction_upper_range, endIterationProduction_upper_temporary]
      apply endIterationProduction_nonAffine_disjoint
        (k := 1) (K := 258) (path := endIterationProductionRegisters.path 1 258)
        (affineRegister := endIterationProductionRegisters.lengthRP) (target := endIterationProductionRegisters.lengthT)
        (range := 547) (temporary := 548)
      · intro wire hwire
        obtain ⟨hlow, hhigh⟩ := endIterationProduction_lengthRP_bounds hwire
        exact ⟨(by exact (by decide : 519 ≤ 528).trans hlow), hhigh⟩
      · exact endIterationProduction_lengthRP_disjoint_lengthT
      · intro wire hwire
        exact (endIterationProduction_upper_path_bounds hwire).1
      · decide
      · decide
      · intro wire hwire
        exact endIterationProduction_work_map_bounds (k := 1) (K := 258)
          (by decide) (by decide) (by decide) hwire
    · apply endIterationProduction_constantCarry_target_disjoint
      intro wire hwire
      exact (endIterationProduction_lengthT_bounds hwire).2.trans (by decide)
  · refine {
      affine := ?_
      work1Bits := ?_
      work2Bits := ?_
      affineRegisterDisjoint := ?_
      constantCarryDisjointTarget := ?_ }
    · simp [ConstantLayout, endIterationProductionRegisters, EndIterationRegisters.constants,
        EndIterationRegisters.carry, EndIterationRegisters.width]
      decide
    · refine {
        decoder := hlowerDecoder
        wires := ?_
        cell := ?_
        targetNodup := List.nodup_range'
        targetDisjoint := ?_ }
      · apply List.nodup_append.mpr
        refine ⟨unaryLayout_decoderNodup hlowerDecoder, ?_, ?_⟩
        · rw [endIterationProduction_K5Decode, endIterationProduction_lower_range, endIterationProduction_lower_temporary]
          exact endIterationProduction_zeroMap_tail_nodup (k := 164) (K := 259)
            (range := 545) (temporary := 546)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
        · rw [endIterationProduction_K5Decode, endIterationProduction_lower_range, endIterationProduction_lower_temporary]
          exact endIterationProduction_protected_tail_disjoint (k := 164) (K := 259)
              (tree := endIterationProductionRegisters.lowerTree 256 ⟨1, 258, 164, 259⟩)
              (path := endIterationProductionRegisters.path 164 259) (range := 545) (temporary := 546)
              (by decide) (by decide) (by decide)
              (fun wire hwire ↦ by
                obtain ⟨hlow, hhigh⟩ := endIterationProduction_lower_index_bounds hwire
                exact ⟨hlow, hhigh.trans (by decide)⟩)
              (fun wire hwire ↦ endIterationProduction_lower_path_bounds hwire)
              (by decide) (by decide)
      · intro label hlabel guard hguard
        rw [endIterationProduction_K5Decode, endIterationProduction_lower_range, endIterationProduction_lower_temporary]
        apply endIterationProduction_cell12 (k := 164) (K := 259) (range := 545)
          (temporary := 546) (guard := guard)
          (by decide) (by decide) (by decide) hlabel
          (by decide) (by decide) (by decide)
        simpa only [endIterationProductionRegisters] using hguard
      · rw [endIterationProduction_K5Decode, endIterationProduction_lower_range, endIterationProduction_lower_temporary]
        apply endIterationProduction_target_disjoint
          (k := 164) (K := 259)
          (tree := endIterationProductionRegisters.lowerTree 256 ⟨1, 258, 164, 259⟩)
          (path := endIterationProductionRegisters.path 164 259) (targets := endIterationProductionRegisters.lengthRP)
          (range := 545) (temporary := 546)
          (firstAt := endIterationProductionRegisters.work1At) (secondAt := endIterationProductionRegisters.work2At)
        · intro wire hwire
          obtain ⟨hlow, hhigh⟩ := endIterationProduction_lengthRP_bounds hwire
          exact ⟨(by exact (by decide : 519 ≤ 528).trans hlow), hhigh⟩
        · intro wire hwire hindex
          obtain ⟨htargetLow, htargetHigh⟩ := endIterationProduction_lengthRP_bounds hwire
          obtain ⟨hsourceLow, hsourceHigh⟩ := endIterationProduction_lower_index_bounds hindex
          exact (not_lt_of_ge htargetLow)
            (lt_of_le_of_lt hsourceHigh (by decide))
        · intro wire hwire
          exact (endIterationProduction_lower_path_bounds hwire).1
        · decide
        · decide
        · intro wire hwire
          exact endIterationProduction_work_map_bounds (k := 164) (K := 259)
            (by decide) (by decide) (by decide) hwire
    · refine {
        decoder := hlowerDecoder
        wires := ?_
        cell := ?_
        targetNodup := List.nodup_range'
        targetDisjoint := ?_ }
      · apply List.nodup_append.mpr
        refine ⟨unaryLayout_decoderNodup hlowerDecoder, ?_, ?_⟩
        · rw [endIterationProduction_K5Decode, endIterationProduction_lower_range, endIterationProduction_lower_temporary]
          exact endIterationProduction_zeroMap_tail_reverse_nodup (k := 164) (K := 259)
            (range := 545) (temporary := 546)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
        · rw [endIterationProduction_K5Decode, endIterationProduction_lower_range, endIterationProduction_lower_temporary]
          exact endIterationProduction_protected_tail_reverse_disjoint (k := 164) (K := 259)
              (tree := endIterationProductionRegisters.lowerTree 256 ⟨1, 258, 164, 259⟩)
              (path := endIterationProductionRegisters.path 164 259) (range := 545) (temporary := 546)
              (by decide) (by decide) (by decide)
              (fun wire hwire ↦ by
                obtain ⟨hlow, hhigh⟩ := endIterationProduction_lower_index_bounds hwire
                exact ⟨hlow, hhigh.trans (by decide)⟩)
              (fun wire hwire ↦ endIterationProduction_lower_path_bounds hwire)
              (by decide) (by decide)
      · intro label hlabel guard hguard
        rw [endIterationProduction_K5Decode, endIterationProduction_lower_range, endIterationProduction_lower_temporary]
        apply endIterationProduction_cell21 (k := 164) (K := 259) (range := 545)
          (temporary := 546) (guard := guard)
          (by decide) (by decide) (by decide) hlabel
          (by decide) (by decide) (by decide)
        simpa only [endIterationProductionRegisters] using hguard
      · rw [endIterationProduction_K5Decode, endIterationProduction_lower_range, endIterationProduction_lower_temporary]
        apply endIterationProduction_target_disjoint
          (k := 164) (K := 259)
          (tree := endIterationProductionRegisters.lowerTree 256 ⟨1, 258, 164, 259⟩)
          (path := endIterationProductionRegisters.path 164 259) (targets := endIterationProductionRegisters.lengthRP)
          (range := 545) (temporary := 546)
          (firstAt := endIterationProductionRegisters.work2At) (secondAt := endIterationProductionRegisters.work1At)
        · intro wire hwire
          obtain ⟨hlow, hhigh⟩ := endIterationProduction_lengthRP_bounds hwire
          exact ⟨(by exact (by decide : 519 ≤ 528).trans hlow), hhigh⟩
        · intro wire hwire hindex
          obtain ⟨htargetLow, htargetHigh⟩ := endIterationProduction_lengthRP_bounds hwire
          obtain ⟨hsourceLow, hsourceHigh⟩ := endIterationProduction_lower_index_bounds hindex
          exact (not_lt_of_ge htargetLow)
            (lt_of_le_of_lt hsourceHigh (by decide))
        · intro wire hwire
          exact (endIterationProduction_lower_path_bounds hwire).1
        · decide
        · decide
        · intro wire hwire
          apply endIterationProduction_work_map_bounds (k := 164) (K := 259)
            (by decide) (by decide) (by decide)
          rcases List.mem_append.mp hwire with hwork2 | hwork1
          · exact List.mem_append.mpr (Or.inr hwork2)
          · exact List.mem_append.mpr (Or.inl hwork1)
    · rw [endIterationProduction_K5Decode, endIterationProduction_lower_range, endIterationProduction_lower_temporary]
      apply endIterationProduction_nonAffine_disjoint
        (k := 164) (K := 259) (path := endIterationProductionRegisters.path 164 259)
        (affineRegister := endIterationProductionRegisters.lengthT) (target := endIterationProductionRegisters.lengthRP)
        (range := 545) (temporary := 546)
      · intro wire hwire
        obtain ⟨hlow, hhigh⟩ := endIterationProduction_lengthT_bounds hwire
        exact ⟨hlow, hhigh.trans (by decide)⟩
      · exact endIterationProduction_lengthT_disjoint_lengthRP
      · intro wire hwire
        exact (endIterationProduction_lower_path_bounds hwire).1
      · decide
      · decide
      · intro wire hwire
        exact endIterationProduction_work_map_bounds (k := 164) (K := 259)
          (by decide) (by decide) (by decide) hwire
    · apply endIterationProduction_constantCarry_target_disjoint
      intro wire hwire
      exact (endIterationProduction_lengthRP_bounds hwire).2

set_option maxRecDepth 100000 in
/-- Production resources of the pinned forward and inverse end-of-iteration source blocks.
The 549 roles are one dense physical allocation; the two length blocks reuse its 12 scratch
wires serially. -/
theorem swapWorkAndLengthUnaryShared_secp256k1_resources :
    endIterationProductionRegisters.allWires.length = 549 ∧
      eeaToffoliCount (swapWorkAndLengthUnaryShared
        endIterationProductionRegisters 256
        (endIterationWindowsAt 256 1024)) = 14463 ∧
      eeaCnotCount (swapWorkAndLengthUnaryShared
        endIterationProductionRegisters 256
        (endIterationWindowsAt 256 1024)) = 12034 ∧
      eeaXCount (swapWorkAndLengthUnaryShared
        endIterationProductionRegisters 256
        (endIterationWindowsAt 256 1024)) = 16948 ∧
      ShorECDLP.tCount (swapWorkAndLengthUnaryShared
        endIterationProductionRegisters 256
        (endIterationWindowsAt 256 1024)) = 101241 ∧
      eeaToffoliCount (swapWorkAndLengthUnarySharedInverse
        endIterationProductionRegisters 256
        (endIterationWindowsAt 256 1024)) = 14463 ∧
      eeaCnotCount (swapWorkAndLengthUnarySharedInverse
        endIterationProductionRegisters 256
        (endIterationWindowsAt 256 1024)) = 12034 ∧
      eeaXCount (swapWorkAndLengthUnarySharedInverse
        endIterationProductionRegisters 256
        (endIterationWindowsAt 256 1024)) = 16948 ∧
      ShorECDLP.tCount (swapWorkAndLengthUnarySharedInverse
        endIterationProductionRegisters 256
        (endIterationWindowsAt 256 1024)) = 101241 := by
  have hlayout := endIterationProduction_layout
  have hresources := swapWorkAndLengthUnaryShared_resourceCounts
    endIterationProductionRegisters 256 (endIterationWindowsAt 256 1024)
    (by decide) hlayout
  have hwork : endIterationProductionRegisters.work1.length =
      endIterationProductionRegisters.work2.length := by decide
  rw [endIterationProduction_windows] at hresources
  norm_num [EndIterationRegisters.allWires, endIterationProductionRegisters,
    endIterationToffoliFormula, endIterationCnotFormula,
    endIterationXFormula, endIterationTFormula,
    EndIterationWindows.K5Decode, zeroMapLabels,
    lowBitCount, constantBits] at hresources
  have hroles : endIterationProductionRegisters.allWires.length = 549 := by
    norm_num [EndIterationRegisters.allWires, endIterationProductionRegisters]
  rcases hresources with ⟨hToffoli, hCnot, hX, hT⟩
  have hToffoli' : eeaToffoliCount (swapWorkAndLengthUnaryShared
      endIterationProductionRegisters 256
      (endIterationWindowsAt 256 1024)) = 14463 := by
    simpa only [endIterationProduction_windows] using hToffoli
  have hCnot' : eeaCnotCount (swapWorkAndLengthUnaryShared
      endIterationProductionRegisters 256
      (endIterationWindowsAt 256 1024)) = 12034 := by
    simpa only [endIterationProduction_windows] using hCnot
  have hX' : eeaXCount (swapWorkAndLengthUnaryShared
      endIterationProductionRegisters 256
      (endIterationWindowsAt 256 1024)) = 16948 := by
    simpa only [endIterationProduction_windows] using hX
  have hT' : ShorECDLP.tCount (swapWorkAndLengthUnaryShared
      endIterationProductionRegisters 256
      (endIterationWindowsAt 256 1024)) = 101241 := by
    simpa only [endIterationProduction_windows] using hT
  exact ⟨hroles, hToffoli', hCnot', hX', hT',
    (swapWorkAndLengthUnarySharedInverse_toffoliCount
      endIterationProductionRegisters 256
      (endIterationWindowsAt 256 1024) hwork).trans hToffoli',
    (swapWorkAndLengthUnarySharedInverse_cnotCount
      endIterationProductionRegisters 256
      (endIterationWindowsAt 256 1024) hwork).trans hCnot',
    (swapWorkAndLengthUnarySharedInverse_xCount
      endIterationProductionRegisters 256
      (endIterationWindowsAt 256 1024)).trans hX',
    (swapWorkAndLengthUnarySharedInverse_tCount
      endIterationProductionRegisters 256
      (endIterationWindowsAt 256 1024) hwork).trans hT'⟩

private def endIterationSmallRegisters : EndIterationRegisters where
  control := 0
  work1 := List.range' 1 7
  work2 := List.range' 8 7
  lengthT := List.range' 15 3
  lengthRP := List.range' 18 3
  scratch := List.range' 21 5

private def endIterationSmallWindows : EndIterationWindows := ⟨2, 5, 2, 4⟩

set_option maxRecDepth 100000 in
/-- Direct constructor regression on a four-bit instance.  It independently evaluates both
source orders rather than reusing the symbolic production formula. -/
theorem swapWorkAndLengthUnaryShared_small_resources :
    eeaToffoliCount (swapWorkAndLengthUnaryShared
      endIterationSmallRegisters 4 endIterationSmallWindows) = 299 ∧
    eeaCnotCount (swapWorkAndLengthUnaryShared
      endIterationSmallRegisters 4 endIterationSmallWindows) = 312 ∧
    eeaXCount (swapWorkAndLengthUnaryShared
      endIterationSmallRegisters 4 endIterationSmallWindows) = 328 ∧
    ShorECDLP.tCount (swapWorkAndLengthUnaryShared
      endIterationSmallRegisters 4 endIterationSmallWindows) = 2093 ∧
    eeaToffoliCount (swapWorkAndLengthUnarySharedInverse
      endIterationSmallRegisters 4 endIterationSmallWindows) = 299 ∧
    eeaCnotCount (swapWorkAndLengthUnarySharedInverse
      endIterationSmallRegisters 4 endIterationSmallWindows) = 312 ∧
    eeaXCount (swapWorkAndLengthUnarySharedInverse
      endIterationSmallRegisters 4 endIterationSmallWindows) = 328 ∧
    ShorECDLP.tCount (swapWorkAndLengthUnarySharedInverse
      endIterationSmallRegisters 4 endIterationSmallWindows) = 2093 := by
  decide

end

end ShorECDLP.Paper2607_13816
