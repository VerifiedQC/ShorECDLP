import ShorECDLP.Submission.«2607_13816».EEA.Increment
import Mathlib.Data.List.Rotate

/-!
# Algorithm-3 shift blocks

This module implements the remaining shift primitives and the literal `pre_shift_gate` and
`post_shift_gate` surrounding the arithmetic core of one optimized EEA microstep.  The gate order
matches the pinned supplemental generator: controlled decrement uses its explicit negative-control
borrow chain, and the right-by-two word rotation uses the source's parity-cycle decomposition rather
than two adjacent one-position cascades.
-/

namespace ShorECDLP.Paper2607_13816

open _root_.ShorECDLP.Classical

/-! ## Literal controlled decrement -/

/-- Boolean ripple specification for subtracting one controlled borrow from an LSB-first word. -/
def decrementBits : Bool → List Bool → List Bool
  | _, [] => []
  | borrow, bit :: bits =>
      Bool.xor bit borrow :: decrementBits (!bit && borrow) bits

/-- The pinned source's inner negative-control borrow chain. -/
def decrementTail : List Wire → Wire → List Wire → Circuit
  | [], _, _ => []
  | [bit], borrow, [] => [.CX borrow bit]
  | bit :: next :: rest, borrow, nextBorrow :: borrows =>
      [.X bit, .CCX bit borrow nextBorrow, .X bit] ++
        decrementTail (next :: rest) nextBorrow borrows ++
        [.X bit, .CCX bit borrow nextBorrow, .X bit, .CX borrow bit]
  | _, _, _ => []

/-- Controlled subtraction of one modulo `2^register.length`, with the exact gate order of
`dec_mod2n_1ctrl` in the pinned supplement at its source precondition of exactly `n - 1` borrow
wires.  The total Lean fallback returns an empty circuit at invalid arities rather than modeling
the Python generator's exception; all source and semantic claims below impose the valid width. -/
def controlledDecrement : Wire → List Wire → List Wire → Circuit
  | _, [], _ => []
  | control, [bit], [] => [.CX control bit]
  | control, low :: next :: rest, firstBorrow :: borrows =>
      [.X low, .CCX control low firstBorrow, .X low, .CX control low] ++
        decrementTail (next :: rest) firstBorrow borrows ++
        [.CX control low, .X low, .CCX control low firstBorrow,
          .X low, .CX control low]
  | _, _, _ => []

/- Small literal-source regression. -/
example (control b₀ b₁ b₂ c₀ c₁ : Wire) :
    controlledDecrement control ([b₀, b₁, b₂]) ([c₀, c₁]) =
      [.X b₀, .CCX control b₀ c₀, .X b₀, .CX control b₀,
        .X b₁, .CCX b₁ c₀ c₁, .X b₁, .CX c₁ b₂,
        .X b₁, .CCX b₁ c₀ c₁, .X b₁, .CX c₀ b₁,
        .CX control b₀, .X b₀, .CCX control b₀ c₀, .X b₀,
        .CX control b₀] := by
  rfl

private theorem decrementTail_usesOnly
    (bits : List Wire) (borrow : Wire) (borrows : List Wire) :
    PaperCircuitUsesOnly (borrow :: bits ++ borrows)
      (decrementTail bits borrow borrows) := by
  induction bits generalizing borrow borrows with
  | nil => simp [decrementTail, PaperCircuitUsesOnly]
  | cons bit tail ih =>
      cases tail with
      | nil =>
          cases borrows with
          | nil =>
              simp [decrementTail, PaperCircuitUsesOnly,
                PaperGateUsesOnly, gateWires]
          | cons nextBorrow borrows =>
              simp [decrementTail, PaperCircuitUsesOnly]
      | cons next rest =>
          cases borrows with
          | nil => simp [decrementTail, PaperCircuitUsesOnly]
          | cons nextBorrow borrows =>
              rw [decrementTail]
              apply PaperCircuitUsesOnly.append
              · apply PaperCircuitUsesOnly.append
                · intro gate hgate
                  simp at hgate
                  rcases hgate with rfl | rfl | rfl <;>
                    simp [PaperGateUsesOnly, gateWires]
                · apply (ih nextBorrow borrows).mono
                  intro wire hwire
                  simp only [List.mem_cons, List.mem_append] at hwire ⊢
                  rcases hwire with hword | hborrows
                  · rcases hword with rfl | hword
                    · exact Or.inr (Or.inl rfl)
                    · rcases hword with rfl | hrest
                      · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
                      · exact Or.inl (Or.inr (Or.inr (Or.inr hrest)))
                  · exact Or.inr (Or.inr hborrows)
              · intro gate hgate
                simp at hgate
                rcases hgate with rfl | rfl | rfl | rfl <;>
                  simp [PaperGateUsesOnly, gateWires]

/-- The explicit decrement touches only the control, target word, and borrow bank. -/
theorem controlledDecrement_usesOnly
    (control : Wire) (register borrows : List Wire) :
    PaperCircuitUsesOnly (control :: register ++ borrows)
      (controlledDecrement control register borrows) := by
  cases register with
  | nil => simp [controlledDecrement, PaperCircuitUsesOnly]
  | cons low tail =>
      cases tail with
      | nil =>
          cases borrows with
          | nil =>
              simp [controlledDecrement, PaperCircuitUsesOnly,
                PaperGateUsesOnly, gateWires]
          | cons firstBorrow borrows =>
              simp [controlledDecrement, PaperCircuitUsesOnly]
      | cons next rest =>
          cases borrows with
          | nil => simp [controlledDecrement, PaperCircuitUsesOnly]
          | cons firstBorrow borrows =>
              rw [controlledDecrement]
              apply PaperCircuitUsesOnly.append
              · apply PaperCircuitUsesOnly.append
                · intro gate hgate
                  simp at hgate
                  rcases hgate with rfl | rfl | rfl | rfl <;>
                    simp [PaperGateUsesOnly, gateWires]
                · apply (decrementTail_usesOnly (next :: rest)
                    firstBorrow borrows).mono
                  intro wire hwire
                  simp only [List.mem_cons, List.mem_append] at hwire ⊢
                  rcases hwire with hword | hborrows
                  · rcases hword with rfl | hword
                    · exact Or.inr (Or.inl rfl)
                    · rcases hword with rfl | hrest
                      · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
                      · exact Or.inl (Or.inr (Or.inr (Or.inr hrest)))
                  · exact Or.inr (Or.inr hborrows)
              · intro gate hgate
                simp at hgate
                rcases hgate with rfl | rfl | rfl | rfl | rfl <;>
                  simp [PaperGateUsesOnly, gateWires]

private theorem decrementTail_HPFree
    (bits : List Wire) (borrow : Wire) (borrows : List Wire) :
    HPFree (decrementTail bits borrow borrows) := by
  induction bits generalizing borrow borrows with
  | nil => simp [decrementTail]
  | cons bit tail ih =>
      cases tail <;> cases borrows <;>
        simp [decrementTail, ih]

@[simp]
theorem controlledDecrement_HPFree
    (control : Wire) (register borrows : List Wire) :
    HPFree (controlledDecrement control register borrows) := by
  cases register with
  | nil => simp [controlledDecrement]
  | cons low tail =>
      cases tail <;> cases borrows <;>
        simp [controlledDecrement, decrementTail_HPFree]

private theorem shift_wireValues_congr
    (wires : List Wire) (left right : BasisState)
    (h : ∀ wire ∈ wires, left wire = right wire) :
    wireValues wires left = wireValues wires right := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq]
      exact ⟨h wire (by simp), ih (fun other hother =>
        h other (by simp [hother]))⟩

private theorem shift_list_eq_nil_of_one_eq_length_add_one
    (items : List α) (hlength : 1 = items.length + 1) :
    items = [] := by
  apply List.length_eq_zero_iff.mp
  omega

private theorem decrementTail_correct
    (bits : List Wire) (borrow : Wire) (borrows : List Wire)
    (state : BasisState)
    (hlength : bits.length = borrows.length + 1)
    (hnd : (borrow :: bits ++ borrows).Nodup)
    (hclean : Clean borrows state) :
    let after := run (decrementTail bits borrow borrows) state
    wireValues bits after =
        decrementBits (state borrow) (wireValues bits state) ∧
      ∀ wire, wire ∉ bits → after wire = state wire := by
  induction bits generalizing borrow borrows state with
  | nil => simp at hlength
  | cons bit tail ih =>
      cases tail with
      | nil =>
          have hborrows : borrows = [] :=
            shift_list_eq_nil_of_one_eq_length_add_one borrows (by simpa using hlength)
          subst borrows
          constructor
          · simp [decrementTail, wireValues, decrementBits, run, applyGate, upd]
          · intro wire hwire
            simp only [List.mem_singleton] at hwire
            simp [decrementTail, run, applyGate, upd, hwire]
      | cons next rest =>
          cases borrows with
          | nil => simp at hlength
          | cons nextBorrow borrows =>
              have htailLength : (next :: rest).length = borrows.length + 1 := by
                simpa using hlength
              have hborrow :
                  borrow ∉ bit :: next :: rest ++ nextBorrow :: borrows :=
                (List.nodup_cons.mp hnd).1
              have hword :
                  (bit :: next :: rest ++ nextBorrow :: borrows).Nodup :=
                (List.nodup_cons.mp hnd).2
              have hbit : bit ∉ next :: rest ++ nextBorrow :: borrows :=
                (List.nodup_cons.mp hword).1
              have htail := (List.nodup_cons.mp hword).2
              have hinner :
                  (nextBorrow :: next :: rest ++ borrows).Nodup := by
                have hperm :
                    ((next :: rest) ++ nextBorrow :: borrows).Perm
                      (nextBorrow :: (next :: rest) ++ borrows) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := borrows) (a := nextBorrow))
                exact htail.perm hperm
              have hbb : bit ≠ borrow := by
                intro equality
                exact hborrow (by simp [equality])
              have hbn : bit ≠ nextBorrow := by
                intro equality
                exact hbit (by simp [equality])
              have hborrowNext : borrow ≠ nextBorrow := by
                intro equality
                exact hborrow (by simp [equality])
              have hnextBorrowFalse : state nextBorrow = false :=
                hclean nextBorrow (by simp)
              let first :=
                run [.X bit, .CCX bit borrow nextBorrow, .X bit] state
              have hfirstNext :
                  first nextBorrow = (!state bit && state borrow) := by
                simp [first, run, applyGate, upd, Ne.symm hbb,
                  hbn, Ne.symm hbn,
                  hnextBorrowFalse]
              have hfirstBit : first bit = state bit := by
                simp [first, run, applyGate, upd, Ne.symm hbb,
                  hbn, Ne.symm hbn]
              have hfirstBorrow : first borrow = state borrow := by
                simp [first, run, applyGate, upd, Ne.symm hbb,
                  hborrowNext]
              have hfirstTail :
                  wireValues (next :: rest) first =
                    wireValues (next :: rest) state := by
                apply shift_wireValues_congr
                intro wire hwire
                have hwBit : wire ≠ bit := by
                  intro equality
                  subst wire
                  exact hbit (List.mem_append_left (nextBorrow :: borrows) hwire)
                have hwNext : wire ≠ nextBorrow := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left borrows hwire)
                simp [first, run, applyGate, upd, hwBit, hwNext]
              have hcleanFirst : Clean borrows first := by
                intro wire hwire
                have hwBit : wire ≠ bit := by
                  intro equality
                  subst wire
                  exact hbit (List.mem_append_right (next :: rest)
                    (by simp [hwire]))
                have hwNext : wire ≠ nextBorrow := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_right (next :: rest) hwire)
                simpa [first, run, applyGate, upd, hwBit, hwNext] using
                  hclean wire (by simp [hwire])
              have hrecursive := ih nextBorrow borrows first
                htailLength hinner hcleanFirst
              let middle :=
                run (decrementTail (next :: rest) nextBorrow borrows) first
              have hmiddleValues :
                  wireValues (next :: rest) middle =
                    decrementBits (!state bit && state borrow)
                      (wireValues (next :: rest) state) := by
                have hrecursiveValues :
                    wireValues (next :: rest) middle =
                      decrementBits (first nextBorrow)
                        (wireValues (next :: rest) first) := by
                  simpa only [middle] using hrecursive.1
                rw [hrecursiveValues, hfirstNext, hfirstTail]
              have hmiddleOutside :
                  ∀ wire, wire ∉ next :: rest → middle wire = first wire :=
                hrecursive.2
              have hmiddleBit : middle bit = state bit := by
                rw [hmiddleOutside bit]
                · exact hfirstBit
                · intro hmem
                  exact hbit (List.mem_append_left (nextBorrow :: borrows) hmem)
              have hmiddleBorrow : middle borrow = state borrow := by
                rw [hmiddleOutside borrow]
                · exact hfirstBorrow
                · intro hmem
                  exact hborrow (List.mem_append_left (nextBorrow :: borrows)
                    (List.mem_cons_of_mem bit hmem))
              have hmiddleNextBorrow :
                  middle nextBorrow = (!state bit && state borrow) := by
                rw [hmiddleOutside nextBorrow]
                · exact hfirstNext
                · intro hmem
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left borrows hmem)
              let after :=
                run [.X bit, .CCX bit borrow nextBorrow, .X bit,
                  .CX borrow bit] middle
              have hafterBit :
                  after bit = Bool.xor (state bit) (state borrow) := by
                simp [after, run, applyGate, upd, Ne.symm hbb,
                  hbn, Ne.symm hbn, hborrowNext,
                  hmiddleBit, hmiddleBorrow,
                  hmiddleNextBorrow]
              have hafterTail :
                  wireValues (next :: rest) after =
                    wireValues (next :: rest) middle := by
                apply shift_wireValues_congr
                intro wire hwire
                have hwBit : wire ≠ bit := by
                  intro equality
                  subst wire
                  exact hbit (List.mem_append_left (nextBorrow :: borrows) hwire)
                have hwNext : wire ≠ nextBorrow := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left borrows hwire)
                simp [after, run, applyGate, upd, hwBit, hwNext]
              rw [decrementTail, run_append, run_append]
              change
                wireValues (bit :: next :: rest) after =
                    decrementBits (state borrow)
                      (wireValues (bit :: next :: rest) state) ∧
                  ∀ wire, wire ∉ bit :: next :: rest →
                    after wire = state wire
              constructor
              · change
                  after bit :: wireValues (next :: rest) after =
                    Bool.xor (state bit) (state borrow) ::
                      decrementBits (!state bit && state borrow)
                        (wireValues (next :: rest) state)
                rw [hafterBit, hafterTail, hmiddleValues]
              · intro wire hwire
                simp only [List.mem_cons, not_or] at hwire
                have hwireTail : wire ∉ next :: rest := by
                  simpa only [List.mem_cons, not_or] using hwire.2
                by_cases hnextBorrow : wire = nextBorrow
                · subst wire
                  simp [after, run, applyGate, upd, Ne.symm hbb,
                    hbn, Ne.symm hbn, hborrowNext, hmiddleBit,
                    hmiddleBorrow, hmiddleNextBorrow, hnextBorrowFalse]
                · have hmiddleWire := hmiddleOutside wire hwireTail
                  have hafterWire : after wire = middle wire := by
                    simp [after, run, applyGate, upd, hwire.1, hnextBorrow]
                  rw [hafterWire, hmiddleWire]
                  simp [first, run, applyGate, upd, hwire.1, hnextBorrow]

/-- The exact source decrement changes only the target word, subtracts its restored control bit,
and returns every clean borrow wire to zero. -/
theorem controlledDecrement_correct
    (control : Wire) (register borrows : List Wire) (state : BasisState)
    (hlength : register.length = borrows.length + 1)
    (hnd : (control :: register ++ borrows).Nodup)
    (hclean : Clean borrows state) :
    let after := run (controlledDecrement control register borrows) state
    wireValues register after =
        decrementBits (state control) (wireValues register state) ∧
      ∀ wire, wire ∉ register → after wire = state wire := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have hborrows : borrows = [] :=
            shift_list_eq_nil_of_one_eq_length_add_one borrows (by simpa using hlength)
          subst borrows
          have hcontrol : control ≠ low := by
            simpa [List.nodup_cons] using (List.nodup_cons.mp hnd).1
          constructor
          · simp [controlledDecrement, wireValues, decrementBits,
              run, applyGate, upd]
          · intro wire hwire
            simp only [List.mem_singleton] at hwire
            simp [controlledDecrement, run, applyGate, upd, hwire]
      | cons next rest =>
          cases borrows with
          | nil => simp at hlength
          | cons firstBorrow borrows =>
              have htailLength : (next :: rest).length = borrows.length + 1 := by
                simpa using hlength
              have hcontrol :
                  control ∉ low :: next :: rest ++ firstBorrow :: borrows :=
                (List.nodup_cons.mp hnd).1
              have hword :
                  (low :: next :: rest ++ firstBorrow :: borrows).Nodup :=
                (List.nodup_cons.mp hnd).2
              have hlow : low ∉ next :: rest ++ firstBorrow :: borrows :=
                (List.nodup_cons.mp hword).1
              have htail := (List.nodup_cons.mp hword).2
              have hinner :
                  (firstBorrow :: next :: rest ++ borrows).Nodup := by
                have hperm :
                    ((next :: rest) ++ firstBorrow :: borrows).Perm
                      (firstBorrow :: (next :: rest) ++ borrows) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := borrows) (a := firstBorrow))
                exact htail.perm hperm
              have hcl : control ≠ low := by
                intro equality
                exact hcontrol (by simp [equality])
              have hcf : control ≠ firstBorrow := by
                intro equality
                exact hcontrol (by simp [equality])
              have hlf : low ≠ firstBorrow := by
                intro equality
                exact hlow (by simp [equality])
              have hfirstBorrowFalse : state firstBorrow = false :=
                hclean firstBorrow (by simp)
              let first :=
                run [.X low, .CCX control low firstBorrow, .X low,
                  .CX control low] state
              have hfirstBorrow :
                  first firstBorrow = (state control && !state low) := by
                simp [first, run, applyGate, upd, hcl,
                  hcf, hlf, Ne.symm hlf,
                  hfirstBorrowFalse]
              have hfirstLow :
                  first low = Bool.xor (state low) (state control) := by
                simp [first, run, applyGate, upd, hcl, hcf, hlf,
                  hfirstBorrowFalse]
              have hfirstControl : first control = state control := by
                simp [first, run, applyGate, upd, hcl, hcf]
              have hfirstTail :
                  wireValues (next :: rest) first =
                    wireValues (next :: rest) state := by
                apply shift_wireValues_congr
                intro wire hwire
                have hwLow : wire ≠ low := by
                  intro equality
                  subst wire
                  exact hlow (List.mem_append_left (firstBorrow :: borrows) hwire)
                have hwBorrow : wire ≠ firstBorrow := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left borrows hwire)
                simp [first, run, applyGate, upd, hwLow, hwBorrow]
              have hcleanFirst : Clean borrows first := by
                intro wire hwire
                have hwLow : wire ≠ low := by
                  intro equality
                  subst wire
                  exact hlow (List.mem_append_right (next :: rest)
                    (by simp [hwire]))
                have hwBorrow : wire ≠ firstBorrow := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_right (next :: rest) hwire)
                simpa [first, run, applyGate, upd, hwLow, hwBorrow] using
                  hclean wire (by simp [hwire])
              have hrecursive := decrementTail_correct
                (next :: rest) firstBorrow borrows first
                htailLength hinner hcleanFirst
              let middle :=
                run (decrementTail (next :: rest) firstBorrow borrows) first
              have hmiddleValues :
                  wireValues (next :: rest) middle =
                    decrementBits (!state low && state control)
                      (wireValues (next :: rest) state) := by
                have hvalues :
                    wireValues (next :: rest) middle =
                      decrementBits (first firstBorrow)
                        (wireValues (next :: rest) first) := by
                  simpa only [middle] using hrecursive.1
                rw [hvalues, hfirstBorrow, hfirstTail]
                simp [Bool.and_comm]
              have hmiddleOutside :
                  ∀ wire, wire ∉ next :: rest → middle wire = first wire :=
                hrecursive.2
              have hmiddleLow :
                  middle low = Bool.xor (state low) (state control) := by
                rw [hmiddleOutside low]
                · exact hfirstLow
                · intro hmem
                  exact hlow (List.mem_append_left (firstBorrow :: borrows) hmem)
              have hmiddleControl : middle control = state control := by
                rw [hmiddleOutside control]
                · exact hfirstControl
                · intro hmem
                  exact hcontrol (List.mem_append_left (firstBorrow :: borrows)
                    (List.mem_cons_of_mem low hmem))
              have hmiddleFirstBorrow :
                  middle firstBorrow = (state control && !state low) := by
                rw [hmiddleOutside firstBorrow]
                · exact hfirstBorrow
                · intro hmem
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left borrows hmem)
              let after :=
                run [.CX control low, .X low,
                  .CCX control low firstBorrow, .X low,
                  .CX control low] middle
              have hafterLow :
                  after low = Bool.xor (state low) (state control) := by
                simp [after, run, applyGate, upd, hcl, hcf, hlf,
                  hmiddleLow, hmiddleControl, hmiddleFirstBorrow]
              have hafterTail :
                  wireValues (next :: rest) after =
                    wireValues (next :: rest) middle := by
                apply shift_wireValues_congr
                intro wire hwire
                have hwLow : wire ≠ low := by
                  intro equality
                  subst wire
                  exact hlow (List.mem_append_left (firstBorrow :: borrows) hwire)
                have hwBorrow : wire ≠ firstBorrow := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left borrows hwire)
                simp [after, run, applyGate, upd, hwLow, hwBorrow]
              rw [controlledDecrement, run_append, run_append]
              change
                wireValues (low :: next :: rest) after =
                    decrementBits (state control)
                      (wireValues (low :: next :: rest) state) ∧
                  ∀ wire, wire ∉ low :: next :: rest →
                    after wire = state wire
              constructor
              · change
                  after low :: wireValues (next :: rest) after =
                    Bool.xor (state low) (state control) ::
                      decrementBits (!state low && state control)
                        (wireValues (next :: rest) state)
                rw [hafterLow, hafterTail, hmiddleValues]
              · intro wire hwire
                simp only [List.mem_cons, not_or] at hwire
                have hwireTail : wire ∉ next :: rest := by
                  simpa only [List.mem_cons, not_or] using hwire.2
                by_cases hfirstBorrow : wire = firstBorrow
                · subst wire
                  simp [after, run, applyGate, upd, hcl, hcf, hlf,
                    Ne.symm hlf, hmiddleLow, hmiddleControl,
                    hmiddleFirstBorrow, hfirstBorrowFalse]
                · have hmiddleWire := hmiddleOutside wire hwireTail
                  have hafterWire : after wire = middle wire := by
                    simp [after, run, applyGate, upd, hwire.1, hfirstBorrow]
                  rw [hafterWire, hmiddleWire]
                  simp [first, run, applyGate, upd, hwire.1, hfirstBorrow]

/-- The external control is restored exactly. -/
theorem controlledDecrement_control
    (control : Wire) (register borrows : List Wire) (state : BasisState)
    (hlength : register.length = borrows.length + 1)
    (hnd : (control :: register ++ borrows).Nodup)
    (hclean : Clean borrows state) :
    run (controlledDecrement control register borrows) state control =
      state control := by
  have hcontrol : control ∉ register := by
    intro hmem
    exact (List.nodup_cons.mp hnd).1
      (List.mem_append_left borrows hmem)
  exact (controlledDecrement_correct control register borrows state
    hlength hnd hclean).2 control hcontrol

/-- Every clean borrow wire is returned to zero. -/
theorem controlledDecrement_clean
    (control : Wire) (register borrows : List Wire) (state : BasisState)
    (hlength : register.length = borrows.length + 1)
    (hnd : (control :: register ++ borrows).Nodup)
    (hclean : Clean borrows state) :
    Clean borrows
      (run (controlledDecrement control register borrows) state) := by
  have hcross := (List.nodup_append.mp (List.nodup_cons.mp hnd).2).2.2
  intro wire hwire
  have hnot : wire ∉ register := by
    intro hmem
    exact hcross wire hmem wire hwire rfl
  rw [(controlledDecrement_correct control register borrows state
    hlength hnd hclean).2 wire hnot]
  exact hclean wire hwire

private theorem decrementTail_wellFormed
    (bits : List Wire) (borrow : Wire) (borrows : List Wire)
    (hnd : (borrow :: bits ++ borrows).Nodup) :
    CircuitWellFormed (decrementTail bits borrow borrows) := by
  induction bits generalizing borrow borrows with
  | nil => simp [decrementTail]
  | cons bit tail ih =>
      cases tail with
      | nil =>
          cases borrows with
          | nil =>
              have hborrow : borrow ≠ bit := by
                simpa [List.nodup_cons] using (List.nodup_cons.mp hnd).1
              simp [decrementTail, Gate.WellFormed, hborrow]
          | cons nextBorrow borrows => simp [decrementTail]
      | cons next rest =>
          cases borrows with
          | nil => simp [decrementTail]
          | cons nextBorrow borrows =>
              have hborrow :
                  borrow ∉ bit :: next :: rest ++ nextBorrow :: borrows :=
                (List.nodup_cons.mp hnd).1
              have htail :
                  (bit :: next :: rest ++ nextBorrow :: borrows).Nodup :=
                (List.nodup_cons.mp hnd).2
              have hbit : bit ∉ next :: rest ++ nextBorrow :: borrows :=
                (List.nodup_cons.mp htail).1
              have htail := (List.nodup_cons.mp htail).2
              have hinner :
                  (nextBorrow :: next :: rest ++ borrows).Nodup := by
                have hperm :
                    ((next :: rest) ++ nextBorrow :: borrows).Perm
                      (nextBorrow :: (next :: rest) ++ borrows) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := borrows) (a := nextBorrow))
                exact htail.perm hperm
              have hbb : bit ≠ borrow := by
                intro equality
                exact hborrow (by simp [equality])
              have hbn : bit ≠ nextBorrow := by
                intro equality
                exact hbit (by simp [equality])
              have hborrowNext : borrow ≠ nextBorrow := by
                intro equality
                exact hborrow (by simp [equality])
              rw [decrementTail, circuitWellFormed_append,
                circuitWellFormed_append]
              refine ⟨⟨?_, ih nextBorrow borrows hinner⟩, ?_⟩
              · simp [CircuitWellFormed, Gate.WellFormed,
                  hbb, hbn, hborrowNext]
              · simp [CircuitWellFormed, Gate.WellFormed,
                  hbb, Ne.symm hbb, hbn, hborrowNext]

/-- Physical well-formedness of the exact controlled decrement. -/
theorem controlledDecrement_wellFormed
    (control : Wire) (register borrows : List Wire)
    (hnd : (control :: register ++ borrows).Nodup) :
    CircuitWellFormed (controlledDecrement control register borrows) := by
  cases register with
  | nil => simp [controlledDecrement]
  | cons low tail =>
      cases tail with
      | nil =>
          cases borrows with
          | nil =>
              have hcl : control ≠ low := by
                simpa [List.nodup_cons] using (List.nodup_cons.mp hnd).1
              simp [controlledDecrement, Gate.WellFormed, hcl]
          | cons firstBorrow borrows => simp [controlledDecrement]
      | cons next rest =>
          cases borrows with
          | nil => simp [controlledDecrement]
          | cons firstBorrow borrows =>
              have hcontrol :
                  control ∉ low :: next :: rest ++ firstBorrow :: borrows :=
                (List.nodup_cons.mp hnd).1
              have htail :
                  (low :: next :: rest ++ firstBorrow :: borrows).Nodup :=
                (List.nodup_cons.mp hnd).2
              have hlow : low ∉ next :: rest ++ firstBorrow :: borrows :=
                (List.nodup_cons.mp htail).1
              have htail := (List.nodup_cons.mp htail).2
              have hinner :
                  (firstBorrow :: next :: rest ++ borrows).Nodup := by
                have hperm :
                    ((next :: rest) ++ firstBorrow :: borrows).Perm
                      (firstBorrow :: (next :: rest) ++ borrows) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := borrows) (a := firstBorrow))
                exact htail.perm hperm
              have hcl : control ≠ low := by
                intro equality
                exact hcontrol (by simp [equality])
              have hcf : control ≠ firstBorrow := by
                intro equality
                exact hcontrol (by simp [equality])
              have hlf : low ≠ firstBorrow := by
                intro equality
                exact hlow (by simp [equality])
              rw [controlledDecrement, circuitWellFormed_append,
                circuitWellFormed_append]
              refine ⟨⟨?_, decrementTail_wellFormed
                (next :: rest) firstBorrow borrows hinner⟩, ?_⟩
              · simp [CircuitWellFormed, Gate.WellFormed, hcl, hcf, hlf]
              · simp [CircuitWellFormed, Gate.WellFormed,
                  hcl, hcf, hlf]

private theorem decrementTail_toffoliCount
    (bits : List Wire) (borrow : Wire) (borrows : List Wire)
    (hlength : bits.length = borrows.length + 1) :
    eeaToffoliCount (decrementTail bits borrow borrows) =
      2 * (bits.length - 1) := by
  induction bits generalizing borrow borrows with
  | nil => simp at hlength
  | cons bit tail ih =>
      cases tail with
      | nil =>
          have : borrows = [] :=
            shift_list_eq_nil_of_one_eq_length_add_one borrows (by simpa using hlength)
          subst borrows
          rfl
      | cons next rest =>
          cases borrows with
          | nil => simp at hlength
          | cons nextBorrow borrows =>
              have htailLength : (next :: rest).length = borrows.length + 1 := by
                simpa using hlength
              rw [decrementTail, eeaToffoliCount_append,
                eeaToffoliCount_append, ih nextBorrow borrows htailLength]
              simp [eeaToffoliCount]
              omega

private theorem decrementTail_cnotCount
    (bits : List Wire) (borrow : Wire) (borrows : List Wire)
    (hlength : bits.length = borrows.length + 1) :
    eeaCnotCount (decrementTail bits borrow borrows) = bits.length := by
  induction bits generalizing borrow borrows with
  | nil => simp at hlength
  | cons bit tail ih =>
      cases tail with
      | nil =>
          have : borrows = [] :=
            shift_list_eq_nil_of_one_eq_length_add_one borrows (by simpa using hlength)
          subst borrows
          rfl
      | cons next rest =>
          cases borrows with
          | nil => simp at hlength
          | cons nextBorrow borrows =>
              have htailLength : (next :: rest).length = borrows.length + 1 := by
                simpa using hlength
              rw [decrementTail, eeaCnotCount_append,
                eeaCnotCount_append, ih nextBorrow borrows htailLength]
              simp [eeaCnotCount]

private theorem decrementTail_xCount
    (bits : List Wire) (borrow : Wire) (borrows : List Wire)
    (hlength : bits.length = borrows.length + 1) :
    eeaXCount (decrementTail bits borrow borrows) =
      4 * (bits.length - 1) := by
  induction bits generalizing borrow borrows with
  | nil => simp at hlength
  | cons bit tail ih =>
      cases tail with
      | nil =>
          have : borrows = [] :=
            shift_list_eq_nil_of_one_eq_length_add_one borrows (by simpa using hlength)
          subst borrows
          rfl
      | cons next rest =>
          cases borrows with
          | nil => simp at hlength
          | cons nextBorrow borrows =>
              have htailLength : (next :: rest).length = borrows.length + 1 := by
                simpa using hlength
              rw [decrementTail, eeaXCount_append,
                eeaXCount_append, ih nextBorrow borrows htailLength]
              simp [eeaXCount]
              omega

private theorem decrementTail_tCount
    (bits : List Wire) (borrow : Wire) (borrows : List Wire)
    (hlength : bits.length = borrows.length + 1) :
    tCount (decrementTail bits borrow borrows) =
      14 * (bits.length - 1) := by
  induction bits generalizing borrow borrows with
  | nil => simp at hlength
  | cons bit tail ih =>
      cases tail with
      | nil =>
          have : borrows = [] :=
            shift_list_eq_nil_of_one_eq_length_add_one borrows (by simpa using hlength)
          subst borrows
          rfl
      | cons next rest =>
          cases borrows with
          | nil => simp at hlength
          | cons nextBorrow borrows =>
              have htailLength : (next :: rest).length = borrows.length + 1 := by
                simpa using hlength
              rw [decrementTail, tCount_append, tCount_append,
                ih nextBorrow borrows htailLength]
              simp [tCost]
              omega

/-- Two borrow-chain Toffolis per non-low bit. -/
theorem controlledDecrement_toffoliCount
    (control : Wire) (register borrows : List Wire)
    (hlength : register.length = borrows.length + 1) :
    eeaToffoliCount (controlledDecrement control register borrows) =
      2 * (register.length - 1) := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have : borrows = [] :=
            shift_list_eq_nil_of_one_eq_length_add_one borrows (by simpa using hlength)
          subst borrows
          rfl
      | cons next rest =>
          cases borrows with
          | nil => simp at hlength
          | cons firstBorrow borrows =>
              have htailLength : (next :: rest).length = borrows.length + 1 := by
                simpa using hlength
              rw [controlledDecrement, eeaToffoliCount_append,
                eeaToffoliCount_append,
                decrementTail_toffoliCount _ _ _ htailLength]
              simp [eeaToffoliCount]
              omega

/-- At width at least two, the explicit decrement uses `n+2` CNOTs. -/
theorem controlledDecrement_cnotCount
    (control low next : Wire) (rest borrows : List Wire)
    (hlength : (low :: next :: rest).length = borrows.length + 1) :
    eeaCnotCount
        (controlledDecrement control (low :: next :: rest) borrows) =
      (low :: next :: rest).length + 2 := by
  cases borrows with
  | nil => simp at hlength
  | cons firstBorrow borrows =>
      have htailLength : (next :: rest).length = borrows.length + 1 := by
        simpa using hlength
      rw [controlledDecrement, eeaCnotCount_append,
        eeaCnotCount_append, decrementTail_cnotCount _ _ _ htailLength]
      simp [eeaCnotCount]
      omega

/-- Four negative-control conjugating X gates per non-low bit. -/
theorem controlledDecrement_xCount
    (control : Wire) (register borrows : List Wire)
    (hlength : register.length = borrows.length + 1) :
    eeaXCount (controlledDecrement control register borrows) =
      4 * (register.length - 1) := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have : borrows = [] :=
            shift_list_eq_nil_of_one_eq_length_add_one borrows (by simpa using hlength)
          subst borrows
          rfl
      | cons next rest =>
          cases borrows with
          | nil => simp at hlength
          | cons firstBorrow borrows =>
              have htailLength : (next :: rest).length = borrows.length + 1 := by
                simpa using hlength
              rw [controlledDecrement, eeaXCount_append,
                eeaXCount_append, decrementTail_xCount _ _ _ htailLength]
              simp [eeaXCount]
              omega

/-- Constructor-derived T count of the explicit decrement. -/
theorem controlledDecrement_tCount
    (control : Wire) (register borrows : List Wire)
    (hlength : register.length = borrows.length + 1) :
    tCount (controlledDecrement control register borrows) =
      14 * (register.length - 1) := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have : borrows = [] :=
            shift_list_eq_nil_of_one_eq_length_add_one borrows (by simpa using hlength)
          subst borrows
          rfl
      | cons next rest =>
          cases borrows with
          | nil => simp at hlength
          | cons firstBorrow borrows =>
              have htailLength : (next :: rest).length = borrows.length + 1 := by
                simpa using hlength
              rw [controlledDecrement, tCount_append, tCount_append,
                decrementTail_tCount _ _ _ htailLength]
              simp [tCost]
              omega

/-! ## Source cycle decomposition for a right rotation by two -/

/-- Entries at even positions, in increasing source-index order. -/
def evenPositions : List α → List α
  | [] => []
  | [value] => [value]
  | even :: _odd :: rest => even :: evenPositions rest

/-- Entries at odd positions, in increasing source-index order. -/
def oddPositions : List α → List α
  | [] => []
  | [_] => []
  | _even :: odd :: rest => odd :: oddPositions rest

/-- The cycles visited by `controlled_rotate_right_by_two` in the pinned source.  Odd-sized words
have one cycle (`evens ++ odds`); even-sized words have the two parity cycles separately. -/
def rightTwoCycles (register : List Wire) : List (List Wire) :=
  if register.length ≤ 2 then []
  else if register.length % 2 = 0 then
    [evenPositions register, oddPositions register]
  else
    [evenPositions register ++ oddPositions register]

/-- Pivot transpositions implementing one source permutation cycle. -/
def controlledCycle (control : Wire) : List Wire → Circuit
  | [] => []
  | _pivot :: [] => []
  | pivot :: next :: rest =>
      controlledSwap control pivot next ++
        controlledCycle control (pivot :: rest)

/-- Controlled cyclic right rotation by two, using `m - gcd(m,2)` Fredkin gates rather than two
adjacent-swap cascades. -/
def controlledRotateRightTwo (control : Wire) (register : List Wire) : Circuit :=
  (rightTwoCycles register).flatMap (controlledCycle control)

/-- The alternating parity lists contain every source entry exactly once. -/
theorem evenPositions_append_oddPositions_perm (values : List α) :
    (evenPositions values ++ oddPositions values).Perm values := by
  induction values using List.twoStepInduction with
  | nil => simp [evenPositions, oddPositions]
  | singleton first => simp [evenPositions, oddPositions]
  | cons_cons first second rest ih _ =>
      simp only [evenPositions, oddPositions, List.cons_append]
      apply List.Perm.cons first
      exact (List.perm_middle (l₁ := evenPositions rest)
        (l₂ := oddPositions rest) (a := second)).trans
          (List.Perm.cons second ih)

/-- Above the source's size-two no-op boundary, flattening the visited cycles is a permutation of
the word. -/
theorem rightTwoCycles_flatten_perm
    (register : List Wire) (hsize : 2 < register.length) :
    (rightTwoCycles register).flatten.Perm register := by
  have hnotSmall : ¬register.length ≤ 2 := by omega
  by_cases heven : register.length % 2 = 0
  · simpa [rightTwoCycles, hnotSmall, heven] using
      evenPositions_append_oddPositions_perm register
  · simpa [rightTwoCycles, hnotSmall, heven] using
      evenPositions_append_oddPositions_perm register

/-- Pure basis-state swap used to state the direct semantics of a source permutation cycle. -/
def swapWireState (left right : Wire) (state : BasisState) : BasisState :=
  state[left ↦ state right][right ↦ state left]

/-- Apply the source cycle's pivot transpositions as a pure basis-state permutation. -/
def applyRightTwoCycle : List Wire → BasisState → BasisState
  | [], state => state
  | [_], state => state
  | pivot :: next :: rest, state =>
      applyRightTwoCycle (pivot :: rest) (swapWireState pivot next state)

/-- Apply every source parity cycle in order. -/
def applyRightTwoCycles : List (List Wire) → BasisState → BasisState
  | [], state => state
  | cycle :: cycles, state =>
      applyRightTwoCycles cycles (applyRightTwoCycle cycle state)

/-- Circuit-independent right-by-two permutation implemented by the pinned cycle decomposition. -/
def rotateRightTwoState (register : List Wire) (state : BasisState) : BasisState :=
  applyRightTwoCycles (rightTwoCycles register) state

private theorem applyRightTwoCycle_preservesOutside
    (cycle : List Wire) (state : BasisState) (wire : Wire)
    (hwire : wire ∉ cycle) :
    applyRightTwoCycle cycle state wire = state wire := by
  cases cycle with
  | nil => simp [applyRightTwoCycle]
  | cons pivot tail =>
      induction tail generalizing state with
      | nil => simp [applyRightTwoCycle]
      | cons next rest ih =>
          simp only [List.mem_cons, not_or] at hwire
          rw [applyRightTwoCycle, ih]
          · simp [swapWireState, upd, hwire.1, hwire.2.1]
          · simpa only [List.mem_cons, not_or] using ⟨hwire.1, hwire.2.2⟩

private theorem run_controlledCycle_cons
    (control pivot : Wire) : ∀ (tail : List Wire) (state : BasisState),
    (control :: pivot :: tail).Nodup →
    run (controlledCycle control (pivot :: tail)) state =
      if state control then applyRightTwoCycle (pivot :: tail) state
      else state := by
  intro tail
  induction tail with
  | nil =>
      intro state _
      simp [controlledCycle, applyRightTwoCycle]
  | cons next rest ih =>
      intro state hnd
      have hcontrol : control ∉ pivot :: next :: rest :=
        (List.nodup_cons.mp hnd).1
      have hpivot : pivot ∉ next :: rest :=
        (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      have hrecursive : (control :: pivot :: rest).Nodup := by
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          exact hcontrol (by
            simp only [List.mem_cons] at hmem ⊢
            rcases hmem with equality | hmem
            · exact Or.inl equality
            · exact Or.inr (Or.inr hmem))
        · apply List.nodup_cons.mpr
          exact ⟨fun hmem => hpivot (by simp [hmem]),
            ((List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).tail⟩
      have hcp : control ≠ pivot := by
        intro equality
        exact hcontrol (by simp [equality])
      have hcn : control ≠ next := by
        intro equality
        exact hcontrol (by simp [equality])
      have hpn : pivot ≠ next := by
        intro equality
        exact hpivot (by simp [equality])
      rw [controlledCycle, run_append,
        run_controlledSwap control pivot next state hcp hcn hpn]
      rw [applyRightTwoCycle]
      change
        run (controlledCycle control (pivot :: rest))
            (if state control then swapWireState pivot next state else state) =
          if state control then
            applyRightTwoCycle (pivot :: rest) (swapWireState pivot next state)
          else state
      cases hc : state control <;>
        simp [hc, ih _ hrecursive, swapWireState, upd, hcp, hcn]

/-- Exact whole-state action of one pivot cycle. -/
theorem run_controlledCycle
    (control : Wire) (cycle : List Wire) (state : BasisState)
    (hnd : (control :: cycle).Nodup) :
    run (controlledCycle control cycle) state =
      if state control then applyRightTwoCycle cycle state else state := by
  cases cycle with
  | nil => simp [controlledCycle, applyRightTwoCycle]
  | cons pivot tail => exact run_controlledCycle_cons control pivot tail state hnd

private theorem applyRightTwoCycles_preservesOutside
    (cycles : List (List Wire)) (state : BasisState) (wire : Wire)
    (hwire : wire ∉ cycles.flatten) :
    applyRightTwoCycles cycles state wire = state wire := by
  induction cycles generalizing state with
  | nil => rfl
  | cons cycle cycles ih =>
      simp only [List.flatten_cons, List.mem_append, not_or] at hwire
      rw [applyRightTwoCycles, ih _ hwire.2,
        applyRightTwoCycle_preservesOutside cycle state wire hwire.1]

private theorem run_controlledCycles
    (control : Wire) : ∀ (cycles : List (List Wire)) (state : BasisState),
    (control :: cycles.flatten).Nodup →
    run (cycles.flatMap (controlledCycle control)) state =
      if state control then applyRightTwoCycles cycles state else state := by
  intro cycles
  induction cycles with
  | nil => simp [applyRightTwoCycles]
  | cons cycle cycles ih =>
      intro state hnd
      have hcontrol : control ∉ cycle ++ cycles.flatten :=
        (List.nodup_cons.mp hnd).1
      have htail : (cycle ++ cycles.flatten).Nodup :=
        (List.nodup_cons.mp hnd).2
      have hsplit := List.nodup_append.mp htail
      have hcycle : (control :: cycle).Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨fun hmem => hcontrol (List.mem_append_left _ hmem), hsplit.1⟩
      have hcycles : (control :: cycles.flatten).Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨fun hmem => hcontrol (List.mem_append_right _ hmem), hsplit.2.1⟩
      rw [List.flatMap_cons, run_append,
        run_controlledCycle control cycle state hcycle]
      split
      · rename_i htrue
        have hcontrolAfter :
            applyRightTwoCycle cycle state control = state control := by
          apply applyRightTwoCycle_preservesOutside
          intro hmem
          exact hcontrol (List.mem_append_left _ hmem)
        rw [ih _ hcycles, hcontrolAfter, htrue]
        rfl
      · rename_i hfalse
        cases hc : state control <;> simp_all

private theorem controlledCycle_cons_usesOnly
    (control pivot : Wire) : ∀ tail : List Wire,
    PaperCircuitUsesOnly (control :: pivot :: tail)
      (controlledCycle control (pivot :: tail)) := by
  intro tail
  induction tail with
  | nil => simp [controlledCycle, PaperCircuitUsesOnly]
  | cons next rest ih =>
      rw [controlledCycle]
      apply PaperCircuitUsesOnly.append
      · apply (controlledSwap_usesOnly control pivot next).mono
        intro item hitem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hitem ⊢
        rcases hitem with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
      · apply ih.mono
        intro item hitem
        simp only [List.mem_cons] at hitem ⊢
        rcases hitem with rfl | rfl | hitem
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr hitem))

/-- One source permutation cycle touches only its control and cycle word. -/
theorem controlledCycle_usesOnly (control : Wire) (cycle : List Wire) :
    PaperCircuitUsesOnly (control :: cycle) (controlledCycle control cycle) := by
  cases cycle with
  | nil => simp [controlledCycle, PaperCircuitUsesOnly]
  | cons pivot tail => exact controlledCycle_cons_usesOnly control pivot tail

/-- Direct whole-state semantics of the source-exact right-by-two cycle circuit. -/
theorem run_controlledRotateRightTwo
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    run (controlledRotateRightTwo control register) state =
      if state control then rotateRightTwoState register state else state := by
  by_cases hsize : register.length ≤ 2
  · simp [controlledRotateRightTwo, rightTwoCycles, hsize,
      rotateRightTwoState, applyRightTwoCycles]
  · have hlarge : 2 < register.length := by omega
    have hperm := rightTwoCycles_flatten_perm register hlarge
    have hcycles : (control :: (rightTwoCycles register).flatten).Nodup := by
      exact hnd.perm (List.Perm.cons control hperm.symm)
    exact run_controlledCycles control (rightTwoCycles register) state hcycles

private theorem shift_wireValues_swapWireState
    (wires : List Wire) (left right : Wire) (state : BasisState)
    (hleft : left ∉ wires) (hright : right ∉ wires) :
    wireValues wires (swapWireState left right state) =
      wireValues wires state := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [List.mem_cons, not_or] at hleft hright
      have hwireLeft : wire ≠ left := Ne.symm hleft.1
      have hwireRight : wire ≠ right := Ne.symm hright.1
      simp only [wireValues, List.map_cons, List.cons.injEq]
      exact ⟨by simp [swapWireState, upd, hwireLeft, hwireRight],
        ih hleft.2 hright.2⟩

private theorem wireValues_applyRightTwoCycle_outside
    (observed cycle : List Wire) (state : BasisState)
    (hdisjoint : ∀ wire ∈ observed, wire ∉ cycle) :
    wireValues observed (applyRightTwoCycle cycle state) =
      wireValues observed state := by
  induction observed with
  | nil => rfl
  | cons wire observed ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq]
      exact ⟨applyRightTwoCycle_preservesOutside cycle state wire
          (hdisjoint wire (by simp)),
        ih (fun item hitem => hdisjoint item (by simp [hitem]))⟩

private def insertAfterHead (value : α) : List α → List α
  | [] => [value]
  | head :: tail => head :: value :: tail

private theorem rotate_insert_after_head
    (first second : α) (rest : List α) :
    insertAfterHead first ((second :: rest).rotate rest.length) =
      (first :: second :: rest).rotate (rest.length + 1) := by
  induction rest using List.reverseRecOn with
  | nil => simp [insertAfterHead]
  | append_singleton value rest ih =>
      simp [insertAfterHead, List.length_append,
        List.rotate_eq_drop_append_take]

private theorem applyRightTwoCycle_values
    (cycle : List Wire) (state : BasisState)
    (hnd : cycle.Nodup) :
    wireValues cycle (applyRightTwoCycle cycle state) =
      (wireValues cycle state).rotate (cycle.length - 1) := by
  cases cycle with
  | nil => simp [applyRightTwoCycle, wireValues]
  | cons pivot tail =>
      induction tail generalizing pivot state with
      | nil => simp [applyRightTwoCycle, wireValues]
      | cons next rest ih =>
          have hpivot : pivot ∉ next :: rest :=
            (List.nodup_cons.mp hnd).1
          have htail : (next :: rest).Nodup :=
            (List.nodup_cons.mp hnd).2
          have hnext : next ∉ rest := (List.nodup_cons.mp htail).1
          have hrest : rest.Nodup := (List.nodup_cons.mp htail).2
          have hrecursive : (pivot :: rest).Nodup := by
            apply List.nodup_cons.mpr
            exact ⟨fun hmem => hpivot (List.mem_cons_of_mem next hmem), hrest⟩
          have hnextOutside : next ∉ pivot :: rest := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun equality => hpivot (by simp [equality]), hnext⟩
          have hpivotRest : pivot ∉ rest := by
            intro hmem
            exact hpivot (List.mem_cons_of_mem next hmem)
          have hpivotNext : pivot ≠ next := by
            intro equality
            exact hpivot (by simp [equality])
          let swapped := swapWireState pivot next state
          let after := applyRightTwoCycle (pivot :: rest) swapped
          have hih :
              wireValues (pivot :: rest) after =
                (wireValues (pivot :: rest) swapped).rotate
                  ((pivot :: rest).length - 1) :=
            ih swapped pivot hrecursive
          have hrestSwapped :
              wireValues rest swapped = wireValues rest state := by
            exact shift_wireValues_swapWireState rest pivot next state
              hpivotRest hnext
          have hvaluesSwapped :
              wireValues (pivot :: rest) swapped =
                state next :: wireValues rest state := by
            simp only [wireValues, List.map_cons, List.cons.injEq]
            exact ⟨by simp [swapped, swapWireState, upd, hpivotNext],
              hrestSwapped⟩
          have hih' :
              wireValues (pivot :: rest) after =
                (state next :: wireValues rest state).rotate rest.length := by
            calc
              wireValues (pivot :: rest) after =
                  (wireValues (pivot :: rest) swapped).rotate
                    ((pivot :: rest).length - 1) := hih
              _ = (state next :: wireValues rest state).rotate rest.length := by
                rw [hvaluesSwapped]
                simp
          have hnextAfter : after next = state pivot := by
            calc
              after next = swapped next :=
                applyRightTwoCycle_preservesOutside
                  (pivot :: rest) swapped next hnextOutside
              _ = state pivot := by simp [swapped, swapWireState]
          rw [applyRightTwoCycle]
          change wireValues (pivot :: next :: rest) after = _
          calc
            wireValues (pivot :: next :: rest) after =
                insertAfterHead (state pivot)
                  (wireValues (pivot :: rest) after) := by
              simp [wireValues, insertAfterHead, hnextAfter]
            _ = insertAfterHead (state pivot)
                ((state next :: wireValues rest state).rotate rest.length) := by
              rw [hih']
            _ = (state pivot :: state next :: wireValues rest state).rotate
                (rest.length + 1) :=
              by simpa [wireValues] using
                rotate_insert_after_head (state pivot) (state next)
                  (wireValues rest state)
            _ = (wireValues (pivot :: next :: rest) state).rotate
                ((pivot :: next :: rest).length - 1) := by
              simp [wireValues]

private def interleaveParity : List α → List α → List α
  | [], odds => odds
  | evens, [] => evens
  | even :: evens, odd :: odds =>
      even :: odd :: interleaveParity evens odds

private theorem interleaveParity_even_odd (values : List α) :
    interleaveParity (evenPositions values) (oddPositions values) = values := by
  induction values using List.twoStepInduction with
  | nil => rfl
  | singleton value => rfl
  | cons_cons first second rest ih _ =>
      simp [evenPositions, oddPositions, interleaveParity, ih]

private theorem wireValues_evenPositions
    (wires : List Wire) (state : BasisState) :
    wireValues (evenPositions wires) state =
      evenPositions (wireValues wires state) := by
  induction wires using List.twoStepInduction with
  | nil => rfl
  | singleton wire => rfl
  | cons_cons first second rest ih _ =>
      have ih' : List.map state (evenPositions rest) =
          evenPositions (List.map state rest) := by
        simpa only [wireValues] using ih
      simp [wireValues, evenPositions, ih']

private theorem wireValues_oddPositions
    (wires : List Wire) (state : BasisState) :
    wireValues (oddPositions wires) state =
      oddPositions (wireValues wires state) := by
  induction wires using List.twoStepInduction with
  | nil => rfl
  | singleton wire => rfl
  | cons_cons first second rest ih _ =>
      have ih' : List.map state (oddPositions rest) =
          oddPositions (List.map state rest) := by
        simpa only [wireValues] using ih
      simp [wireValues, oddPositions, ih']

private theorem evenPositions_append_two
    (values : List α) (first second : α) :
    evenPositions (values ++ [first, second]) =
      if values.length % 2 = 0 then evenPositions values ++ [first]
      else evenPositions values ++ [second] := by
  induction values using List.twoStepInduction with
  | nil => simp [evenPositions]
  | singleton value => simp [evenPositions]
  | cons_cons head next rest ih _ =>
      simp only [List.cons_append, evenPositions, List.length_cons]
      rw [ih]
      by_cases hparity : rest.length % 2 = 0
      · simp [hparity, Nat.add_mod]
      · have hodd : rest.length % 2 = 1 := by omega
        simp [hodd, Nat.add_mod]

private theorem oddPositions_append_two
    (values : List α) (first second : α) :
    oddPositions (values ++ [first, second]) =
      if values.length % 2 = 0 then oddPositions values ++ [second]
      else oddPositions values ++ [first] := by
  induction values using List.twoStepInduction with
  | nil => simp [oddPositions]
  | singleton value => simp [oddPositions]
  | cons_cons head next rest ih _ =>
      simp only [List.cons_append, oddPositions, List.length_cons]
      rw [ih]
      by_cases hparity : rest.length % 2 = 0
      · simp [hparity, Nat.add_mod]
      · have hodd : rest.length % 2 = 1 := by omega
        simp [hodd, Nat.add_mod]

private theorem evenPositions_length_of_odd
    (values : List α) (hodd : values.length % 2 ≠ 0) :
    (evenPositions values).length = (oddPositions values).length + 1 := by
  induction values using List.twoStepInduction with
  | nil => simp at hodd
  | singleton value => simp [evenPositions, oddPositions]
  | cons_cons first second rest ih _ =>
      simp only [List.length_cons] at hodd
      have hrestOdd : rest.length % 2 ≠ 0 := by
        omega
      simpa [evenPositions, oddPositions] using ih hrestOdd

private theorem interleaveParity_rotate_right_two_of_even
    (values : List α) (hlarge : 2 < values.length)
    (heven : values.length % 2 = 0) :
    interleaveParity
        ((evenPositions values).rotate ((evenPositions values).length - 1))
        ((oddPositions values).rotate ((oddPositions values).length - 1)) =
      values.rotate (values.length - 2) := by
  induction values using List.reverseRecOn with
  | nil => simp at hlarge
  | append_singleton beforeLast last _ =>
      induction beforeLast using List.reverseRecOn with
      | nil => simp at hlarge
      | append_singleton initial penultimate _ =>
          have hinitialEven : initial.length % 2 = 0 := by
            simpa [List.length_append, Nat.add_mod] using heven
          rw [show (initial ++ [penultimate]) ++ [last] =
              initial ++ [penultimate, last] by simp]
          rw [evenPositions_append_two, oddPositions_append_two]
          simp [hinitialEven, List.length_append,
            interleaveParity, interleaveParity_even_odd]

private theorem interleaveParity_rotate_right_two_of_odd
    (values : List α) (hlarge : 2 < values.length)
    (hodd : values.length % 2 ≠ 0) :
    let evens := evenPositions values
    let rotated := (evens ++ oddPositions values).rotate
      ((evens ++ oddPositions values).length - 1)
    interleaveParity (rotated.take evens.length) (rotated.drop evens.length) =
      values.rotate (values.length - 2) := by
  induction values using List.reverseRecOn with
  | nil => simp at hlarge
  | append_singleton beforeLast last _ =>
      induction beforeLast using List.reverseRecOn with
      | nil => simp at hlarge
      | append_singleton initial penultimate _ =>
          have hinitialOdd : initial.length % 2 ≠ 0 := by
            intro heven
            apply hodd
            simpa [List.length_append, Nat.add_mod] using heven
          have hparityLength :=
            evenPositions_length_of_odd initial hinitialOdd
          rw [show (initial ++ [penultimate]) ++ [last] =
              initial ++ [penultimate, last] by simp]
          rw [evenPositions_append_two, oddPositions_append_two]
          simp only [hinitialOdd, if_false, List.length_append,
            List.length_singleton]
          rw [show evenPositions initial ++ [last] ++
                (oddPositions initial ++ [penultimate]) =
              (evenPositions initial ++ [last] ++ oddPositions initial) ++
                [penultimate] by simp [List.append_assoc]]
          rw [show (evenPositions initial).length + 1 +
                ((oddPositions initial).length + 1) - 1 =
              (evenPositions initial ++ [last] ++
                oddPositions initial).length by
              simp [hparityLength]
              omega]
          rw [List.rotate_append_length_eq]
          simp [hparityLength, interleaveParity,
            interleaveParity_even_odd]

/-- Reading the pure source-cycle state in register order gives the ordinary right rotation by
two.  `List.rotate` is a left rotation, so the offset `length - 2` is exactly right-by-two; for
words of length at most two both the source circuit and this expression are the identity. -/
theorem rotateRightTwoState_values
    (register : List Wire) (state : BasisState)
    (hnd : register.Nodup) :
    wireValues register (rotateRightTwoState register state) =
      (wireValues register state).rotate (register.length - 2) := by
  by_cases hsize : register.length ≤ 2
  · have hzero : register.length - 2 = 0 := by omega
    simp [rotateRightTwoState, rightTwoCycles, hsize,
      applyRightTwoCycles, hzero]
  · have hlarge : 2 < register.length := by omega
    have hcombined :
        (evenPositions register ++ oddPositions register).Nodup :=
      (evenPositions_append_oddPositions_perm register).nodup_iff.mpr hnd
    have hsplit := List.nodup_append.mp hcombined
    by_cases heven : register.length % 2 = 0
    · let evenCycle := evenPositions register
      let oddCycle := oddPositions register
      let first := applyRightTwoCycle evenCycle state
      let after := applyRightTwoCycle oddCycle first
      have hevenValues :
          wireValues evenCycle first =
            (wireValues evenCycle state).rotate (evenCycle.length - 1) :=
        applyRightTwoCycle_values evenCycle state hsplit.1
      have hoddFirst : wireValues oddCycle first = wireValues oddCycle state := by
        apply wireValues_applyRightTwoCycle_outside
        intro wire hwire
        exact fun hevenMem => hsplit.2.2 wire hevenMem wire hwire rfl
      have hoddValues :
          wireValues oddCycle after =
            (wireValues oddCycle state).rotate (oddCycle.length - 1) := by
        calc
          wireValues oddCycle after =
              (wireValues oddCycle first).rotate (oddCycle.length - 1) :=
            applyRightTwoCycle_values oddCycle first hsplit.2.1
          _ = (wireValues oddCycle state).rotate
                (oddCycle.length - 1) := by rw [hoddFirst]
      have hevenAfter : wireValues evenCycle after = wireValues evenCycle first := by
        apply wireValues_applyRightTwoCycle_outside
        intro wire hwire
        exact fun hoddMem => hsplit.2.2 wire hwire wire hoddMem rfl
      have hstate : rotateRightTwoState register state = after := by
        simp [rotateRightTwoState, rightTwoCycles, hsize, heven,
          applyRightTwoCycles, evenCycle, oddCycle, first, after]
      rw [hstate]
      change wireValues register after = _
      calc
        wireValues register after =
            interleaveParity (wireValues evenCycle after)
              (wireValues oddCycle after) := by
          rw [wireValues_evenPositions, wireValues_oddPositions]
          exact (interleaveParity_even_odd
            (wireValues register after)).symm
        _ = interleaveParity
              ((wireValues evenCycle state).rotate
                (evenCycle.length - 1))
              ((wireValues oddCycle state).rotate
                (oddCycle.length - 1)) := by
          rw [hevenAfter, hevenValues, hoddValues]
        _ = (wireValues register state).rotate (register.length - 2) := by
          have hevenMap := wireValues_evenPositions register state
          have hoddMap := wireValues_oddPositions register state
          simp only [wireValues] at hevenMap hoddMap
          have hevenLength : (evenPositions register).length =
              (evenPositions (List.map state register)).length := by
            simpa using congrArg List.length hevenMap
          have hoddLength : (oddPositions register).length =
              (oddPositions (List.map state register)).length := by
            simpa using congrArg List.length hoddMap
          dsimp only [evenCycle, oddCycle]
          simp only [wireValues]
          rw [hevenMap, hoddMap]
          rw [hevenLength, hoddLength]
          simpa [wireValues] using
            interleaveParity_rotate_right_two_of_even
              (wireValues register state)
              (by simpa [wireValues] using hlarge)
              (by simpa [wireValues] using heven)
    · let cycle := evenPositions register ++ oddPositions register
      let after := applyRightTwoCycle cycle state
      have hcycleValues :
          wireValues cycle after =
            (wireValues cycle state).rotate (cycle.length - 1) :=
        applyRightTwoCycle_values cycle state hcombined
      let rotated := (wireValues cycle state).rotate (cycle.length - 1)
      have hevenAfter :
          wireValues (evenPositions register) after =
            rotated.take (evenPositions register).length := by
        have htake := congrArg (List.take (evenPositions register).length)
          hcycleValues
        simpa [cycle, rotated, wireValues] using htake
      have hoddAfter :
          wireValues (oddPositions register) after =
            rotated.drop (evenPositions register).length := by
        have hdrop := congrArg (List.drop (evenPositions register).length)
          hcycleValues
        simpa [cycle, rotated, wireValues] using hdrop
      have hstate : rotateRightTwoState register state = after := by
        simp [rotateRightTwoState, rightTwoCycles, hsize, heven,
          applyRightTwoCycles, cycle, after]
      rw [hstate]
      change wireValues register after = _
      calc
        wireValues register after =
            interleaveParity
              (wireValues (evenPositions register) after)
              (wireValues (oddPositions register) after) := by
          rw [wireValues_evenPositions, wireValues_oddPositions]
          exact (interleaveParity_even_odd
            (wireValues register after)).symm
        _ = interleaveParity
              (rotated.take (evenPositions register).length)
              (rotated.drop (evenPositions register).length) := by
          rw [hevenAfter, hoddAfter]
        _ = (wireValues register state).rotate (register.length - 2) := by
          have hevenMap := wireValues_evenPositions register state
          have hoddMap := wireValues_oddPositions register state
          simp only [wireValues] at hevenMap hoddMap
          have hevenLength : (evenPositions register).length =
              (evenPositions (List.map state register)).length := by
            simpa using congrArg List.length hevenMap
          have hoddLength : (oddPositions register).length =
              (oddPositions (List.map state register)).length := by
            simpa using congrArg List.length hoddMap
          dsimp only [rotated, cycle]
          simp only [wireValues, List.map_append]
          rw [hevenMap, hoddMap]
          simp only [List.length_append]
          rw [hevenLength, hoddLength]
          simpa [wireValues] using
            interleaveParity_rotate_right_two_of_odd
              (wireValues register state)
              (by simpa [wireValues] using hlarge)
              (by simpa [wireValues] using heven)

/-- Direct register semantics of the optimized controlled right-by-two circuit. -/
theorem run_controlledRotateRightTwo_values
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    wireValues register
        (run (controlledRotateRightTwo control register) state) =
      if state control then
        (wireValues register state).rotate (register.length - 2)
      else wireValues register state := by
  rw [run_controlledRotateRightTwo control register state hnd]
  split
  · exact rotateRightTwoState_values register state
      (List.nodup_cons.mp hnd).2
  · rfl

/-- The right-by-two circuit touches only its control and target word. -/
theorem controlledRotateRightTwo_usesOnly
    (control : Wire) (register : List Wire) :
    PaperCircuitUsesOnly (control :: register)
      (controlledRotateRightTwo control register) := by
  intro gate hgate wire hwire
  by_cases hsize : register.length ≤ 2
  · simp [controlledRotateRightTwo, rightTwoCycles, hsize] at hgate
  · have hlarge : 2 < register.length := by omega
    have hperm := rightTwoCycles_flatten_perm register hlarge
    have hcycleGate :
        ∃ cycle ∈ rightTwoCycles register,
          gate ∈ controlledCycle control cycle := by
      simpa [controlledRotateRightTwo] using hgate
    obtain ⟨cycle, hcycle, hgate⟩ := hcycleGate
    have hcycleSubset : ∀ item ∈ cycle, item ∈ register := by
      intro item hitem
      have : item ∈ (rightTwoCycles register).flatten := by
        simp only [List.mem_flatten]
        exact ⟨cycle, hcycle, hitem⟩
      exact (List.Perm.mem_iff hperm).mp this
    have huses := controlledCycle_usesOnly control cycle
    have := huses gate hgate wire hwire
    simp only [List.mem_cons] at this ⊢
    rcases this with rfl | hwire
    · exact Or.inl rfl
    · exact Or.inr (hcycleSubset wire hwire)

private theorem controlledCycle_cons_HPFree
    (control pivot : Wire) : ∀ tail : List Wire,
    HPFree (controlledCycle control (pivot :: tail)) := by
  intro tail
  induction tail with
  | nil => simp [controlledCycle]
  | cons next rest ih =>
      simp [controlledCycle, controlledSwap_HPFree, ih]

/-- Every gate in one source permutation cycle is classical. -/
@[simp]
theorem controlledCycle_HPFree (control : Wire) (cycle : List Wire) :
    HPFree (controlledCycle control cycle) := by
  cases cycle with
  | nil => simp [controlledCycle]
  | cons pivot tail => exact controlledCycle_cons_HPFree control pivot tail

private theorem controlledCycles_HPFree
    (control : Wire) : ∀ cycles : List (List Wire),
    HPFree (cycles.flatMap (controlledCycle control)) := by
  intro cycles
  induction cycles with
  | nil => simp
  | cons cycle cycles ih =>
      simp only [List.flatMap_cons]
      exact (hpFree_append _ _).2
        ⟨controlledCycle_HPFree control cycle, ih⟩

/-- The full right-by-two cycle circuit is H/P-free. -/
@[simp]
theorem controlledRotateRightTwo_HPFree
    (control : Wire) (register : List Wire) :
    HPFree (controlledRotateRightTwo control register) :=
  controlledCycles_HPFree control (rightTwoCycles register)

private theorem controlledCycle_cons_wellFormed
    (control pivot : Wire) : ∀ tail : List Wire,
    (control :: pivot :: tail).Nodup →
    CircuitWellFormed (controlledCycle control (pivot :: tail)) := by
  intro tail
  induction tail with
  | nil => simp [controlledCycle]
  | cons next rest ih =>
      intro hnd
      have hcontrol : control ∉ pivot :: next :: rest :=
        (List.nodup_cons.mp hnd).1
      have hpivot : pivot ∉ next :: rest :=
        (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      have hrecursive : (control :: pivot :: rest).Nodup := by
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          exact hcontrol (by
            simp only [List.mem_cons] at hmem ⊢
            rcases hmem with equality | hmem
            · exact Or.inl equality
            · exact Or.inr (Or.inr hmem))
        · apply List.nodup_cons.mpr
          exact ⟨fun hmem => hpivot (by simp [hmem]),
            ((List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).tail⟩
      have hcp : control ≠ pivot := by
        intro equality
        exact hcontrol (by simp [equality])
      have hcn : control ≠ next := by
        intro equality
        exact hcontrol (by simp [equality])
      have hpn : pivot ≠ next := by
        intro equality
        exact hpivot (by simp [equality])
      rw [controlledCycle, circuitWellFormed_append]
      exact ⟨controlledSwap_wellFormed control pivot next hcp hcn hpn,
        ih hrecursive⟩

/-- Physical well-formedness of one source permutation cycle. -/
theorem controlledCycle_wellFormed
    (control : Wire) (cycle : List Wire)
    (hnd : (control :: cycle).Nodup) :
    CircuitWellFormed (controlledCycle control cycle) := by
  cases cycle with
  | nil => simp [controlledCycle]
  | cons pivot tail => exact controlledCycle_cons_wellFormed control pivot tail hnd

private theorem controlledCycles_wellFormed
    (control : Wire) : ∀ cycles : List (List Wire),
    (control :: cycles.flatten).Nodup →
    CircuitWellFormed (cycles.flatMap (controlledCycle control)) := by
  intro cycles
  induction cycles with
  | nil => simp
  | cons cycle cycles ih =>
      intro hnd
      have hcontrol : control ∉ cycle ++ cycles.flatten :=
        (List.nodup_cons.mp hnd).1
      have hsplit := List.nodup_append.mp (List.nodup_cons.mp hnd).2
      have hcycle : (control :: cycle).Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨fun hmem => hcontrol (List.mem_append_left _ hmem), hsplit.1⟩
      have hcycles : (control :: cycles.flatten).Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨fun hmem => hcontrol (List.mem_append_right _ hmem), hsplit.2.1⟩
      rw [List.flatMap_cons, circuitWellFormed_append]
      exact ⟨controlledCycle_wellFormed control cycle hcycle, ih hcycles⟩

/-- Physical well-formedness of the full source cycle decomposition. -/
theorem controlledRotateRightTwo_wellFormed
    (control : Wire) (register : List Wire)
    (hnd : (control :: register).Nodup) :
    CircuitWellFormed (controlledRotateRightTwo control register) := by
  by_cases hsize : register.length ≤ 2
  · simp [controlledRotateRightTwo, rightTwoCycles, hsize]
  · have hlarge : 2 < register.length := by omega
    have hperm := rightTwoCycles_flatten_perm register hlarge
    apply controlledCycles_wellFormed
    exact hnd.perm (List.Perm.cons control hperm.symm)

private theorem controlledCycle_cons_toffoliCount
    (control pivot : Wire) : ∀ tail : List Wire,
    eeaToffoliCount (controlledCycle control (pivot :: tail)) = tail.length := by
  intro tail
  induction tail with
  | nil => simp [controlledCycle, eeaToffoliCount]
  | cons next rest ih =>
      rw [controlledCycle, eeaToffoliCount_append,
        controlledSwap_toffoliCount, ih]
      simp
      omega

/-- One Fredkin per non-pivot member of a source cycle. -/
theorem controlledCycle_toffoliCount
    (control : Wire) (cycle : List Wire) :
    eeaToffoliCount (controlledCycle control cycle) = cycle.length - 1 := by
  cases cycle with
  | nil => simp [controlledCycle, eeaToffoliCount]
  | cons pivot tail =>
      rw [controlledCycle_cons_toffoliCount]
      simp

private theorem controlledCycle_cons_cnotCount
    (control pivot : Wire) : ∀ tail : List Wire,
    eeaCnotCount (controlledCycle control (pivot :: tail)) =
      2 * tail.length := by
  intro tail
  induction tail with
  | nil => simp [controlledCycle, eeaCnotCount]
  | cons next rest ih =>
      rw [controlledCycle, eeaCnotCount_append,
        controlledSwap_cnotCount, ih]
      simp
      omega

/-- Two CNOTs per Fredkin in a source cycle. -/
theorem controlledCycle_cnotCount
    (control : Wire) (cycle : List Wire) :
    eeaCnotCount (controlledCycle control cycle) =
      2 * (cycle.length - 1) := by
  cases cycle with
  | nil => simp [controlledCycle, eeaCnotCount]
  | cons pivot tail =>
      rw [controlledCycle_cons_cnotCount]
      simp

private theorem controlledCycle_cons_tCount
    (control pivot : Wire) : ∀ tail : List Wire,
    tCount (controlledCycle control (pivot :: tail)) = 7 * tail.length := by
  intro tail
  induction tail with
  | nil => simp [controlledCycle, tCount]
  | cons next rest ih =>
      rw [controlledCycle, tCount_append, controlledSwap_tCount, ih]
      simp
      omega

/-- Seven T gates per Fredkin in a source cycle. -/
theorem controlledCycle_tCount
    (control : Wire) (cycle : List Wire) :
    tCount (controlledCycle control cycle) = 7 * (cycle.length - 1) := by
  cases cycle with
  | nil => simp [controlledCycle, tCount]
  | cons pivot tail =>
      rw [controlledCycle_cons_tCount]
      simp

/-- Source-visible count of the pivot transpositions in the parity-cycle decomposition. -/
def rightTwoSwapCount (register : List Wire) : Nat :=
  ((rightTwoCycles register).map fun cycle => cycle.length - 1).sum

/-- Odd source widths above two form one cycle and therefore use exactly `width - 1` swaps. -/
theorem rightTwoSwapCount_of_odd
    (register : List Wire) (hlarge : 2 < register.length)
    (hodd : register.length % 2 ≠ 0) :
    rightTwoSwapCount register = register.length - 1 := by
  have hnotSmall : ¬register.length ≤ 2 := by omega
  have hlength :
      (evenPositions register ++ oddPositions register).length = register.length :=
    (evenPositions_append_oddPositions_perm register).length_eq
  simp [rightTwoSwapCount, rightTwoCycles, hnotSmall, hodd, hlength]

private theorem controlledCycles_toffoliCount
    (control : Wire) : ∀ cycles : List (List Wire),
    eeaToffoliCount (cycles.flatMap (controlledCycle control)) =
      (cycles.map fun cycle => cycle.length - 1).sum := by
  intro cycles
  induction cycles with
  | nil => rfl
  | cons cycle cycles ih =>
      rw [List.flatMap_cons, eeaToffoliCount_append,
        controlledCycle_toffoliCount, ih]
      rfl

private theorem controlledCycles_cnotCount
    (control : Wire) : ∀ cycles : List (List Wire),
    eeaCnotCount (cycles.flatMap (controlledCycle control)) =
      2 * (cycles.map fun cycle => cycle.length - 1).sum := by
  intro cycles
  induction cycles with
  | nil => rfl
  | cons cycle cycles ih =>
      rw [List.flatMap_cons, eeaCnotCount_append,
        controlledCycle_cnotCount, ih]
      simp
      omega

private theorem controlledCycles_tCount
    (control : Wire) : ∀ cycles : List (List Wire),
    tCount (cycles.flatMap (controlledCycle control)) =
      7 * (cycles.map fun cycle => cycle.length - 1).sum := by
  intro cycles
  induction cycles with
  | nil => rfl
  | cons cycle cycles ih =>
      rw [List.flatMap_cons, tCount_append, controlledCycle_tCount, ih]
      simp
      omega

/-- The right-by-two circuit contains exactly the source cycle's swap count in Toffolis. -/
theorem controlledRotateRightTwo_toffoliCount
    (control : Wire) (register : List Wire) :
    eeaToffoliCount (controlledRotateRightTwo control register) =
      rightTwoSwapCount register := by
  exact controlledCycles_toffoliCount control (rightTwoCycles register)

/-- Each source-cycle Fredkin contributes two CNOTs. -/
theorem controlledRotateRightTwo_cnotCount
    (control : Wire) (register : List Wire) :
    eeaCnotCount (controlledRotateRightTwo control register) =
      2 * rightTwoSwapCount register := by
  exact controlledCycles_cnotCount control (rightTwoCycles register)

private theorem controlledCycle_cons_xCount
    (control pivot : Wire) : ∀ tail : List Wire,
    eeaXCount (controlledCycle control (pivot :: tail)) = 0 := by
  intro tail
  induction tail with
  | nil => simp [controlledCycle, eeaXCount]
  | cons next rest ih =>
      rw [controlledCycle, eeaXCount_append, controlledSwap_xCount, ih]

/-- Source permutation cycles contain no standalone X gates. -/
@[simp]
theorem controlledCycle_xCount
    (control : Wire) (cycle : List Wire) :
    eeaXCount (controlledCycle control cycle) = 0 := by
  cases cycle with
  | nil => simp [controlledCycle, eeaXCount]
  | cons pivot tail => exact controlledCycle_cons_xCount control pivot tail

private theorem controlledCycles_xCount
    (control : Wire) : ∀ cycles : List (List Wire),
    eeaXCount (cycles.flatMap (controlledCycle control)) = 0 := by
  intro cycles
  induction cycles with
  | nil => rfl
  | cons cycle cycles ih =>
      rw [List.flatMap_cons, eeaXCount_append,
        controlledCycle_xCount, ih]

/-- The right-by-two cycle circuit contains no standalone X gates. -/
@[simp]
theorem controlledRotateRightTwo_xCount
    (control : Wire) (register : List Wire) :
    eeaXCount (controlledRotateRightTwo control register) = 0 :=
  controlledCycles_xCount control (rightTwoCycles register)

/-- Constructor-derived T count of the right-by-two cycle circuit. -/
theorem controlledRotateRightTwo_tCount
    (control : Wire) (register : List Wire) :
    tCount (controlledRotateRightTwo control register) =
      7 * rightTwoSwapCount register := by
  exact controlledCycles_tCount control (rightTwoCycles register)

/-! ## Gate-independent word updates -/

/-- Write a Boolean word back to a list of physical wires.  This is a specification-side state
operation, not a circuit constructor.  It is public because the exported shift-state contract is
defined in terms of this operation. -/
def writeWireValues : List Wire → List Bool → BasisState → BasisState
  | wire :: wires, bit :: bits, state =>
      (writeWireValues wires bits state)[wire ↦ bit]
  | _, _, state => state

private theorem writeWireValues_preservesOutside
    (wires : List Wire) (bits : List Bool) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ wires) :
    writeWireValues wires bits state wire = state wire := by
  induction wires generalizing bits state with
  | nil => simp [writeWireValues]
  | cons head tail ih =>
      cases bits with
      | nil => simp [writeWireValues]
      | cons bit bits =>
          simp only [List.mem_cons, not_or] at hwire
          simp [writeWireValues, upd, hwire.1, ih bits state hwire.2]

private theorem wireValues_writeWireValues
    (wires : List Wire) (bits : List Bool) (state : BasisState)
    (hnd : wires.Nodup) (hlength : bits.length = wires.length) :
    wireValues wires (writeWireValues wires bits state) = bits := by
  induction wires generalizing bits state with
  | nil =>
      have : bits = [] := List.length_eq_zero_iff.mp (by simpa using hlength)
      subst bits
      rfl
  | cons head tail ih =>
      cases bits with
      | nil => simp at hlength
      | cons bit bits =>
          have hhead : head ∉ tail := (List.nodup_cons.mp hnd).1
          have htail : tail.Nodup := (List.nodup_cons.mp hnd).2
          have htailLength : bits.length = tail.length := by simpa using hlength
          have htailUpdated :
              wireValues tail
                  ((writeWireValues tail bits state)[head ↦ bit]) =
                wireValues tail (writeWireValues tail bits state) := by
            apply shift_wireValues_congr
            intro wire hwire
            have hne : wire ≠ head := by
              intro equality
              subst wire
              exact hhead hwire
            simp [upd, hne]
          simp only [writeWireValues, wireValues, List.map_cons]
          change
            (writeWireValues tail bits state)[head ↦ bit] head ::
                wireValues tail
                  ((writeWireValues tail bits state)[head ↦ bit]) =
              bit :: bits
          rw [htailUpdated, ih bits state htail htailLength]
          simp [upd]

private theorem shift_wireValues_eq_at
    (wires : List Wire) (left right : BasisState)
    (hvalues : wireValues wires left = wireValues wires right)
    {wire : Wire} (hwire : wire ∈ wires) :
    left wire = right wire := by
  induction wires with
  | nil => simp at hwire
  | cons head tail ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq] at hvalues
      rcases List.mem_cons.mp hwire with rfl | hwire
      · exact hvalues.1
      · exact ih hvalues.2 hwire

private theorem state_eq_writeWireValues
    (wires : List Wire) (bits : List Bool)
    (before after : BasisState)
    (hnd : wires.Nodup) (hlength : bits.length = wires.length)
    (hvalues : wireValues wires after = bits)
    (houtside : ∀ wire, wire ∉ wires → after wire = before wire) :
    after = writeWireValues wires bits before := by
  funext wire
  by_cases hwire : wire ∈ wires
  · apply shift_wireValues_eq_at wires
    calc
      wireValues wires after = bits := hvalues
      _ = wireValues wires (writeWireValues wires bits before) :=
        (wireValues_writeWireValues wires bits before hnd hlength).symm
    exact hwire
  · rw [houtside wire hwire,
      writeWireValues_preservesOutside wires bits before hwire]

private theorem incrementBits_length (carry : Bool) (bits : List Bool) :
    (incrementBits carry bits).length = bits.length := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih => simp [incrementBits, ih]

private theorem decrementBits_length (borrow : Bool) (bits : List Bool) :
    (decrementBits borrow bits).length = bits.length := by
  induction bits generalizing borrow with
  | nil => rfl
  | cons bit bits ih => simp [decrementBits, ih]

private theorem rotateLeftOne_length (bits : List α) :
    (rotateLeftOne bits).length = bits.length := by
  cases bits <;> simp [rotateLeftOne]

/-- Pure specification state for a controlled one-position left rotation. -/
def rotateLeftWordState
    (enabled : Bool) (register : List Wire) (state : BasisState) : BasisState :=
  writeWireValues register
    (if enabled then rotateLeftOne (wireValues register state)
      else wireValues register state) state

/-- Pure specification state for a controlled increment. -/
def incrementWordState
    (enabled : Bool) (register : List Wire) (state : BasisState) : BasisState :=
  writeWireValues register
    (incrementBits enabled (wireValues register state)) state

/-- Pure specification state for a controlled decrement. -/
def decrementWordState
    (enabled : Bool) (register : List Wire) (state : BasisState) : BasisState :=
  writeWireValues register
    (decrementBits enabled (wireValues register state)) state

private theorem run_controlledRotateLeftOne_eq_state
    (control : Wire) (register : List Wire) (state : BasisState)
    (hnd : (control :: register).Nodup) :
    run (controlledRotateLeftOne control register) state =
      rotateLeftWordState (state control) register state := by
  apply state_eq_writeWireValues register _ state _
  · exact (List.nodup_cons.mp hnd).2
  · split
    · simpa [wireValues] using
        rotateLeftOne_length (wireValues register state)
    · simp [wireValues]
  · exact run_controlledRotateLeftOne_values control register state hnd
  · intro wire hwire
    by_cases hcontrol : wire = control
    · subst wire
      exact controlledRotateLeftOne_control control register state
        (List.nodup_cons.mp hnd).1
    · exact (controlledRotateLeftOne_usesOnly control register).preservesOutside
        state (by simp [hcontrol, hwire])

private theorem run_controlledIncrement_eq_state
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledIncrement control register carries) state =
      incrementWordState (state control) register state := by
  have hcorrect := controlledIncrement_correct control register carries state
    hlength hnd hclean
  apply state_eq_writeWireValues register _ state _
  · exact (List.nodup_append.mp (List.nodup_cons.mp hnd).2).1
  · simpa [wireValues] using
      incrementBits_length (state control) (wireValues register state)
  · exact hcorrect.1
  · exact hcorrect.2

private theorem run_controlledDecrement_eq_state
    (control : Wire) (register borrows : List Wire) (state : BasisState)
    (hlength : register.length = borrows.length + 1)
    (hnd : (control :: register ++ borrows).Nodup)
    (hclean : Clean borrows state) :
    run (controlledDecrement control register borrows) state =
      decrementWordState (state control) register state := by
  have hcorrect := controlledDecrement_correct control register borrows state
    hlength hnd hclean
  apply state_eq_writeWireValues register _ state _
  · exact (List.nodup_append.mp (List.nodup_cons.mp hnd).2).1
  · simpa [wireValues] using
      decrementBits_length (state control) (wireValues register state)
  · exact hcorrect.1
  · exact hcorrect.2

/-! ## Literal pre/post shift wrappers -/

/-- Physical roles shared by the source's pre- and post-shift blocks.  `phase1IsZero` is active in
the pre block and is one of the four reserved post-block scratch wires. -/
structure ShiftRegisters where
  phase1 : Wire
  phase2 : Wire
  work : List Wire
  lengthS : List Wire
  phase1IsZero : Wire
  both : Wire
  carries : List Wire
  reserved : List Wire
deriving Repr

/-- The complete source scratch register: `shift_width + 4` wires in the production layout. -/
def ShiftRegisters.scratch (registers : ShiftRegisters) : List Wire :=
  [registers.phase1IsZero, registers.both] ++
    registers.carries ++ registers.reserved

/-- Exact physical support used by either shift circuit.  The three reserved source wires are
allocated for the shared scratch layout but are deliberately absent from this list. -/
def ShiftRegisters.usedWires (registers : ShiftRegisters) : List Wire :=
  [registers.phase1, registers.phase1IsZero, registers.phase2, registers.both] ++
    registers.work ++ registers.lengthS ++ registers.carries

/-- A duplicate-free roster of every source-allocated physical role. -/
def ShiftRegisters.allWires (registers : ShiftRegisters) : List Wire :=
  [registers.phase1, registers.phase1IsZero, registers.phase2, registers.both] ++
    registers.work ++ registers.lengthS ++ registers.carries ++ registers.reserved

/-- Shared physical conditions for the literal source wrappers. -/
structure ShiftLayout (registers : ShiftRegisters) : Prop where
  carry_capacity : registers.lengthS.length = registers.carries.length + 1
  reserved_size : registers.reserved.length = 3
  physical : registers.allWires.Nodup

/-- Every source scratch wire starts clear. -/
def ShiftReady (registers : ShiftRegisters) (state : BasisState) : Prop :=
  Clean registers.scratch state

/-- Circuit-independent payload transition shared by both shift blocks. -/
def shiftPayloadState
    (firstEnabled secondEnabled : Bool)
    (work lengthS : List Wire) (both : Wire)
    (state : BasisState) : BasisState :=
  let left := rotateLeftWordState firstEnabled work state
  let increased := incrementWordState firstEnabled lengthS left
  let bothEnabled := firstEnabled && secondEnabled
  let marked := increased[both ↦ Bool.xor (increased both) bothEnabled]
  let right := if marked both then rotateRightTwoState work marked else marked
  let decreased := decrementWordState (right both) lengthS right
  let decreasedTwice := decrementWordState (decreased both) lengthS decreased
  decreasedTwice[both ↦
    Bool.xor (decreasedTwice both) bothEnabled]

private def shiftBody
    (firstControl phase2 : Wire) (work lengthS : List Wire)
    (both : Wire) (carries : List Wire) : Circuit :=
  controlledRotateLeftOne firstControl work ++
    controlledIncrement firstControl lengthS carries ++
    [.CCX firstControl phase2 both] ++
    controlledRotateRightTwo both work ++
    controlledDecrement both lengthS carries ++
    controlledDecrement both lengthS carries ++
    [.CCX firstControl phase2 both]

private theorem shiftBody_usesOnly
    (firstControl phase2 : Wire) (work lengthS : List Wire)
    (both : Wire) (carries : List Wire) :
    PaperCircuitUsesOnly
      (firstControl :: phase2 :: both :: work ++ lengthS ++ carries)
      (shiftBody firstControl phase2 work lengthS both carries) := by
  have hleft : PaperCircuitUsesOnly
      (firstControl :: phase2 :: both :: work ++ lengthS ++ carries)
      (controlledRotateLeftOne firstControl work) := by
    apply (controlledRotateLeftOne_usesOnly firstControl work).mono
    intro wire hwire
    simp only [List.mem_cons, List.mem_append] at hwire ⊢
    aesop
  have hincrement : PaperCircuitUsesOnly
      (firstControl :: phase2 :: both :: work ++ lengthS ++ carries)
      (controlledIncrement firstControl lengthS carries) := by
    apply (controlledIncrement_usesOnly firstControl lengthS carries).mono
    intro wire hwire
    simp only [List.mem_cons, List.mem_append] at hwire ⊢
    aesop
  have hmark :
      PaperCircuitUsesOnly
        (firstControl :: phase2 :: both :: work ++ lengthS ++ carries)
        ([.CCX firstControl phase2 both] : Circuit) := by
    simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
  have hright : PaperCircuitUsesOnly
      (firstControl :: phase2 :: both :: work ++ lengthS ++ carries)
      (controlledRotateRightTwo both work) := by
    apply (controlledRotateRightTwo_usesOnly both work).mono
    intro wire hwire
    simp only [List.mem_cons, List.mem_append] at hwire ⊢
    aesop
  have hdecrement : PaperCircuitUsesOnly
      (firstControl :: phase2 :: both :: work ++ lengthS ++ carries)
      (controlledDecrement both lengthS carries) := by
    apply (controlledDecrement_usesOnly both lengthS carries).mono
    intro wire hwire
    simp only [List.mem_cons, List.mem_append] at hwire ⊢
    aesop
  exact ((((((hleft.append hincrement).append hmark).append hright).append
    hdecrement).append hdecrement).append hmark)

/-- Literal `pre_shift_gate`: compute `phase1 = 0`, shift/increment under it, perform the optional
phase-two correction, and erase the negative-control flag. -/
def preShiftUnitary (registers : ShiftRegisters) : Circuit :=
  [.X registers.phase1, .CX registers.phase1 registers.phase1IsZero,
    .X registers.phase1] ++
    shiftBody registers.phase1IsZero registers.phase2 registers.work
      registers.lengthS registers.both registers.carries ++
    [.X registers.phase1, .CX registers.phase1 registers.phase1IsZero,
      .X registers.phase1]

/-- Literal `post_shift_gate`: the same payload block controlled directly by phase one. -/
def postShiftUnitary (registers : ShiftRegisters) : Circuit :=
  shiftBody registers.phase1 registers.phase2 registers.work
    registers.lengthS registers.both registers.carries

/-- Gate-independent complete pre-shift transition, including the temporary negative-control
flag. -/
def preShiftState (registers : ShiftRegisters) (state : BasisState) : BasisState :=
  let phase1IsZero := !state registers.phase1
  let marked := state[registers.phase1IsZero ↦
    Bool.xor (state registers.phase1IsZero) phase1IsZero]
  let shifted := shiftPayloadState (marked registers.phase1IsZero)
    (marked registers.phase2) registers.work registers.lengthS
    registers.both marked
  shifted[registers.phase1IsZero ↦
    Bool.xor (shifted registers.phase1IsZero) (!shifted registers.phase1)]

/-- Gate-independent complete post-shift transition. -/
def postShiftState (registers : ShiftRegisters) (state : BasisState) : BasisState :=
  shiftPayloadState (state registers.phase1) (state registers.phase2)
    registers.work registers.lengthS registers.both state

private theorem rotateLeftWordState_preservesOutside
    (enabled : Bool) (register : List Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    rotateLeftWordState enabled register state wire = state wire :=
  writeWireValues_preservesOutside register _ state hwire

private theorem incrementWordState_preservesOutside
    (enabled : Bool) (register : List Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    incrementWordState enabled register state wire = state wire :=
  writeWireValues_preservesOutside register _ state hwire

private theorem decrementWordState_preservesOutside
    (enabled : Bool) (register : List Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    decrementWordState enabled register state wire = state wire :=
  writeWireValues_preservesOutside register _ state hwire

private theorem rotateRightTwoState_preservesOutside
    (register : List Wire) (state : BasisState)
    {wire : Wire} (hwire : wire ∉ register) :
    rotateRightTwoState register state wire = state wire := by
  unfold rotateRightTwoState
  apply applyRightTwoCycles_preservesOutside
  by_cases hsize : register.length ≤ 2
  · simp [rightTwoCycles, hsize]
  · have hlarge : 2 < register.length := by omega
    have hperm := rightTwoCycles_flatten_perm register hlarge
    intro hmem
    exact hwire ((List.Perm.mem_iff hperm).mp hmem)

private theorem shiftPayloadState_preservesOutside
    (firstEnabled secondEnabled : Bool)
    (work lengthS : List Wire) (both : Wire) (state : BasisState)
    {wire : Wire}
    (hwork : wire ∉ work) (hlength : wire ∉ lengthS)
    (hboth : wire ≠ both) :
    shiftPayloadState firstEnabled secondEnabled work lengthS both state wire =
      state wire := by
  let left := rotateLeftWordState firstEnabled work state
  let increased := incrementWordState firstEnabled lengthS left
  let bothEnabled := firstEnabled && secondEnabled
  let marked := increased[both ↦ Bool.xor (increased both) bothEnabled]
  let right := if marked both then rotateRightTwoState work marked else marked
  let decreased := decrementWordState (right both) lengthS right
  let decreasedTwice := decrementWordState (decreased both) lengthS decreased
  have hleft : left wire = state wire :=
    rotateLeftWordState_preservesOutside _ _ _ hwork
  have hincreased : increased wire = left wire :=
    incrementWordState_preservesOutside _ _ _ hlength
  have hmarked : marked wire = increased wire := by
    simp [marked, upd, hboth]
  have hright : right wire = marked wire := by
    simp only [right]
    split
    · exact rotateRightTwoState_preservesOutside work marked hwork
    · rfl
  have hdecreased : decreased wire = right wire :=
    decrementWordState_preservesOutside _ _ _ hlength
  have hdecreasedTwice : decreasedTwice wire = decreased wire :=
    decrementWordState_preservesOutside _ _ _ hlength
  change decreasedTwice[both ↦
      Bool.xor (decreasedTwice both) bothEnabled] wire = state wire
  rw [upd_other _ _ _ hboth, hdecreasedTwice, hdecreased, hright,
    hmarked, hincreased, hleft]

private theorem shiftPayloadState_restoresBoth
    (firstEnabled secondEnabled : Bool)
    (work lengthS : List Wire) (both : Wire) (state : BasisState)
    (hwork : both ∉ work) (hlength : both ∉ lengthS) :
    shiftPayloadState firstEnabled secondEnabled work lengthS both state both =
      state both := by
  let left := rotateLeftWordState firstEnabled work state
  let increased := incrementWordState firstEnabled lengthS left
  let bothEnabled := firstEnabled && secondEnabled
  let marked := increased[both ↦ Bool.xor (increased both) bothEnabled]
  let right := if marked both then rotateRightTwoState work marked else marked
  let decreased := decrementWordState (right both) lengthS right
  let decreasedTwice := decrementWordState (decreased both) lengthS decreased
  have hleft : left both = state both :=
    rotateLeftWordState_preservesOutside _ _ _ hwork
  have hincreased : increased both = left both :=
    incrementWordState_preservesOutside _ _ _ hlength
  have hmarked : marked both = Bool.xor (state both) bothEnabled := by
    simp [marked, hincreased, hleft]
  have hright : right both = marked both := by
    simp only [right]
    split
    · exact rotateRightTwoState_preservesOutside work marked hwork
    · rfl
  have hdecreased : decreased both = right both :=
    decrementWordState_preservesOutside _ _ _ hlength
  have hdecreasedTwice : decreasedTwice both = decreased both :=
    decrementWordState_preservesOutside _ _ _ hlength
  change decreasedTwice[both ↦
      Bool.xor (decreasedTwice both) bothEnabled] both = state both
  rw [upd_same, hdecreasedTwice, hdecreased, hright, hmarked]
  cases state both <;> cases bothEnabled <;> rfl

private theorem shiftPayloadState_preservesClean
    (firstEnabled secondEnabled : Bool)
    (work lengthS scratch : List Wire) (both : Wire) (state : BasisState)
    (hwork : ∀ wire ∈ scratch, wire ∉ work)
    (hlength : ∀ wire ∈ scratch, wire ∉ lengthS)
    (hclean : Clean scratch state) :
    Clean scratch
      (shiftPayloadState firstEnabled secondEnabled work lengthS both state) := by
  intro wire hwire
  by_cases hboth : wire = both
  · subst wire
    rw [shiftPayloadState_restoresBoth firstEnabled secondEnabled work lengthS
      both state (hwork both hwire) (hlength both hwire)]
    exact hclean both hwire
  · rw [shiftPayloadState_preservesOutside firstEnabled secondEnabled work lengthS
      both state (hwork wire hwire) (hlength wire hwire) hboth]
    exact hclean wire hwire

private theorem ShiftLayout.preBodyNodup
    {registers : ShiftRegisters} (hlayout : ShiftLayout registers) :
    (registers.phase1IsZero :: registers.phase2 :: registers.both ::
      registers.work ++ registers.lengthS ++ registers.carries).Nodup := by
  apply List.Sublist.nodup ?_ hlayout.physical
  simp [ShiftRegisters.allWires]

private theorem ShiftLayout.postBodyNodup
    {registers : ShiftRegisters} (hlayout : ShiftLayout registers) :
    (registers.phase1 :: registers.phase2 :: registers.both ::
      registers.work ++ registers.lengthS ++ registers.carries).Nodup := by
  apply List.Sublist.nodup ?_ hlayout.physical
  simp [ShiftRegisters.allWires]

private theorem ShiftLayout.phaseFlagNodup
    {registers : ShiftRegisters} (hlayout : ShiftLayout registers) :
    [registers.phase1, registers.phase1IsZero].Nodup := by
  apply List.Sublist.nodup ?_ hlayout.physical
  simp [ShiftRegisters.allWires]

private theorem ShiftLayout.scratchWorkDisjoint
    {registers : ShiftRegisters} (hlayout : ShiftLayout registers) :
    ∀ wire ∈ registers.scratch, wire ∉ registers.work := by
  have hnormalized :
      ([registers.phase1, registers.phase1IsZero, registers.phase2,
          registers.both] ++
        (registers.work ++ (registers.lengthS ++
          (registers.carries ++ registers.reserved)))).Nodup := by
    simpa [ShiftRegisters.allWires, List.append_assoc] using hlayout.physical
  have hprefixSplit := List.nodup_append.mp hnormalized
  have hworkSplit := List.nodup_append.mp hprefixSplit.2.1
  intro wire hscratch hwork
  have hcases :
      wire = registers.phase1IsZero ∨ wire = registers.both ∨
        wire ∈ registers.carries ∨ wire ∈ registers.reserved := by
    simpa [ShiftRegisters.scratch, List.mem_append] using hscratch
  rcases hcases with hflag | hboth | hcarry | hreserved
  · have hprefix : wire ∈
        [registers.phase1, registers.phase1IsZero, registers.phase2,
          registers.both] := by simp [hflag]
    have htail : wire ∈ registers.work ++
        (registers.lengthS ++ (registers.carries ++ registers.reserved)) := by
      simp [hwork]
    exact (hprefixSplit.2.2 wire hprefix wire htail) rfl
  · have hprefix : wire ∈
        [registers.phase1, registers.phase1IsZero, registers.phase2,
          registers.both] := by simp [hboth]
    have htail : wire ∈ registers.work ++
        (registers.lengthS ++ (registers.carries ++ registers.reserved)) := by
      simp [hwork]
    exact (hprefixSplit.2.2 wire hprefix wire htail) rfl
  · have hrest : wire ∈ registers.lengthS ++
        (registers.carries ++ registers.reserved) := by simp [hcarry]
    exact (hworkSplit.2.2 wire hwork wire hrest) rfl
  · have hrest : wire ∈ registers.lengthS ++
        (registers.carries ++ registers.reserved) := by simp [hreserved]
    exact (hworkSplit.2.2 wire hwork wire hrest) rfl

private theorem ShiftLayout.scratchLengthDisjoint
    {registers : ShiftRegisters} (hlayout : ShiftLayout registers) :
    ∀ wire ∈ registers.scratch, wire ∉ registers.lengthS := by
  have hnormalized :
      ([registers.phase1, registers.phase1IsZero, registers.phase2,
          registers.both] ++
        (registers.work ++ (registers.lengthS ++
          (registers.carries ++ registers.reserved)))).Nodup := by
    simpa [ShiftRegisters.allWires, List.append_assoc] using hlayout.physical
  have hprefixSplit := List.nodup_append.mp hnormalized
  have hworkSplit := List.nodup_append.mp hprefixSplit.2.1
  have hlengthSplit := List.nodup_append.mp hworkSplit.2.1
  intro wire hscratch hlength
  have hcases :
      wire = registers.phase1IsZero ∨ wire = registers.both ∨
        wire ∈ registers.carries ∨ wire ∈ registers.reserved := by
    simpa [ShiftRegisters.scratch, List.mem_append] using hscratch
  rcases hcases with hflag | hboth | hcarry | hreserved
  · have hprefix : wire ∈
        [registers.phase1, registers.phase1IsZero, registers.phase2,
          registers.both] := by simp [hflag]
    have htail : wire ∈ registers.work ++
        (registers.lengthS ++ (registers.carries ++ registers.reserved)) := by
      simp [hlength]
    exact (hprefixSplit.2.2 wire hprefix wire htail) rfl
  · have hprefix : wire ∈
        [registers.phase1, registers.phase1IsZero, registers.phase2,
          registers.both] := by simp [hboth]
    have htail : wire ∈ registers.work ++
        (registers.lengthS ++ (registers.carries ++ registers.reserved)) := by
      simp [hlength]
    exact (hprefixSplit.2.2 wire hprefix wire htail) rfl
  · have hrest : wire ∈ registers.carries ++ registers.reserved := by
      simp [hcarry]
    exact (hlengthSplit.2.2 wire hlength wire hrest) rfl
  · have hrest : wire ∈ registers.carries ++ registers.reserved := by
      simp [hreserved]
    exact (hlengthSplit.2.2 wire hlength wire hrest) rfl

private theorem run_negativeControlFlag
    (source flag : Wire) (state : BasisState) (hne : source ≠ flag) :
    run [.X source, .CX source flag, .X source] state =
      state[flag ↦ Bool.xor (state flag) (!state source)] := by
  funext wire
  by_cases hws : wire = source
  · subst wire
    simp [run, applyGate, upd, hne, Ne.symm hne]
  · by_cases hwf : wire = flag
    · subst wire
      cases hs : state source <;> cases hf : state flag <;>
        simp [run, applyGate, upd, hne, Ne.symm hne, hs, hf]
    · simp [run, applyGate, upd, hws, hwf]

private theorem shiftBody_componentNodup
    (firstControl phase2 : Wire) (work lengthS : List Wire)
    (both : Wire) (carries : List Wire)
    (hnd : (firstControl :: phase2 :: both ::
      work ++ lengthS ++ carries).Nodup) :
    (firstControl :: work).Nodup ∧
      (firstControl :: lengthS ++ carries).Nodup ∧
      [firstControl, phase2, both].Nodup ∧
      (both :: work).Nodup ∧
      (both :: lengthS ++ carries).Nodup := by
  have hfirstRest : firstControl ∉ phase2 :: both :: work ++ lengthS ++ carries :=
    (List.nodup_cons.mp hnd).1
  have hnd1 : (phase2 :: both :: work ++ lengthS ++ carries).Nodup :=
    (List.nodup_cons.mp hnd).2
  have hphase2Rest : phase2 ∉ both :: work ++ lengthS ++ carries :=
    (List.nodup_cons.mp hnd1).1
  have hnd2 : (both :: work ++ lengthS ++ carries).Nodup :=
    (List.nodup_cons.mp hnd1).2
  have hbothRest : both ∉ work ++ lengthS ++ carries :=
    (List.nodup_cons.mp hnd2).1
  have htailNodup : (work ++ (lengthS ++ carries)).Nodup := by
    simpa [List.append_assoc] using (List.nodup_cons.mp hnd2).2
  have hworkSplit := List.nodup_append.mp htailNodup
  have hfirstWork : firstControl ∉ work := by
    intro hwire
    exact hfirstRest (by simp [hwire])
  have hbothWork : both ∉ work := by
    intro hwire
    exact hbothRest (by simp [hwire])
  have hfirstTail : firstControl ∉ lengthS ++ carries := by
    intro hwire
    rcases List.mem_append.mp hwire with hwire | hwire
    · exact hfirstRest (by simp [hwire])
    · exact hfirstRest (by simp [hwire])
  have hbothTail : both ∉ lengthS ++ carries := by
    intro hwire
    rcases List.mem_append.mp hwire with hwire | hwire
    · exact hbothRest (by simp [hwire])
    · exact hbothRest (by simp [hwire])
  have hfirstPhase2 : firstControl ≠ phase2 := by
    intro equality
    exact hfirstRest (by simp [equality])
  have hfirstBoth : firstControl ≠ both := by
    intro equality
    exact hfirstRest (by simp [equality])
  have hphase2Both : phase2 ≠ both := by
    intro equality
    exact hphase2Rest (by simp [equality])
  exact ⟨List.nodup_cons.mpr ⟨hfirstWork, hworkSplit.1⟩,
    List.nodup_cons.mpr ⟨hfirstTail, hworkSplit.2.1⟩,
    by simp [List.nodup_cons, hfirstPhase2, hfirstBoth, hphase2Both],
    List.nodup_cons.mpr ⟨hbothWork, hworkSplit.1⟩,
    List.nodup_cons.mpr ⟨hbothTail, hworkSplit.2.1⟩⟩

private theorem run_shiftBody
    (firstControl phase2 : Wire) (work lengthS : List Wire)
    (both : Wire) (carries : List Wire) (state : BasisState)
    (hlength : lengthS.length = carries.length + 1)
    (hnd : (firstControl :: phase2 :: both ::
      work ++ lengthS ++ carries).Nodup)
    (hclean : Clean (both :: carries) state) :
    run (shiftBody firstControl phase2 work lengthS both carries) state =
      shiftPayloadState (state firstControl) (state phase2)
        work lengthS both state := by
  have hfirstRest : firstControl ∉ phase2 :: both :: work ++ lengthS ++ carries :=
    (List.nodup_cons.mp hnd).1
  have hnd1 : (phase2 :: both :: work ++ lengthS ++ carries).Nodup :=
    (List.nodup_cons.mp hnd).2
  have hphase2Rest : phase2 ∉ both :: work ++ lengthS ++ carries :=
    (List.nodup_cons.mp hnd1).1
  have hnd2 : (both :: work ++ lengthS ++ carries).Nodup :=
    (List.nodup_cons.mp hnd1).2
  have hbothRest : both ∉ work ++ lengthS ++ carries :=
    (List.nodup_cons.mp hnd2).1
  have htailNodup : (work ++ (lengthS ++ carries)).Nodup := by
    simpa [List.append_assoc] using (List.nodup_cons.mp hnd2).2
  have hworkSplit := List.nodup_append.mp htailNodup
  have hlengthSplit := List.nodup_append.mp hworkSplit.2.1
  have hfirstWork : firstControl ∉ work := by
    intro hwire
    exact hfirstRest (by simp [hwire])
  have hfirstLength : firstControl ∉ lengthS := by
    intro hwire
    exact hfirstRest (by simp [hwire])
  have hphase2Work : phase2 ∉ work := by
    intro hwire
    exact hphase2Rest (by simp [hwire])
  have hphase2Length : phase2 ∉ lengthS := by
    intro hwire
    exact hphase2Rest (by simp [hwire])
  have hbothWork : both ∉ work := by
    intro hwire
    exact hbothRest (by simp [hwire])
  have hbothLength : both ∉ lengthS := by
    intro hwire
    exact hbothRest (by simp [hwire])
  have hcarryWork : ∀ wire ∈ carries, wire ∉ work := by
    intro wire hcarry hwire
    exact (hworkSplit.2.2 wire hwire wire
      (List.mem_append_right lengthS hcarry)) rfl
  have hcarryLength : ∀ wire ∈ carries, wire ∉ lengthS := by
    intro wire hcarry hwire
    exact (hlengthSplit.2.2 wire hwire wire hcarry) rfl
  have hcarryBoth : ∀ wire ∈ carries, wire ≠ both := by
    intro wire hcarry equality
    subst wire
    exact hbothRest (by simp [hcarry])
  have hfirstBoth : firstControl ≠ both := by
    intro equality
    exact hfirstRest (by simp [equality])
  have hphase2Both : phase2 ≠ both := by
    intro equality
    exact hphase2Rest (by simp [equality])
  obtain ⟨hrotate, hincrement, hmark, hrightRotate, hdecrement⟩ :=
    shiftBody_componentNodup firstControl phase2 work lengthS both carries hnd
  have hcleanCarries : Clean carries state := by
    intro wire hwire
    exact hclean wire (by simp [hwire])
  have hbothFalse : state both = false := hclean both (by simp)

  let left := rotateLeftWordState (state firstControl) work state
  have hrunLeft :
      run (controlledRotateLeftOne firstControl work) state = left :=
    run_controlledRotateLeftOne_eq_state firstControl work state hrotate
  have hleftFirst : left firstControl = state firstControl := by
    simpa only [left] using
      rotateLeftWordState_preservesOutside (state firstControl) work state hfirstWork
  have hleftPhase2 : left phase2 = state phase2 := by
    simpa only [left] using
      rotateLeftWordState_preservesOutside (state firstControl) work state hphase2Work
  have hleftBoth : left both = state both := by
    simpa only [left] using
      rotateLeftWordState_preservesOutside (state firstControl) work state hbothWork
  have hcleanLeft : Clean carries left := by
    intro wire hwire
    have hleftWire : left wire = state wire := by
      simpa only [left] using
        rotateLeftWordState_preservesOutside (state firstControl) work state
          (hcarryWork wire hwire)
    rw [hleftWire]
    exact hcleanCarries wire hwire

  let increased := incrementWordState (state firstControl) lengthS left
  have hrunIncreased :
      run (controlledIncrement firstControl lengthS carries) left = increased := by
    simpa only [increased, hleftFirst] using
      run_controlledIncrement_eq_state firstControl lengthS carries left
        hlength hincrement hcleanLeft
  have hincreasedFirst : increased firstControl = state firstControl := by
    simpa only [increased, hleftFirst] using
      incrementWordState_preservesOutside (state firstControl) lengthS left hfirstLength
  have hincreasedPhase2 : increased phase2 = state phase2 := by
    simpa only [increased, hleftPhase2] using
      incrementWordState_preservesOutside (state firstControl) lengthS left hphase2Length
  have hincreasedBoth : increased both = false := by
    simpa only [increased, hleftBoth, hbothFalse] using
      incrementWordState_preservesOutside (state firstControl) lengthS left hbothLength
  have hcleanIncreased : Clean carries increased := by
    intro wire hwire
    have hincreasedWire : increased wire = left wire := by
      simpa only [increased] using
        incrementWordState_preservesOutside (state firstControl) lengthS left
          (hcarryLength wire hwire)
    rw [hincreasedWire]
    exact hcleanLeft wire hwire

  let bothEnabled := state firstControl && state phase2
  let marked := increased[both ↦ Bool.xor (increased both) bothEnabled]
  have hrunMarked : run [.CCX firstControl phase2 both] increased = marked := by
    simp [run, applyGate, marked, bothEnabled, hincreasedFirst,
      hincreasedPhase2]
  have hmarkedBoth : marked both = bothEnabled := by
    simp [marked, hincreasedBoth]
  have hmarkedFirst : marked firstControl = state firstControl := by
    simp [marked, upd, hfirstBoth, hincreasedFirst]
  have hmarkedPhase2 : marked phase2 = state phase2 := by
    simp [marked, upd, hphase2Both, hincreasedPhase2]
  have hcleanMarked : Clean carries marked := by
    intro wire hwire
    have hmarkedWire : marked wire = increased wire := by
      simp [marked, upd, hcarryBoth wire hwire]
    rw [hmarkedWire]
    exact hcleanIncreased wire hwire

  let right := if marked both then rotateRightTwoState work marked else marked
  have hrunRight :
      run (controlledRotateRightTwo both work) marked = right := by
    simpa [right] using
      run_controlledRotateRightTwo both work marked hrightRotate
  have hrightBoth : right both = marked both := by
    simp only [right]
    split
    · exact rotateRightTwoState_preservesOutside work marked hbothWork
    · rfl
  have hrightFirst : right firstControl = state firstControl := by
    simp only [right]
    split
    · rw [rotateRightTwoState_preservesOutside work marked hfirstWork,
        hmarkedFirst]
    · exact hmarkedFirst
  have hrightPhase2 : right phase2 = state phase2 := by
    simp only [right]
    split
    · rw [rotateRightTwoState_preservesOutside work marked hphase2Work,
        hmarkedPhase2]
    · exact hmarkedPhase2
  have hcleanRight : Clean carries right := by
    intro wire hwire
    simp only [right]
    split
    · rw [rotateRightTwoState_preservesOutside work marked
        (hcarryWork wire hwire)]
      exact hcleanMarked wire hwire
    · exact hcleanMarked wire hwire

  let decreased := decrementWordState (right both) lengthS right
  have hrunDecreased :
      run (controlledDecrement both lengthS carries) right = decreased :=
    by
      simpa only [decreased] using
        run_controlledDecrement_eq_state both lengthS carries right hlength
          hdecrement hcleanRight
  have hdecreasedBoth : decreased both = right both := by
    simpa only [decreased] using
      decrementWordState_preservesOutside (right both) lengthS right hbothLength
  have hdecreasedFirst : decreased firstControl = state firstControl := by
    simpa only [decreased, hrightFirst] using
      decrementWordState_preservesOutside (right both) lengthS right hfirstLength
  have hdecreasedPhase2 : decreased phase2 = state phase2 := by
    simpa only [decreased, hrightPhase2] using
      decrementWordState_preservesOutside (right both) lengthS right hphase2Length
  have hcleanDecreased : Clean carries decreased := by
    intro wire hwire
    have hdecreasedWire : decreased wire = right wire := by
      simpa only [decreased] using
        decrementWordState_preservesOutside (right both) lengthS right
          (hcarryLength wire hwire)
    rw [hdecreasedWire]
    exact hcleanRight wire hwire

  let decreasedTwice := decrementWordState (decreased both) lengthS decreased
  have hrunDecreasedTwice :
      run (controlledDecrement both lengthS carries) decreased =
        decreasedTwice := by
    simpa only [decreasedTwice, hdecreasedBoth] using
      run_controlledDecrement_eq_state both lengthS carries decreased hlength
        hdecrement hcleanDecreased
  have hdecreasedTwiceFirst :
      decreasedTwice firstControl = state firstControl := by
    simpa only [decreasedTwice, hdecreasedFirst] using
      decrementWordState_preservesOutside (decreased both) lengthS decreased hfirstLength
  have hdecreasedTwicePhase2 :
      decreasedTwice phase2 = state phase2 := by
    simpa only [decreasedTwice, hdecreasedPhase2] using
      decrementWordState_preservesOutside (decreased both) lengthS decreased hphase2Length

  rw [shiftBody]
  simp only [run_append]
  rw [hrunLeft, hrunIncreased, hrunMarked, hrunRight,
    hrunDecreased, hrunDecreasedTwice]
  change
    run [.CCX firstControl phase2 both] decreasedTwice =
      decreasedTwice[both ↦
        Bool.xor (decreasedTwice both) bothEnabled]
  simp [run, applyGate, hdecreasedTwiceFirst,
    hdecreasedTwicePhase2, bothEnabled]

/-- Direct whole-state semantics of the literal pre-shift wrapper. -/
theorem run_preShiftUnitary
    (registers : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout registers) (hready : ShiftReady registers state) :
    run (preShiftUnitary registers) state = preShiftState registers state := by
  have hphaseFlag := hlayout.phaseFlagNodup
  have hphaseFlagNe : registers.phase1 ≠ registers.phase1IsZero := by
    intro equality
    exact (List.nodup_cons.mp hphaseFlag).1 (by simp [equality])
  let marked := state[registers.phase1IsZero ↦
    Bool.xor (state registers.phase1IsZero) (!state registers.phase1)]
  have hrunMarked :
      run [.X registers.phase1,
          .CX registers.phase1 registers.phase1IsZero,
          .X registers.phase1] state = marked := by
    simpa only [marked] using
      run_negativeControlFlag registers.phase1 registers.phase1IsZero state
        hphaseFlagNe
  have hflagBody :
      registers.phase1IsZero ∉ registers.both :: registers.carries := by
    have hrest := (List.nodup_cons.mp hlayout.preBodyNodup).1
    intro hmem
    rcases List.mem_cons.mp hmem with equality | hcarry
    · exact hrest (by simp [equality])
    · exact hrest (by simp [hcarry])
  have hcleanBody : Clean (registers.both :: registers.carries) marked := by
    intro wire hwire
    have hwireFlag : wire ≠ registers.phase1IsZero := by
      intro equality
      subst wire
      exact hflagBody hwire
    rw [show marked wire = state wire by
      simp [marked, upd, hwireFlag]]
    apply hready wire
    rcases List.mem_cons.mp hwire with equality | hcarry
    · subst wire
      simp [ShiftRegisters.scratch]
    · simp [ShiftRegisters.scratch, hcarry]
  let shifted := shiftPayloadState (marked registers.phase1IsZero)
    (marked registers.phase2) registers.work registers.lengthS
    registers.both marked
  have hrunShifted :
      run (shiftBody registers.phase1IsZero registers.phase2 registers.work
          registers.lengthS registers.both registers.carries) marked = shifted := by
    simpa only [shifted] using
      run_shiftBody registers.phase1IsZero registers.phase2 registers.work
        registers.lengthS registers.both registers.carries marked
        hlayout.carry_capacity hlayout.preBodyNodup hcleanBody
  have hrunCleared :
      run [.X registers.phase1,
          .CX registers.phase1 registers.phase1IsZero,
          .X registers.phase1] shifted =
        shifted[registers.phase1IsZero ↦
          Bool.xor (shifted registers.phase1IsZero)
            (!shifted registers.phase1)] :=
    run_negativeControlFlag registers.phase1 registers.phase1IsZero shifted
      hphaseFlagNe
  rw [preShiftUnitary, run_append, run_append, hrunMarked, hrunShifted,
    hrunCleared]
  rfl

/-- Direct whole-state semantics of the literal post-shift wrapper. -/
theorem run_postShiftUnitary
    (registers : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout registers) (hready : ShiftReady registers state) :
    run (postShiftUnitary registers) state = postShiftState registers state := by
  have hcleanBody : Clean (registers.both :: registers.carries) state := by
    intro wire hwire
    apply hready wire
    rcases List.mem_cons.mp hwire with equality | hcarry
    · subst wire
      simp [ShiftRegisters.scratch]
    · simp [ShiftRegisters.scratch, hcarry]
  simpa only [postShiftUnitary, postShiftState] using
    run_shiftBody registers.phase1 registers.phase2 registers.work
      registers.lengthS registers.both registers.carries state
      hlayout.carry_capacity hlayout.postBodyNodup hcleanBody

/-- The pre-shift circuit uses exactly the declared non-reserved support. -/
theorem preShiftUnitary_usesOnly (registers : ShiftRegisters) :
    PaperCircuitUsesOnly registers.usedWires (preShiftUnitary registers) := by
  have hflag : PaperCircuitUsesOnly registers.usedWires
      ([.X registers.phase1,
        .CX registers.phase1 registers.phase1IsZero,
        .X registers.phase1] : Circuit) := by
    simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires,
      ShiftRegisters.usedWires]
  have hbody : PaperCircuitUsesOnly registers.usedWires
      (shiftBody registers.phase1IsZero registers.phase2 registers.work
        registers.lengthS registers.both registers.carries) := by
    apply
      (shiftBody_usesOnly registers.phase1IsZero registers.phase2 registers.work
        registers.lengthS registers.both registers.carries).mono
    intro wire hwire
    simp only [ShiftRegisters.usedWires, List.mem_cons, List.mem_append]
      at hwire ⊢
    aesop
  simpa only [preShiftUnitary] using (hflag.append hbody).append hflag

/-- The post-shift circuit uses only the declared non-reserved support. -/
theorem postShiftUnitary_usesOnly (registers : ShiftRegisters) :
    PaperCircuitUsesOnly registers.usedWires (postShiftUnitary registers) := by
  simpa only [postShiftUnitary] using
    (shiftBody_usesOnly registers.phase1 registers.phase2 registers.work
      registers.lengthS registers.both registers.carries).mono (by
        intro wire hwire
        simp only [ShiftRegisters.usedWires, List.mem_cons, List.mem_append]
          at hwire ⊢
        aesop)

/-- Pre-shift leaves every wire outside its exact support unchanged. -/
theorem preShiftUnitary_preservesOutside
    (registers : ShiftRegisters) (state : BasisState) {wire : Wire}
    (hwire : wire ∉ registers.usedWires) :
    run (preShiftUnitary registers) state wire = state wire :=
  (preShiftUnitary_usesOnly registers).preservesOutside state hwire

/-- Post-shift leaves every wire outside its exact support unchanged. -/
theorem postShiftUnitary_preservesOutside
    (registers : ShiftRegisters) (state : BasisState) {wire : Wire}
    (hwire : wire ∉ registers.usedWires) :
    run (postShiftUnitary registers) state wire = state wire :=
  (postShiftUnitary_usesOnly registers).preservesOutside state hwire

/-- The literal pre-shift wrapper is H/P-free. -/
@[simp]
theorem preShiftUnitary_HPFree (registers : ShiftRegisters) :
    HPFree (preShiftUnitary registers) := by
  simp [preShiftUnitary, shiftBody]

/-- The literal post-shift wrapper is H/P-free. -/
@[simp]
theorem postShiftUnitary_HPFree (registers : ShiftRegisters) :
    HPFree (postShiftUnitary registers) := by
  simp [postShiftUnitary, shiftBody]

private theorem shiftBody_wellFormed
    (firstControl phase2 : Wire) (work lengthS : List Wire)
    (both : Wire) (carries : List Wire)
    (hnd : (firstControl :: phase2 :: both ::
      work ++ lengthS ++ carries).Nodup) :
    CircuitWellFormed
      (shiftBody firstControl phase2 work lengthS both carries) := by
  obtain ⟨hrotate, hincrement, hmark, hright, hdecrement⟩ :=
    shiftBody_componentNodup firstControl phase2 work lengthS both carries hnd
  have hfirstRest : firstControl ∉ [phase2, both] :=
    (List.nodup_cons.mp hmark).1
  have hphase2Rest : phase2 ∉ [both] :=
    (List.nodup_cons.mp (List.nodup_cons.mp hmark).2).1
  have hfirstPhase2 : firstControl ≠ phase2 := by
    intro equality
    exact hfirstRest (by simp [equality])
  have hfirstBoth : firstControl ≠ both := by
    intro equality
    exact hfirstRest (by simp [equality])
  have hphase2Both : phase2 ≠ both := by
    intro equality
    exact hphase2Rest (by simp [equality])
  have hmarkWellFormed :
      CircuitWellFormed ([.CCX firstControl phase2 both] : Circuit) := by
    simp [CircuitWellFormed, Gate.WellFormed, hfirstPhase2, hfirstBoth,
      hphase2Both]
  have hleftWellFormed :=
    controlledRotateLeftOne_wellFormed firstControl work hrotate
  have hincrementWellFormed :=
    controlledIncrement_wellFormed firstControl lengthS carries hincrement
  have hrightWellFormed :=
    controlledRotateRightTwo_wellFormed both work hright
  have hdecrementWellFormed :=
    controlledDecrement_wellFormed both lengthS carries hdecrement
  simp only [shiftBody, circuitWellFormed_append]
  aesop

/-- Physical well-formedness of the complete pre-shift wrapper. -/
theorem preShiftUnitary_wellFormed
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers) :
    CircuitWellFormed (preShiftUnitary registers) := by
  have hphaseFlag := hlayout.phaseFlagNodup
  have hphaseFlagNe : registers.phase1 ≠ registers.phase1IsZero := by
    intro equality
    exact (List.nodup_cons.mp hphaseFlag).1 (by simp [equality])
  have hflagWellFormed : CircuitWellFormed
      ([.X registers.phase1,
        .CX registers.phase1 registers.phase1IsZero,
        .X registers.phase1] : Circuit) := by
    simp [CircuitWellFormed, Gate.WellFormed, hphaseFlagNe]
  have hbodyWellFormed :=
    shiftBody_wellFormed registers.phase1IsZero registers.phase2 registers.work
      registers.lengthS registers.both registers.carries hlayout.preBodyNodup
  simp only [preShiftUnitary, circuitWellFormed_append]
  aesop

/-- Physical well-formedness of the complete post-shift wrapper. -/
theorem postShiftUnitary_wellFormed
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers) :
    CircuitWellFormed (postShiftUnitary registers) := by
  exact shiftBody_wellFormed registers.phase1 registers.phase2 registers.work
    registers.lengthS registers.both registers.carries hlayout.postBodyNodup

/-- Post-shift restores the complete shared scratch allocation, including the three reserved
source wires which it never touches. -/
theorem postShiftUnitary_ready
    (registers : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout registers) (hready : ShiftReady registers state) :
    ShiftReady registers (run (postShiftUnitary registers) state) := by
  rw [run_postShiftUnitary registers state hlayout hready]
  exact shiftPayloadState_preservesClean (state registers.phase1)
    (state registers.phase2) registers.work registers.lengthS registers.scratch
    registers.both state hlayout.scratchWorkDisjoint
    hlayout.scratchLengthDisjoint hready

/-- Pre-shift erases its temporary negative-control flag and restores every shared scratch wire. -/
theorem preShiftUnitary_ready
    (registers : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout registers) (hready : ShiftReady registers state) :
    ShiftReady registers (run (preShiftUnitary registers) state) := by
  have hflagMem : registers.phase1IsZero ∈ registers.scratch := by
    simp [ShiftRegisters.scratch]
  have hflagFalse : state registers.phase1IsZero = false :=
    hready registers.phase1IsZero hflagMem
  have hphaseFlag := hlayout.phaseFlagNodup
  have hphaseFlagNe : registers.phase1 ≠ registers.phase1IsZero := by
    intro equality
    exact (List.nodup_cons.mp hphaseFlag).1 (by simp [equality])
  have hflagBoth : registers.phase1IsZero ≠ registers.both := by
    have hrest := (List.nodup_cons.mp hlayout.preBodyNodup).1
    intro equality
    exact hrest (by simp [equality])
  have hphase1Rest := (List.nodup_cons.mp hlayout.postBodyNodup).1
  have hphase1Work : registers.phase1 ∉ registers.work := by
    intro hwire
    exact hphase1Rest (by simp [hwire])
  have hphase1Length : registers.phase1 ∉ registers.lengthS := by
    intro hwire
    exact hphase1Rest (by simp [hwire])
  have hphase1Both : registers.phase1 ≠ registers.both := by
    intro equality
    exact hphase1Rest (by simp [equality])
  have hflagWork : registers.phase1IsZero ∉ registers.work :=
    hlayout.scratchWorkDisjoint registers.phase1IsZero hflagMem
  have hflagLength : registers.phase1IsZero ∉ registers.lengthS :=
    hlayout.scratchLengthDisjoint registers.phase1IsZero hflagMem
  let marked := state[registers.phase1IsZero ↦
    Bool.xor (state registers.phase1IsZero) (!state registers.phase1)]
  let shifted := shiftPayloadState (marked registers.phase1IsZero)
    (marked registers.phase2) registers.work registers.lengthS
    registers.both marked
  have hshiftedFlag :
      shifted registers.phase1IsZero = !state registers.phase1 := by
    calc
      shifted registers.phase1IsZero = marked registers.phase1IsZero := by
        simpa only [shifted] using
          shiftPayloadState_preservesOutside (marked registers.phase1IsZero)
            (marked registers.phase2) registers.work registers.lengthS
            registers.both marked hflagWork hflagLength hflagBoth
      _ = !state registers.phase1 := by simp [marked, hflagFalse]
  have hshiftedPhase1 : shifted registers.phase1 = state registers.phase1 := by
    calc
      shifted registers.phase1 = marked registers.phase1 := by
        simpa only [shifted] using
          shiftPayloadState_preservesOutside (marked registers.phase1IsZero)
            (marked registers.phase2) registers.work registers.lengthS
            registers.both marked hphase1Work hphase1Length hphase1Both
      _ = state registers.phase1 := by
        simp [marked, upd, hphaseFlagNe]
  rw [run_preShiftUnitary registers state hlayout hready]
  intro wire hwire
  change shifted[registers.phase1IsZero ↦
      Bool.xor (shifted registers.phase1IsZero)
        (!shifted registers.phase1)] wire = false
  by_cases hwireFlag : wire = registers.phase1IsZero
  · subst wire
    rw [upd_same, hshiftedFlag, hshiftedPhase1]
    cases state registers.phase1 <;> rfl
  · rw [upd_other _ _ _ hwireFlag]
    by_cases hwireBoth : wire = registers.both
    · subst wire
      rw [show shifted registers.both = marked registers.both by
        simpa only [shifted] using
          shiftPayloadState_restoresBoth (marked registers.phase1IsZero)
            (marked registers.phase2) registers.work registers.lengthS
            registers.both marked
            (hlayout.scratchWorkDisjoint registers.both hwire)
            (hlayout.scratchLengthDisjoint registers.both hwire)]
      rw [show marked registers.both = state registers.both by
        simp [marked, upd, Ne.symm hflagBoth]]
      exact hready registers.both hwire
    · rw [show shifted wire = marked wire by
        simpa only [shifted] using
          shiftPayloadState_preservesOutside (marked registers.phase1IsZero)
            (marked registers.phase2) registers.work registers.lengthS
            registers.both marked
            (hlayout.scratchWorkDisjoint wire hwire)
            (hlayout.scratchLengthDisjoint wire hwire) hwireBoth]
      rw [show marked wire = state wire by
        simp [marked, upd, hwireFlag]]
      exact hready wire hwire

private theorem run_run_adjoint_shift
    (circuit : Circuit) (hwellFormed : CircuitWellFormed circuit)
    (state : BasisState) :
    run circuit (run circuit.adjoint state) = state := by
  have hadjoint : CircuitWellFormed circuit.adjoint := by
    simpa using hwellFormed
  have hinverse := run_adjoint_run_classical circuit.adjoint hadjoint state
  simpa using hinverse

/-- The explicit adjoint of pre-shift cancels pre-shift on every basis state. -/
theorem run_preShiftUnitary_adjoint_after
    (registers : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout registers) :
    run (preShiftUnitary registers).adjoint
        (run (preShiftUnitary registers) state) = state :=
  run_adjoint_run_classical (preShiftUnitary registers)
    (preShiftUnitary_wellFormed registers hlayout) state

/-- Pre-shift cancels its explicit adjoint on every basis state. -/
theorem run_preShiftUnitary_after_adjoint
    (registers : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout registers) :
    run (preShiftUnitary registers)
        (run (preShiftUnitary registers).adjoint state) = state :=
  run_run_adjoint_shift (preShiftUnitary registers)
    (preShiftUnitary_wellFormed registers hlayout) state

/-- The explicit adjoint of post-shift cancels post-shift on every basis state. -/
theorem run_postShiftUnitary_adjoint_after
    (registers : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout registers) :
    run (postShiftUnitary registers).adjoint
        (run (postShiftUnitary registers) state) = state :=
  run_adjoint_run_classical (postShiftUnitary registers)
    (postShiftUnitary_wellFormed registers hlayout) state

/-- Post-shift cancels its explicit adjoint on every basis state. -/
theorem run_postShiftUnitary_after_adjoint
    (registers : ShiftRegisters) (state : BasisState)
    (hlayout : ShiftLayout registers) :
    run (postShiftUnitary registers)
        (run (postShiftUnitary registers).adjoint state) = state :=
  run_run_adjoint_shift (postShiftUnitary registers)
    (postShiftUnitary_wellFormed registers hlayout) state

private theorem controlledIncrement_cnotCount_of_two_le
    (control : Wire) (register carries : List Wire)
    (hlength : register.length = carries.length + 1)
    (hwidth : 2 ≤ register.length) :
    eeaCnotCount (controlledIncrement control register carries) =
      register.length + 2 := by
  cases register with
  | nil => simp at hwidth
  | cons low tail =>
      cases tail with
      | nil => simp at hwidth
      | cons next rest =>
          exact controlledIncrement_cnotCount control low next rest carries hlength

private theorem controlledDecrement_cnotCount_of_two_le
    (control : Wire) (register borrows : List Wire)
    (hlength : register.length = borrows.length + 1)
    (hwidth : 2 ≤ register.length) :
    eeaCnotCount (controlledDecrement control register borrows) =
      register.length + 2 := by
  cases register with
  | nil => simp at hwidth
  | cons low tail =>
      cases tail with
      | nil => simp at hwidth
      | cons next rest =>
          exact controlledDecrement_cnotCount control low next rest borrows hlength

private theorem shiftBody_toffoliCount
    (firstControl phase2 : Wire) (work lengthS : List Wire)
    (both : Wire) (carries : List Wire)
    (hlength : lengthS.length = carries.length + 1) :
    eeaToffoliCount (shiftBody firstControl phase2 work lengthS both carries) =
      (work.length - 1) + 6 * (lengthS.length - 1) +
        rightTwoSwapCount work + 2 := by
  simp only [shiftBody, eeaToffoliCount_append]
  rw [controlledRotateLeftOne_toffoliCount,
    controlledIncrement_toffoliCount _ _ _ hlength,
    controlledRotateRightTwo_toffoliCount,
    controlledDecrement_toffoliCount _ _ _ hlength]
  simp [eeaToffoliCount]
  omega

private theorem shiftBody_cnotCount
    (firstControl phase2 : Wire) (work lengthS : List Wire)
    (both : Wire) (carries : List Wire)
    (hlength : lengthS.length = carries.length + 1)
    (hwidth : 2 ≤ lengthS.length) :
    eeaCnotCount (shiftBody firstControl phase2 work lengthS both carries) =
      2 * (work.length - 1) + 3 * (lengthS.length + 2) +
        2 * rightTwoSwapCount work := by
  simp only [shiftBody, eeaCnotCount_append]
  rw [controlledRotateLeftOne_cnotCount,
    controlledIncrement_cnotCount_of_two_le _ _ _ hlength hwidth,
    controlledRotateRightTwo_cnotCount,
    controlledDecrement_cnotCount_of_two_le _ _ _ hlength hwidth]
  simp [eeaCnotCount]
  omega

private theorem shiftBody_xCount
    (firstControl phase2 : Wire) (work lengthS : List Wire)
    (both : Wire) (carries : List Wire)
    (hlength : lengthS.length = carries.length + 1) :
    eeaXCount (shiftBody firstControl phase2 work lengthS both carries) =
      8 * (lengthS.length - 1) := by
  simp only [shiftBody, eeaXCount_append]
  rw [controlledRotateLeftOne_xCount, controlledIncrement_xCount,
    controlledRotateRightTwo_xCount,
    controlledDecrement_xCount _ _ _ hlength]
  simp [eeaXCount]
  omega

private theorem shiftBody_tCount
    (firstControl phase2 : Wire) (work lengthS : List Wire)
    (both : Wire) (carries : List Wire)
    (hlength : lengthS.length = carries.length + 1) :
    tCount (shiftBody firstControl phase2 work lengthS both carries) =
      7 * (work.length - 1) + 42 * (lengthS.length - 1) +
        7 * rightTwoSwapCount work + 14 := by
  simp only [shiftBody, tCount_append]
  rw [controlledRotateLeftOne_tCount,
    controlledIncrement_tCount _ _ _ hlength,
    controlledRotateRightTwo_tCount,
    controlledDecrement_tCount _ _ _ hlength]
  simp [tCount, tCost]
  omega

/-- Exact constructor-derived Toffoli formula for pre-shift. -/
theorem preShiftUnitary_toffoliCount
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers) :
    eeaToffoliCount (preShiftUnitary registers) =
      (registers.work.length - 1) + 6 * (registers.lengthS.length - 1) +
        rightTwoSwapCount registers.work + 2 := by
  simp only [preShiftUnitary, eeaToffoliCount_append]
  rw [shiftBody_toffoliCount _ _ _ _ _ _ hlayout.carry_capacity]
  simp [eeaToffoliCount]

/-- Exact constructor-derived Toffoli formula for post-shift. -/
theorem postShiftUnitary_toffoliCount
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers) :
    eeaToffoliCount (postShiftUnitary registers) =
      (registers.work.length - 1) + 6 * (registers.lengthS.length - 1) +
        rightTwoSwapCount registers.work + 2 := by
  exact shiftBody_toffoliCount registers.phase1 registers.phase2 registers.work
    registers.lengthS registers.both registers.carries hlayout.carry_capacity

/-- Exact constructor-derived CNOT formula for pre-shift. -/
theorem preShiftUnitary_cnotCount
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers)
    (hwidth : 2 ≤ registers.lengthS.length) :
    eeaCnotCount (preShiftUnitary registers) =
      2 * (registers.work.length - 1) + 3 * (registers.lengthS.length + 2) +
        2 * rightTwoSwapCount registers.work + 2 := by
  simp only [preShiftUnitary, eeaCnotCount_append]
  rw [shiftBody_cnotCount _ _ _ _ _ _ hlayout.carry_capacity hwidth]
  simp [eeaCnotCount]
  omega

/-- Exact constructor-derived CNOT formula for post-shift. -/
theorem postShiftUnitary_cnotCount
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers)
    (hwidth : 2 ≤ registers.lengthS.length) :
    eeaCnotCount (postShiftUnitary registers) =
      2 * (registers.work.length - 1) + 3 * (registers.lengthS.length + 2) +
        2 * rightTwoSwapCount registers.work := by
  exact shiftBody_cnotCount registers.phase1 registers.phase2 registers.work
    registers.lengthS registers.both registers.carries hlayout.carry_capacity hwidth

/-- Exact constructor-derived standalone-X formula for pre-shift. -/
theorem preShiftUnitary_xCount
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers) :
    eeaXCount (preShiftUnitary registers) =
      8 * (registers.lengthS.length - 1) + 4 := by
  simp only [preShiftUnitary, eeaXCount_append]
  rw [shiftBody_xCount _ _ _ _ _ _ hlayout.carry_capacity]
  simp [eeaXCount]
  omega

/-- Exact constructor-derived standalone-X formula for post-shift. -/
theorem postShiftUnitary_xCount
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers) :
    eeaXCount (postShiftUnitary registers) =
      8 * (registers.lengthS.length - 1) := by
  exact shiftBody_xCount registers.phase1 registers.phase2 registers.work
    registers.lengthS registers.both registers.carries hlayout.carry_capacity

/-- Exact constructor-derived T-count formula for pre-shift. -/
theorem preShiftUnitary_tCount
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers) :
    tCount (preShiftUnitary registers) =
      7 * (registers.work.length - 1) +
        42 * (registers.lengthS.length - 1) +
        7 * rightTwoSwapCount registers.work + 14 := by
  simp only [preShiftUnitary, tCount_append]
  rw [shiftBody_tCount _ _ _ _ _ _ hlayout.carry_capacity]
  simp [tCount, tCost]

/-- Exact constructor-derived T-count formula for post-shift. -/
theorem postShiftUnitary_tCount
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers) :
    tCount (postShiftUnitary registers) =
      7 * (registers.work.length - 1) +
        42 * (registers.lengthS.length - 1) +
        7 * rightTwoSwapCount registers.work + 14 := by
  exact shiftBody_tCount registers.phase1 registers.phase2 registers.work
    registers.lengthS registers.both registers.carries hlayout.carry_capacity

/-- The source's production widths allocate 13 scratch wires, touch 280 wires, and reserve 283
physical roles in total. -/
theorem shiftRegisters_productionWidths
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers)
    (hwork : registers.work.length = 259)
    (hlength : registers.lengthS.length = 9) :
    registers.scratch.length = 13 ∧
      registers.usedWires.length = 280 ∧
      registers.allWires.length = 283 := by
  have hcarries : registers.carries.length = 8 := by
    have hcapacity := hlayout.carry_capacity
    rw [hlength] at hcapacity
    omega
  constructor
  · simp [ShiftRegisters.scratch, hcarries, hlayout.reserved_size]
  constructor
  · simp [ShiftRegisters.usedWires, hwork, hlength, hcarries]
  · simp [ShiftRegisters.allWires, hwork, hlength, hcarries,
      hlayout.reserved_size]

/-- Exact production resources of the pinned `pre_shift_gate` (`work = 259`, `shift = 9`). -/
theorem preShiftUnitary_productionResources
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers)
    (hwork : registers.work.length = 259)
    (hlength : registers.lengthS.length = 9) :
    eeaToffoliCount (preShiftUnitary registers) = 566 ∧
      eeaCnotCount (preShiftUnitary registers) = 1067 ∧
      eeaXCount (preShiftUnitary registers) = 68 ∧
      tCount (preShiftUnitary registers) = 3962 := by
  have hlarge : 2 < registers.work.length := by omega
  have hodd : registers.work.length % 2 ≠ 0 := by omega
  have hswaps : rightTwoSwapCount registers.work = 258 := by
    rw [rightTwoSwapCount_of_odd registers.work hlarge hodd, hwork]
  have hwidth : 2 ≤ registers.lengthS.length := by omega
  constructor
  · rw [preShiftUnitary_toffoliCount registers hlayout, hwork, hlength, hswaps]
  constructor
  · rw [preShiftUnitary_cnotCount registers hlayout hwidth, hwork, hlength,
      hswaps]
  constructor
  · rw [preShiftUnitary_xCount registers hlayout, hlength]
  · rw [preShiftUnitary_tCount registers hlayout, hwork, hlength, hswaps]

/-- Exact production resources of the pinned `post_shift_gate` (`work = 259`, `shift = 9`). -/
theorem postShiftUnitary_productionResources
    (registers : ShiftRegisters) (hlayout : ShiftLayout registers)
    (hwork : registers.work.length = 259)
    (hlength : registers.lengthS.length = 9) :
    eeaToffoliCount (postShiftUnitary registers) = 566 ∧
      eeaCnotCount (postShiftUnitary registers) = 1065 ∧
      eeaXCount (postShiftUnitary registers) = 64 ∧
      tCount (postShiftUnitary registers) = 3962 := by
  have hlarge : 2 < registers.work.length := by omega
  have hodd : registers.work.length % 2 ≠ 0 := by omega
  have hswaps : rightTwoSwapCount registers.work = 258 := by
    rw [rightTwoSwapCount_of_odd registers.work hlarge hodd, hwork]
  have hwidth : 2 ≤ registers.lengthS.length := by omega
  constructor
  · rw [postShiftUnitary_toffoliCount registers hlayout, hwork, hlength, hswaps]
  constructor
  · rw [postShiftUnitary_cnotCount registers hlayout hwidth, hwork, hlength,
      hswaps]
  constructor
  · rw [postShiftUnitary_xCount registers hlayout, hlength]
  · rw [postShiftUnitary_tCount registers hlayout, hwork, hlength, hswaps]

/-! ## Pinned-source regressions -/

private def preShiftSmallRegisters : ShiftRegisters where
  phase1 := 0
  phase2 := 1
  work := [2, 3, 4, 5, 6]
  lengthS := [7, 8, 9]
  phase1IsZero := 10
  both := 11
  carries := [12, 13]
  reserved := [14, 15, 16]

private def postShiftSmallRegisters : ShiftRegisters where
  phase1 := 0
  phase2 := 1
  work := [2, 3, 4, 5, 6]
  lengthS := [7, 8, 9]
  phase1IsZero := 13
  both := 10
  carries := [11, 12]
  reserved := [14, 15, 16]

/-- Exact flattened `work_size = 5`, `shift_width = 3` pre-shift stream emitted by pinned
supplement commit `e64aa3c`.  This checks every role and the complete wrapper order. -/
theorem preShiftUnitary_source_regression :
    preShiftUnitary preShiftSmallRegisters =
      [.X 0, .CX 0 10, .X 0,
       .CX 3 2, .CCX 10 2 3, .CX 3 2,
       .CX 4 3, .CCX 10 3 4, .CX 4 3,
       .CX 5 4, .CCX 10 4 5, .CX 5 4,
       .CX 6 5, .CCX 10 5 6, .CX 6 5,
       .CCX 10 7 12, .CX 10 7,
       .CCX 8 12 13, .CX 13 9,
       .CCX 8 12 13, .CX 12 8,
       .CX 10 7, .CCX 10 7 12, .CX 10 7,
       .CCX 10 1 11,
       .CX 4 2, .CCX 11 2 4, .CX 4 2,
       .CX 6 2, .CCX 11 2 6, .CX 6 2,
       .CX 3 2, .CCX 11 2 3, .CX 3 2,
       .CX 5 2, .CCX 11 2 5, .CX 5 2,
       .X 7, .CCX 11 7 12, .X 7, .CX 11 7,
       .X 8, .CCX 8 12 13, .X 8, .CX 13 9,
       .X 8, .CCX 8 12 13, .X 8, .CX 12 8,
       .CX 11 7, .X 7, .CCX 11 7 12, .X 7, .CX 11 7,
       .X 7, .CCX 11 7 12, .X 7, .CX 11 7,
       .X 8, .CCX 8 12 13, .X 8, .CX 13 9,
       .X 8, .CCX 8 12 13, .X 8, .CX 12 8,
       .CX 11 7, .X 7, .CCX 11 7 12, .X 7, .CX 11 7,
       .CCX 10 1 11,
       .X 0, .CX 0 10, .X 0] := by
  simp [preShiftUnitary, preShiftSmallRegisters, shiftBody,
    controlledRotateLeftOne, controlledIncrement, incrementTail,
    controlledRotateRightTwo, rightTwoCycles, evenPositions, oddPositions,
    controlledCycle, controlledSwap, controlledDecrement, decrementTail]

/-- Exact flattened `work_size = 5`, `shift_width = 3` post-shift stream emitted by pinned
supplement commit `e64aa3c`.  Its source allocation uses `Scratch[0]` for `both` and begins the
borrow/carry chain at `Scratch[1]`. -/
theorem postShiftUnitary_source_regression :
    postShiftUnitary postShiftSmallRegisters =
      [.CX 3 2, .CCX 0 2 3, .CX 3 2,
       .CX 4 3, .CCX 0 3 4, .CX 4 3,
       .CX 5 4, .CCX 0 4 5, .CX 5 4,
       .CX 6 5, .CCX 0 5 6, .CX 6 5,
       .CCX 0 7 11, .CX 0 7,
       .CCX 8 11 12, .CX 12 9,
       .CCX 8 11 12, .CX 11 8,
       .CX 0 7, .CCX 0 7 11, .CX 0 7,
       .CCX 0 1 10,
       .CX 4 2, .CCX 10 2 4, .CX 4 2,
       .CX 6 2, .CCX 10 2 6, .CX 6 2,
       .CX 3 2, .CCX 10 2 3, .CX 3 2,
       .CX 5 2, .CCX 10 2 5, .CX 5 2,
       .X 7, .CCX 10 7 11, .X 7, .CX 10 7,
       .X 8, .CCX 8 11 12, .X 8, .CX 12 9,
       .X 8, .CCX 8 11 12, .X 8, .CX 11 8,
       .CX 10 7, .X 7, .CCX 10 7 11, .X 7, .CX 10 7,
       .X 7, .CCX 10 7 11, .X 7, .CX 10 7,
       .X 8, .CCX 8 11 12, .X 8, .CX 12 9,
       .X 8, .CCX 8 11 12, .X 8, .CX 11 8,
       .CX 10 7, .X 7, .CCX 10 7 11, .X 7, .CX 10 7,
       .CCX 0 1 10] := by
  simp [postShiftUnitary, postShiftSmallRegisters, shiftBody,
    controlledRotateLeftOne, controlledIncrement, incrementTail,
    controlledRotateRightTwo, rightTwoCycles, evenPositions, oddPositions,
    controlledCycle, controlledSwap, controlledDecrement, decrementTail]

private def preShiftSecp256k1Registers : ShiftRegisters where
  phase1 := 0
  phase2 := 1
  work := List.range' 2 259
  lengthS := List.range' 261 9
  phase1IsZero := 270
  both := 271
  carries := List.range' 272 8
  reserved := List.range' 280 3

set_option maxRecDepth 100000 in
private theorem preShiftSecp256k1Layout :
    ShiftLayout preShiftSecp256k1Registers := by
  refine ⟨by simp [preShiftSecp256k1Registers],
    by simp [preShiftSecp256k1Registers], ?_⟩
  decide

private def postShiftSecp256k1Registers : ShiftRegisters where
  phase1 := 0
  phase2 := 1
  work := List.range' 2 259
  lengthS := List.range' 261 9
  phase1IsZero := 279
  both := 270
  carries := List.range' 271 8
  reserved := List.range' 280 3

set_option maxRecDepth 100000 in
private theorem postShiftSecp256k1Layout :
    ShiftLayout postShiftSecp256k1Registers := by
  refine ⟨by simp [postShiftSecp256k1Registers],
    by simp [postShiftSecp256k1Registers], ?_⟩
  decide

/-- Closed production pre-shift witness: the source allocates 283 physical roles, touches 280
of them, restores all 13 scratch roles, and emits the exact constructor-derived resources. -/
theorem preShiftUnitary_secp256k1_resources :
    preShiftSecp256k1Registers.scratch.length = 13 ∧
      preShiftSecp256k1Registers.usedWires.length = 280 ∧
      preShiftSecp256k1Registers.allWires.length = 283 ∧
      eeaToffoliCount (preShiftUnitary preShiftSecp256k1Registers) = 566 ∧
      eeaCnotCount (preShiftUnitary preShiftSecp256k1Registers) = 1067 ∧
      eeaXCount (preShiftUnitary preShiftSecp256k1Registers) = 68 ∧
      tCount (preShiftUnitary preShiftSecp256k1Registers) = 3962 := by
  have hwork : preShiftSecp256k1Registers.work.length = 259 := by
    simp [preShiftSecp256k1Registers]
  have hlength : preShiftSecp256k1Registers.lengthS.length = 9 := by
    simp [preShiftSecp256k1Registers]
  obtain ⟨hscratch, hused, hall⟩ := shiftRegisters_productionWidths
    preShiftSecp256k1Registers preShiftSecp256k1Layout hwork hlength
  obtain ⟨htoffoli, hcnot, hx, ht⟩ := preShiftUnitary_productionResources
    preShiftSecp256k1Registers preShiftSecp256k1Layout hwork hlength
  exact ⟨hscratch, hused, hall, htoffoli, hcnot, hx, ht⟩

/-- Closed production post-shift witness.  The four source-unused scratch roles are represented by
`phase1IsZero :: reserved`; all 13 shared scratch roles are restored. -/
theorem postShiftUnitary_secp256k1_resources :
    postShiftSecp256k1Registers.scratch.length = 13 ∧
      postShiftSecp256k1Registers.usedWires.length = 280 ∧
      postShiftSecp256k1Registers.allWires.length = 283 ∧
      eeaToffoliCount (postShiftUnitary postShiftSecp256k1Registers) = 566 ∧
      eeaCnotCount (postShiftUnitary postShiftSecp256k1Registers) = 1065 ∧
      eeaXCount (postShiftUnitary postShiftSecp256k1Registers) = 64 ∧
      tCount (postShiftUnitary postShiftSecp256k1Registers) = 3962 := by
  have hwork : postShiftSecp256k1Registers.work.length = 259 := by
    simp [postShiftSecp256k1Registers]
  have hlength : postShiftSecp256k1Registers.lengthS.length = 9 := by
    simp [postShiftSecp256k1Registers]
  obtain ⟨hscratch, hused, hall⟩ := shiftRegisters_productionWidths
    postShiftSecp256k1Registers postShiftSecp256k1Layout hwork hlength
  obtain ⟨htoffoli, hcnot, hx, ht⟩ := postShiftUnitary_productionResources
    postShiftSecp256k1Registers postShiftSecp256k1Layout hwork hlength
  exact ⟨hscratch, hused, hall, htoffoli, hcnot, hx, ht⟩

/- Width-five source regression: the single cycle is `0,2,4,1,3`. -/
example (control w₀ w₁ w₂ w₃ w₄ : Wire) :
    controlledRotateRightTwo control ([w₀, w₁, w₂, w₃, w₄]) =
      controlledSwap control w₀ w₂ ++
      controlledSwap control w₀ w₄ ++
      controlledSwap control w₀ w₁ ++
      controlledSwap control w₀ w₃ := by
  simp [controlledRotateRightTwo, rightTwoCycles, evenPositions,
    oddPositions, controlledCycle, List.append_assoc]

/- Width-six source regression: the even cycle precedes the odd cycle. -/
example (control w₀ w₁ w₂ w₃ w₄ w₅ : Wire) :
    controlledRotateRightTwo control ([w₀, w₁, w₂, w₃, w₄, w₅]) =
      controlledSwap control w₀ w₂ ++
      controlledSwap control w₀ w₄ ++
      controlledSwap control w₁ w₃ ++
      controlledSwap control w₁ w₅ := by
  simp [controlledRotateRightTwo, rightTwoCycles, evenPositions,
    oddPositions, controlledCycle, List.append_assoc]

end ShorECDLP.Paper2607_13816
