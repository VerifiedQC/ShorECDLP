import ShorECDLP.Submission.«2607_13816».EEA.BitCircuits

/-!
# Clean-chain controlled increment

This is the literal `inc_mod2n_1ctrl` construction used by the pinned supplement.  The
least-significant bit is first.  A width-`n` register uses `n-1` clean carry wires; the carry
conjunctions are computed on the forward sweep and cleared on the reverse sweep.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

/-- Boolean ripple specification for adding a single carry bit to an LSB-first word. -/
def incrementBits : Bool → List Bool → List Bool
  | _, [] => []
  | carry, bit :: bits =>
      Bool.xor bit carry :: incrementBits (bit && carry) bits

/-- The inner carry chain, starting at the second data bit. -/
def incrementTail : List Wire → Wire → List Wire → Circuit
  | [], _, _ => []
  | [bit], carry, [] => [.CX carry bit]
  | bit :: next :: rest, carry, nextCarry :: carries =>
      [.CCX bit carry nextCarry] ++
        incrementTail (next :: rest) nextCarry carries ++
        [.CCX bit carry nextCarry, .CX carry bit]
  | _, _, _ => []

/-- Controlled addition of one modulo `2^register.length`. -/
def controlledIncrement : Wire → List Wire → List Wire → Circuit
  | _, [], _ => []
  | control, [bit], [] => [.CX control bit]
  | control, low :: next :: rest, firstCarry :: carries =>
      [.CCX control low firstCarry, .CX control low] ++
        incrementTail (next :: rest) firstCarry carries ++
        [.CX control low, .CCX control low firstCarry, .CX control low]
  | _, _, _ => []

private theorem incrementTail_usesOnly
    (bits : List Wire) (carry : Wire) (carries : List Wire) :
    PaperCircuitUsesOnly (carry :: bits ++ carries)
      (incrementTail bits carry carries) := by
  induction bits generalizing carry carries with
  | nil => simp [incrementTail, PaperCircuitUsesOnly]
  | cons bit tail ih =>
      cases tail with
      | nil =>
          cases carries with
          | nil =>
              simp [incrementTail, PaperCircuitUsesOnly,
                PaperGateUsesOnly, gateWires]
          | cons nextCarry carries =>
              simp [incrementTail, PaperCircuitUsesOnly]
      | cons next rest =>
          cases carries with
          | nil => simp [incrementTail, PaperCircuitUsesOnly]
          | cons nextCarry carries =>
              rw [incrementTail]
              apply PaperCircuitUsesOnly.append
              · apply PaperCircuitUsesOnly.append
                · intro gate hgate
                  simp at hgate
                  subst gate
                  simp [PaperGateUsesOnly, gateWires]
                · apply (ih nextCarry carries).mono
                  intro wire hwire
                  simp only [List.mem_cons, List.mem_append] at hwire ⊢
                  rcases hwire with hword | hcarries
                  · rcases hword with rfl | hword
                    · exact Or.inr (Or.inl rfl)
                    · rcases hword with rfl | hrest
                      · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
                      · exact Or.inl (Or.inr (Or.inr (Or.inr hrest)))
                  · exact Or.inr (Or.inr hcarries)
              · intro gate hgate
                simp at hgate
                rcases hgate with rfl | rfl
                · simp [PaperGateUsesOnly, gateWires]
                · simp [PaperGateUsesOnly, gateWires]

/-- The supplement's controlled increment touches exactly the declared control, word, and
clean carry bank. -/
theorem controlledIncrement_usesOnly
    (control : Wire) (register carries : List Wire) :
    PaperCircuitUsesOnly (control :: register ++ carries)
      (controlledIncrement control register carries) := by
  cases register with
  | nil => simp [controlledIncrement, PaperCircuitUsesOnly]
  | cons low tail =>
      cases tail with
      | nil =>
          cases carries with
          | nil =>
              simp [controlledIncrement, PaperCircuitUsesOnly,
                PaperGateUsesOnly, gateWires]
          | cons firstCarry carries =>
              simp [controlledIncrement, PaperCircuitUsesOnly]
      | cons next rest =>
          cases carries with
          | nil => simp [controlledIncrement, PaperCircuitUsesOnly]
          | cons firstCarry carries =>
              rw [controlledIncrement]
              apply PaperCircuitUsesOnly.append
              · apply PaperCircuitUsesOnly.append
                · intro gate hgate
                  simp at hgate
                  rcases hgate with rfl | rfl
                  · simp [PaperGateUsesOnly, gateWires]
                  · simp [PaperGateUsesOnly, gateWires]
                · apply (incrementTail_usesOnly (next :: rest)
                    firstCarry carries).mono
                  intro wire hwire
                  simp only [List.mem_cons, List.mem_append] at hwire ⊢
                  rcases hwire with hword | hcarries
                  · rcases hword with rfl | hword
                    · exact Or.inr (Or.inl rfl)
                    · rcases hword with rfl | hrest
                      · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
                      · exact Or.inl (Or.inr (Or.inr (Or.inr hrest)))
                  · exact Or.inr (Or.inr hcarries)
              · intro gate hgate
                simp at hgate
                rcases hgate with rfl | rfl | rfl
                · simp [PaperGateUsesOnly, gateWires]
                · simp [PaperGateUsesOnly, gateWires]
                · simp [PaperGateUsesOnly, gateWires]

private theorem incrementTail_HPFree
    (bits : List Wire) (carry : Wire) (carries : List Wire) :
    HPFree (incrementTail bits carry carries) := by
  induction bits generalizing carry carries with
  | nil => simp [incrementTail]
  | cons bit tail ih =>
      cases tail <;> cases carries <;>
        simp [incrementTail, ih]

@[simp]
theorem controlledIncrement_HPFree
    (control : Wire) (register carries : List Wire) :
    HPFree (controlledIncrement control register carries) := by
  cases register with
  | nil => simp [controlledIncrement]
  | cons low tail =>
      cases tail <;> cases carries <;>
        simp [controlledIncrement, incrementTail_HPFree]

private theorem wireValues_congr
    (wires : List Wire) (left right : BasisState)
    (h : ∀ wire ∈ wires, left wire = right wire) :
    wireValues wires left = wireValues wires right := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [wireValues, List.map_cons, List.cons.injEq]
      exact ⟨h wire (by simp), ih (fun other hother =>
        h other (by simp [hother]))⟩

private theorem list_eq_nil_of_one_eq_length_add_one
    (items : List α) (hlength : 1 = items.length + 1) :
    items = [] := by
  apply List.length_eq_zero_iff.mp
  omega

private theorem incrementTail_correct
    (bits : List Wire) (carry : Wire) (carries : List Wire)
    (state : BasisState)
    (hlength : bits.length = carries.length + 1)
    (hnd : (carry :: bits ++ carries).Nodup)
    (hclean : Clean carries state) :
    let after := run (incrementTail bits carry carries) state
    wireValues bits after =
        incrementBits (state carry) (wireValues bits state) ∧
      ∀ wire, wire ∉ bits → after wire = state wire := by
  induction bits generalizing carry carries state with
  | nil => simp at hlength
  | cons bit tail ih =>
      cases tail with
      | nil =>
          have hcarries : carries = [] :=
            list_eq_nil_of_one_eq_length_add_one carries (by simpa using hlength)
          subst carries
          constructor
          · simp [incrementTail, wireValues, incrementBits, run, applyGate, upd]
          · intro wire hwire
            simp only [List.mem_singleton] at hwire
            simp [incrementTail, run, applyGate, upd, hwire]
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons nextCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              have hcarry :
                  carry ∉ bit :: next :: rest ++ nextCarry :: carries :=
                (List.nodup_cons.mp hnd).1
              have hword :
                  (bit :: next :: rest ++ nextCarry :: carries).Nodup :=
                (List.nodup_cons.mp hnd).2
              have hbit : bit ∉ next :: rest ++ nextCarry :: carries :=
                (List.nodup_cons.mp hword).1
              have htail := (List.nodup_cons.mp hword).2
              have hinner :
                  (nextCarry :: next :: rest ++ carries).Nodup := by
                have hperm :
                    ((next :: rest) ++ nextCarry :: carries).Perm
                      (nextCarry :: (next :: rest) ++ carries) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := carries) (a := nextCarry))
                exact htail.perm hperm
              have hbc : bit ≠ carry := by
                intro equality
                exact hcarry (by simp [equality])
              have hbn : bit ≠ nextCarry := by
                intro equality
                exact hbit (by simp [equality])
              have hcn : carry ≠ nextCarry := by
                intro equality
                exact hcarry (by simp [equality])
              have hnextCarryFalse : state nextCarry = false :=
                hclean nextCarry (by simp)
              let first := applyGate (.CCX bit carry nextCarry) state
              have hfirstNext : first nextCarry = (state bit && state carry) := by
                simp [first, applyGate, hnextCarryFalse]
              have hfirstTail :
                  wireValues (next :: rest) first =
                    wireValues (next :: rest) state := by
                apply wireValues_congr
                intro wire hwire
                have hw : wire ≠ nextCarry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left carries hwire)
                simp [first, applyGate, upd, hw]
              have hcleanFirst : Clean carries first := by
                intro wire hwire
                have hw : wire ≠ nextCarry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_right (next :: rest) hwire)
                simpa [first, applyGate, upd, hw] using
                  hclean wire (by simp [hwire])
              have hrecursive := ih nextCarry carries first htailLength hinner hcleanFirst
              let middle := run (incrementTail (next :: rest) nextCarry carries) first
              have hmiddleValues :
                  wireValues (next :: rest) middle =
                    incrementBits (state bit && state carry)
                      (wireValues (next :: rest) state) := by
                have hrecursiveValues :
                    wireValues (next :: rest) middle =
                      incrementBits (first nextCarry)
                        (wireValues (next :: rest) first) := by
                  simpa only [middle] using hrecursive.1
                rw [hrecursiveValues, hfirstNext, hfirstTail]
              have hmiddleOutside :
                  ∀ wire, wire ∉ next :: rest → middle wire = first wire :=
                hrecursive.2
              have hmiddleBit : middle bit = state bit := by
                rw [hmiddleOutside bit]
                · simp [first, applyGate, upd, hbn]
                · intro hmem
                  exact hbit (List.mem_append_left (nextCarry :: carries) hmem)
              have hmiddleCarry : middle carry = state carry := by
                rw [hmiddleOutside carry]
                · simp [first, applyGate, upd, hcn]
                · intro hmem
                  exact hcarry (List.mem_append_left (nextCarry :: carries)
                    (List.mem_cons_of_mem bit hmem))
              have hmiddleNextCarry :
                  middle nextCarry = (state bit && state carry) := by
                rw [hmiddleOutside nextCarry]
                · exact hfirstNext
                · intro hmem
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left carries hmem)
              let after :=
                run [.CCX bit carry nextCarry, .CX carry bit] middle
              have hafterBit :
                  after bit = Bool.xor (state bit) (state carry) := by
                simp [after, run, applyGate, upd, hbn, hcn,
                  hmiddleBit, hmiddleCarry]
              have hafterTail :
                  wireValues (next :: rest) after =
                    wireValues (next :: rest) middle := by
                apply wireValues_congr
                intro wire hwire
                have hwireBit : wire ≠ bit := by
                  intro equality
                  subst wire
                  exact hbit (List.mem_append_left (nextCarry :: carries) hwire)
                have hwireNextCarry : wire ≠ nextCarry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left carries hwire)
                simp [after, run, applyGate, upd, hwireBit, hwireNextCarry]
              rw [incrementTail, run_append, run_append]
              change
                wireValues (bit :: next :: rest) after =
                    incrementBits (state carry)
                      (wireValues (bit :: next :: rest) state) ∧
                  ∀ wire, wire ∉ bit :: next :: rest →
                    after wire = state wire
              constructor
              · change
                  after bit :: wireValues (next :: rest) after =
                    Bool.xor (state bit) (state carry) ::
                      incrementBits (state bit && state carry)
                        (wireValues (next :: rest) state)
                rw [hafterBit, hafterTail, hmiddleValues]
              · intro wire hwire
                simp only [List.mem_cons, not_or] at hwire
                have hwireTail : wire ∉ next :: rest := by
                  simpa only [List.mem_cons, not_or] using hwire.2
                by_cases hnextCarry : wire = nextCarry
                · subst wire
                  simp [after, run, applyGate, upd, hbn, Ne.symm hbn, hcn,
                    hmiddleBit, hmiddleCarry, hmiddleNextCarry,
                    hnextCarryFalse]
                · have hmiddleWire := hmiddleOutside wire hwireTail
                  have hafterWire : after wire = middle wire := by
                    simp [after, run, applyGate, upd, hwire.1, hnextCarry]
                  rw [hafterWire, hmiddleWire]
                  simp [first, applyGate, upd, hnextCarry]

/-- The exact controlled increment changes only the target word.  In particular its control and
clean carry bank are restored, while the word is incremented modulo its width when the control is
set. -/
theorem controlledIncrement_correct
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    let after := run (controlledIncrement control register carries) state
    wireValues register after =
        incrementBits (state control) (wireValues register state) ∧
      ∀ wire, wire ∉ register → after wire = state wire := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have hcarries : carries = [] :=
            list_eq_nil_of_one_eq_length_add_one carries (by simpa using hlength)
          subst carries
          have hcontrol : control ≠ low := by
            simpa [List.nodup_cons] using (List.nodup_cons.mp hnd).1
          constructor
          · simp [controlledIncrement, wireValues, incrementBits, run, applyGate, upd]
          · intro wire hwire
            simp only [List.mem_singleton] at hwire
            simp [controlledIncrement, run, applyGate, upd, hwire]
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons firstCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              have hcontrol :
                  control ∉ low :: next :: rest ++ firstCarry :: carries :=
                (List.nodup_cons.mp hnd).1
              have hword :
                  (low :: next :: rest ++ firstCarry :: carries).Nodup :=
                (List.nodup_cons.mp hnd).2
              have hlow : low ∉ next :: rest ++ firstCarry :: carries :=
                (List.nodup_cons.mp hword).1
              have htail := (List.nodup_cons.mp hword).2
              have hinner :
                  (firstCarry :: next :: rest ++ carries).Nodup := by
                have hperm :
                    ((next :: rest) ++ firstCarry :: carries).Perm
                      (firstCarry :: (next :: rest) ++ carries) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := carries) (a := firstCarry))
                exact htail.perm hperm
              have hcl : control ≠ low := by
                intro equality
                exact hcontrol (by simp [equality])
              have hcf : control ≠ firstCarry := by
                intro equality
                exact hcontrol (by simp [equality])
              have hlf : low ≠ firstCarry := by
                intro equality
                exact hlow (by simp [equality])
              have hfirstCarryFalse : state firstCarry = false :=
                hclean firstCarry (by simp)
              let first :=
                run [.CCX control low firstCarry, .CX control low] state
              have hfirstCarry :
                  first firstCarry = (state control && state low) := by
                simp [first, run, applyGate, upd, hcf, hlf, Ne.symm hlf,
                  hfirstCarryFalse]
              have hfirstLow :
                  first low = Bool.xor (state low) (state control) := by
                simp [first, run, applyGate, upd, hcf, hlf,
                  hfirstCarryFalse]
              have hfirstControl : first control = state control := by
                simp [first, run, applyGate, upd, hcl, hcf]
              have hfirstTail :
                  wireValues (next :: rest) first =
                    wireValues (next :: rest) state := by
                apply wireValues_congr
                intro wire hwire
                have hwLow : wire ≠ low := by
                  intro equality
                  subst wire
                  exact hlow (List.mem_append_left (firstCarry :: carries) hwire)
                have hwCarry : wire ≠ firstCarry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left carries hwire)
                simp [first, run, applyGate, upd, hwLow, hwCarry]
              have hcleanFirst : Clean carries first := by
                intro wire hwire
                have hwLow : wire ≠ low := by
                  intro equality
                  subst wire
                  exact hlow (List.mem_append_right (next :: rest)
                    (by simp [hwire]))
                have hwCarry : wire ≠ firstCarry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_right (next :: rest) hwire)
                simpa [first, run, applyGate, upd, hwLow, hwCarry] using
                  hclean wire (by simp [hwire])
              have hrecursive := incrementTail_correct
                (next :: rest) firstCarry carries first
                htailLength hinner hcleanFirst
              let middle :=
                run (incrementTail (next :: rest) firstCarry carries) first
              have hmiddleValues :
                  wireValues (next :: rest) middle =
                    incrementBits (state low && state control)
                      (wireValues (next :: rest) state) := by
                have hrecursiveValues :
                    wireValues (next :: rest) middle =
                      incrementBits (first firstCarry)
                        (wireValues (next :: rest) first) := by
                  simpa only [middle] using hrecursive.1
                rw [hrecursiveValues, hfirstCarry, hfirstTail]
                simp [Bool.and_comm]
              have hmiddleOutside :
                  ∀ wire, wire ∉ next :: rest → middle wire = first wire :=
                hrecursive.2
              have hmiddleLow :
                  middle low = Bool.xor (state low) (state control) := by
                rw [hmiddleOutside low]
                · exact hfirstLow
                · intro hmem
                  exact hlow (List.mem_append_left (firstCarry :: carries) hmem)
              have hmiddleControl : middle control = state control := by
                rw [hmiddleOutside control]
                · exact hfirstControl
                · intro hmem
                  exact hcontrol (List.mem_append_left (firstCarry :: carries)
                    (List.mem_cons_of_mem low hmem))
              have hmiddleFirstCarry :
                  middle firstCarry = (state control && state low) := by
                rw [hmiddleOutside firstCarry]
                · exact hfirstCarry
                · intro hmem
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left carries hmem)
              let after :=
                run [.CX control low, .CCX control low firstCarry,
                  .CX control low] middle
              have hafterLow :
                  after low = Bool.xor (state low) (state control) := by
                simp [after, run, applyGate, upd, hcl, hcf, hlf,
                  hmiddleLow, hmiddleControl, hmiddleFirstCarry]
              have hafterTail :
                  wireValues (next :: rest) after =
                    wireValues (next :: rest) middle := by
                apply wireValues_congr
                intro wire hwire
                have hwLow : wire ≠ low := by
                  intro equality
                  subst wire
                  exact hlow (List.mem_append_left (firstCarry :: carries) hwire)
                have hwCarry : wire ≠ firstCarry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left carries hwire)
                simp [after, run, applyGate, upd, hwLow, hwCarry]
              rw [controlledIncrement, run_append, run_append]
              change
                wireValues (low :: next :: rest) after =
                    incrementBits (state control)
                      (wireValues (low :: next :: rest) state) ∧
                  ∀ wire, wire ∉ low :: next :: rest →
                    after wire = state wire
              constructor
              · change
                  after low :: wireValues (next :: rest) after =
                    Bool.xor (state low) (state control) ::
                      incrementBits (state low && state control)
                        (wireValues (next :: rest) state)
                rw [hafterLow, hafterTail, hmiddleValues]
              · intro wire hwire
                simp only [List.mem_cons, not_or] at hwire
                have hwireTail : wire ∉ next :: rest := by
                  simpa only [List.mem_cons, not_or] using hwire.2
                by_cases hfirstCarry : wire = firstCarry
                · subst wire
                  simp [after, run, applyGate, upd, hcl, hcf, hlf,
                    Ne.symm hlf, hmiddleLow, hmiddleControl,
                    hmiddleFirstCarry, hfirstCarryFalse]
                · have hmiddleWire := hmiddleOutside wire hwireTail
                  have hafterWire : after wire = middle wire := by
                    simp [after, run, applyGate, upd, hwire.1, hfirstCarry]
                  rw [hafterWire, hmiddleWire]
                  simp [first, run, applyGate, upd, hwire.1, hfirstCarry]

/-- The external control is restored exactly. -/
theorem controlledIncrement_control
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    run (controlledIncrement control register carries) state control =
      state control := by
  have hcontrol : control ∉ register := by
    intro hmem
    exact (List.nodup_cons.mp hnd).1
      (List.mem_append_left carries hmem)
  exact (controlledIncrement_correct control register carries state
    hlength hnd hclean).2 control hcontrol

/-- Every clean carry wire is returned to zero. -/
theorem controlledIncrement_clean
    (control : Wire) (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (control :: register ++ carries).Nodup)
    (hclean : Clean carries state) :
    Clean carries
      (run (controlledIncrement control register carries) state) := by
  have hcross := (List.nodup_append.mp (List.nodup_cons.mp hnd).2).2.2
  intro wire hwire
  have hnot : wire ∉ register := by
    intro hmem
    exact hcross wire hmem wire hwire rfl
  rw [(controlledIncrement_correct control register carries state
    hlength hnd hclean).2 wire hnot]
  exact hclean wire hwire

private theorem incrementTail_wellFormed
    (bits : List Wire) (carry : Wire) (carries : List Wire)
    (hnd : (carry :: bits ++ carries).Nodup) :
    CircuitWellFormed (incrementTail bits carry carries) := by
  induction bits generalizing carry carries with
  | nil => simp [incrementTail]
  | cons bit tail ih =>
      cases tail with
      | nil =>
          cases carries with
          | nil =>
              have hcarry : carry ≠ bit := by
                simpa [List.nodup_cons] using (List.nodup_cons.mp hnd).1
              simp [incrementTail, Gate.WellFormed, hcarry]
          | cons nextCarry carries => simp [incrementTail]
      | cons next rest =>
          cases carries with
          | nil => simp [incrementTail]
          | cons nextCarry carries =>
              have hcarry : carry ∉ bit :: next :: rest ++ nextCarry :: carries :=
                (List.nodup_cons.mp hnd).1
              have htail : (bit :: next :: rest ++ nextCarry :: carries).Nodup :=
                (List.nodup_cons.mp hnd).2
              have hbit : bit ∉ next :: rest ++ nextCarry :: carries :=
                (List.nodup_cons.mp htail).1
              have htail := (List.nodup_cons.mp htail).2
              have hnextCarryTail :
                  (nextCarry :: next :: rest ++ carries).Nodup := by
                have hperm :
                    ((next :: rest) ++ nextCarry :: carries).Perm
                      (nextCarry :: (next :: rest) ++ carries) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := carries) (a := nextCarry))
                exact htail.perm hperm
              have hbc : bit ≠ carry := by
                intro equality
                exact hcarry (by simp [equality])
              have hbn : bit ≠ nextCarry := by
                intro equality
                exact hbit (by simp [equality])
              have hcn : carry ≠ nextCarry := by
                intro equality
                exact hcarry (by simp [equality])
              rw [incrementTail, circuitWellFormed_append,
                circuitWellFormed_append]
              refine ⟨⟨?_, ih nextCarry carries hnextCarryTail⟩, ?_⟩
              · simp [CircuitWellFormed, Gate.WellFormed, hbc, hbn, hcn]
              · simp [CircuitWellFormed, Gate.WellFormed,
                  hbc, Ne.symm hbc, hbn, hcn]

/-- Physical well-formedness of the exact controlled increment. -/
theorem controlledIncrement_wellFormed
    (control : Wire) (register carries : List Wire)
    (hnd : (control :: register ++ carries).Nodup) :
    CircuitWellFormed (controlledIncrement control register carries) := by
  cases register with
  | nil => simp [controlledIncrement]
  | cons low tail =>
      cases tail with
      | nil =>
          cases carries with
          | nil =>
              have hcl : control ≠ low := by
                simpa [List.nodup_cons] using (List.nodup_cons.mp hnd).1
              simp [controlledIncrement, Gate.WellFormed, hcl]
          | cons firstCarry carries => simp [controlledIncrement]
      | cons next rest =>
          cases carries with
          | nil => simp [controlledIncrement]
          | cons firstCarry carries =>
              have hcontrol :
                  control ∉ low :: next :: rest ++ firstCarry :: carries :=
                (List.nodup_cons.mp hnd).1
              have htail :
                  (low :: next :: rest ++ firstCarry :: carries).Nodup :=
                (List.nodup_cons.mp hnd).2
              have hlow : low ∉ next :: rest ++ firstCarry :: carries :=
                (List.nodup_cons.mp htail).1
              have htail := (List.nodup_cons.mp htail).2
              have hinner :
                  (firstCarry :: next :: rest ++ carries).Nodup := by
                have hperm :
                    ((next :: rest) ++ firstCarry :: carries).Perm
                      (firstCarry :: (next :: rest) ++ carries) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := carries) (a := firstCarry))
                exact htail.perm hperm
              have hcl : control ≠ low := by
                intro equality
                exact hcontrol (by simp [equality])
              have hcf : control ≠ firstCarry := by
                intro equality
                exact hcontrol (by simp [equality])
              have hlf : low ≠ firstCarry := by
                intro equality
                exact hlow (by simp [equality])
              rw [controlledIncrement, circuitWellFormed_append,
                circuitWellFormed_append]
              refine ⟨⟨?_, incrementTail_wellFormed
                (next :: rest) firstCarry carries hinner⟩, ?_⟩
              · simp [CircuitWellFormed, Gate.WellFormed, hcl, hcf, hlf]
              · simp [CircuitWellFormed, Gate.WellFormed, hcl, hcf, hlf]

private theorem incrementTail_toffoliCount
    (bits : List Wire) (carry : Wire) (carries : List Wire)
    (hlength : bits.length = carries.length + 1) :
    eeaToffoliCount (incrementTail bits carry carries) =
      2 * (bits.length - 1) := by
  induction bits generalizing carry carries with
  | nil => simp at hlength
  | cons bit tail ih =>
      cases tail with
      | nil =>
          have : carries = [] := list_eq_nil_of_one_eq_length_add_one carries
            (by simpa using hlength)
          subst carries
          rfl
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons nextCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              rw [incrementTail, eeaToffoliCount_append,
                eeaToffoliCount_append, ih nextCarry carries htailLength]
              simp [eeaToffoliCount]
              omega

private theorem incrementTail_cnotCount
    (bits : List Wire) (carry : Wire) (carries : List Wire)
    (hlength : bits.length = carries.length + 1) :
    eeaCnotCount (incrementTail bits carry carries) = bits.length := by
  induction bits generalizing carry carries with
  | nil => simp at hlength
  | cons bit tail ih =>
      cases tail with
      | nil =>
          have : carries = [] := list_eq_nil_of_one_eq_length_add_one carries
            (by simpa using hlength)
          subst carries
          rfl
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons nextCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              rw [incrementTail, eeaCnotCount_append,
                eeaCnotCount_append, ih nextCarry carries htailLength]
              simp [eeaCnotCount]

private theorem incrementTail_tCount
    (bits : List Wire) (carry : Wire) (carries : List Wire)
    (hlength : bits.length = carries.length + 1) :
    tCount (incrementTail bits carry carries) =
      14 * (bits.length - 1) := by
  induction bits generalizing carry carries with
  | nil => simp at hlength
  | cons bit tail ih =>
      cases tail with
      | nil =>
          have : carries = [] := list_eq_nil_of_one_eq_length_add_one carries
            (by simpa using hlength)
          subst carries
          rfl
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons nextCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              rw [incrementTail, tCount_append, tCount_append,
                ih nextCarry carries htailLength]
              simp [tCost]
              omega

/-- Exact Toffoli count: two carry-chain Toffolis per non-low bit. -/
theorem controlledIncrement_toffoliCount
    (control : Wire) (register carries : List Wire)
    (hlength : register.length = carries.length + 1) :
    eeaToffoliCount (controlledIncrement control register carries) =
      2 * (register.length - 1) := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have : carries = [] := list_eq_nil_of_one_eq_length_add_one carries
            (by simpa using hlength)
          subst carries
          rfl
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons firstCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              rw [controlledIncrement, eeaToffoliCount_append,
                eeaToffoliCount_append,
                incrementTail_toffoliCount _ _ _ htailLength]
              simp [eeaToffoliCount]
              omega

/-- At width at least two, the exact CNOT count is `n+2`. -/
theorem controlledIncrement_cnotCount
    (control low next : Wire) (rest carries : List Wire)
    (hlength : (low :: next :: rest).length = carries.length + 1) :
    eeaCnotCount
        (controlledIncrement control (low :: next :: rest) carries) =
      (low :: next :: rest).length + 2 := by
  cases carries with
  | nil => simp at hlength
  | cons firstCarry carries =>
      have htailLength : (next :: rest).length = carries.length + 1 := by
        simpa using hlength
      rw [controlledIncrement, eeaCnotCount_append,
        eeaCnotCount_append, incrementTail_cnotCount _ _ _ htailLength]
      simp [eeaCnotCount]
      omega

/-- Constructor-derived T count of the exact controlled increment. -/
theorem controlledIncrement_tCount
    (control : Wire) (register carries : List Wire)
    (hlength : register.length = carries.length + 1) :
    tCount (controlledIncrement control register carries) =
      14 * (register.length - 1) := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have : carries = [] := list_eq_nil_of_one_eq_length_add_one carries
            (by simpa using hlength)
          subst carries
          rfl
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons firstCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              rw [controlledIncrement, tCount_append, tCount_append,
                incrementTail_tCount _ _ _ htailLength]
              simp [tCost]
              omega

/-! ## Literal uncontrolled increment used by endpoint affine transforms -/

/-- Addition of one modulo the register width, with the exact gate order of
`inc_mod2n_uncontrolled` in the pinned supplement.  A width-`n` word consumes the first
`n - 1` clean wires; outside that capacity the total Lean definition falls back to `[]`,
whereas the Python generator raises. -/
def uncontrolledIncrement : List Wire → List Wire → Circuit
  | [], _ => []
  | [bit], _ => [.X bit]
  | low :: next :: rest, firstCarry :: carries =>
      [.CX low firstCarry] ++
        incrementTail (next :: rest) firstCarry carries ++
        [.CX low firstCarry, .X low]
  | _ :: _ :: _, [] => []

/-- The exact uncontrolled increment changes only its target word, adds one modulo the
word width, and restores every clean carry wire. -/
theorem uncontrolledIncrement_correct
    (register carries : List Wire) (state : BasisState)
    (hlength : register.length = carries.length + 1)
    (hnd : (register ++ carries).Nodup)
    (hclean : Clean carries state) :
    let after := run (uncontrolledIncrement register carries) state
    wireValues register after =
        incrementBits true (wireValues register state) ∧
      ∀ wire, wire ∉ register → after wire = state wire := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have hcarries : carries = [] :=
            list_eq_nil_of_one_eq_length_add_one carries (by simpa using hlength)
          subst carries
          constructor
          · simp [uncontrolledIncrement, wireValues, incrementBits, run, applyGate]
          · intro wire hwire
            simp only [List.mem_singleton] at hwire
            simp [uncontrolledIncrement, run, applyGate, upd, hwire]
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons firstCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              have hword :
                  (low :: next :: rest ++ firstCarry :: carries).Nodup := by
                simpa [List.cons_append] using hnd
              have hlow : low ∉ next :: rest ++ firstCarry :: carries :=
                (List.nodup_cons.mp hword).1
              have htail := (List.nodup_cons.mp hword).2
              have hinner :
                  (firstCarry :: next :: rest ++ carries).Nodup := by
                have hperm :
                    ((next :: rest) ++ firstCarry :: carries).Perm
                      (firstCarry :: (next :: rest) ++ carries) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := carries) (a := firstCarry))
                exact htail.perm hperm
              have hlowCarry : low ≠ firstCarry := by
                intro equality
                exact hlow (by simp [equality])
              have hcarryFalse : state firstCarry = false :=
                hclean firstCarry (by simp)
              let first := run [.CX low firstCarry] state
              have hfirstCarry : first firstCarry = state low := by
                simp [first, run, applyGate, hcarryFalse]
              have hfirstLow : first low = state low := by
                simp [first, run, applyGate, upd, hlowCarry]
              have hfirstTail :
                  wireValues (next :: rest) first =
                    wireValues (next :: rest) state := by
                apply wireValues_congr
                intro wire hwire
                have hw : wire ≠ firstCarry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left carries hwire)
                simp [first, run, applyGate, upd, hw]
              have hcleanFirst : Clean carries first := by
                intro wire hwire
                have hw : wire ≠ firstCarry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_right (next :: rest) hwire)
                simpa [first, run, applyGate, upd, hw] using
                  hclean wire (by simp [hwire])
              have hrecursive := incrementTail_correct
                (next :: rest) firstCarry carries first
                htailLength hinner hcleanFirst
              let middle :=
                run (incrementTail (next :: rest) firstCarry carries) first
              have hmiddleValues :
                  wireValues (next :: rest) middle =
                    incrementBits (state low)
                      (wireValues (next :: rest) state) := by
                have hvalues :
                    wireValues (next :: rest) middle =
                      incrementBits (first firstCarry)
                        (wireValues (next :: rest) first) := by
                  simpa only [middle] using hrecursive.1
                rw [hvalues, hfirstCarry, hfirstTail]
              have hmiddleOutside :
                  ∀ wire, wire ∉ next :: rest → middle wire = first wire :=
                hrecursive.2
              have hmiddleLow : middle low = state low := by
                rw [hmiddleOutside low]
                · exact hfirstLow
                · intro hmem
                  exact hlow (List.mem_append_left (firstCarry :: carries) hmem)
              have hmiddleCarry : middle firstCarry = state low := by
                rw [hmiddleOutside firstCarry]
                · exact hfirstCarry
                · intro hmem
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left carries hmem)
              let after := run [.CX low firstCarry, .X low] middle
              have hafterLow : after low = !state low := by
                simp [after, run, applyGate, upd, hlowCarry, hmiddleLow]
              have hafterTail :
                  wireValues (next :: rest) after =
                    wireValues (next :: rest) middle := by
                apply wireValues_congr
                intro wire hwire
                have hwLow : wire ≠ low := by
                  intro equality
                  subst wire
                  exact hlow (List.mem_append_left (firstCarry :: carries) hwire)
                have hwCarry : wire ≠ firstCarry := by
                  intro equality
                  subst wire
                  exact (List.nodup_cons.mp hinner).1
                    (List.mem_append_left carries hwire)
                simp [after, run, applyGate, upd, hwLow, hwCarry]
              rw [uncontrolledIncrement, run_append, run_append]
              change
                wireValues (low :: next :: rest) after =
                    incrementBits true
                      (wireValues (low :: next :: rest) state) ∧
                  ∀ wire, wire ∉ low :: next :: rest →
                    after wire = state wire
              constructor
              · change
                  after low :: wireValues (next :: rest) after =
                    Bool.xor (state low) true ::
                      incrementBits (state low && true)
                        (wireValues (next :: rest) state)
                rw [hafterLow, hafterTail, hmiddleValues]
                cases state low <;> rfl
              · intro wire hwire
                simp only [List.mem_cons, not_or] at hwire
                have hwireTail : wire ∉ next :: rest := by
                  simpa only [List.mem_cons, not_or] using hwire.2
                by_cases hwCarry : wire = firstCarry
                · subst wire
                  simp [after, run, applyGate, upd, hlowCarry,
                    Ne.symm hlowCarry, hmiddleLow, hmiddleCarry, hcarryFalse]
                · have hmiddleWire := hmiddleOutside wire hwireTail
                  have hafterWire : after wire = middle wire := by
                    simp [after, run, applyGate, upd, hwire.1, hwCarry]
                  rw [hafterWire, hmiddleWire]
                  simp [first, run, applyGate, upd, hwCarry]

@[simp]
theorem uncontrolledIncrement_HPFree
    (register carries : List Wire) :
    HPFree (uncontrolledIncrement register carries) := by
  cases register with
  | nil => simp [uncontrolledIncrement]
  | cons low tail =>
      cases tail <;> cases carries <;>
        simp [uncontrolledIncrement, incrementTail_HPFree]

/-- Exact support of the source uncontrolled increment. -/
theorem uncontrolledIncrement_usesOnly
    (register carries : List Wire) :
    PaperCircuitUsesOnly (register ++ carries)
      (uncontrolledIncrement register carries) := by
  cases register with
  | nil => simp [uncontrolledIncrement, PaperCircuitUsesOnly]
  | cons low tail =>
      cases tail with
      | nil =>
          simp [uncontrolledIncrement, PaperCircuitUsesOnly,
            PaperGateUsesOnly, gateWires]
      | cons next rest =>
          cases carries with
          | nil => simp [uncontrolledIncrement, PaperCircuitUsesOnly]
          | cons firstCarry carries =>
              rw [uncontrolledIncrement]
              apply PaperCircuitUsesOnly.append
              · apply PaperCircuitUsesOnly.append
                · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
                · apply (incrementTail_usesOnly
                    (next :: rest) firstCarry carries).mono
                  intro wire hwire
                  simp only [List.mem_cons, List.mem_append] at hwire ⊢
                  rcases hwire with (rfl | rfl | hrest) | hcarries
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inl (Or.inr (Or.inl rfl))
                  · exact Or.inl (Or.inr (Or.inr hrest))
                  · exact Or.inr (Or.inr hcarries)
              · intro gate hgate
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
                rcases hgate with rfl | rfl
                · simp [PaperGateUsesOnly, gateWires]
                · simp [PaperGateUsesOnly, gateWires]

/-- Physical well-formedness of the exact uncontrolled increment. -/
theorem uncontrolledIncrement_wellFormed
    (register carries : List Wire)
    (hnd : (register ++ carries).Nodup) :
    CircuitWellFormed (uncontrolledIncrement register carries) := by
  cases register with
  | nil => simp [uncontrolledIncrement]
  | cons low tail =>
      cases tail with
      | nil => simp [uncontrolledIncrement, CircuitWellFormed, Gate.WellFormed]
      | cons next rest =>
          cases carries with
          | nil => simp [uncontrolledIncrement]
          | cons firstCarry carries =>
              have hword :
                  (low :: next :: rest ++ firstCarry :: carries).Nodup := by
                simpa [List.cons_append] using hnd
              have hlow := (List.nodup_cons.mp hword).1
              have htail := (List.nodup_cons.mp hword).2
              have hinner :
                  (firstCarry :: next :: rest ++ carries).Nodup := by
                have hperm :
                    ((next :: rest) ++ firstCarry :: carries).Perm
                      (firstCarry :: (next :: rest) ++ carries) := by
                  simpa [List.append_assoc] using
                    (List.perm_middle (l₁ := next :: rest)
                      (l₂ := carries) (a := firstCarry))
                exact htail.perm hperm
              have hlowCarry : low ≠ firstCarry := by
                intro equality
                exact hlow (by simp [equality])
              rw [uncontrolledIncrement, circuitWellFormed_append,
                circuitWellFormed_append]
              exact ⟨⟨by simp [CircuitWellFormed, Gate.WellFormed,
                hlowCarry], incrementTail_wellFormed _ _ _ hinner⟩,
                by simp [CircuitWellFormed, Gate.WellFormed,
                  hlowCarry]⟩

/-- Exact Toffoli count of the source uncontrolled increment. -/
theorem uncontrolledIncrement_toffoliCount
    (register carries : List Wire)
    (hlength : register.length = carries.length + 1) :
    eeaToffoliCount (uncontrolledIncrement register carries) =
      2 * (register.length - 2) := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have : carries = [] := list_eq_nil_of_one_eq_length_add_one carries
            (by simpa using hlength)
          subst carries
          rfl
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons firstCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              rw [uncontrolledIncrement, eeaToffoliCount_append,
                eeaToffoliCount_append,
                incrementTail_toffoliCount _ _ _ htailLength]
              simp [eeaToffoliCount]

/-- Exact CNOT count at width at least two. -/
theorem uncontrolledIncrement_cnotCount
    (low next : Wire) (rest carries : List Wire)
    (hlength : (low :: next :: rest).length = carries.length + 1) :
    eeaCnotCount (uncontrolledIncrement (low :: next :: rest) carries) =
      (low :: next :: rest).length + 1 := by
  cases carries with
  | nil => simp at hlength
  | cons firstCarry carries =>
      have htailLength : (next :: rest).length = carries.length + 1 := by
        simpa using hlength
      rw [uncontrolledIncrement, eeaCnotCount_append,
        eeaCnotCount_append, incrementTail_cnotCount _ _ _ htailLength]
      simp [eeaCnotCount]
      omega

/-- Constructor-derived T count of the source uncontrolled increment. -/
theorem uncontrolledIncrement_tCount
    (register carries : List Wire)
    (hlength : register.length = carries.length + 1) :
    tCount (uncontrolledIncrement register carries) =
      14 * (register.length - 2) := by
  cases register with
  | nil => simp at hlength
  | cons low tail =>
      cases tail with
      | nil =>
          have : carries = [] := list_eq_nil_of_one_eq_length_add_one carries
            (by simpa using hlength)
          subst carries
          rfl
      | cons next rest =>
          cases carries with
          | nil => simp at hlength
          | cons firstCarry carries =>
              have htailLength : (next :: rest).length = carries.length + 1 := by
                simpa using hlength
              rw [uncontrolledIncrement, tCount_append, tCount_append,
                incrementTail_tCount _ _ _ htailLength]
              simp [tCost]

end ShorECDLP.Paper2607_13816
