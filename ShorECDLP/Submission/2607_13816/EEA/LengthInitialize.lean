import ShorECDLP.Submission.«2607_13816».EEA.KnownScratch
import ShorECDLP.Submission.«2607_13816».EEA.LengthBlocks

namespace ShorECDLP.Paper2607_13816

open _root_.ShorECDLP.Classical

set_option linter.unusedSimpArgs false

private theorem xorState_upd_outside (enabled : Bool) (targets : List Wire) (value : Nat)
    (state : BasisState) (wire : Wire) (bit : Bool) (hout : wire ∉ targets) :
    xorConstantState enabled targets value state[wire ↦ bit] =
      (xorConstantState enabled targets value state)[wire ↦ bit] := by
  induction targets generalizing value state with
  | nil => rfl
  | cons target targets ih =>
      simp only [List.mem_cons, not_or] at hout
      simp only [xorConstantState]
      split
      · have he : (state[wire ↦ bit])[target ↦ Bool.xor (state[wire ↦ bit] target) enabled] =
            (state[target ↦ Bool.xor (state target) enabled])[wire ↦ bit] := by
          funext w
          simp [upd, Ne.symm hout.1]
          split <;> split <;> simp_all
        rw [he, ih (value / 2) _ hout.2]
      · exact ih (value / 2) state hout.2

private theorem matches_agrees (controls : List Wire) (value bit : Nat)
    (left right : BasisState) (h : ∀ wire ∈ controls, left wire = right wire) :
    registerMatchesFrom controls value bit left = registerMatchesFrom controls value bit right := by
  induction controls generalizing bit with
  | nil => rfl
  | cons wire wires ih =>
      simp only [registerMatchesFrom]
      rw [h wire (by simp), ih (bit+1) (by intro w hw; exact h w (by simp [hw]))]

/-- Compute a first-one predicate, XOR its encoded value, then clear the temporary flag. -/
def lengthInitializeCase (controls : List Wire) (pattern : Nat) (targets : List Wire)
    (encoded : Nat) (flag : Wire) (scratches : List Wire) (known : Nat) : Circuit :=
  knownScratchControl controls pattern flag scratches known ++
    controlledXorConstant flag targets encoded ++
    knownScratchControl controls pattern flag scratches known

/-- A single source case changes precisely the encoded word selected by its prefix predicate. -/
theorem run_lengthInitializeCase (controls : List Wire) (pattern : Nat) (targets : List Wire)
    (encoded : Nat) (flag : Wire) (scratches : List Wire) (known : Nat) (state : BasisState)
    (hlayout : ComputeControlLayout controls flag scratches)
    (htargets : ∀ wire ∈ targets, wire ∉ controls ∧ wire ≠ flag ∧ wire ∉ scratches)
    (hknown : wireValues scratches state = constantBits scratches.length known)
    (hflag : state flag = false) :
    run (lengthInitializeCase controls pattern targets encoded flag scratches known) state =
      xorConstantState (registerMatches controls pattern state) targets encoded state := by
  let predicate := registerMatches controls pattern state
  let flagged := state[flag ↦ predicate]
  let written := xorConstantState predicate targets encoded flagged
  have hflagout : flag ∉ targets := by
    intro hm
    exact (htargets flag hm).2.1 rfl
  have hfirst : run (knownScratchControl controls pattern flag scratches known) state = flagged := by
    rw [run_knownScratchControl controls pattern flag scratches known state hlayout hknown, hflag]
    simp [flagged, predicate]
  have hwrite : run (controlledXorConstant flag targets encoded) flagged = written := by
    rw [run_controlledXorConstant flag targets encoded flagged (by
      intro w hw; exact Ne.symm (htargets w hw).2.1)]
    simp [written, flagged]
  have hparts := List.nodup_append.mp hlayout.2
  have hflagScratch := (List.nodup_cons.mp hparts.2.1).1
  have hflagControls : flag ∉ controls := by
    intro hf
    exact hparts.2.2 flag hf flag (by simp) rfl
  have hwoutside (wire : Wire) (hw : wire ∉ targets) (hf : wire ≠ flag) :
      written wire = state wire := by
    rw [show written wire = xorConstantState predicate targets encoded flagged wire by rfl,
      xorConstantState_preservesOutside predicate targets encoded flagged wire hw]
    simp [flagged, upd, hf]
  have hknown' : wireValues scratches written = constantBits scratches.length known := by
    rw [← hknown]
    apply List.map_congr_left
    intro w hw
    exact hwoutside w (by intro hm; exact (htargets w hm).2.2 hw)
      (by intro he; subst w; exact hflagScratch hw)
  have hpred : registerMatches controls pattern written = predicate := by
    apply matches_agrees controls pattern 0 written state
    intro w hw
    exact hwoutside w (by intro hm; exact (htargets w hm).1 hw)
      (by intro he; subst w; exact hflagControls hw)
  have hflag' : written flag = predicate := by
    exact (xorConstantState_preservesOutside predicate targets encoded flagged flag hflagout).trans (by simp [flagged, upd])
  rw [lengthInitializeCase, run_append, run_append, hfirst, hwrite,
    run_knownScratchControl controls pattern flag scratches known written hlayout hknown',
    hpred, hflag', Bool.xor_self]
  rw [show written = (xorConstantState predicate targets encoded state)[flag ↦ predicate] from
    xorState_upd_outside predicate targets encoded state flag predicate hflagout]
  change ((xorConstantState predicate targets encoded state)[flag ↦ predicate])[flag ↦ false] =
    xorConstantState predicate targets encoded state
  funext w
  by_cases hw : w = flag
  · subst w
    simp [upd, xorConstantState_preservesOutside predicate targets encoded state flag hflagout, hflag]
  · simp [upd, hw]

theorem lengthInitializeCase_wellFormed (controls : List Wire) (pattern : Nat)
    (targets : List Wire) (encoded : Nat) (flag : Wire) (scratches : List Wire) (known : Nat)
    (hlayout : ComputeControlLayout controls flag scratches)
    (htargets : ∀ wire ∈ targets, flag ≠ wire) :
    CircuitWellFormed (lengthInitializeCase controls pattern targets encoded flag scratches known) := by
  simp only [lengthInitializeCase, circuitWellFormed_append]
  exact ⟨⟨knownScratchControl_wellFormed controls pattern flag scratches known hlayout,
    controlledXorConstant_wellFormed flag targets encoded htargets⟩,
    knownScratchControl_wellFormed controls pattern flag scratches known hlayout⟩

/-- Gate costs are derived from the explicit two predicate computations and selected XOR. -/
theorem lengthInitializeCase_counts (controls : List Wire) (pattern : Nat)
    (targets : List Wire) (encoded : Nat) (flag : Wire) (scratches : List Wire) (known : Nat)
    (henough : controls.length - 2 ≤ scratches.length) :
    eeaToffoliCount (lengthInitializeCase controls pattern targets encoded flag scratches known) =
        2 * mcxVChainToffoliCost controls.length ∧
    eeaCnotCount (lengthInitializeCase controls pattern targets encoded flag scratches known) =
        2 * mcxVChainCnotCost controls.length + lowBitCount targets.length encoded ∧
    ShorECDLP.tCount (lengthInitializeCase controls pattern targets encoded flag scratches known) =
        14 * mcxVChainToffoliCost controls.length := by
  have h := knownScratchControl_counts controls pattern flag scratches known henough
  simp only [lengthInitializeCase, eeaToffoliCount_append, eeaCnotCount_append, tCount_append,
    h.1, h.2.1, h.2.2, controlledXorConstant_toffoliCount,
    controlledXorConstant_cnotCount, controlledXorConstant_tCount]
  omega

theorem registerMatchesFrom_iff (controls : List Wire) (value bit : Nat) (state : BasisState) :
    registerMatchesFrom controls value bit state = true ↔
      ∀ i (hi : i < controls.length), state controls[i] = value.testBit (bit + i) := by
  induction controls generalizing bit with
  | nil => simp [registerMatchesFrom]
  | cons wire controls ih =>
      simp only [registerMatchesFrom, Bool.and_eq_true, decide_eq_true_eq]
      rw [ih]
      constructor
      · rintro ⟨hhead, htail⟩ i hi
        cases i with
        | zero => simpa using hhead
        | succ i => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail i (by simpa using hi)
      · intro h
        constructor
        · simpa using h 0 (by simp)
        · intro i hi
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i+1) (by simpa using hi)

/-- Each prefix detector is true exactly at the first set input bit. -/
theorem lengthInitialize_prefix_match (input : List Wire) (first : Nat)
    (state : BasisState) (hfirst : first < input.length) :
    registerMatches (input.take (first + 1)) (2 ^ first) state =
      decide (input.findIdx state = first) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, List.findIdx_eq hfirst]
  change registerMatchesFrom (input.take (first+1)) (2^first) 0 state = true ↔ _
  rw [registerMatchesFrom_iff]
  simp only [Nat.zero_add, Nat.testBit_two_pow]
  constructor
  · intro h
    constructor
    · have ht := h first (by simp [List.length_take]; omega)
      simpa using ht
    · intro j hj
      have ht := h j (by simp [List.length_take]; omega)
      simpa [show first ≠ j by omega] using ht
  · rintro ⟨hhead, htail⟩ i hi
    have hil : i ≤ first := by simp only [List.length_take] at hi; omega
    by_cases he : i = first
    · subst i; simpa using hhead
    · simpa [show first ≠ i by omega] using htail i (by omega)

theorem lengthInitialize_zero_match (input : List Wire) (state : BasisState) :
    registerMatches input 0 state = decide (input.findIdx state = input.length) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, List.findIdx_eq_length]
  change registerMatchesFrom input 0 0 state = true ↔ _
  rw [registerMatchesFrom_iff]
  simp only [Nat.zero_add, Nat.zero_testBit]
  constructor
  · intro h wire hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    exact h i hi
  · intro h i hi
    exact h _ (List.getElem_mem hi)

/-- Source first-one cases followed by the all-zero sentinel case. Controls are in
big-endian input order; `pattern` is little-endian over each prefix. -/
def lengthInitializeCases (input : List Wire) (width : Nat) : List (List Wire × Nat × Nat) :=
  (List.range input.length).map (fun first =>
    (input.take (first + 1), 2 ^ first, input.length - first - 1)) ++
    [(input, 0, 2 ^ width - 1)]

/-- Explicit first-one scan with known-modulus v-chain scratch reuse. -/
def lengthInitializeScan (targets : List Wire) (flag : Wire) (scratches : List Wire)
    (known : Nat) : List (List Wire × Nat × Nat) → Circuit
  | [] => []
  | (controls, pattern, encoded) :: cases =>
      lengthInitializeCase controls pattern targets encoded flag scratches known ++
        lengthInitializeScan targets flag scratches known cases

/-- The pinned length initializer with its formerly abstract MCX operations lowered explicitly. -/
def lengthInitialize (input targets : List Wire) (flag : Wire) (scratches : List Wire)
    (known : Nat) : Circuit :=
  lengthInitializeScan targets flag scratches known (lengthInitializeCases input targets.length)

/-- The selected encoded-XOR recurrence on the output word. Predicates read the original input. -/
def lengthInitializeWord (state : BasisState) : List (List Wire × Nat × Nat) → List Bool → List Bool
  | [], bits => bits
  | (controls, pattern, encoded) :: cases, bits =>
      lengthInitializeWord state cases
        (gatedXorConstantBits (registerMatches controls pattern state) bits encoded)

private theorem lengthInitializeWord_append (state : BasisState)
    (left right : List (List Wire × Nat × Nat)) (bits : List Bool) :
    lengthInitializeWord state (left ++ right) bits =
      lengthInitializeWord state right (lengthInitializeWord state left bits) := by
  induction left generalizing bits with
  | nil => rfl
  | cons row left ih =>
      rcases row with ⟨controls, pattern, encoded⟩
      exact ih _

private theorem lengthInitializeWord_indices (input : List Wire) (state : BasisState)
    (indices : List Nat) (hnd : indices.Nodup) (hbound : ∀ i ∈ indices, i < input.length)
    (bits : List Bool) :
    lengthInitializeWord state (indices.map (fun first =>
      (input.take (first+1), 2^first, input.length-first-1))) bits =
      if input.findIdx state ∈ indices then
        xorConstantBits bits (input.length-input.findIdx state-1) else bits := by
  induction indices generalizing bits with
  | nil => simp [lengthInitializeWord]
  | cons first indices ih =>
      have hn := List.nodup_cons.mp hnd
      have hb : first < input.length := hbound first (by simp)
      have htail : ∀ i ∈ indices, i < input.length := by intro i hi; exact hbound i (by simp [hi])
      simp only [List.map_cons, lengthInitializeWord, lengthInitialize_prefix_match input first state hb]
      rw [ih hn.2 htail]
      by_cases he : input.findIdx state = first
      · have hnot : input.findIdx state ∉ indices := by simpa [he] using hn.1
        simp [he, hnot, hn.1, gatedXorConstantBits]
      · simp [he, gatedXorConstantBits]

/-- The source scan writes the encoded position of the highest set bit, with all-ones
as the zero-input sentinel. This is the bit-length-minus-one encoding, truncated to the target. -/
theorem lengthInitializeWord_correct (input : List Wire) (width : Nat)
    (state : BasisState) (bits : List Bool) :
    lengthInitializeWord state (lengthInitializeCases input width) bits =
      xorConstantBits bits (if input.findIdx state < input.length then
        input.length - input.findIdx state - 1 else 2 ^ width - 1) := by
  rw [lengthInitializeCases, lengthInitializeWord_append,
    lengthInitializeWord_indices input state (List.range input.length)
      List.nodup_range (by intro i hi; exact List.mem_range.mp hi)]
  simp only [lengthInitializeWord, lengthInitialize_zero_match, List.mem_range]
  have hle := List.findIdx_le_length (xs := input) (p := state)
  by_cases h : input.findIdx state < input.length
  · have hn : input.findIdx state ≠ input.length := by omega
    simp [h, hn, gatedXorConstantBits]
  · have he : input.findIdx state = input.length := by omega
    simp [h, he, gatedXorConstantBits]

private theorem lengthInitializeWord_agrees (cases : List (List Wire × Nat × Nat))
    (left right : BasisState)
    (h : ∀ row ∈ cases, ∀ wire ∈ row.1, left wire = right wire) (bits : List Bool) :
    lengthInitializeWord left cases bits = lengthInitializeWord right cases bits := by
  induction cases generalizing bits with
  | nil => rfl
  | cons row cases ih =>
      rcases row with ⟨controls, pattern, encoded⟩
      have hp := matches_agrees controls pattern 0 left right (h (controls, pattern, encoded) (by simp))
      simp only [lengthInitializeWord]
      rw [show registerMatches controls pattern left = registerMatches controls pattern right from hp]
      exact ih (by intro row hr; exact h row (by simp [hr])) _

/-- The complete scan XORs exactly its source-selected encodings and changes no other wire.
The scratch constant and clean flag are restored after every case, not assumed at the end. -/
theorem run_lengthInitializeScan (targets : List Wire) (flag : Wire) (scratches : List Wire)
    (known : Nat) (cases : List (List Wire × Nat × Nat)) (state : BasisState)
    (hnd : targets.Nodup)
    (hlayout : ∀ row ∈ cases, ComputeControlLayout row.1 flag scratches)
    (htargets : ∀ row ∈ cases, ∀ wire ∈ targets, wire ∉ row.1 ∧ wire ≠ flag ∧ wire ∉ scratches)
    (hknown : wireValues scratches state = constantBits scratches.length known)
    (hflag : state flag = false) :
    wireValues targets (run (lengthInitializeScan targets flag scratches known cases) state) =
        lengthInitializeWord state cases (wireValues targets state) ∧
      ∀ wire, wire ∉ targets →
        run (lengthInitializeScan targets flag scratches known cases) state wire = state wire := by
  induction cases generalizing state with
  | nil => simp [lengthInitializeScan, lengthInitializeWord, run]
  | cons row cases ih =>
      rcases row with ⟨controls, pattern, encoded⟩
      let first := xorConstantState (registerMatches controls pattern state) targets encoded state
      have ht := htargets (controls, pattern, encoded) (by simp)
      have hf : first flag = state flag := xorConstantState_preservesOutside _ _ _ _ flag (by
        intro hm; exact (ht flag hm).2.1 rfl)
      have hk : wireValues scratches first = wireValues scratches state := by
        apply List.map_congr_left
        intro wire hw
        exact xorConstantState_preservesOutside _ _ _ _ wire (by
          intro hm; exact (ht wire hm).2.2 hw)
      have hrec := ih first
        (by intro row hr; exact hlayout row (by simp [hr]))
        (by intro row hr; exact htargets row (by simp [hr])) (hk.trans hknown) (hf.trans hflag)
      rw [lengthInitializeScan, run_append,
        run_lengthInitializeCase controls pattern targets encoded flag scratches known state
          (hlayout (controls, pattern, encoded) (by simp)) ht hknown hflag]
      constructor
      · rw [hrec.1]
        rw [lengthInitializeWord_agrees cases first state (by
          intro row hr wire hw
          exact xorConstantState_preservesOutside _ _ _ _ wire (by
            intro hm; exact (htargets row (by simp [hr]) wire hm).1 hw))]
        rw [wireValues_xorConstantState _ targets encoded state hnd]
        rfl
      · intro wire hw
        exact (hrec.2 wire hw).trans (xorConstantState_preservesOutside _ _ _ _ wire hw)

private theorem lengthInitializeCase_layout (input : List Wire) (width : Nat)
    (flag : Wire) (scratches : List Wire)
    (hlayout : ComputeControlLayout input flag scratches)
    (row : List Wire × Nat × Nat) (hrow : row ∈ lengthInitializeCases input width) :
    ComputeControlLayout row.1 flag scratches ∧ row.1 ⊆ input := by
  have hparts := List.nodup_append.mp hlayout.2
  simp only [lengthInitializeCases, List.mem_append, List.mem_map, List.mem_singleton] at hrow
  rcases hrow with ⟨first, _, rfl⟩ | rfl
  · have hsub : input.take (first+1) ⊆ input := List.take_subset _ _
    constructor
    · constructor
      · simp only [List.length_take]
        have := hlayout.1
        omega
      · exact List.nodup_append.mpr ⟨hparts.1.take, hparts.2.1,
          fun a ha b hb => hparts.2.2 a (hsub ha) b hb⟩
    · exact hsub
  · exact ⟨hlayout, List.Subset.refl _⟩

/-- Direct source initializer contract: XOR the input's bit-length-minus-one encoding into
an arbitrary target word, preserving every other wire including the known workspace. -/
theorem lengthInitialize_correct (input targets : List Wire) (flag : Wire) (scratches : List Wire)
    (known : Nat) (state : BasisState) (hnd : targets.Nodup)
    (hlayout : ComputeControlLayout input flag scratches)
    (htargets : ∀ wire ∈ targets, wire ∉ input ∧ wire ≠ flag ∧ wire ∉ scratches)
    (hknown : wireValues scratches state = constantBits scratches.length known)
    (hflag : state flag = false) :
    wireValues targets (run (lengthInitialize input targets flag scratches known) state) =
        xorConstantBits (wireValues targets state)
          (if input.findIdx state < input.length then input.length-input.findIdx state-1
            else 2 ^ targets.length - 1) ∧
      ∀ wire, wire ∉ targets →
        run (lengthInitialize input targets flag scratches known) state wire = state wire := by
  have h := run_lengthInitializeScan targets flag scratches known
    (lengthInitializeCases input targets.length) state hnd
    (fun row hr => (lengthInitializeCase_layout input targets.length flag scratches hlayout row hr).1)
    (by
      intro row hr wire hw
      have ht := htargets wire hw
      exact ⟨fun hm => ht.1
        ((lengthInitializeCase_layout input targets.length flag scratches hlayout row hr).2 hm), ht.2⟩)
    hknown hflag
  rw [lengthInitializeWord_correct] at h
  exact h

theorem lengthInitializeScan_wellFormed (targets : List Wire) (flag : Wire)
    (scratches : List Wire) (known : Nat) (cases : List (List Wire × Nat × Nat))
    (hlayout : ∀ row ∈ cases, ComputeControlLayout row.1 flag scratches)
    (htargets : ∀ wire ∈ targets, flag ≠ wire) :
    CircuitWellFormed (lengthInitializeScan targets flag scratches known cases) := by
  induction cases with
  | nil => simp [lengthInitializeScan]
  | cons row cases ih =>
      rcases row with ⟨controls, pattern, encoded⟩
      rw [lengthInitializeScan, circuitWellFormed_append]
      exact ⟨lengthInitializeCase_wellFormed controls pattern targets encoded flag scratches known
        (hlayout (controls, pattern, encoded) (by simp)) htargets,
        ih (by intro row hr; exact hlayout row (by simp [hr]))⟩

/-- Closed physical layout for the full source scan. -/
theorem lengthInitialize_wellFormed (input targets : List Wire) (flag : Wire)
    (scratches : List Wire) (known : Nat)
    (hlayout : ComputeControlLayout input flag scratches)
    (htargets : ∀ wire ∈ targets, flag ≠ wire) :
    CircuitWellFormed (lengthInitialize input targets flag scratches known) :=
  lengthInitializeScan_wellFormed targets flag scratches known _
    (fun row hr => (lengthInitializeCase_layout input targets.length flag scratches hlayout row hr).1)
    htargets

theorem lengthInitializeScan_counts (targets : List Wire) (flag : Wire)
    (scratches : List Wire) (known : Nat) (cases : List (List Wire × Nat × Nat))
    (henough : ∀ row ∈ cases, row.1.length - 2 ≤ scratches.length) :
    eeaToffoliCount (lengthInitializeScan targets flag scratches known cases) =
        (cases.map (fun row => 2 * mcxVChainToffoliCost row.1.length)).sum ∧
    eeaCnotCount (lengthInitializeScan targets flag scratches known cases) =
        (cases.map (fun row => 2 * mcxVChainCnotCost row.1.length +
          lowBitCount targets.length row.2.2)).sum ∧
    ShorECDLP.tCount (lengthInitializeScan targets flag scratches known cases) =
        (cases.map (fun row => 14 * mcxVChainToffoliCost row.1.length)).sum := by
  induction cases with
  | nil => simp [lengthInitializeScan, eeaToffoliCount, eeaCnotCount, tCount]
  | cons row cases ih =>
      rcases row with ⟨controls, pattern, encoded⟩
      have h := lengthInitializeCase_counts controls pattern targets encoded flag scratches known
        (henough (controls, pattern, encoded) (by simp))
      have ht := ih (by intro row hr; exact henough row (by simp [hr]))
      simp [lengthInitializeScan, eeaToffoliCount_append, eeaCnotCount_append, tCount_append,
        h.1, h.2.1, h.2.2, ht.1, ht.2.1, ht.2.2]

/-- Exact initializer costs depend on predicate widths and target bits, not labels. -/
theorem lengthInitialize_counts (input targets : List Wire) (flag : Wire)
    (scratches : List Wire) (known : Nat) (henough : input.length - 2 ≤ scratches.length) :
    let cases := lengthInitializeCases input targets.length
    eeaToffoliCount (lengthInitialize input targets flag scratches known) =
        (cases.map (fun row => 2 * mcxVChainToffoliCost row.1.length)).sum ∧
    eeaCnotCount (lengthInitialize input targets flag scratches known) =
        (cases.map (fun row => 2 * mcxVChainCnotCost row.1.length + lowBitCount targets.length row.2.2)).sum ∧
    ShorECDLP.tCount (lengthInitialize input targets flag scratches known) =
        (cases.map (fun row => 14 * mcxVChainToffoliCost row.1.length)).sum := by
  apply lengthInitializeScan_counts
  intro row hr
  simp only [lengthInitializeCases, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨first, _, rfl⟩ | rfl
  · simp only [List.length_take]
    omega
  · exact henough

theorem lengthInitializeScan_HPFree (targets : List Wire) (flag : Wire)
    (scratches : List Wire) (known : Nat) (cases : List (List Wire × Nat × Nat)) :
    HPFree (lengthInitializeScan targets flag scratches known cases) := by
  induction cases with
  | nil => simp [lengthInitializeScan]
  | cons row cases ih =>
      rcases row with ⟨controls, pattern, encoded⟩
      simp [lengthInitializeScan, lengthInitializeCase, hpFree_append,
        knownScratchControl_HPFree, controlledXorConstant_HPFree, ih]

theorem lengthInitialize_HPFree (input targets : List Wire) (flag : Wire)
    (scratches : List Wire) (known : Nat) :
    HPFree (lengthInitialize input targets flag scratches known) :=
  lengthInitializeScan_HPFree targets flag scratches known _

private theorem lengthInitializeCase_usesOnly (input controls : List Wire) (pattern : Nat)
    (targets : List Wire) (encoded : Nat) (flag : Wire) (scratches : List Wire) (known : Nat)
    (hsub : controls ⊆ input) :
    PaperCircuitUsesOnly (input ++ targets ++ flag :: scratches)
      (lengthInitializeCase controls pattern targets encoded flag scratches known) := by
  have hc : PaperCircuitUsesOnly (input ++ targets ++ flag :: scratches)
      (knownScratchControl controls pattern flag scratches known) :=
    (knownScratchControl_usesOnly controls pattern flag scratches known).mono (by
      intro wire hw
      simp only [List.mem_append, List.mem_cons] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inl (Or.inl (hsub hw))
      · exact Or.inr hw)
  have hx : PaperCircuitUsesOnly (input ++ targets ++ flag :: scratches)
      (controlledXorConstant flag targets encoded) :=
    (controlledXorConstant_usesOnly flag targets encoded).mono (by
      intro wire hw
      simp only [List.mem_append, List.mem_cons] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inl (Or.inr hw))
  exact (hc.append hx).append hc

private theorem lengthInitializeScan_usesOnly (input targets : List Wire) (flag : Wire)
    (scratches : List Wire) (known : Nat) (cases : List (List Wire × Nat × Nat))
    (hsub : ∀ row ∈ cases, row.1 ⊆ input) :
    PaperCircuitUsesOnly (input ++ targets ++ flag :: scratches)
      (lengthInitializeScan targets flag scratches known cases) := by
  induction cases with
  | nil => simp [lengthInitializeScan, PaperCircuitUsesOnly]
  | cons row cases ih =>
      rcases row with ⟨controls, pattern, encoded⟩
      exact (lengthInitializeCase_usesOnly input controls pattern targets encoded flag scratches known
        (hsub (controls, pattern, encoded) (by simp))).append
          (ih (by intro row hr; exact hsub row (by simp [hr])))

theorem lengthInitialize_usesOnly (input targets : List Wire) (flag : Wire)
    (scratches : List Wire) (known : Nat)
    (hlayout : ComputeControlLayout input flag scratches) :
    PaperCircuitUsesOnly (input ++ targets ++ flag :: scratches)
      (lengthInitialize input targets flag scratches known) :=
  lengthInitializeScan_usesOnly input targets flag scratches known _
    (fun row hr => (lengthInitializeCase_layout input targets.length flag scratches hlayout row hr).2)

set_option maxRecDepth 10000

/-- Production lowering: 256 input bits, nine encoded-length bits, one clean flag and
254 reusable bits from a known modulus register. Input order is big-endian. -/
def secp256k1LengthInitialize : Circuit :=
  lengthInitialize (List.range 256) (List.range' 256 9) 265 (List.range' 266 254)
    (2 ^ 256 - 2 ^ 32 - 977)

private theorem lengthProduction_layout :
    ComputeControlLayout (List.range 256) 265 (List.range' 266 254) := by
  constructor
  · simp
  · apply List.nodup_append.mpr
    refine ⟨List.nodup_range, ?_, ?_⟩
    · exact List.nodup_cons.mpr ⟨by simp, List.nodup_range'⟩
    · intro a ha b hb he
      simp only [List.mem_range, List.mem_cons, List.mem_range'] at ha hb
      dsimp only [Wire] at *
      omega

private theorem lengthProduction_targets :
    ∀ wire ∈ List.range' 256 9,
      wire ∉ List.range 256 ∧ wire ≠ 265 ∧ wire ∉ List.range' 266 254 := by
  intro wire hw
  simp only [List.mem_range', List.mem_range] at hw ⊢
  omega

set_option maxRecDepth 10000 in
private theorem lengthProduction_costs :
    let cases := lengthInitializeCases (List.range 256) 9
    (cases.map (fun row => 2 * mcxVChainToffoliCost row.1.length)).sum = 131068 ∧
    (cases.map (fun row => 2 * mcxVChainCnotCost row.1.length + lowBitCount 9 row.2.2)).sum = 1035 ∧
    (cases.map (fun row => 14 * mcxVChainToffoliCost row.1.length)).sum = 917476 := by
  decide

private theorem lengthProduction_counts :
    eeaToffoliCount secp256k1LengthInitialize = 131068 ∧
    eeaCnotCount secp256k1LengthInitialize = 1035 ∧
    ShorECDLP.tCount secp256k1LengthInitialize = 917476 := by
  have h := lengthInitializeScan_counts (List.range' 256 9) 265 (List.range' 266 254)
    (2 ^ 256 - 2 ^ 32 - 977) (lengthInitializeCases (List.range 256) 9)
    (fun row hr => (lengthInitializeCase_layout (List.range 256) 9 265
      (List.range' 266 254) lengthProduction_layout row hr).1.1)
  have hc := lengthProduction_costs
  simp only [List.length_range'] at h
  exact ⟨h.1.trans hc.1, h.2.1.trans hc.2.1, h.2.2.trans hc.2.2⟩

private theorem knownScratch_qubit_bound {support : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly support circuit) : qubitCount circuit ≤ support.length := by
  have hsub : (circuitWires circuit).toFinset ⊆ support.toFinset := by
    intro wire hw
    simp only [List.mem_toFinset] at hw ⊢
    obtain ⟨gate, hg, hw⟩ := List.mem_flatMap.mp hw
    exact huses gate hg wire hw
  have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le support)
  rw [qubitCount, ← List.toFinset_card_of_nodup (List.nodup_dedup _)]
  have he : (circuitWires circuit).dedup.toFinset = (circuitWires circuit).toFinset := by
    ext wire; simp
  rw [he]
  exact hcard

private theorem lengthProduction_qubits : qubitCount secp256k1LengthInitialize ≤ 520 := by
  have huses := lengthInitialize_usesOnly (List.range 256) (List.range' 256 9) 265
    (List.range' 266 254) (2 ^ 256 - 2 ^ 32 - 977) lengthProduction_layout
  have h := knownScratch_qubit_bound huses
  simpa only [List.length_append, List.length_range, List.length_range', List.length_cons] using h

attribute [local irreducible] secp256k1LengthInitialize lengthInitialize lengthInitializeScan

/-- One concrete initializer carries semantics, frame restoration, physical well-formedness,
classical-gate refinement and constructor-derived resources. The 520 bound includes the reused
known workspace; these are the costs of this explicit lowering, not Qiskit's abstract MCX. -/
theorem secp256k1LengthInitialize_correct_resources (state : BasisState)
    (hknown : wireValues (List.range' 266 254) state =
      constantBits 254 (2 ^ 256 - 2 ^ 32 - 977)) (hflag : state 265 = false) :
    wireValues (List.range' 256 9) (run secp256k1LengthInitialize state) =
        xorConstantBits (wireValues (List.range' 256 9) state)
          (if (List.range 256).findIdx state < 256 then
            256 - (List.range 256).findIdx state - 1 else 511) ∧
    (∀ wire, wire ∉ List.range' 256 9 → run secp256k1LengthInitialize state wire = state wire) ∧
    CircuitWellFormed secp256k1LengthInitialize ∧ HPFree secp256k1LengthInitialize ∧
    eeaToffoliCount secp256k1LengthInitialize = 131068 ∧
    eeaCnotCount secp256k1LengthInitialize = 1035 ∧
    ShorECDLP.tCount secp256k1LengthInitialize = 917476 ∧
    qubitCount secp256k1LengthInitialize ≤ 520 := by
  have hs := lengthInitialize_correct (List.range 256) (List.range' 256 9) 265
    (List.range' 266 254) (2 ^ 256 - 2 ^ 32 - 977) state List.nodup_range'
    lengthProduction_layout lengthProduction_targets hknown hflag
  have hw := lengthInitialize_wellFormed (List.range 256) (List.range' 256 9) 265
    (List.range' 266 254) (2 ^ 256 - 2 ^ 32 - 977) lengthProduction_layout
    (fun wire hw => Ne.symm (lengthProduction_targets wire hw).2.1)
  have hf := lengthInitialize_HPFree (List.range 256) (List.range' 256 9) 265
    (List.range' 266 254) (2 ^ 256 - 2 ^ 32 - 977)
  simp only [List.length_range, List.length_range', show 2^9-1=511 by decide] at hs
  have hc := lengthProduction_counts
  have hq := lengthProduction_qubits
  unfold secp256k1LengthInitialize at hc hq ⊢
  exact ⟨hs.1, hs.2, hw, hf, hc.1, hc.2.1, hc.2.2, hq⟩

/-- Source length initialization is an XOR update, hence clears itself on the same input. -/
theorem lengthInitialize_twice (input targets : List Wire) (flag : Wire) (scratches : List Wire)
    (known : Nat) (state : BasisState) (hnd : targets.Nodup)
    (hlayout : ComputeControlLayout input flag scratches)
    (htargets : ∀ wire ∈ targets, wire ∉ input ∧ wire ≠ flag ∧ wire ∉ scratches)
    (hknown : wireValues scratches state = constantBits scratches.length known)
    (hflag : state flag = false) :
    run (lengthInitialize input targets flag scratches known)
      (run (lengthInitialize input targets flag scratches known) state) = state := by
  let next := run (lengthInitialize input targets flag scratches known) state
  have hfirst := lengthInitialize_correct input targets flag scratches known state
    hnd hlayout htargets hknown hflag
  have hinput : ∀ w ∈ input, next w = state w := by
    intro w hw
    exact hfirst.2 w (fun hm => (htargets w hm).1 hw)
  have hscratch : wireValues scratches next = wireValues scratches state := by
    apply List.map_congr_left
    intro w hw
    exact hfirst.2 w (fun hm => (htargets w hm).2.2 hw)
  have hnextflag : next flag = false := by
    exact (hfirst.2 flag (fun hm => (htargets flag hm).2.1 rfl)).trans hflag
  have hfind : input.findIdx next = input.findIdx state := by
    have hm : wireValues input next = wireValues input state := List.map_congr_left hinput
    simpa only [wireValues, List.findIdx_map, Function.comp_def] using
      congrArg (List.findIdx id) hm
  have hsecond := lengthInitialize_correct input targets flag scratches known next
    hnd hlayout htargets (hscratch.trans hknown) hnextflag
  rw [hfind, hfirst.1, xorConstantBits_involutive] at hsecond
  funext w
  by_cases hw : w ∈ targets
  · have hvalues := hsecond.1
    change wireValues targets _ = wireValues targets _ at hvalues
    have hex : ∀ (ws : List Wire) (a b : BasisState), wireValues ws a = wireValues ws b →
        ∀ v ∈ ws, a v = b v := by
      intro ws a b he
      induction ws with
      | nil => simp
      | cons x xs ih =>
        simp only [wireValues, List.map_cons, List.cons.injEq] at he
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact he.1
        · exact ih he.2 v hv
    exact hex targets _ _ hvalues w hw
  · exact (hsecond.2 w hw).trans (hfirst.2 w hw)

end ShorECDLP.Paper2607_13816
