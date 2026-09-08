import ShorECDLP.Submission.«2607_13816».EEA.LengthInitialize

/-!
# Source work-bank preparation

The wrapper moves a little-endian input and three clean tail wires into the big-endian
Work2=[000,x] layout. These fixed-width streams preserve the source permutation builder's
swap order; each SWAP is explicitly lowered to three CX gates. The source-ordered Work1
constant toggle then initializes coefficient 1 and the modulus, and the two streams compose
into one bank-preparation circuit with an explicit full-state reverse.
-/

namespace ShorECDLP.Paper2607_13816
open _root_.ShorECDLP.Classical
set_option linter.unusedSimpArgs false

private def workSwap (a b : Wire) : Circuit := [.CX a b, .CX b a, .CX a b]
private def workSwapIndex (a b w : Nat) : Nat := if w = a then b else if w = b then a else w

private theorem run_workSwap (a b : Wire) (state : BasisState) (h : a ≠ b) (wire : Wire) :
    run (workSwap a b) state wire = state (workSwapIndex a b wire) := by
  by_cases ha : wire = a
  · subst wire
    cases hs : state a <;> cases ht : state b <;>
      simp [workSwap, workSwapIndex, run, applyGate, upd, h, Ne.symm h, hs, ht]
  · by_cases hb : wire = b
    · subst wire
      cases hs : state a <;> cases ht : state b <;>
        simp [workSwap, workSwapIndex, run, applyGate, upd, h, Ne.symm h, hs, ht]
    · simp [workSwap, workSwapIndex, run, applyGate, upd, ha, hb]

private def workSwapSequence (base : Nat) : List (Nat × Nat) → Circuit
  | [] => []
  | (a,b) :: pairs => workSwap (base+a) (base+b) ++ workSwapSequence base pairs

private def workPullback : List (Nat × Nat) → Nat → Nat
  | [], wire => wire
  | (a,b) :: pairs, wire => workSwapIndex a b (workPullback pairs wire)

private theorem workSwapIndex_offset (base a b wire : Nat) :
    workSwapIndex (base+a) (base+b) (base+wire) = base + workSwapIndex a b wire := by
  by_cases ha : wire = a
  · subst wire; simp [workSwapIndex]
  · by_cases hb : wire = b
    · subst wire; simp [workSwapIndex, ha]
    · simp [workSwapIndex, ha, hb]

private theorem run_workSwapSequence (base : Nat) (pairs : List (Nat × Nat))
    (state : BasisState) (h : ∀ pair ∈ pairs, pair.1 ≠ pair.2) (wire : Nat) :
    run (workSwapSequence base pairs) state (base+wire) = state (base+workPullback pairs wire) := by
  induction pairs generalizing state wire with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨a,b⟩
      rw [workSwapSequence, run_append,
        ih _ (by intro pair hp; exact h pair (by simp [hp])) wire,
        run_workSwap (base+a) (base+b) state (by
          have hn := h (a,b) (by simp)
          dsimp only at hn
          change base + a ≠ base + b
          omega), workSwapIndex_offset]
      rfl

/-- Swap list emitted by the source permutation builder on 256 input bits. -/
def work2PreparePairs : List (Nat × Nat) :=
  [(0,256),(1,257),(2,258)] ++ (List.range' 3 126).map (fun i => (i,258-i)) ++ [(256,258)]

/-- Swap list emitted by the same source builder on the inverse permutation. -/
def work2RestorePairs : List (Nat × Nat) :=
  [(0,258),(1,257),(2,256)] ++ (List.range' 3 126).map (fun i => (i,258-i)) ++ [(256,258)]

def work2Prepare (base : Nat) : Circuit := workSwapSequence base work2PreparePairs
def work2Restore (base : Nat) : Circuit := workSwapSequence base work2RestorePairs

set_option maxRecDepth 10000 in
private theorem work2Prepare_index :
    (∀ pair ∈ work2PreparePairs, pair.1 ≠ pair.2) ∧
    ∀ i : Fin 259, workPullback work2PreparePairs i =
      if i.val < 3 then 256+i.val else 258-i.val := by decide

set_option maxRecDepth 10000 in
private theorem work2Restore_index :
    (∀ pair ∈ work2RestorePairs, pair.1 ≠ pair.2) ∧
    ∀ i : Fin 259, workPullback work2RestorePairs i =
      if i.val < 256 then 258-i.val else i.val-256 := by decide

/-- Direct source-coordinate semantics, valid for arbitrary contents of the three tail wires. -/
theorem work2Prepare_correct (base : Nat) (state : BasisState) (i : Fin 259) :
    run (work2Prepare base) state (base+i.val) =
      state (base + if i.val < 3 then 256+i.val else 258-i.val) := by
  rw [work2Prepare, run_workSwapSequence base work2PreparePairs state work2Prepare_index.1,
    work2Prepare_index.2 i]

theorem work2Restore_correct (base : Nat) (state : BasisState) (i : Fin 259) :
    run (work2Restore base) state (base+i.val) =
      state (base + if i.val < 256 then 258-i.val else i.val-256) := by
  rw [work2Restore, run_workSwapSequence base work2RestorePairs state work2Restore_index.1,
    work2Restore_index.2 i]

private theorem workSwapSequence_usesOnly (base : Nat) (pairs : List (Nat × Nat))
    (h : ∀ pair ∈ pairs, pair.1 < 259 ∧ pair.2 < 259) :
    PaperCircuitUsesOnly (List.range' base 259) (workSwapSequence base pairs) := by
  induction pairs with
  | nil => simp [workSwapSequence, PaperCircuitUsesOnly]
  | cons pair pairs ih =>
      rcases pair with ⟨a,b⟩
      have hp := h (a,b) (by simp)
      dsimp only at hp
      have ha : base+a ∈ List.range' base 259 := by simp; omega
      have hb : base+b ∈ List.range' base 259 := by simp; omega
      apply PaperCircuitUsesOnly.append
      · simp [workSwap, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires, ha, hb, hp.1, hp.2]
      · exact ih (by intro pair hp; exact h pair (by simp [hp]))

private theorem workSwapSequence_wellFormed (base : Nat) (pairs : List (Nat × Nat))
    (h : ∀ pair ∈ pairs, pair.1 ≠ pair.2) : CircuitWellFormed (workSwapSequence base pairs) := by
  induction pairs with
  | nil => simp [workSwapSequence]
  | cons pair pairs ih =>
      rcases pair with ⟨a,b⟩
      have hp := h (a,b) (by simp)
      dsimp only at hp
      have hab : base+a ≠ base+b := by dsimp at hp; omega
      have hba : base+b ≠ base+a := Ne.symm hab
      rw [workSwapSequence, circuitWellFormed_append]
      exact ⟨by simp [workSwap, CircuitWellFormed, Gate.WellFormed, hab, hba, hp, Ne.symm hp],
        ih (by intro pair hp; exact h pair (by simp [hp]))⟩

private theorem workSwapSequence_resources (base : Nat) (pairs : List (Nat × Nat)) :
    HPFree (workSwapSequence base pairs) ∧
    eeaCnotCount (workSwapSequence base pairs) = 3 * pairs.length ∧
    eeaToffoliCount (workSwapSequence base pairs) = 0 ∧
    ShorECDLP.tCount (workSwapSequence base pairs) = 0 := by
  induction pairs with
  | nil => simp [workSwapSequence, eeaCnotCount, eeaToffoliCount, tCount]
  | cons pair pairs ih =>
      rcases pair with ⟨a,b⟩
      simp only [workSwapSequence, hpFree_append, eeaCnotCount_append,
        eeaToffoliCount_append, tCount_append, ih.1, ih.2.1, ih.2.2.1, ih.2.2.2,
        List.length_cons]
      simp [workSwap, eeaCnotCount, eeaToffoliCount, tCost]
      omega

set_option maxRecDepth 10000 in

private theorem work2Pairs_bounds :
    (∀ pair ∈ work2PreparePairs, pair.1 < 259 ∧ pair.2 < 259) ∧
    (∀ pair ∈ work2RestorePairs, pair.1 < 259 ∧ pair.2 < 259) ∧
    work2PreparePairs.length = 130 ∧ work2RestorePairs.length = 130 := by decide

theorem work2Prepare_frame (base : Nat) (state : BasisState) (wire : Wire)
    (hout : wire ∉ List.range' base 259) : run (work2Prepare base) state wire = state wire :=
  (workSwapSequence_usesOnly base work2PreparePairs work2Pairs_bounds.1).preservesOutside state hout

theorem work2Restore_frame (base : Nat) (state : BasisState) (wire : Wire)
    (hout : wire ∉ List.range' base 259) : run (work2Restore base) state wire = state wire :=
  (workSwapSequence_usesOnly base work2RestorePairs work2Pairs_bounds.2.1).preservesOutside state hout

theorem work2Prepare_resources (base : Nat) :
    CircuitWellFormed (work2Prepare base) ∧ HPFree (work2Prepare base) ∧
    eeaCnotCount (work2Prepare base) = 390 ∧
    eeaToffoliCount (work2Prepare base) = 0 ∧ ShorECDLP.tCount (work2Prepare base) = 0 := by
  have h := workSwapSequence_resources base work2PreparePairs
  rw [work2Pairs_bounds.2.2.1] at h
  exact ⟨workSwapSequence_wellFormed base work2PreparePairs work2Prepare_index.1, h⟩

theorem work2Restore_resources (base : Nat) :
    CircuitWellFormed (work2Restore base) ∧ HPFree (work2Restore base) ∧
    eeaCnotCount (work2Restore base) = 390 ∧
    eeaToffoliCount (work2Restore base) = 0 ∧ ShorECDLP.tCount (work2Restore base) = 0 := by
  have h := workSwapSequence_resources base work2RestorePairs
  rw [work2Pairs_bounds.2.2.2] at h
  exact ⟨workSwapSequence_wellFormed base work2RestorePairs work2Restore_index.1, h⟩

/-- The source reverse restores the entire basis state, including arbitrary tail contents. -/
theorem work2Restore_after_prepare (base : Nat) (state : BasisState) :
    run (work2Restore base) (run (work2Prepare base) state) = state := by
  funext wire
  by_cases hw : wire ∈ List.range' base 259
  · obtain ⟨i, hi, he⟩ := List.mem_range'.mp hw
    simp only [Nat.one_mul] at he
    subst wire
    rw [work2Restore_correct base (run (work2Prepare base) state) ⟨i,hi⟩]
    dsimp only
    by_cases h : i < 256
    · rw [if_pos h]
      have hj : 258-i < 259 := by omega
      rw [work2Prepare_correct base state ⟨258-i,hj⟩]
      dsimp only
      rw [if_neg (by omega : ¬258-i < 3)]
      exact congrArg state (congrArg (fun x : Nat => base+x) (by omega))
    · rw [if_neg h]
      have hj : i-256 < 259 := by omega
      rw [work2Prepare_correct base state ⟨i-256,hj⟩]
      dsimp only
      rw [if_pos (by omega : i-256 < 3)]
      exact congrArg state (congrArg (fun x : Nat => base+x) (by omega))
  · rw [work2Restore_frame base _ wire hw, work2Prepare_frame base state wire hw]

/-- Clean tail bits become the three leading zero bits required by Algorithm 3. -/
theorem work2Prepare_clean_header (base : Nat) (state : BasisState)
    (hclean : Clean (List.range' (base+256) 3) state) (i : Fin 3) :
    run (work2Prepare base) state (base+i.val) = false := by
  have hi : i.val < 259 := by have := i.isLt; omega
  rw [work2Prepare_correct base state ⟨i.val, hi⟩]
  simp only [i.isLt, if_true]
  exact hclean _ (List.mem_range'.mpr ⟨i.val, i.isLt, by simp [Nat.add_assoc]⟩)

/-- The prepared data portion is exactly the reversal of the original little-endian input. -/
theorem work2Prepare_input_bit (base : Nat) (state : BasisState) (i : Fin 256) :
    run (work2Prepare base) state (base+3+i.val) = state (base+255-i.val) := by
  have hi : 3+i.val < 259 := by have := i.isLt; omega
  have h := work2Prepare_correct base state ⟨3+i.val, hi⟩
  dsimp only at h
  simp only [show ¬3+i.val < 3 by omega, if_false] at h
  have hi255 : i.val ≤ 255 := by omega
  rw [Nat.add_sub_assoc hi255]
  simpa only [Nat.add_assoc, show 258-(3+i.val)=255-i.val by omega] using h

/-- Source `_toggle_work1_constant`: leading t=1 followed by the big-endian modulus. -/
def work1Load (base value : Nat) : Circuit :=
  [.X base] ++ (xorConstant (List.range' (base+3) 256).reverse value).adjoint

private theorem run_xorConstant_adjoint (register : List Wire) (value : Nat)
    (state : BasisState) (hnd : register.Nodup) :
    run (xorConstant register value).adjoint state = run (xorConstant register value) state := by
  have h := run_adjoint_run_classical (xorConstant register value)
    (xorConstant_wellFormed register value) (run (xorConstant register value) state)
  rw [run_xorConstant_twice register value state hnd] at h
  exact h

private theorem work1Load_state (base value : Nat) (state : BasisState) :
    run (work1Load base value) state =
      (run (xorConstant (List.range' (base+3) 256).reverse value) state)[base ↦ !state base] := by
  have hout : base ∉ (List.range' (base+3) 256).reverse := by simp
  rw [work1Load, run_append, run_xorConstant_adjoint _ _ _ (by simpa only [List.nodup_reverse] using (List.nodup_range' (s := base+3) (n := 256))),
    show run [.X base] state = state[base ↦ !state base] by rfl,
    (xorConstant_usesOnly _ value).run_upd_outside base _ state hout]

/-- Applying the constant toggle twice restores the entire state, without a clean-input premise. -/
theorem work1Load_twice (base value : Nat) (state : BasisState) :
    run (work1Load base value) (run (work1Load base value) state) = state := by
  have hout : base ∉ (List.range' (base+3) 256).reverse := by simp
  have huses := xorConstant_usesOnly (List.range' (base+3) 256).reverse value
  rw [work1Load_state, work1Load_state,
    huses.run_upd_outside base _ _ hout,
    run_xorConstant_twice _ value state (by simpa only [List.nodup_reverse] using (List.nodup_range' (s := base+3) (n := 256)))]
  funext wire
  by_cases hw : wire = base <;> simp [upd, hw]

private theorem work1_clean_word (wires : List Wire) (state : BasisState)
    (h : Clean wires state) : wireValues wires state = List.replicate wires.length false := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      simp only [wireValues, List.map_cons, List.length_cons, List.replicate_succ]
      exact congrArg₂ List.cons (h wire (by simp)) (ih (by intro w hw; exact h w (by simp [hw])))

/-- The loaded modulus word is little-endian when read in reverse Work1 data order. -/
theorem work1Load_word (base value : Nat) (state : BasisState)
    (hclean : Clean (List.range' (base+3) 256) state) :
    wireValues (List.range' (base+3) 256).reverse (run (work1Load base value) state) =
      constantBits 256 value := by
  have hnd : (List.range' (base+3) 256).reverse.Nodup := by simpa only [List.nodup_reverse] using (List.nodup_range' (s := base+3) (n := 256))
  have hc : Clean (List.range' (base+3) 256).reverse state := by
    intro w hw; exact hclean w (by simpa using hw)
  have hx := (xorConstant_correct (List.range' (base+3) 256).reverse value state hnd).1
  rw [work1_clean_word _ state hc] at hx
  rw [work1Load_state]
  have hframe : wireValues (List.range' (base+3) 256).reverse
      ((run (xorConstant (List.range' (base+3) 256).reverse value) state)[base ↦ !state base]) =
      wireValues (List.range' (base+3) 256).reverse
        (run (xorConstant (List.range' (base+3) 256).reverse value) state) := by
    apply List.map_congr_left
    intro wire hw
    have he : wire ≠ base := by
      have hm : wire ∈ List.range' (base+3) 256 := by simpa using hw
      obtain ⟨i, hi, he⟩ := List.mem_range'.mp hm
      simp only [Nat.one_mul] at he
      intro hb
      have heq : base = base+3+i := by simpa [hb] using he
      exact (Nat.ne_of_lt (by omega : base < base+3+i)) heq
    simp [upd, he]
  rw [hframe, hx]
  simp only [List.length_reverse, List.length_range']
  rfl

/-- The source's leading coefficient bit is toggled independently of the modulus data. -/
theorem work1Load_header (base value : Nat) (state : BasisState) :
    run (work1Load base value) state base = !state base := by
  rw [work1Load_state]
  simp

theorem work1Load_frame (base value : Nat) (state : BasisState) (wire : Wire)
    (hout : wire ∉ base :: List.range' (base+3) 256) :
    run (work1Load base value) state wire = state wire := by
  simp only [List.mem_cons, not_or] at hout
  rw [work1Load_state]
  simp only [upd, hout.1, if_false]
  exact (xorConstant_usesOnly _ value).preservesOutside state (by simpa using hout.2)

private theorem work1_hpFree_adjoint {circuit : Circuit} (h : HPFree circuit) :
    HPFree circuit.adjoint := by
  induction circuit with
  | nil => simp
  | cons gate circuit ih =>
      have hp := (hpFree_cons gate circuit).mp h
      rw [circuit_adjoint_cons, hpFree_append]
      constructor
      · exact ih hp.2
      · cases gate <;> simp_all

theorem work1Load_resources (base value : Nat) :
    CircuitWellFormed (work1Load base value) ∧ HPFree (work1Load base value) ∧
    (work1Load base value).length = 1 + constantBitCount 256 value ∧
    eeaCnotCount (work1Load base value) = 0 ∧
    eeaToffoliCount (work1Load base value) = 0 ∧ ShorECDLP.tCount (work1Load base value) = 0 := by
  have hx := xorConstant_wellFormed (List.range' (base+3) 256).reverse value
  have hf := work1_hpFree_adjoint (xorConstant_HPFree (List.range' (base+3) 256).reverse value)
  simp only [work1Load, circuitWellFormed_append, hpFree_append,
    eeaCnotCount_append, eeaToffoliCount_append, tCount_append,
    eeaCnotCount_adjoint, eeaToffoliCount_adjoint, tCount_adjoint,
    xorConstant_cnotCount, xorConstant_toffoliCount, xorConstant_tCount]
  refine ⟨⟨by simp [CircuitWellFormed, Gate.WellFormed], (circuitWellFormed_adjoint _).mpr hx⟩,
    ⟨by simp, hf⟩, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.adjoint, xorConstant_gateCount, Nat.add_comm]
  · rfl
  · rfl
  · rfl

set_option maxRecDepth 10000
attribute [local irreducible] work1Load work2Prepare

/-- Source-order initialization of the two Algorithm-3 work banks in the schedule's allocation. -/
def workRegistersPrepare : Circuit :=
  work2Prepare 263 ++ work1Load 4 (2 ^ 256 - 2 ^ 32 - 977)

private theorem work1Load_preserves_work2 (state : BasisState) (wire : Wire) (hw : (263 : Nat) ≤ wire) :
    run (work1Load 4 (2 ^ 256 - 2 ^ 32 - 977)) state wire = state wire := by
  exact work1Load_frame 4 _ state wire (by
    simp at hw ⊢
    exact ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 4 < 263) hw), fun _ => hw⟩)

/-- Initializing both banks produces Work1=(t=1,r=p) and Work2=(s=0,r'=x), preserving
all other physical roles. Input bits occupy the first 256 Work2 slots in little-endian order. -/
theorem workRegistersPrepare_correct (state : BasisState)
    (hwork1 : Clean (List.range' 4 259) state)
    (htail : Clean (List.range' 519 3) state) :
    run workRegistersPrepare state 4 = true ∧
    run workRegistersPrepare state 5 = false ∧
    run workRegistersPrepare state 6 = false ∧
    wireValues (List.range' 7 256).reverse (run workRegistersPrepare state) =
      constantBits 256 (2 ^ 256 - 2 ^ 32 - 977) ∧
    (∀ i : Fin 3, run workRegistersPrepare state (263+i.val) = false) ∧
    (∀ i : Fin 256, run workRegistersPrepare state (266+i.val) = state (518-i.val)) ∧
    ∀ wire, wire ∉ List.range' 4 518 → run workRegistersPrepare state wire = state wire := by
  let first := run (work2Prepare 263) state
  have hc : Clean (List.range' 4 259) first := by
    intro wire hw
    rw [show first wire = run (work2Prepare 263) state wire by rfl,
      work2Prepare_frame 263 state wire (by simp at hw ⊢; omega)]
    exact hwork1 wire hw
  have hdata : Clean (List.range' 7 256) first := by
    intro wire hw
    exact hc wire (by simp at hw ⊢; omega)
  have hheader := work1Load_header 4 (2 ^ 256 - 2 ^ 32 - 977) first
  have hword := work1Load_word 4 (2 ^ 256 - 2 ^ 32 - 977) first hdata
  rw [hc 4 (by decide)] at hheader
  simp only [Bool.not_false] at hheader
  simp only [workRegistersPrepare, run_append]
  refine ⟨hheader, ?_, ?_, hword, ?_, ?_, ?_⟩
  · rw [work1Load_frame 4 _ first 5 (by decide)]; exact hc 5 (by decide)
  · rw [work1Load_frame 4 _ first 6 (by decide)]; exact hc 6 (by decide)
  · intro i
    rw [work1Load_preserves_work2 first _ (Nat.le_add_right 263 i.val)]
    exact work2Prepare_clean_header 263 state htail i
  · intro i
    rw [work1Load_preserves_work2 first _ (Nat.le_trans (by decide : 263 ≤ 266) (Nat.le_add_right 266 i.val))]
    exact work2Prepare_input_bit 263 state i
  · intro wire hw
    rw [work1Load_frame 4 _ first wire (by
      simp at hw ⊢
      change (wire : Nat) ≠ 4 ∧ (7 ≤ wire → 263 ≤ wire)
      omega)]
    exact work2Prepare_frame 263 state wire (by simp at hw ⊢; omega)

/-- The same concrete bank-preparation circuit has only 390 CX and 251 X gates. -/
theorem workRegistersPrepare_resources :
    CircuitWellFormed workRegistersPrepare ∧ HPFree workRegistersPrepare ∧
    eeaCnotCount workRegistersPrepare = 390 ∧
    eeaToffoliCount workRegistersPrepare = 0 ∧ ShorECDLP.tCount workRegistersPrepare = 0 := by
  have hp := work2Prepare_resources 263
  have hl := work1Load_resources 4 (2 ^ 256 - 2 ^ 32 - 977)
  simp only [workRegistersPrepare, circuitWellFormed_append, hpFree_append,
    eeaCnotCount_append, eeaToffoliCount_append, tCount_append,
    hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2,
    hl.1, hl.2.1, hl.2.2.2.1, hl.2.2.2.2.1, hl.2.2.2.2.2]
  decide

/-- Reverse the initial bank preparation in the source order. -/
def workRegistersRestore : Circuit :=
  work1Load 4 (2 ^ 256 - 2 ^ 32 - 977) ++ work2Restore 263

theorem workRegistersRestore_after_prepare (state : BasisState) :
    run workRegistersRestore (run workRegistersPrepare state) = state := by
  rw [workRegistersRestore, workRegistersPrepare, run_append, run_append,
    work1Load_twice, work2Restore_after_prepare]

theorem workRegistersRestore_resources :
    CircuitWellFormed workRegistersRestore ∧ HPFree workRegistersRestore ∧
    eeaCnotCount workRegistersRestore = 390 ∧
    eeaToffoliCount workRegistersRestore = 0 ∧ ShorECDLP.tCount workRegistersRestore = 0 := by
  have hp := work2Restore_resources 263
  have hl := work1Load_resources 4 (2 ^ 256 - 2 ^ 32 - 977)
  simp only [workRegistersRestore, circuitWellFormed_append, hpFree_append,
    eeaCnotCount_append, eeaToffoliCount_append, tCount_append,
    hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2,
    hl.1, hl.2.1, hl.2.2.2.1, hl.2.2.2.2.1, hl.2.2.2.2.2]
  decide

private theorem workSwapSequence_length (base : Nat) (pairs : List (Nat × Nat)) :
    (workSwapSequence base pairs).length = 3 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨a,b⟩
      simp only [workSwapSequence, List.length_append, ih, workSwap, List.length_cons, List.length_nil]
      omega

private theorem workRegistersPrepare_length : workRegistersPrepare.length = 641 := by
  have hp := workSwapSequence_length 263 work2PreparePairs
  rw [work2Pairs_bounds.2.2.1] at hp
  have hl := (work1Load_resources 4 (2 ^ 256 - 2 ^ 32 - 977)).2.2.1
  have hc : constantBitCount 256 (2 ^ 256 - 2 ^ 32 - 977) = 250 := by decide
  rw [hc] at hl
  rw [workRegistersPrepare, List.length_append, hl]
  unfold work2Prepare
  omega

private theorem workRegistersPrepare_usesOnly :
    PaperCircuitUsesOnly (List.range' 4 518) workRegistersPrepare := by
  have hp : PaperCircuitUsesOnly (List.range' 4 518) (work2Prepare 263) := by
    unfold work2Prepare
    exact (workSwapSequence_usesOnly 263 work2PreparePairs work2Pairs_bounds.1).mono (by
      intro wire hw
      simp at hw ⊢
      omega)
  have hl : PaperCircuitUsesOnly (List.range' 4 518)
      (work1Load 4 (2 ^ 256 - 2 ^ 32 - 977)) := by
    unfold work1Load
    apply PaperCircuitUsesOnly.append
    · simp [PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
    · exact (xorConstant_usesOnly _ _).adjoint.mono (by
        intro wire hw
        simp at hw ⊢
        omega)
  exact hp.append hl

attribute [local irreducible] workRegistersPrepare

private theorem workRegistersPrepare_qubits : qubitCount workRegistersPrepare ≤ 518 := by
  have hsub : (circuitWires workRegistersPrepare).toFinset ⊆ (List.range' 4 518).toFinset := by
    intro wire hw
    simp only [List.mem_toFinset] at hw ⊢
    obtain ⟨gate,hg,hw⟩ := List.mem_flatMap.mp hw
    exact workRegistersPrepare_usesOnly gate hg wire hw
  have hc := (Finset.card_le_card hsub).trans (List.toFinset_card_le (List.range' 4 518))
  have he : (circuitWires workRegistersPrepare).dedup.toFinset =
      (circuitWires workRegistersPrepare).toFinset := by ext wire; simp
  rw [qubitCount, ← List.toFinset_card_of_nodup (List.nodup_dedup _), he]
  simpa only [List.length_range'] using hc

/-- Same-program operational resource certificate for the source bank-preparation stage.
The two 259-wire banks are reused by the later EEA circuit; no additional work bank is allocated. -/
theorem workRegistersPrepare_correct_resources (state : BasisState)
    (hwork1 : Clean (List.range' 4 259) state)
    (htail : Clean (List.range' 519 3) state) :
    run workRegistersPrepare state 4 = true ∧
    wireValues (List.range' 7 256).reverse (run workRegistersPrepare state) =
      constantBits 256 (2 ^ 256 - 2 ^ 32 - 977) ∧
    (∀ i : Fin 3, run workRegistersPrepare state (263+i.val) = false) ∧
    (∀ i : Fin 256, run workRegistersPrepare state (266+i.val) = state (518-i.val)) ∧
    (∀ wire, wire ∉ List.range' 4 518 → run workRegistersPrepare state wire = state wire) ∧
    run workRegistersRestore (run workRegistersPrepare state) = state ∧
    CircuitWellFormed workRegistersPrepare ∧ HPFree workRegistersPrepare ∧
    workRegistersPrepare.length = 641 ∧ eeaCnotCount workRegistersPrepare = 390 ∧
    eeaToffoliCount workRegistersPrepare = 0 ∧ ShorECDLP.tCount workRegistersPrepare = 0 ∧
    qubitCount workRegistersPrepare ≤ 518 ∧
    CircuitWellFormed workRegistersRestore ∧ HPFree workRegistersRestore ∧
    eeaCnotCount workRegistersRestore = 390 ∧ eeaToffoliCount workRegistersRestore = 0 ∧
    ShorECDLP.tCount workRegistersRestore = 0 := by
  have hs := workRegistersPrepare_correct state hwork1 htail
  have hr := workRegistersPrepare_resources
  exact ⟨hs.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2,
    workRegistersRestore_after_prepare state, hr.1, hr.2.1, workRegistersPrepare_length,
    hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, workRegistersPrepare_qubits, workRegistersRestore_resources⟩

end ShorECDLP.Paper2607_13816
