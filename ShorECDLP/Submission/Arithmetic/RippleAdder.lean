import ShorECDLP.Submission.Arithmetic.Adder

/-!
# Reversible n-bit ripple-carry adder (M1.2)

Chains `fullAdder` cells, threading the carry: column `i` takes carry-in from column `i-1`
and produces the carry-out consumed by column `i+1`. Built over `{X, CX, CCX}`, correctness
proved against the classical basis-state semantics.

## Program (syntax-sugared)

All lists are LSB-first. A column is `(aᵢ, bᵢ, sumᵢ)` and `coᵢ` is its fresh carry-out.

```text
ripple([], cin, []) = []
ripple((aᵢ,bᵢ,sumᵢ) :: cols, cin, coᵢ :: couts) =
  fullAdder(aᵢ, bᵢ, cin; sumᵢ, coᵢ)
  ++ ripple(cols, coᵢ, couts)
```

## Specification

Let `A`, `B`, and `S` be the registers obtained by projecting the three column fields, let
`n = cols.length`, and let `after = run (ripple cols cin couts) before`. Under `wiresOK`,
matching lengths, and clean sum/carry outputs,

```text
value(S, after) + 2^n * bit(after, finalCarry)
  = value(A, before) + value(B, before)
tCount(ripple) = 21 * n
HPFree(ripple)
CircuitWellFormed(ripple)
```

The definitions needed to state this relation appear before the main theorem; auxiliary
preservation, bit-column, H/P-free, and well-formedness lemmas support its proof.
-/

namespace ShorECDLP

open Classical

/-- `fullAdder` writes only to its two output wires `s` and `co`; every other wire is left
unchanged. This is what lets the ripple carry preserve already-computed sum bits and the
inputs of later columns. -/
theorem fullAdder_other (a b cin s co : Nat) (st : BasisState) {w : Nat}
    (ws : w ≠ s) (wc : w ≠ co) :
    ⟪fullAdder a b cin s co⟫ st w = st w := by
  simp only [fullAdder, run_cons, run_nil, applyGate,
    upd_other _ _ _ ws, upd_other _ _ _ wc]

/-- Ripple-carry adder over aligned columns. `cols` is a list of `(aᵢ, bᵢ, sumᵢ)` triples
(LSB-first); `cin` is the incoming carry wire; `couts` supplies each column's carry-out wire
(column `i`'s carry-out is column `i+1`'s carry-in). -/
def ripple : List (Nat × Nat × Nat) → Nat → List Nat → Circuit
  | [],             _,   _            => []
  | (a, b, s) :: cols, cin, co :: couts => fullAdder a b cin s co ++ ripple cols co couts
  | _ :: _,         _,   []           => []

/-- The ripple adder costs `21` T per column (one full-adder each), when there is a carry-out
wire for every column. -/
theorem ripple_tCount :
    ∀ (cols : List (Nat × Nat × Nat)) (cin : Nat) (couts : List Nat),
      couts.length = cols.length → tCount (ripple cols cin couts) = 21 * cols.length
  | [],             _,   _,            _ => by simp [ripple]
  | (a, b, s) :: cols, cin, co :: couts, h => by
      have h' : couts.length = cols.length := by
        simpa [List.length_cons, Nat.succ_inj] using h
      rw [ripple, tCount_append, fullAdder_tCount, ripple_tCount cols co couts h']
      simp [List.length_cons, Nat.mul_succ, Nat.add_comm]
  | (_ :: _),       _,   [],           h => by simp at h

/-- The ripple adder writes only to its sum wires and carry-out wires; a wire outside both is
left unchanged. -/
theorem ripple_other (w : Nat) :
    ∀ (cols : List (Nat × Nat × Nat)) (cin : Nat) (couts : List Nat) (st : BasisState),
      (∀ c ∈ cols, w ≠ c.2.2) → (∀ x ∈ couts, w ≠ x) →
      run (ripple cols cin couts) st w = st w := by
  intro cols
  induction cols with
  | nil => intro cin couts st _ _; simp [ripple]
  | cons head rest ih =>
      intro cin couts st hs hc
      obtain ⟨a, b, s⟩ := head
      cases couts with
      | nil => simp [ripple]
      | cons co couts' =>
          have hws : w ≠ s := hs (a, b, s) (List.mem_cons_self ..)
          have hwco : w ≠ co := hc co (List.mem_cons_self ..)
          rw [ripple, run_append,
            ih co couts' (run (fullAdder a b cin s co) st)
              (fun c hc' => hs c (List.mem_cons_of_mem _ hc'))
              (fun x hx => hc x (List.mem_cons_of_mem _ hx)),
            fullAdder_other a b cin s co st hws hwco]

/-- Read a wire as a `0/1` natural. -/
def bit (st : BasisState) (w : Nat) : Nat := if st w then 1 else 0

/-- A register's value depends only on the values of its own wires. -/
theorem regValue_congr (ws : List Nat) (st₁ st₂ : BasisState)
    (h : ∀ w ∈ ws, st₁ w = st₂ w) : regValue ws st₁ = regValue ws st₂ := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      rw [regValue_cons, regValue_cons, h w (List.mem_cons_self ..),
        ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))]

/-- The full-adder column relation: `a + b + cin = sum + 2·carry` on bits. -/
theorem bit_column (a b cin : Bool) :
    (if a then 1 else 0) + (if b then 1 else 0) + (if cin then 1 else 0)
      = (if Bool.xor (Bool.xor a b) cin then 1 else 0)
        + 2 * (if Bool.xor (Bool.xor (a && b) (a && cin)) (b && cin) then 1 else 0) := by
  cases a <;> cases b <;> cases cin <;> decide

/-- The carry-out wire of the whole adder: the last carry in the chain (`cin` if no columns). -/
def carryOut : Nat → List Nat → Nat
  | cin, []          => cin
  | _,   co :: couts => carryOut co couts

/-- Physical wire distinctness for the adder: each column's five wires `a, b, cin, s, co` are
pairwise distinct, and its two output wires `s, co` are distinct from every later column's wires
and carry. This is the honest well-formedness precondition (correctness needs only part of it;
the `WellFormed`/unitarity side needs the full per-column distinctness). -/
def wiresOK : List (Nat × Nat × Nat) → Nat → List Nat → Prop
  | [],               _,   _          => True
  | (a, b, s) :: rest, cin, co :: cs  =>
      (a ≠ b ∧ a ≠ cin ∧ a ≠ s ∧ a ≠ co ∧ b ≠ cin ∧ b ≠ s ∧ b ≠ co ∧ cin ≠ s ∧ cin ≠ co ∧ s ≠ co)
        ∧ (∀ c ∈ rest, (s ≠ c.1 ∧ co ≠ c.1) ∧ (s ≠ c.2.1 ∧ co ≠ c.2.1) ∧ (s ≠ c.2.2 ∧ co ≠ c.2.2))
        ∧ (∀ x ∈ cs, s ≠ x ∧ co ≠ x)
        ∧ wiresOK rest co cs
  | _ :: _,           _,   []         => True

/-- **M1.2 — the ripple-carry adder is correct.** For distinct, fresh wires, the sum register
plus `2^n` times the carry-out equals `a + b + cin` (the ripple-carry identity), hence the sum
register holds `(a + b + cin) mod 2^n`. -/
theorem ripple_correct :
    ∀ (cols : List (Nat × Nat × Nat)) (cin : Nat) (couts : List Nat) (st : BasisState),
      couts.length = cols.length → wiresOK cols cin couts →
      (∀ x ∈ couts, st x = false) → (∀ c ∈ cols, st c.2.2 = false) →
      regValue (cols.map (fun c => c.2.2)) (run (ripple cols cin couts) st)
        + 2 ^ cols.length * bit (run (ripple cols cin couts) st) (carryOut cin couts)
        = regValue (cols.map (fun c => c.1)) st + regValue (cols.map (fun c => c.2.1)) st
          + bit st cin := by
  intro cols
  induction cols with
  | nil =>
      intro cin couts st hlen _ _ _
      obtain rfl : couts = [] := List.length_eq_zero_iff.mp hlen
      simp [ripple, carryOut, bit]
  | cons head rest ih =>
      intro cin couts st hlen hok hfc hfs
      obtain ⟨a, b, s⟩ := head
      cases couts with
      | nil => simp at hlen
      | cons co cs =>
          obtain ⟨⟨_, _, _, hac, _, hbs, hbc, hcs, hcc, hsc⟩, hrest, hcs', hokrest⟩ := hok
          have hlen' : cs.length = rest.length := by simpa using hlen
          have hsf : st s = false := hfs (a, b, s) (List.mem_cons_self ..)
          have hcof : st co = false := hfc co (List.mem_cons_self ..)
          have h_s : (run (fullAdder a b cin s co) st) s
              = Bool.xor (Bool.xor (st a) (st b)) (st cin) :=
            fullAdder_sum a b cin s co st hsf hbs hcs hac hbc hcc hsc
          have h_co : (run (fullAdder a b cin s co) st) co
              = Bool.xor (Bool.xor (st a && st b) (st a && st cin)) (st b && st cin) :=
            fullAdder_carry a b cin s co st hcof hbs hcs hac hbc hcc hsc
          have h_off : ∀ w, w ≠ s → w ≠ co → (run (fullAdder a b cin s co) st) w = st w :=
            fun w hws hwco => fullAdder_other a b cin s co st hws hwco
          -- values on the rest's registers survive the first cell
          have hcongA : regValue (rest.map (fun c => c.1)) (run (fullAdder a b cin s co) st)
              = regValue (rest.map (fun c => c.1)) st := by
            apply regValue_congr
            intro w hw
            simp only [List.mem_map] at hw
            obtain ⟨c, hc, rfl⟩ := hw
            exact h_off c.1 (Ne.symm (hrest c hc).1.1) (Ne.symm (hrest c hc).1.2)
          have hcongB : regValue (rest.map (fun c => c.2.1)) (run (fullAdder a b cin s co) st)
              = regValue (rest.map (fun c => c.2.1)) st := by
            apply regValue_congr
            intro w hw
            simp only [List.mem_map] at hw
            obtain ⟨c, hc, rfl⟩ := hw
            exact h_off c.2.1 (Ne.symm (hrest c hc).2.1.1) (Ne.symm (hrest c hc).2.1.2)
          -- the first cell leaves `s` fresh for the rest, and the rest doesn't touch it
          have h_s_final : (run (ripple rest co cs) (run (fullAdder a b cin s co) st)) s
              = (run (fullAdder a b cin s co) st) s :=
            ripple_other s rest co cs (run (fullAdder a b cin s co) st)
              (fun c hc => (hrest c hc).2.2.1) (fun x hx => (hcs' x hx).1)
          -- apply the induction hypothesis to the rest
          have IH := ih co cs (run (fullAdder a b cin s co) st) hlen' hokrest
            (fun x hx => by
              rw [h_off x (Ne.symm (hcs' x hx).1) (Ne.symm (hcs' x hx).2)]
              exact hfc x (List.mem_cons_of_mem _ hx))
            (fun c hc => by
              rw [h_off c.2.2 (Ne.symm (hrest c hc).2.2.1) (Ne.symm (hrest c hc).2.2.2)]
              exact hfs c (List.mem_cons_of_mem _ hc))
          -- put the induction hypothesis in terms of `st` and bit-values
          simp only [bit] at IH
          rw [h_co, hcongA, hcongB] at IH
          -- expand the goal: whole run, register heads, carry-out wire, and `bit`
          have hrun : run (ripple ((a, b, s) :: rest) cin (co :: cs)) st
              = run (ripple rest co cs) (run (fullAdder a b cin s co) st) := by
            show run (fullAdder a b cin s co ++ ripple rest co cs) st = _
            rw [run_append]
          rw [hrun]
          simp only [List.map_cons, regValue_cons, List.length_cons, carryOut, bit,
            h_s_final, h_s]
          -- align the carry product `2^(n+1)·C` with the IH's `2^n·C`, then linear arithmetic
          rw [Nat.pow_succ, Nat.mul_right_comm (2 ^ rest.length) 2]
          have hbc' := bit_column (st a) (st b) (st cin)
          omega

/-! ## Structural predicates (for the quantum-layer bridge and unitarity)

The adder ships both predicates the downstream milestones consume: `HPFree` (no `H`/`P`, so
`Classical.run` *is* the quantum action — this is what lifts the correctness above to the
quantum layer at M1.4) and `CircuitWellFormed` (distinct wires per gate — the unitarity /
norm-preservation side). -/

/-- The full-adder cell is well-formed when its five wires are suitably distinct. -/
theorem fullAdder_wellFormed (a b cin s co : Nat)
    (hab : a ≠ b) (hacin : a ≠ cin) (has : a ≠ s) (hac : a ≠ co)
    (hbcin : b ≠ cin) (hbs : b ≠ s) (hbc : b ≠ co) (hcs : cin ≠ s) (hcc : cin ≠ co) :
    CircuitWellFormed (fullAdder a b cin s co) := by
  simp only [fullAdder, circuitWellFormed_cons, circuitWellFormed_nil, Gate.WellFormed, and_true]
  exact ⟨⟨hab, hac, hbc⟩, ⟨hacin, hac, hcc⟩, ⟨hbcin, hbc, hcc⟩, has, hbs, hcs⟩

/-- The ripple adder is `H`/`P`-free: it is built purely from `{X, CX, CCX}`, so its classical
semantics coincides with its quantum action (used to lift correctness to the quantum layer). -/
theorem ripple_HPFree (cols : List (Nat × Nat × Nat)) (cin : Nat) (couts : List Nat) :
    Classical.HPFree (ripple cols cin couts) := by
  induction cols generalizing cin couts with
  | nil => simp [ripple]
  | cons head rest ih =>
      obtain ⟨a, b, s⟩ := head
      cases couts with
      | nil => simp [ripple]
      | cons co cs =>
          rw [ripple, Classical.hpFree_append]
          exact ⟨by simp [fullAdder], ih co cs⟩

/-- The ripple adder is well-formed (distinct wires per gate) whenever the wires are distinct. -/
theorem ripple_wellFormed :
    ∀ (cols : List (Nat × Nat × Nat)) (cin : Nat) (couts : List Nat),
      wiresOK cols cin couts → CircuitWellFormed (ripple cols cin couts) := by
  intro cols
  induction cols with
  | nil => intro cin couts _; simp [ripple]
  | cons head rest ih =>
      intro cin couts hok
      obtain ⟨a, b, s⟩ := head
      cases couts with
      | nil => simp [ripple]
      | cons co cs =>
          obtain ⟨⟨hab, hacin, has, hac, hbcin, hbs, hbc, hcs, hcc, _⟩, _, _, hokrest⟩ := hok
          rw [ripple, circuitWellFormed_append]
          exact ⟨fullAdder_wellFormed a b cin s co hab hacin has hac hbcin hbs hbc hcs hcc,
            ih co cs hokrest⟩

end ShorECDLP
