import ShorECDLP.Submission.Arithmetic.Adder

/-!
# Reversible n-bit ripple-carry adder (M1.2)

Chains `fullAdder` cells, threading the carry: bit position `i` takes carry-in from
position `i - 1` and produces the carry-out consumed by position `i + 1`. Built over
`{X, CX, CCX}`, correctness is proved against the classical basis-state semantics.

## Program (syntax-sugared)

All lists are LSB-first and must have the same length.

```text
ripple([], [], [], cin, []) = []
ripple(a :: as, b :: bs, s :: sums, cin, co :: couts) =
  fullAdder(a, b, cin; s, co)
  ++ ripple(as, bs, sums, co, couts)
ripple(mismatched lists) = []
```

## Specification

Let `after = run (ripple a b sum cin couts) before` and `n = a.length`. Under `wiresOK`
and clean sum/carry outputs,

```text
value(sum, after) + 2^n * bit(after, finalCarry)
  = value(a, before) + value(b, before) + bit(before, cin)
tCount(ripple) = 21 * n
HPFree(ripple)
CircuitWellFormed(ripple)
```

`wiresOK` includes both register/carry alignment and the distinctness conditions needed by
the correctness and well-formedness proofs.
-/

namespace ShorECDLP

open Classical
open scoped ArithmeticNotation

/-- Reversible ripple addition on three aligned LSB-first registers. Each recursive step
consumes one input bit from `a` and `b`, one clean output bit from `sum`, and one clean
carry-out wire. Recursion stops when the remaining list shapes no longer align. -/
def ripple : List Wire → List Wire → List Wire → Wire → List Wire → Circuit
  | [],      [],      [],      _,   []       => circuit! {}
  | a :: as, b :: bs, s :: ss, cin, co :: cs =>
      circuit! {
        fullAdder a b cin s co;
        ripple as bs ss co cs
      }
  | _,       _,       _,       _,   _        => circuit! {}

/-- `fullAdder` writes only to its two output wires `s` and `co`; every other wire is left
unchanged. This is what lets the ripple carry preserve already-computed sum bits and the
inputs of later positions. -/
theorem fullAdder_other (a b cin s co : Wire) (st : BasisState) {w : Wire}
    (ws : w ≠ s) (wc : w ≠ co) :
    ⟪fullAdder a b cin s co⟫ st w = st w := by
  simp only [fullAdder, run_cons, run_nil, applyGate,
    upd_other _ _ _ ws, upd_other _ _ _ wc]

/-- The ripple adder costs `21` T per bit when all four lists are aligned. -/
theorem ripple_tCount :
    ∀ (a b sum : List Wire) (cin : Wire) (couts : List Wire),
      b.length = a.length → sum.length = a.length → couts.length = a.length →
      tCount (ripple a b sum cin couts) = 21 * a.length := by
  intro a
  induction a with
  | nil =>
      intro b sum cin couts hb hs hc
      obtain rfl : b = [] := List.length_eq_zero_iff.mp hb
      obtain rfl : sum = [] := List.length_eq_zero_iff.mp hs
      obtain rfl : couts = [] := List.length_eq_zero_iff.mp hc
      simp [ripple]
  | cons a as ih =>
      intro b sum cin couts hb hs hc
      cases b with
      | nil => simp at hb
      | cons b bs =>
          cases sum with
          | nil => simp at hs
          | cons s ss =>
              cases couts with
              | nil => simp at hc
              | cons co cs =>
                  have hb' : bs.length = as.length := by simpa using hb
                  have hs' : ss.length = as.length := by simpa using hs
                  have hc' : cs.length = as.length := by simpa using hc
                  rw [ripple, tCount_append, fullAdder_tCount,
                    ih bs ss co cs hb' hs' hc']
                  simp [List.length_cons, Nat.mul_succ, Nat.add_comm]

/-- The ripple adder writes only to its sum and carry-out registers; a wire outside both is
left unchanged. -/
theorem ripple_other (w : Wire) :
    ∀ (a b sum : List Wire) (cin : Wire) (couts : List Wire) (st : BasisState),
      (∀ x ∈ sum, w ≠ x) → (∀ x ∈ couts, w ≠ x) →
      run (ripple a b sum cin couts) st w = st w := by
  intro a
  induction a with
  | nil =>
      intro b sum cin couts st hs hc
      cases b <;> cases sum <;> cases couts <;> simp [ripple]
  | cons a as ih =>
      intro b sum cin couts st hs hc
      cases b with
      | nil => simp [ripple]
      | cons b bs =>
          cases sum with
          | nil => simp [ripple]
          | cons s ss =>
              cases couts with
              | nil => simp [ripple]
              | cons co cs =>
                  have hws : w ≠ s := hs s (List.mem_cons_self ..)
                  have hwco : w ≠ co := hc co (List.mem_cons_self ..)
                  rw [ripple, run_append,
                    ih bs ss co cs (run (fullAdder a b cin s co) st)
                      (fun x hx => hs x (List.mem_cons_of_mem _ hx))
                      (fun x hx => hc x (List.mem_cons_of_mem _ hx)),
                    fullAdder_other a b cin s co st hws hwco]

/-- Read a wire as a `0/1` natural. -/
def bit (st : BasisState) (w : Wire) : Nat := if st w then 1 else 0

/-- A register's value depends only on the values of its own wires. -/
theorem regValue_congr (ws : List Wire) (st₁ st₂ : BasisState)
    (h : ∀ w ∈ ws, st₁ w = st₂ w) : regValue ws st₁ = regValue ws st₂ := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      rw [regValue_cons, regValue_cons, h w (List.mem_cons_self ..),
        ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))]

/-- The full-adder bit relation: `a + b + cin = sum + 2·carry`. -/
theorem bit_column (a b cin : Bool) :
    (if a then 1 else 0) + (if b then 1 else 0) + (if cin then 1 else 0)
      = (if Bool.xor (Bool.xor a b) cin then 1 else 0)
        + 2 * (if Bool.xor (Bool.xor (a && b) (a && cin)) (b && cin) then 1 else 0) := by
  cases a <;> cases b <;> cases cin <;> decide

/-- The carry-out wire of the whole adder: the last carry in the chain (`cin` if empty). -/
def carryOut : Wire → List Wire → Wire
  | cin, []          => cin
  | _,   co :: couts => carryOut co couts

/-- Register/carry alignment and physical wire distinctness. At each bit position the five
wires `a`, `b`, `cin`, `sum`, and `co` are pairwise distinct. The two output wires are also
distinct from every later register and carry wire, so their values survive the rest of the
ripple computation. -/
def wiresOK : List Wire → List Wire → List Wire → Wire → List Wire → Prop
  | [],      [],      [],      _,   []       => True
  | a :: as, b :: bs, s :: ss, cin, co :: cs =>
      (a ≠ b ∧ a ≠ cin ∧ a ≠ s ∧ a ≠ co ∧
       b ≠ cin ∧ b ≠ s ∧ b ≠ co ∧ cin ≠ s ∧ cin ≠ co ∧ s ≠ co)
        ∧ (∀ x ∈ as, s ≠ x ∧ co ≠ x)
        ∧ (∀ x ∈ bs, s ≠ x ∧ co ≠ x)
        ∧ (∀ x ∈ ss, s ≠ x ∧ co ≠ x)
        ∧ (∀ x ∈ cs, s ≠ x ∧ co ≠ x)
        ∧ wiresOK as bs ss co cs
  | _,       _,       _,       _,   _        => False

/-- **M1.2 — the ripple-carry adder is correct.** For aligned, distinct, fresh wires, the
sum register plus `2^n` times the carry-out equals `a + b + cin`, hence the sum register
holds `(a + b + cin) mod 2^n`. -/
theorem ripple_correct :
    ∀ (a b sum : List Wire) (cin : Wire) (couts : List Wire) (st : BasisState),
      wiresOK a b sum cin couts →
      (∀ x ∈ couts, st x = false) → (∀ x ∈ sum, st x = false) →
      (⟪ripple a b sum cin couts⟫ st)⟦ᵣsum⟧
        + 2 ^ a.length * bit (⟪ripple a b sum cin couts⟫ st) (carryOut cin couts)
        = st⟦ᵣa⟧ + st⟦ᵣb⟧ + bit st cin := by
  intro a
  induction a with
  | nil =>
      intro b sum cin couts st hok hfc hfs
      cases b <;> cases sum <;> cases couts <;> simp_all [wiresOK, ripple, carryOut, bit]
  | cons a as ih =>
      intro b sum cin couts st hok hfc hfs
      cases b with
      | nil => simp [wiresOK] at hok
      | cons b bs =>
          cases sum with
          | nil => simp [wiresOK] at hok
          | cons s ss =>
              cases couts with
              | nil => simp [wiresOK] at hok
              | cons co cs =>
                  obtain ⟨⟨hab, hacin, has, haco, hbcin, hbs, hbco, hcins, hcinco, hsco⟩,
                    hrestA, hrestB, hrestS, hrestC, hokrest⟩ := hok
                  have hsf : st s = false := hfs s (List.mem_cons_self ..)
                  have hcof : st co = false := hfc co (List.mem_cons_self ..)
                  have h_s : (run (fullAdder a b cin s co) st) s
                      = Bool.xor (Bool.xor (st a) (st b)) (st cin) :=
                    fullAdder_sum a b cin s co st hsf hbs hcins haco hbco hcinco hsco
                  have h_co : (run (fullAdder a b cin s co) st) co
                      = Bool.xor (Bool.xor (st a && st b) (st a && st cin))
                        (st b && st cin) :=
                    fullAdder_carry a b cin s co st hcof hbs hcins haco hbco hcinco hsco
                  have h_off : ∀ w, w ≠ s → w ≠ co →
                      (run (fullAdder a b cin s co) st) w = st w :=
                    fun w hws hwco => fullAdder_other a b cin s co st hws hwco
                  have hcongA : regValue as (run (fullAdder a b cin s co) st)
                      = regValue as st := by
                    apply regValue_congr
                    intro w hw
                    exact h_off w (Ne.symm (hrestA w hw).1) (Ne.symm (hrestA w hw).2)
                  have hcongB : regValue bs (run (fullAdder a b cin s co) st)
                      = regValue bs st := by
                    apply regValue_congr
                    intro w hw
                    exact h_off w (Ne.symm (hrestB w hw).1) (Ne.symm (hrestB w hw).2)
                  have h_s_final :
                      (run (ripple as bs ss co cs) (run (fullAdder a b cin s co) st)) s
                        = (run (fullAdder a b cin s co) st) s :=
                    ripple_other s as bs ss co cs (run (fullAdder a b cin s co) st)
                      (fun x hx => (hrestS x hx).1) (fun x hx => (hrestC x hx).1)
                  have IH := ih bs ss co cs (run (fullAdder a b cin s co) st) hokrest
                    (fun x hx => by
                      rw [h_off x (Ne.symm (hrestC x hx).1) (Ne.symm (hrestC x hx).2)]
                      exact hfc x (List.mem_cons_of_mem _ hx))
                    (fun x hx => by
                      rw [h_off x (Ne.symm (hrestS x hx).1) (Ne.symm (hrestS x hx).2)]
                      exact hfs x (List.mem_cons_of_mem _ hx))
                  simp only [bit] at IH
                  rw [h_co, hcongA, hcongB] at IH
                  have hrun : run (ripple (a :: as) (b :: bs) (s :: ss) cin (co :: cs)) st
                      = run (ripple as bs ss co cs) (run (fullAdder a b cin s co) st) := by
                    show run (fullAdder a b cin s co ++ ripple as bs ss co cs) st = _
                    rw [run_append]
                  rw [hrun]
                  simp only [regValue_cons, List.length_cons, carryOut, bit, h_s_final, h_s]
                  rw [Nat.pow_succ, Nat.mul_right_comm (2 ^ as.length) 2]
                  have hbc := bit_column (st a) (st b) (st cin)
                  omega

/-! ## Structural predicates (for the quantum-layer bridge and unitarity)

The adder ships both predicates consumed downstream: `HPFree` (no `H`/`P`, so
`Classical.run` is the quantum action) and `CircuitWellFormed` (distinct wires per gate).
-/

/-- The full-adder cell is well-formed when its five wires are suitably distinct. -/
theorem fullAdder_wellFormed (a b cin s co : Wire)
    (hab : a ≠ b) (hacin : a ≠ cin) (has : a ≠ s) (hac : a ≠ co)
    (hbcin : b ≠ cin) (hbs : b ≠ s) (hbc : b ≠ co) (hcs : cin ≠ s)
    (hcc : cin ≠ co) : CircuitWellFormed (fullAdder a b cin s co) := by
  simp only [fullAdder, circuitWellFormed_cons, circuitWellFormed_nil, Gate.WellFormed, and_true]
  exact ⟨⟨hab, hac, hbc⟩, ⟨hacin, hac, hcc⟩, ⟨hbcin, hbc, hcc⟩, has, hbs, hcs⟩

/-- The ripple adder is `H`/`P`-free because it uses only `{X, CX, CCX}`. -/
theorem ripple_HPFree (a b sum : List Wire) (cin : Wire) (couts : List Wire) :
    Classical.HPFree (ripple a b sum cin couts) := by
  induction a generalizing b sum cin couts with
  | nil => cases b <;> cases sum <;> cases couts <;> simp [ripple]
  | cons a as ih =>
      cases b with
      | nil => simp [ripple]
      | cons b bs =>
          cases sum with
          | nil => simp [ripple]
          | cons s ss =>
              cases couts with
              | nil => simp [ripple]
              | cons co cs =>
                  rw [ripple, Classical.hpFree_append]
                  exact ⟨by simp [fullAdder], ih bs ss co cs⟩

/-- The ripple adder is well-formed whenever `wiresOK` holds. -/
theorem ripple_wellFormed :
    ∀ (a b sum : List Wire) (cin : Wire) (couts : List Wire),
      wiresOK a b sum cin couts → CircuitWellFormed (ripple a b sum cin couts) := by
  intro a
  induction a with
  | nil =>
      intro b sum cin couts hok
      cases b <;> cases sum <;> cases couts <;> simp_all [wiresOK, ripple]
  | cons a as ih =>
      intro b sum cin couts hok
      cases b with
      | nil => simp [wiresOK] at hok
      | cons b bs =>
          cases sum with
          | nil => simp [wiresOK] at hok
          | cons s ss =>
              cases couts with
              | nil => simp [wiresOK] at hok
              | cons co cs =>
                  obtain ⟨⟨hab, hacin, has, hac, hbcin, hbs, hbc, hcs, hcc, _⟩,
                    _, _, _, _, hokrest⟩ := hok
                  rw [ripple, circuitWellFormed_append]
                  exact ⟨fullAdder_wellFormed a b cin s co hab hacin has hac hbcin hbs hbc hcs hcc,
                    ih bs ss co cs hokrest⟩

end ShorECDLP
