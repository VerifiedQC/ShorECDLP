import ShorECDLP.Submission.Arithmetic.RippleAdder
import ShorECDLP.Submission.Arithmetic.Contracts
import ShorECDLP.Submission.Arithmetic.Primitives

/-!
# Modular adder (M1.3) — `(a + b) mod p`

Naive/textbook construction: reuse the general `ripple` adder (M1.2) together with constant
loads, rather than specializing arithmetic to secp256k1's prime `p`. `loadConst` X-es a
constant into a register, so a register–register adder doubles as a constant adder; the
modular adder (later sub-step) adds `b`, conditionally subtracts the constant `p`, and
uncomputes — all over `ripple`.

Built up one sub-step per PR:
- **M1.3.0 ✓** — `loadConst`: load a classical constant into a register.
- **M1.3.1 ✓** — constant adder `addConst` `(a + c)` (load ⇒ ripple ⇒ unload), correctness + `tCount`.
- **M1.3.2** — the generic modular adder `(a + b) mod modulus`; here the
  `addConst`/`ripple` `HPFree`/`WellFormed` compose into the deliverable's full contract.

## Program (syntax-sugared)

All registers have width `w`, are LSB-first, and the public output starts clean.

```text
addConst(a, c; out):
  loadConst(cReg, c)
  ripple(a, cReg; out)
  loadConst(cReg, c)              -- clear cReg

compute(a, b; sum, reduced, flag):
  ripple(a, b; sum)               -- sum = a + b
  addConst(sum, 2^w - modulus; reduced)
                                     -- flag records whether sum >= modulus

modAdd(a, b; clean out, work):
  compute
  selectPoint(flag, sum, reduced; out)
  reverse(compute)                 -- restore every work wire
```

## Specification

`ModAddWiring` supplies the aligned columns, freshness conditions, and
`2 * modulus <= 2^w`. For canonical inputs and a clean output/work area,

```text
after := run(modAdd, before)
value(out, after) = (value(a, before) + value(b, before)) mod modulus
a and b are preserved
work is clean in after
tCount(modAdd) = 91 * w
CircuitUsesOnly(layout.allWires, modAdd)
HPFree(modAdd)
CircuitWellFormed(modAdd)
```

The public theorem `modAdd_contract` packages this complete specification for the exact
`modAdd` term. Lower-level constant-addition and reduction lemmas provide its proof.
-/

namespace ShorECDLP

open Classical

open Arithmetic

/-- The carry-out wire lies among `cin :: couts`, so it avoids any register disjoint from both. -/
theorem carryOut_not_mem (bs : List Nat) :
    ∀ (cin : Nat) (couts : List Nat), cin ∉ bs → (∀ x ∈ couts, x ∉ bs) →
      carryOut cin couts ∉ bs
  | cin, [],      hcin, _      => by simpa [carryOut] using hcin
  | _,   co :: cs, _,   hcouts => by
      rw [carryOut]
      exact carryOut_not_mem bs co cs (hcouts co (List.mem_cons_self ..))
        (fun x hx => hcouts x (List.mem_cons_of_mem _ hx))

/-- **M1.3.1 — constant adder.** Load `c` into the `b` wires, ripple, unload: the sum register
holds `a + c` (with the carry-out), for `c < 2ⁿ` and distinct registers. Reuses the general
`ripple`, so nothing is specialized to a particular constant. -/
def addConst (cols : List (Nat × Nat × Nat)) (cin : Nat) (couts : List Nat) (c : Nat) : Circuit :=
  loadConst (cols.map (fun x => x.2.1)) c
    ++ ripple cols cin couts
    ++ loadConst (cols.map (fun x => x.2.1)) c

theorem addConst_correct
    (cols : List (Nat × Nat × Nat)) (cin : Nat) (couts : List Nat) (c : Nat) (st : BasisState)
    (hlen : couts.length = cols.length)
    (hwok : wiresOK cols cin couts)
    (hbnd : (cols.map (fun x => x.2.1)).Nodup)
    (hAB : ∀ w ∈ cols.map (fun x => x.1), w ∉ cols.map (fun x => x.2.1))
    (hSB : ∀ w ∈ cols.map (fun x => x.2.2), w ∉ cols.map (fun x => x.2.1))
    (hcoutB : ∀ x ∈ couts, x ∉ cols.map (fun x => x.2.1))
    (hcinB : cin ∉ cols.map (fun x => x.2.1))
    (hfc : ∀ x ∈ couts, st x = false)
    (hfs : ∀ cc ∈ cols, st cc.2.2 = false)
    (hfb : ∀ cc ∈ cols, st cc.2.1 = false)
    (hfcin : st cin = false)
    (hc : c < 2 ^ cols.length) :
    regValue (cols.map (fun x => x.2.2)) (run (addConst cols cin couts c) st)
      + 2 ^ cols.length * bit (run (addConst cols cin couts c) st) (carryOut cin couts)
      = regValue (cols.map (fun x => x.1)) st + c := by
  -- membership helpers
  have hbfalse : ∀ w ∈ cols.map (fun x => x.2.1), st w = false := by
    intro w hw; simp only [List.mem_map] at hw; obtain ⟨cc, hcc, rfl⟩ := hw; exact hfb cc hcc
  have hsfalse : ∀ w ∈ cols.map (fun x => x.2.2), st w = false := by
    intro w hw; simp only [List.mem_map] at hw; obtain ⟨cc, hcc, rfl⟩ := hw; exact hfs cc hcc
  -- the carry-out wire is not a `b` wire (it is `cin` or one of `couts`)
  have hcarryB : carryOut cin couts ∉ cols.map (fun x => x.2.1) :=
    carryOut_not_mem _ cin couts hcinB hcoutB
  -- abbreviation for the loaded state
  rw [addConst, run_append, run_append]
  -- st1 := run (loadConst B c) st
  -- (1) after the load, `b` holds `c`, `a` is intact, `s`/`couts`/`cin` are still `false`
  have hload : regValue (cols.map (fun x => x.2.1))
      (run (loadConst (cols.map (fun x => x.2.1)) c) st) = c :=
    loadConst_correct _ c st hbnd hbfalse (by rw [List.length_map]; exact hc)
  have hakeep : regValue (cols.map (fun x => x.1))
      (run (loadConst (cols.map (fun x => x.2.1)) c) st)
      = regValue (cols.map (fun x => x.1)) st := loadConst_regValue _ _ c st hAB
  have hcoutkeep : ∀ x ∈ couts, run (loadConst (cols.map (fun x => x.2.1)) c) st x = false :=
    fun x hx => loadConst_false x _ c st (hcoutB x hx) (hfc x hx)
  have hskeep : ∀ cc ∈ cols,
      run (loadConst (cols.map (fun x => x.2.1)) c) st cc.2.2 = false := by
    intro cc hcc
    exact loadConst_false cc.2.2 _ c st (hSB cc.2.2 (List.mem_map_of_mem hcc)) (hfs cc hcc)
  have hcinkeep : run (loadConst (cols.map (fun x => x.2.1)) c) st cin = false :=
    loadConst_false cin _ c st hcinB hfcin
  -- (2) ripple on the loaded state: s = a + c (+ carry)
  have hrip := ripple_correct cols cin couts
    (run (loadConst (cols.map (fun x => x.2.1)) c) st) hlen hwok hcoutkeep hskeep
  rw [hload, hakeep] at hrip
  -- bit at cin is 0 after the load
  have hcinbit : bit (run (loadConst (cols.map (fun x => x.2.1)) c) st) cin = 0 := by
    rw [bit, hcinkeep]; rfl
  rw [hcinbit, Nat.add_zero] at hrip
  -- (3) the final unload restores `b` but leaves `s` and the carry-out wire untouched
  have hs_unload : regValue (cols.map (fun x => x.2.2))
      (run (loadConst (cols.map (fun x => x.2.1)) c)
        (run (ripple cols cin couts) (run (loadConst (cols.map (fun x => x.2.1)) c) st)))
      = regValue (cols.map (fun x => x.2.2))
        (run (ripple cols cin couts) (run (loadConst (cols.map (fun x => x.2.1)) c) st)) :=
    loadConst_regValue _ _ c _ hSB
  have hcarry_unload : bit (run (loadConst (cols.map (fun x => x.2.1)) c)
        (run (ripple cols cin couts) (run (loadConst (cols.map (fun x => x.2.1)) c) st)))
        (carryOut cin couts)
      = bit (run (ripple cols cin couts) (run (loadConst (cols.map (fun x => x.2.1)) c) st))
        (carryOut cin couts) := by
    rw [bit, bit, loadConst_other (carryOut cin couts) _ c _ hcarryB]
  rw [hs_unload, hcarry_unload, hrip]

/-- A constant adder changes only its sum and carry-output wires; its temporary constant
register is restored by the final `loadConst`. -/
theorem addConst_other (w : Wire) (cols : List (Wire × Wire × Wire)) (cin : Wire)
    (couts : List Wire) (c : Nat) (st : BasisState)
    (hb : w ∉ cols.map (fun x => x.2.1))
    (hs : ∀ x ∈ cols, w ≠ x.2.2) (hc : ∀ x ∈ couts, w ≠ x) :
    run (addConst cols cin couts c) st w = st w := by
  rw [addConst, run_append, run_append,
    loadConst_other w _ c _ hb,
    ripple_other w cols cin couts _ hs hc,
    loadConst_other w _ c _ hb]

/-- The constant adder costs the same `21n` T as the underlying ripple (the loads are T-free).
Its `HPFree`/`WellFormed` land at M1.3.2, where they compose with `ripple_HPFree`/`_wellFormed`
into the deliverable modular adder's full contract. -/
theorem addConst_tCount (cols : List (Nat × Nat × Nat)) (cin : Nat) (couts : List Nat) (c : Nat)
    (hlen : couts.length = cols.length) :
    tCount (addConst cols cin couts c) = 21 * cols.length := by
  rw [addConst, tCount_append, tCount_append, ripple_tCount cols cin couts hlen,
    loadConst_tCount]
  omega

/-! ## M1.3.2 — reduce once, copy, and uncompute

For canonical field inputs `a,b < p`, the unreduced sum is below `2p`, so one conditional
subtraction is enough.  We use one spare high bit (`w = 257` for secp256k1):

1. `ripple` computes `x = a + b` into a fresh `w`-bit register;
2. `addConst (2^w - p)` computes a candidate `y`; its carry is exactly the predicate `p ≤ x`;
3. `selectPoint` writes `x` or `y` into the fresh public output according to that carry;
4. the two arithmetic stages are run backwards, restoring every work register to its input
   value while leaving the selected output in place.

The last step is Bennett compute-copy-uncompute.  It is deliberately included here rather than
leaving the ripple carry banks as garbage for every downstream modular multiplication.
-/

/-- Every `n`-wire LSB-first register denotes a number below `2^n`. -/
theorem regValue_lt_two_pow (ws : List Wire) (st : BasisState) :
    regValue ws st < 2 ^ ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      rw [regValue_cons, List.length_cons, Nat.pow_succ]
      by_cases h : st w <;> simp [h] <;> omega

/-- A one-subtraction candidate selects the canonical remainder.  The Boolean is the
carry-out from adding `M - modulus`: it is true exactly when `modulus ≤ x`. -/
theorem reduceOnce_select_eq_mod (modulus M x y : Nat) (flag : Bool)
    (hmod : 0 < modulus) (hfit : 2 * modulus ≤ M) (hx : x < 2 * modulus)
    (hy : y < M)
    (heq : y + M * (if flag then 1 else 0) = x + (M - modulus)) :
    (if flag then y else x) = x % modulus := by
  have hmodM : modulus ≤ M := by omega
  cases flag with
  | false =>
      simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at heq ⊢
      have hsmall : x < modulus := by omega
      exact (Nat.mod_eq_of_lt hsmall).symm
  | true =>
      simp only [if_true, Nat.mul_one] at heq ⊢
      have hover : modulus ≤ x := by omega
      have hsub : y = x - modulus := by omega
      rw [hsub, Nat.mod_eq_sub_mod hover, Nat.mod_eq_of_lt (by omega)]

/-- The target wire of a primitive gate. -/
def gateTarget : Gate → Wire
  | .X t       => t
  | .H t       => t
  | .CX _ t    => t
  | .CCX _ _ t => t
  | .P _ _ t   => t

/-- All wires read or written by a primitive gate. -/
def gateWires : Gate → List Wire
  | .X t       => [t]
  | .H t       => [t]
  | .CX c t    => [c, t]
  | .CCX a b t => [a, b, t]
  | .P _ _ t   => [t]

/-- The (not necessarily duplicate-free) support of a circuit. -/
def circuitWires (c : Circuit) : List Wire := c.flatMap gateWires

/-- A gate's target belongs to its support. -/
theorem gateTarget_mem_gateWires (g : Gate) : gateTarget g ∈ gateWires g := by
  cases g <;> simp [gateTarget, gateWires]

/-- A gate maps states that agree on a wire set to states that still agree on that set,
provided all of the gate's own wires belong to it. -/
theorem applyGate_congr_on (g : Gate) (ws : List Wire) (s t : BasisState)
    (hg : ∀ w ∈ gateWires g, w ∈ ws) (hst : ∀ w ∈ ws, s w = t w) :
    ∀ w ∈ ws, applyGate g s w = applyGate g t w := by
  intro w hw
  cases g with
  | X target =>
      have ht := hst target (hg target (by simp [gateWires]))
      by_cases h : w = target
      · subst w; simp [applyGate, upd, ht]
      · simpa [applyGate, upd, h] using hst w hw
  | H target => exact hst w hw
  | CX control target =>
      have hc := hst control (hg control (by simp [gateWires]))
      have ht := hst target (hg target (by simp [gateWires]))
      by_cases h : w = target
      · subst w; simp [applyGate, upd, hc, ht]
      · simpa [applyGate, upd, h] using hst w hw
  | CCX a b target =>
      have ha := hst a (hg a (by simp [gateWires]))
      have hb := hst b (hg b (by simp [gateWires]))
      have ht := hst target (hg target (by simp [gateWires]))
      by_cases h : w = target
      · subst w; simp [applyGate, upd, ha, hb, ht]
      · simpa [applyGate, upd, h] using hst w hw
  | P dir k target => exact hst w hw

/-- Circuit execution preserves agreement on a containing wire set. -/
theorem run_congr_on (c : Circuit) (ws : List Wire) (s t : BasisState)
    (hc : ∀ g ∈ c, ∀ w ∈ gateWires g, w ∈ ws)
    (hst : ∀ w ∈ ws, s w = t w) :
    ∀ w ∈ ws, run c s w = run c t w := by
  induction c generalizing s t with
  | nil => exact hst
  | cons g c ih =>
      simp only [run_cons]
      apply ih
      · intro g' hg' w hw
        exact hc g' (List.mem_cons_of_mem _ hg') w hw
      · exact applyGate_congr_on g ws s t
          (fun w hw => hc g (List.mem_cons_self ..) w hw) hst

/-- A gate changes only its target wire. -/
theorem applyGate_other_target (g : Gate) (st : BasisState) (w : Wire)
    (h : w ≠ gateTarget g) : applyGate g st w = st w := by
  cases g with
  | X t => simpa [gateTarget, applyGate] using upd_other st t (!st t) h
  | H _ => rfl
  | CX c t => simpa [gateTarget, applyGate] using upd_other st t (Bool.xor (st t) (st c)) h
  | CCX a b t =>
      simpa [gateTarget, applyGate] using upd_other st t (Bool.xor (st t) (st a && st b)) h
  | P _ _ _ => rfl

/-- A circuit leaves a wire outside its target list unchanged. -/
theorem run_other_targets (c : Circuit) (st : BasisState) (w : Wire)
    (h : w ∉ c.map gateTarget) : run c st w = st w := by
  induction c generalizing st with
  | nil => rfl
  | cons g c ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [run_cons, ih _ h.2, applyGate_other_target g st w h.1]

/-- On the classical gates used by arithmetic, a well-formed primitive gate is self-inverse. -/
theorem applyGate_twice (g : Gate) (st : BasisState)
    (hc : IsClassicalGate g) (hwf : g.WellFormed) : applyGate g (applyGate g st) = st := by
  funext w
  cases g with
  | X t =>
      by_cases h : w = t
      · subst w; simp [applyGate, upd]
      · simp [applyGate, upd, h]
  | H t => simp at hc
  | CX c t =>
      by_cases h : w = t
      · subst w
        simp only [Gate.WellFormed] at hwf
        simp [applyGate, upd, hwf]
      · simp [applyGate, upd, h]
  | CCX a b t =>
      by_cases h : w = t
      · subst w
        simp only [Gate.WellFormed] at hwf
        simp [applyGate, upd, hwf]
      · simp [applyGate, upd, h]
  | P dir k t => simp at hc

/-- Reversing an arithmetic circuit undoes its classical action. -/
theorem run_reverse_cancel (c : Circuit) (st : BasisState)
    (hc : HPFree c) (hwf : CircuitWellFormed c) : run c.reverse (run c st) = st := by
  induction c generalizing st with
  | nil => rfl
  | cons g c ih =>
      simp only [hpFree_cons] at hc
      simp only [circuitWellFormed_cons] at hwf
      rw [run_cons, List.reverse_cons, run_append]
      rw [ih (applyGate g st) hc.2 hwf.2]
      simpa [run_cons, run_nil] using applyGate_twice g st hc.1 hwf.1

/-- Reversal preserves the arithmetic guard. -/
theorem hpFree_reverse (c : Circuit) (h : HPFree c) : HPFree c.reverse := by
  intro g hg
  exact h g (by simpa using hg)

/-- Reversal preserves primitive-gate well-formedness. -/
theorem wellFormed_reverse (c : Circuit) (h : CircuitWellFormed c) :
    CircuitWellFormed c.reverse := by
  intro g hg
  exact h g (by simpa using hg)

/-- Reversal does not change the T-count of an arithmetic circuit. -/
theorem tCount_reverse (c : Circuit) : tCount c.reverse = tCount c := by
  simp [tCount]

/-- The constant adder is arithmetic (`H`/`P`-free). -/
theorem addConst_HPFree (cols : List (Wire × Wire × Wire)) (cin : Wire)
    (couts : List Wire) (c : Nat) : HPFree (addConst cols cin couts c) := by
  rw [addConst, hpFree_append, hpFree_append]
  exact ⟨⟨loadConst_HPFree _ _, ripple_HPFree _ _ _⟩, loadConst_HPFree _ _⟩

/-- The constant adder is well-formed whenever its ripple core is. -/
theorem addConst_wellFormed (cols : List (Wire × Wire × Wire)) (cin : Wire)
    (couts : List Wire) (c : Nat) (h : wiresOK cols cin couts) :
    CircuitWellFormed (addConst cols cin couts c) := by
  rw [addConst, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨loadConst_wellFormed _ _, ripple_wellFormed cols cin couts h⟩,
    loadConst_wellFormed _ _⟩

/-- Forward computation of the unreduced sum and the conditional-subtraction candidate. -/
def modAddCompute (addCols redCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) : Circuit :=
  ripple addCols cin₁ couts₁
    ++ addConst redCols cin₂ couts₂ (2 ^ redCols.length - modulus)

/-- Clean modular adder: compute both candidates, select directly into the fresh public output,
then reverse only the candidate computation.  The selector output is outside the compute
support, so the reverse pass restores every sum/carry/candidate work wire without erasing the
answer. -/
def modAdd (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) : Circuit :=
  let compute := modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus
  compute ++ selectPoint (carryOut cin₂ couts₂) selectCols ++ compute.reverse

/-- **M1.3.2 — clean modular addition is correct.**

All three column lists have the same width.  `redCols` reads the sum register produced by
`addCols`; `selectCols` reads that same sum and the reduction candidate.  The explicit
freshness/disjointness hypotheses are the gate-level layout obligations: the second stage's
work wires survive the first stage as zeroes, and the public output is outside the complete
compute circuit.  For canonical inputs and a width satisfying `2*modulus ≤ 2^width`, the
selected output is `(a+b) % modulus`. -/
theorem modAdd_correct
    (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (st : BasisState)
    (haddLen : couts₁.length = addCols.length)
    (hredLen : couts₂.length = redCols.length)
    (hwidth : redCols.length = addCols.length)
    (haddOK : wiresOK addCols cin₁ couts₁)
    (hredOK : wiresOK redCols cin₂ couts₂)
    (hselectOK : selectOK (carryOut cin₂ couts₂) selectCols)
    (hredA : redCols.map (fun c => c.1) = addCols.map (fun c => c.2.2))
    (hselectX : selectCols.map (fun c => c.1) = addCols.map (fun c => c.2.2))
    (hselectY : selectCols.map (fun c => c.2.1) = redCols.map (fun c => c.2.2))
    (hmod : 0 < modulus)
    (hfit : 2 * modulus ≤ 2 ^ addCols.length)
    (ha : regValue (addCols.map (fun c => c.1)) st < modulus)
    (hb : regValue (addCols.map (fun c => c.2.1)) st < modulus)
    (haddCarryFresh : ∀ w ∈ couts₁, st w = false)
    (haddSumFresh : ∀ c ∈ addCols, st c.2.2 = false)
    (hcin₁Fresh : st cin₁ = false)
    (hredBNodup : (redCols.map (fun c => c.2.1)).Nodup)
    (hredAB : ∀ w ∈ redCols.map (fun c => c.1),
      w ∉ redCols.map (fun c => c.2.1))
    (hredSB : ∀ w ∈ redCols.map (fun c => c.2.2),
      w ∉ redCols.map (fun c => c.2.1))
    (hredCarryB : ∀ w ∈ couts₂, w ∉ redCols.map (fun c => c.2.1))
    (hredCinB : cin₂ ∉ redCols.map (fun c => c.2.1))
    (hredAS : ∀ w ∈ redCols.map (fun c => c.1),
      w ∉ redCols.map (fun c => c.2.2))
    (hredACarry : ∀ w ∈ redCols.map (fun c => c.1), w ∉ couts₂)
    (hredCarryFresh : ∀ w ∈ couts₂,
      st w = false ∧ w ∉ (ripple addCols cin₁ couts₁).map gateTarget)
    (hredSumFresh : ∀ c ∈ redCols,
      st c.2.2 = false ∧ c.2.2 ∉ (ripple addCols cin₁ couts₁).map gateTarget)
    (hredBFresh : ∀ c ∈ redCols,
      st c.2.1 = false ∧ c.2.1 ∉ (ripple addCols cin₁ couts₁).map gateTarget)
    (hcin₂Fresh : st cin₂ = false ∧
      cin₂ ∉ (ripple addCols cin₁ couts₁).map gateTarget)
    (houtFresh : ∀ c ∈ selectCols,
      st c.2.2 = false ∧
        c.2.2 ∉ (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus).map gateTarget) :
    regValue (selectCols.map (fun c => c.2.2))
        (run (modAdd addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) st) =
      (regValue (addCols.map (fun c => c.1)) st +
        regValue (addCols.map (fun c => c.2.1)) st) % modulus := by
  have hripple := ripple_correct addCols cin₁ couts₁ st haddLen haddOK
    haddCarryFresh haddSumFresh
  have hcinbit : bit st cin₁ = 0 := by simp [bit, hcin₁Fresh]
  rw [hcinbit, Nat.add_zero] at hripple
  have hsumBound :
      regValue (addCols.map (fun c => c.1)) st +
        regValue (addCols.map (fun c => c.2.1)) st < 2 * modulus := by
    omega
  have hsumPow :
      regValue (addCols.map (fun c => c.1)) st +
        regValue (addCols.map (fun c => c.2.1)) st < 2 ^ addCols.length := by
    omega
  have hsum :
      regValue (addCols.map (fun c => c.2.2))
          (run (ripple addCols cin₁ couts₁) st) =
        regValue (addCols.map (fun c => c.1)) st +
          regValue (addCols.map (fun c => c.2.1)) st := by
    by_cases hc : run (ripple addCols cin₁ couts₁) st (carryOut cin₁ couts₁)
    · simp [bit, hc] at hripple
      exfalso
      apply (Nat.not_le_of_lt hsumPow)
      rw [← hripple]
      omega
    · simpa [bit, hc] using hripple
  have hredCarryFresh' : ∀ w ∈ couts₂,
      run (ripple addCols cin₁ couts₁) st w = false := by
    intro w hw
    rw [run_other_targets _ _ w (hredCarryFresh w hw).2, (hredCarryFresh w hw).1]
  have hredSumFresh' : ∀ c ∈ redCols,
      run (ripple addCols cin₁ couts₁) st c.2.2 = false := by
    intro c hc
    rw [run_other_targets _ _ c.2.2 (hredSumFresh c hc).2, (hredSumFresh c hc).1]
  have hredBFresh' : ∀ c ∈ redCols,
      run (ripple addCols cin₁ couts₁) st c.2.1 = false := by
    intro c hc
    rw [run_other_targets _ _ c.2.1 (hredBFresh c hc).2, (hredBFresh c hc).1]
  have hcin₂Fresh' : run (ripple addCols cin₁ couts₁) st cin₂ = false := by
    rw [run_other_targets _ _ cin₂ hcin₂Fresh.2, hcin₂Fresh.1]
  have hconstBound : 2 ^ redCols.length - modulus < 2 ^ redCols.length := by
    rw [hwidth]
    omega
  have hreduce := addConst_correct redCols cin₂ couts₂
    (2 ^ redCols.length - modulus) (run (ripple addCols cin₁ couts₁) st)
    hredLen hredOK hredBNodup hredAB hredSB hredCarryB hredCinB
    hredCarryFresh' hredSumFresh' hredBFresh' hcin₂Fresh' hconstBound
  rw [hredA, hsum] at hreduce
  have hcompute :
      run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st =
        run (addConst redCols cin₂ couts₂ (2 ^ redCols.length - modulus))
          (run (ripple addCols cin₁ couts₁) st) := by
    rw [modAddCompute, run_append]
  have hsumPreserved :
      regValue (addCols.map (fun c => c.2.2))
          (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st) =
        regValue (addCols.map (fun c => c.1)) st +
          regValue (addCols.map (fun c => c.2.1)) st := by
    rw [hcompute]
    calc
      regValue (addCols.map (fun c => c.2.2))
          (run (addConst redCols cin₂ couts₂ (2 ^ redCols.length - modulus))
            (run (ripple addCols cin₁ couts₁) st)) =
          regValue (addCols.map (fun c => c.2.2))
            (run (ripple addCols cin₁ couts₁) st) := by
              apply regValue_congr
              intro w hw
              have hwred : w ∈ redCols.map (fun c => c.1) := by
                rw [hredA]
                exact hw
              exact addConst_other w redCols cin₂ couts₂
                (2 ^ redCols.length - modulus) _ (hredAB w hwred)
                (fun c hc hEq => hredAS w hwred (hEq ▸ List.mem_map_of_mem hc))
                (fun x hx hEq => hredACarry w hwred (hEq ▸ hx))
      _ = _ := hsum
  have hcandidate :
      regValue (redCols.map (fun c => c.2.2))
          (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st) +
        2 ^ addCols.length *
          (if run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st
              (carryOut cin₂ couts₂) then 1 else 0) =
        (regValue (addCols.map (fun c => c.1)) st +
          regValue (addCols.map (fun c => c.2.1)) st) +
          (2 ^ addCols.length - modulus) := by
    rw [hcompute]
    simpa [bit, hwidth] using hreduce
  have houtFresh' : ∀ c ∈ selectCols,
      run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st c.2.2 = false := by
    intro c hc
    rw [run_other_targets _ _ c.2.2 (houtFresh c hc).2, (houtFresh c hc).1]
  have hselected := selectPoint_correct (carryOut cin₂ couts₂) selectCols
    (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st)
    hselectOK houtFresh'
  rw [hselectY, hselectX, hsumPreserved] at hselected
  have hyBound :
      regValue (redCols.map (fun c => c.2.2))
          (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st) <
        2 ^ addCols.length := by
    have h := regValue_lt_two_pow (redCols.map (fun c => c.2.2))
      (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st)
    simpa [List.length_map, hwidth] using h
  have hreduced := reduceOnce_select_eq_mod modulus (2 ^ addCols.length)
    (regValue (addCols.map (fun c => c.1)) st +
      regValue (addCols.map (fun c => c.2.1)) st)
    (regValue (redCols.map (fun c => c.2.2))
      (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st))
    (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st
      (carryOut cin₂ couts₂)) hmod hfit hsumBound hyBound hcandidate
  have hforward :
      regValue (selectCols.map (fun c => c.2.2))
          (run (selectPoint (carryOut cin₂ couts₂) selectCols)
            (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st)) =
        (regValue (addCols.map (fun c => c.1)) st +
          regValue (addCols.map (fun c => c.2.1)) st) % modulus :=
    hselected.trans hreduced
  rw [modAdd, run_append, run_append]
  calc
    regValue (selectCols.map (fun c => c.2.2))
        (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus).reverse
          (run (selectPoint (carryOut cin₂ couts₂) selectCols)
            (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st))) =
      regValue (selectCols.map (fun c => c.2.2))
        (run (selectPoint (carryOut cin₂ couts₂) selectCols)
          (run (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) st)) := by
            apply regValue_congr
            intro w hw
            apply run_other_targets
            simp only [List.map_reverse, List.mem_reverse]
            simp only [List.mem_map] at hw
            obtain ⟨c, hc, rfl⟩ := hw
            exact (houtFresh c hc).2
    _ = _ := hforward

theorem modAddCompute_tCount (addCols redCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (hadd : couts₁.length = addCols.length)
    (hred : couts₂.length = redCols.length) (hlen : redCols.length = addCols.length) :
    tCount (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus)
      = 42 * addCols.length := by
  rw [modAddCompute, tCount_append, ripple_tCount _ _ _ hadd,
    addConst_tCount _ _ _ _ hred]
  omega

theorem modAdd_tCount (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) (modulus : Nat)
    (hadd : couts₁.length = addCols.length) (hred : couts₂.length = redCols.length)
    (hlen₁ : redCols.length = addCols.length) (hlen₂ : selectCols.length = addCols.length) :
    tCount (modAdd addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus)
      = 91 * addCols.length := by
  rw [modAdd, tCount_append, tCount_append, tCount_reverse,
    modAddCompute_tCount _ _ _ _ _ _ _ hadd hred hlen₁, selectPoint_tCount]
  omega

theorem modAddCompute_HPFree (addCols redCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) :
    HPFree (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modAddCompute, hpFree_append]
  exact ⟨ripple_HPFree _ _ _, addConst_HPFree _ _ _ _⟩

theorem modAddCompute_wellFormed (addCols redCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (ha : wiresOK addCols cin₁ couts₁) (hr : wiresOK redCols cin₂ couts₂) :
    CircuitWellFormed (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modAddCompute, circuitWellFormed_append]
  exact ⟨ripple_wellFormed _ _ _ ha, addConst_wellFormed _ _ _ _ hr⟩

theorem modAdd_HPFree (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) :
    HPFree (modAdd addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modAdd, hpFree_append, hpFree_append]
  have hc := modAddCompute_HPFree addCols redCols cin₁ couts₁ cin₂ couts₂ modulus
  exact ⟨⟨hc, selectPoint_HPFree _ _⟩, hpFree_reverse _ hc⟩

theorem modAdd_wellFormed (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) (modulus : Nat)
    (ha : wiresOK addCols cin₁ couts₁) (hr : wiresOK redCols cin₂ couts₂)
    (hs : selectOK (carryOut cin₂ couts₂) selectCols) :
    CircuitWellFormed (modAdd addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modAdd, circuitWellFormed_append, circuitWellFormed_append]
  have hc := modAddCompute_wellFormed addCols redCols cin₁ couts₁ cin₂ couts₂ modulus ha hr
  exact ⟨⟨hc, selectPoint_wellFormed _ _ hs⟩, wellFormed_reverse _ hc⟩

/-- The Bennett tail restores every non-output wire.  This is the reusable-work guarantee:
all arithmetic sum, constant-scratch, and carry wires return to their input values, while the
fresh selector output is retained.  The output must be outside the full compute support, not
merely outside its target list, because changing a later inverse control would spoil cleanup. -/
theorem modAdd_clean
    (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (st : BasisState)
    (ha : wiresOK addCols cin₁ couts₁) (hr : wiresOK redCols cin₂ couts₂)
    (hs : selectOK (carryOut cin₂ couts₂) selectCols)
    (hout : ∀ w ∈ selectCols.map (fun c => c.2.2),
      w ∉ circuitWires (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus)) :
    ∀ w, w ∉ selectCols.map (fun c => c.2.2) →
      run (modAdd addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) st w = st w := by
  let compute := modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus
  let selector := selectPoint (carryOut cin₂ couts₂) selectCols
  have hcomputeHP : HPFree compute :=
    modAddCompute_HPFree addCols redCols cin₁ couts₁ cin₂ couts₂ modulus
  have hcomputeWF : CircuitWellFormed compute :=
    modAddCompute_wellFormed addCols redCols cin₁ couts₁ cin₂ couts₂ modulus ha hr
  have hsupport : ∀ u ∈ circuitWires compute,
      run selector (run compute st) u = run compute st u := by
    intro u hu
    apply selectPoint_other (carryOut cin₂ couts₂) u selectCols _ hs
    intro huo
    exact (hout u huo) hu
  have hreverseSupport : ∀ g ∈ compute.reverse, ∀ u ∈ gateWires g,
      u ∈ circuitWires compute := by
    intro g hg u hu
    simp only [circuitWires, List.mem_flatMap]
    exact ⟨g, by simpa using hg, hu⟩
  have hreverseAgree := run_congr_on compute.reverse (circuitWires compute)
    (run selector (run compute st)) (run compute st) hreverseSupport hsupport
  have hcancel := run_reverse_cancel compute st hcomputeHP hcomputeWF
  intro w hw
  change run (compute ++ selector ++ compute.reverse) st w = st w
  rw [run_append, run_append]
  by_cases htarget : w ∈ compute.map gateTarget
  · have hwsupport : w ∈ circuitWires compute := by
      simp only [List.mem_map] at htarget
      obtain ⟨g, hg, rfl⟩ := htarget
      simp only [circuitWires, List.mem_flatMap]
      exact ⟨g, hg, gateTarget_mem_gateWires g⟩
    calc
      run compute.reverse (run selector (run compute st)) w =
          run compute.reverse (run compute st) w := hreverseAgree w hwsupport
      _ = st w := congrFun hcancel w
  · rw [run_other_targets compute.reverse _ w (by simpa using htarget),
      selectPoint_other (carryOut cin₂ couts₂) w selectCols _ hs hw,
      run_other_targets compute st w htarget]

namespace ModAddSupport

/-! ## Syntactic support -/

/-- `Gate.UsesOnly` is exactly containment of the complete gate support. -/
theorem gate_usesOnly_iff (ws : List Wire) (g : Gate) :
    g.UsesOnly ws ↔ ∀ w ∈ gateWires g, w ∈ ws := by
  cases g <;> simp [Gate.UsesOnly, gateWires]

/-- The gatewise and flattened presentations of a circuit footprint agree. -/
theorem circuitUsesOnly_iff_support (ws : List Wire) (c : Circuit) :
    CircuitUsesOnly ws c ↔ ∀ w ∈ circuitWires c, w ∈ ws := by
  constructor
  · intro h w hw
    simp only [circuitWires, List.mem_flatMap] at hw
    obtain ⟨g, hg, hwg⟩ := hw
    exact (gate_usesOnly_iff ws g).mp (h g hg) w hwg
  · intro h g hg
    apply (gate_usesOnly_iff ws g).mpr
    intro w hw
    apply h w
    simp only [circuitWires, List.mem_flatMap]
    exact ⟨g, hg, hw⟩

theorem circuitUsesOnly_mono {small big : List Wire} {c : Circuit}
    (h : CircuitUsesOnly small c) (hsub : ∀ w ∈ small, w ∈ big) :
    CircuitUsesOnly big c := by
  intro g hg
  apply (gate_usesOnly_iff big g).mpr
  intro w hw
  exact hsub w ((gate_usesOnly_iff small g).mp (h g hg) w hw)

@[simp] theorem circuitUsesOnly_nil (ws : List Wire) :
    CircuitUsesOnly ws ([] : Circuit) := by
  intro g hg
  simp at hg

theorem circuitUsesOnly_append (ws : List Wire) (c₁ c₂ : Circuit) :
    CircuitUsesOnly ws (c₁ ++ c₂) ↔
      CircuitUsesOnly ws c₁ ∧ CircuitUsesOnly ws c₂ := by
  constructor
  · intro h
    constructor
    · intro g hg
      exact h g (List.mem_append_left c₂ hg)
    · intro g hg
      exact h g (List.mem_append_right c₁ hg)
  · intro h g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.1 g hg
    · exact h.2 g hg

theorem circuitUsesOnly_reverse (ws : List Wire) (c : Circuit) :
    CircuitUsesOnly ws c.reverse ↔ CircuitUsesOnly ws c := by
  constructor <;> intro h g hg
  · exact h g (by simpa using hg)
  · exact h g (by simpa using hg)

/-- The complete five-wire footprint of a full-adder cell. -/
theorem fullAdder_usesOnly (a b cin s co : Wire) :
    CircuitUsesOnly [a, b, cin, s, co] (fullAdder a b cin s co) := by
  simp [CircuitUsesOnly, fullAdder, Gate.UsesOnly]

/-- Flatten the three role registers of a column list. -/
def colsWires (cols : List (Wire × Wire × Wire)) : List Wire :=
  cols.flatMap (fun c => [c.1, c.2.1, c.2.2])

/-- All inputs, threaded carries, and sums that a ripple circuit may use. -/
def rippleFootprint (cols : List (Wire × Wire × Wire))
    (cin : Wire) (couts : List Wire) : List Wire :=
  cin :: (couts ++ colsWires cols)

/-- A ripple circuit stays inside its column/carry footprint, even for truncated `couts`. -/
theorem ripple_usesOnly :
    ∀ (cols : List (Wire × Wire × Wire)) (cin : Wire) (couts : List Wire),
      CircuitUsesOnly (rippleFootprint cols cin couts) (ripple cols cin couts) := by
  intro cols
  induction cols with
  | nil => intro cin couts; exact circuitUsesOnly_nil _
  | cons head rest ih =>
      intro cin couts
      obtain ⟨a,b,s⟩ := head
      cases couts with
      | nil => exact circuitUsesOnly_nil _
      | cons co cs =>
          rw [ripple, circuitUsesOnly_append]
          constructor
          · exact circuitUsesOnly_mono (fullAdder_usesOnly a b cin s co) (by
              intro w hw
              simp only [List.mem_cons] at hw
              simp only [rippleFootprint, colsWires, List.flatMap_cons,
                List.mem_cons, List.mem_append, List.mem_flatMap]
              rcases hw with rfl | rfl | rfl | rfl | rfl | hw
              · simp
              · simp
              · simp
              · simp
              · simp
              · contradiction)
          · exact circuitUsesOnly_mono (ih co cs) (by
              intro w hw
              simp only [rippleFootprint, colsWires, List.flatMap_cons,
                List.mem_cons, List.mem_append, List.mem_flatMap] at hw ⊢
              rcases hw with rfl | hw | ⟨c, hc, hcw⟩
              · exact Or.inr (Or.inl (Or.inl rfl))
              · exact Or.inr (Or.inl (Or.inr hw))
              · exact Or.inr (Or.inr (Or.inr ⟨c, hc, hcw⟩)))

/-- Constant addition has the same footprint as its ripple core: its loaded B-register is
already one of the column roles. -/
theorem addConst_usesOnly (cols : List (Wire × Wire × Wire))
    (cin : Wire) (couts : List Wire) (k : Nat) :
    CircuitUsesOnly (rippleFootprint cols cin couts) (addConst cols cin couts k) := by
  have hb : ∀ w ∈ cols.map (fun c => c.2.1), w ∈ rippleFootprint cols cin couts := by
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨c, hc, rfl⟩ := hw
    simp only [rippleFootprint, List.mem_cons, List.mem_append, colsWires, List.mem_flatMap]
    exact Or.inr (Or.inr ⟨c, hc, by simp⟩)
  rw [addConst, circuitUsesOnly_append, circuitUsesOnly_append]
  exact ⟨⟨circuitUsesOnly_mono (Arithmetic.loadConst_usesOnly _ k) hb,
    ripple_usesOnly cols cin couts⟩,
    circuitUsesOnly_mono (Arithmetic.loadConst_usesOnly _ k) hb⟩

/-- The owner registers A/B/O followed by all modular-addition work registers. -/
def modAddAllWires
    (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) : List Wire :=
  addCols.map (fun c => c.1) ++
  addCols.map (fun c => c.2.1) ++
  selectCols.map (fun c => c.2.2) ++
  addCols.map (fun c => c.2.2) ++
  redCols.map (fun c => c.2.1) ++
  redCols.map (fun c => c.2.2) ++
  [cin₁] ++ couts₁ ++ [cin₂] ++ couts₂

theorem carryOut_mem_footprint (cin : Wire) (couts : List Wire) :
    carryOut cin couts ∈ cin :: couts := by
  induction couts generalizing cin with
  | nil => simp [carryOut]
  | cons co cs ih =>
      rw [carryOut]
      exact List.mem_cons_of_mem cin (ih co)

/-- Every control and target of `modAdd` belongs to its declared register layout. -/
theorem modAdd_usesOnly
    (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (hredA : redCols.map (fun c => c.1) = addCols.map (fun c => c.2.2))
    (hselectX : selectCols.map (fun c => c.1) = addCols.map (fun c => c.2.2))
    (hselectY : selectCols.map (fun c => c.2.1) = redCols.map (fun c => c.2.2)) :
    CircuitUsesOnly (modAddAllWires addCols redCols selectCols cin₁ couts₁ cin₂ couts₂)
      (modAdd addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  let all := modAddAllWires addCols redCols selectCols cin₁ couts₁ cin₂ couts₂
  have hadd : ∀ w ∈ rippleFootprint addCols cin₁ couts₁, w ∈ all := by
    intro w hw
    simp only [rippleFootprint, List.mem_cons, List.mem_append, colsWires,
      List.mem_flatMap] at hw
    rcases hw with rfl | hw
    · simp [all, modAddAllWires]
    · rcases hw with hw | ⟨c, hc, hw⟩
      · simp [all, modAddAllWires, hw]
      · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
        rcases hw' with rfl | rfl | rfl
        · simp [all, modAddAllWires, List.mem_map_of_mem hc]
        · simp [all, modAddAllWires, List.mem_map_of_mem hc]
        · simp [all, modAddAllWires, List.mem_map_of_mem hc]
  have hred : ∀ w ∈ rippleFootprint redCols cin₂ couts₂, w ∈ all := by
    intro w hw
    simp only [rippleFootprint, List.mem_cons, List.mem_append, colsWires,
      List.mem_flatMap] at hw
    rcases hw with rfl | hw
    · simp [all, modAddAllWires]
    · rcases hw with hw | ⟨c, hc, hw⟩
      · simp [all, modAddAllWires, hw]
      · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
        rcases hw' with rfl | rfl | rfl
        · have hm : c.1 ∈ addCols.map (fun d => d.2.2) := by
            rw [← hredA]
            exact List.mem_map_of_mem hc
          simp [all, modAddAllWires, hm]
        · simp [all, modAddAllWires, List.mem_map_of_mem hc]
        · simp [all, modAddAllWires, List.mem_map_of_mem hc]
  have hselect : ∀ w ∈ selectFootprint (carryOut cin₂ couts₂) selectCols, w ∈ all := by
    intro w hw
    simp only [selectFootprint, List.mem_cons, List.mem_flatMap] at hw
    rcases hw with rfl | ⟨c, hc, hw⟩
    · have hcarry := carryOut_mem_footprint cin₂ couts₂
      simp only [List.mem_cons] at hcarry
      rcases hcarry with hcarry | hcarry
      · rw [hcarry]
        simp [all, modAddAllWires]
      · simp [all, modAddAllWires, hcarry]
    · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
      rcases hw' with rfl | rfl | rfl
      · have hm : c.1 ∈ addCols.map (fun d => d.2.2) := by
          rw [← hselectX]
          exact List.mem_map_of_mem hc
        simp [all, modAddAllWires, hm]
      · have hm : c.2.1 ∈ redCols.map (fun d => d.2.2) := by
          rw [← hselectY]
          exact List.mem_map_of_mem hc
        simp [all, modAddAllWires, hm]
      · simp [all, modAddAllWires, List.mem_map_of_mem hc]
  rw [modAdd, circuitUsesOnly_append, circuitUsesOnly_append]
  have hcompute : CircuitUsesOnly all
      (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) := by
    rw [modAddCompute, circuitUsesOnly_append]
    exact ⟨circuitUsesOnly_mono (ripple_usesOnly addCols cin₁ couts₁) hadd,
      circuitUsesOnly_mono (addConst_usesOnly redCols cin₂ couts₂ _) hred⟩
  exact ⟨⟨hcompute, circuitUsesOnly_mono (selectPoint_usesOnly _ _) hselect⟩,
    (circuitUsesOnly_reverse all _).2 hcompute⟩

/-- The compute/uncompute core excludes selector outputs from its declared support. -/
theorem modAddCompute_usesOnly
    (addCols redCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (hredA : redCols.map (fun c => c.1) = addCols.map (fun c => c.2.2)) :
    CircuitUsesOnly
      (addCols.map (fun c => c.1) ++
       addCols.map (fun c => c.2.1) ++
       addCols.map (fun c => c.2.2) ++
       redCols.map (fun c => c.2.1) ++
       redCols.map (fun c => c.2.2) ++
       [cin₁] ++ couts₁ ++ [cin₂] ++ couts₂)
      (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  let all :=
    addCols.map (fun c => c.1) ++
    addCols.map (fun c => c.2.1) ++
    addCols.map (fun c => c.2.2) ++
    redCols.map (fun c => c.2.1) ++
    redCols.map (fun c => c.2.2) ++
    [cin₁] ++ couts₁ ++ [cin₂] ++ couts₂
  have hadd : ∀ w ∈ rippleFootprint addCols cin₁ couts₁, w ∈ all := by
    intro w hw
    simp only [rippleFootprint, List.mem_cons, List.mem_append,
      colsWires, List.mem_flatMap] at hw
    rcases hw with rfl | hw
    · simp [all]
    · rcases hw with hw | ⟨c, hc, hw⟩
      · simp [all, hw]
      · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
        rcases hw' with rfl | rfl | rfl <;> simp [all, List.mem_map_of_mem hc]
  have hred : ∀ w ∈ rippleFootprint redCols cin₂ couts₂, w ∈ all := by
    intro w hw
    simp only [rippleFootprint, List.mem_cons, List.mem_append,
      colsWires, List.mem_flatMap] at hw
    rcases hw with rfl | hw
    · simp [all]
    · rcases hw with hw | ⟨c, hc, hw⟩
      · simp [all, hw]
      · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
        rcases hw' with rfl | rfl | rfl
        · have hm : c.1 ∈ addCols.map (fun d => d.2.2) := by
            rw [← hredA]
            exact List.mem_map_of_mem hc
          simp [all, hm]
        · simp [all, List.mem_map_of_mem hc]
        · simp [all, List.mem_map_of_mem hc]
  rw [modAddCompute, circuitUsesOnly_append]
  exact ⟨circuitUsesOnly_mono (ripple_usesOnly addCols cin₁ couts₁) hadd,
    circuitUsesOnly_mono (addConst_usesOnly redCols cin₂ couts₂ _) hred⟩

end ModAddSupport

/-! ## Clean modular-addition contract -/

/-- Public `A`, public `B`, public output `O`, followed by each owned work register exactly
once: unreduced sum `X`, loaded constant `K`, reduction candidate `Y`, then the two carry
banks and their carry-ins. The selector flag is the final wire of `couts₂`, so it is not
listed a second time. -/
def modAddLayout
    (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) :
    RegisterLayout where
  lhs := addCols.map (fun c => c.1)
  rhs := addCols.map (fun c => c.2.1)
  out := selectCols.map (fun c => c.2.2)
  work :=
    addCols.map (fun c => c.2.2) ++
    redCols.map (fun c => c.2.1) ++
    redCols.map (fun c => c.2.2) ++
    [cin₁] ++ couts₁ ++ [cin₂] ++ couts₂

/-- The genuine construction parameters of one concrete modular-adder instance.

All cross-register disjointness and stage-freshness facts are derived inside `modAdd_contract`
from `RegisterLayout.Valid`; callers do not have to restate consequences of its global
`Nodup` premise. -/
structure ModAddWiring
    (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) : Prop where
  addLen : couts₁.length = addCols.length
  redLen : couts₂.length = redCols.length
  width : redCols.length = addCols.length
  selectLen : selectCols.length = addCols.length
  addOK : wiresOK addCols cin₁ couts₁
  redOK : wiresOK redCols cin₂ couts₂
  selectOK : ShorECDLP.selectOK (carryOut cin₂ couts₂) selectCols
  redA : redCols.map (fun c => c.1) = addCols.map (fun c => c.2.2)
  selectX : selectCols.map (fun c => c.1) = addCols.map (fun c => c.2.2)
  selectY : selectCols.map (fun c => c.2.1) = redCols.map (fun c => c.2.2)
  modulusPos : 0 < modulus
  fit : 2 * modulus ≤ 2 ^ addCols.length

/-- Any target occurrence contributes a support occurrence. -/
private theorem mem_circuitWires_of_mem_targets (c : Circuit) (w : Wire)
    (h : w ∈ c.map gateTarget) : w ∈ circuitWires c := by
  simp only [List.mem_map] at h
  obtain ⟨g, hg, rfl⟩ := h
  simp only [circuitWires, List.mem_flatMap]
  exact ⟨g, hg, gateTarget_mem_gateWires g⟩

/-- **M1.3.2 contract.** The exact `modAdd` term is correct, clean, confined to its declared
registers, counted, H/P-free, and physically well-formed. -/
theorem modAdd_contract
    (addCols redCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (wiring : ModAddWiring addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) :
    ModAddContract
      (modAdd addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus)
      (modAddLayout addCols redCols selectCols cin₁ couts₁ cin₂ couts₂)
      modulus (91 * addCols.length) := by
  let layout := modAddLayout addCols redCols selectCols cin₁ couts₁ cin₂ couts₂
  let program := modAdd addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus
  refine {
    correct := ?_
    usesOnly := ?_
    counted := ?_
    hpFree := ?_
    wellFormed := ?_
  }
  · intro st hvalid ha hb hclean
    dsimp only
    let A := addCols.map (fun c => c.1)
    let B := addCols.map (fun c => c.2.1)
    let O := selectCols.map (fun c => c.2.2)
    let X := addCols.map (fun c => c.2.2)
    let K := redCols.map (fun c => c.2.1)
    let Y := redCols.map (fun c => c.2.2)

    have hnodup :
        (A ++ (B ++ (O ++ (X ++ (K ++ (Y ++
          ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂))))))))).Nodup := by
      simpa [A, B, O, X, K, Y, layout, modAddLayout, RegisterLayout.allWires,
        List.append_assoc] using hvalid.2.2

    rcases List.nodup_append.mp hnodup with ⟨_, htailA, hAcrossA⟩
    rcases List.nodup_append.mp htailA with ⟨_, htailB, hAcrossB⟩
    rcases List.nodup_append.mp htailB with ⟨_, htailO, hAcrossO⟩
    rcases List.nodup_append.mp htailO with ⟨_, htailX, hAcrossX⟩
    rcases List.nodup_append.mp htailX with ⟨hKNodup, htailK, hAcrossK⟩
    rcases List.nodup_append.mp htailK with ⟨_, htailY, hAcrossY⟩
    rcases List.nodup_append.mp htailY with ⟨_, htailCin₁, hAcrossCin₁⟩
    rcases List.nodup_append.mp htailCin₁ with ⟨_, _, hAcrossCouts₁⟩

    have hworkClean : Clean layout.work st := by
      intro w hw
      exact hclean w (List.mem_append_right _ hw)
    have haddCarryFresh : ∀ w ∈ couts₁, st w = false := by
      intro w hw
      apply hworkClean w
      simp [layout, modAddLayout, hw]
    have haddSumFresh : ∀ c ∈ addCols, st c.2.2 = false := by
      intro c hc
      apply hworkClean c.2.2
      simp [layout, modAddLayout, List.mem_map_of_mem hc]
    have hcin₁Fresh : st cin₁ = false := by
      apply hworkClean cin₁
      simp [layout, modAddLayout]

    have hredAB : ∀ w ∈ X, w ∉ K := by
      intro w hwX hwK
      exact hAcrossX w hwX w (by simp [hwK]) rfl
    have hredSB : ∀ w ∈ Y, w ∉ K := by
      intro w hwY hwK
      exact hAcrossK w hwK w (by simp [hwY]) rfl
    have hredCarryB : ∀ w ∈ couts₂, w ∉ K := by
      intro w hwC hwK
      exact hAcrossK w hwK w (by simp [hwC]) rfl
    have hredCinB : cin₂ ∉ K := by
      intro hwK
      exact hAcrossK cin₂ hwK cin₂ (by simp) rfl
    have hredAS : ∀ w ∈ X, w ∉ Y := by
      intro w hwX hwY
      exact hAcrossX w hwX w (by simp [hwY]) rfl
    have hredACarry : ∀ w ∈ X, w ∉ couts₂ := by
      intro w hwX hwC
      exact hAcrossX w hwX w (by simp [hwC]) rfl

    have htargetSupport : ∀ w ∈ (ripple addCols cin₁ couts₁).map gateTarget,
        w ∈ ModAddSupport.rippleFootprint addCols cin₁ couts₁ := by
      intro w hw
      exact (ModAddSupport.circuitUsesOnly_iff_support _ _).mp
        (ModAddSupport.ripple_usesOnly addCols cin₁ couts₁) w
        (mem_circuitWires_of_mem_targets _ _ hw)

    have hnotRippleK : ∀ w ∈ K,
        w ∉ (ripple addCols cin₁ couts₁).map gateTarget := by
      intro w hwK hwTarget
      have hw := htargetSupport w hwTarget
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append,
        ModAddSupport.colsWires, List.mem_flatMap] at hw
      rcases hw with rfl | hw
      · exact hAcrossK w hwK w (by simp) rfl
      · rcases hw with hw | ⟨c, hc, hw⟩
        · exact hAcrossK w hwK w (by simp [hw]) rfl
        · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
          rcases hw' with rfl | rfl | rfl
          · exact hAcrossA c.1 (by simp [A, List.mem_map_of_mem hc]) c.1
              (by simp [K, hwK]) rfl
          · exact hAcrossB c.2.1 (by simp [B, List.mem_map_of_mem hc]) c.2.1
              (by simp [K, hwK]) rfl
          · exact hAcrossX c.2.2 (by simp [X, List.mem_map_of_mem hc]) c.2.2
              (by simp [K, hwK]) rfl
    have hnotRippleY : ∀ w ∈ Y,
        w ∉ (ripple addCols cin₁ couts₁).map gateTarget := by
      intro w hwY hwTarget
      have hw := htargetSupport w hwTarget
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append,
        ModAddSupport.colsWires, List.mem_flatMap] at hw
      rcases hw with rfl | hw
      · exact hAcrossY w hwY w (by simp) rfl
      · rcases hw with hw | ⟨c, hc, hw⟩
        · exact hAcrossY w hwY w (by simp [hw]) rfl
        · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
          rcases hw' with rfl | rfl | rfl
          · exact hAcrossA c.1 (by simp [A, List.mem_map_of_mem hc]) c.1
              (by simp [Y, hwY]) rfl
          · exact hAcrossB c.2.1 (by simp [B, List.mem_map_of_mem hc]) c.2.1
              (by simp [Y, hwY]) rfl
          · exact hAcrossX c.2.2 (by simp [X, List.mem_map_of_mem hc]) c.2.2
              (by simp [Y, hwY]) rfl
    have hnotRippleCin₂ : cin₂ ∉ (ripple addCols cin₁ couts₁).map gateTarget := by
      intro hwTarget
      have hw := htargetSupport cin₂ hwTarget
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append,
        ModAddSupport.colsWires, List.mem_flatMap] at hw
      rcases hw with hEq | hw
      · exact hAcrossCin₁ cin₁ (by simp) cin₂ (by simp) hEq.symm
      · rcases hw with hw | ⟨c, hc, hw⟩
        · exact hAcrossCouts₁ cin₂ hw cin₂ (by simp) rfl
        · have hw' : cin₂ = c.1 ∨ cin₂ = c.2.1 ∨ cin₂ = c.2.2 := by simpa using hw
          rcases hw' with hw' | hw' | hw'
          · subst cin₂
            exact hAcrossA c.1 (by simp [A, List.mem_map_of_mem hc]) c.1 (by simp) rfl
          · subst cin₂
            exact hAcrossB c.2.1 (by simp [B, List.mem_map_of_mem hc]) c.2.1 (by simp) rfl
          · subst cin₂
            exact hAcrossX c.2.2 (by simp [X, List.mem_map_of_mem hc]) c.2.2 (by simp) rfl
    have hnotRippleCouts₂ : ∀ w ∈ couts₂,
        w ∉ (ripple addCols cin₁ couts₁).map gateTarget := by
      intro w hwC hwTarget
      have hw := htargetSupport w hwTarget
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append,
        ModAddSupport.colsWires, List.mem_flatMap] at hw
      rcases hw with rfl | hw
      · exact hAcrossCin₁ w (by simp) w (by simp [hwC]) rfl
      · rcases hw with hw | ⟨c, hc, hw⟩
        · exact hAcrossCouts₁ w hw w (by simp [hwC]) rfl
        · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
          rcases hw' with rfl | rfl | rfl
          · exact hAcrossA c.1 (by simp [A, List.mem_map_of_mem hc]) c.1
              (by simp [hwC]) rfl
          · exact hAcrossB c.2.1 (by simp [B, List.mem_map_of_mem hc]) c.2.1
              (by simp [hwC]) rfl
          · exact hAcrossX c.2.2 (by simp [X, List.mem_map_of_mem hc]) c.2.2
              (by simp [hwC]) rfl

    have hredCarryFresh : ∀ w ∈ couts₂,
        st w = false ∧ w ∉ (ripple addCols cin₁ couts₁).map gateTarget := by
      intro w hw
      constructor
      · apply hworkClean w
        simp [layout, modAddLayout, hw]
      · exact hnotRippleCouts₂ w hw
    have hredSumFresh : ∀ c ∈ redCols,
        st c.2.2 = false ∧ c.2.2 ∉ (ripple addCols cin₁ couts₁).map gateTarget := by
      intro c hc
      constructor
      · apply hworkClean c.2.2
        simp [layout, modAddLayout, List.mem_map_of_mem hc]
      · apply hnotRippleY c.2.2
        exact List.mem_map_of_mem hc
    have hredBFresh : ∀ c ∈ redCols,
        st c.2.1 = false ∧ c.2.1 ∉ (ripple addCols cin₁ couts₁).map gateTarget := by
      intro c hc
      constructor
      · apply hworkClean c.2.1
        simp [layout, modAddLayout, List.mem_map_of_mem hc]
      · apply hnotRippleK c.2.1
        exact List.mem_map_of_mem hc
    have hcin₂Fresh : st cin₂ = false ∧
        cin₂ ∉ (ripple addCols cin₁ couts₁).map gateTarget := by
      constructor
      · apply hworkClean cin₂
        simp [layout, modAddLayout]
      · exact hnotRippleCin₂

    have hcomputeSupport : ∀ w ∈ circuitWires
        (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus),
        w ∈ A ++ (B ++ (X ++ (K ++ (Y ++
          ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂))))))) := by
      simpa [A, B, X, K, Y] using
        (ModAddSupport.circuitUsesOnly_iff_support _ _).mp
          (ModAddSupport.modAddCompute_usesOnly
            addCols redCols cin₁ couts₁ cin₂ couts₂ modulus wiring.redA)
    have houtFreshSupport : ∀ w ∈ O,
        w ∉ circuitWires
          (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus) := by
      intro w hwO hwSupport
      have hw := hcomputeSupport w hwSupport
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hwA | hwB | hwX | hwK | hwY | hwCin₁ | hwCouts₁ | hwCin₂ | hwCouts₂
      · exact hAcrossA w hwA w (by simp [hwO]) rfl
      · exact hAcrossB w hwB w (by simp [hwO]) rfl
      · exact hAcrossO w hwO w (by simp [hwX]) rfl
      · exact hAcrossO w hwO w (by simp [hwK]) rfl
      · exact hAcrossO w hwO w (by simp [hwY]) rfl
      · subst w
        exact hAcrossO cin₁ hwO cin₁ (by simp) rfl
      · exact hAcrossO w hwO w (by simp [hwCouts₁]) rfl
      · subst w
        exact hAcrossO cin₂ hwO cin₂ (by simp) rfl
      · exact hAcrossO w hwO w (by simp [hwCouts₂]) rfl
    have houtFresh : ∀ c ∈ selectCols,
        st c.2.2 = false ∧
          c.2.2 ∉ (modAddCompute addCols redCols cin₁ couts₁ cin₂ couts₂ modulus).map
            gateTarget := by
      intro c hc
      have hco : c.2.2 ∈ O := List.mem_map_of_mem hc
      constructor
      · exact hclean c.2.2 (List.mem_append_left _ hco)
      · intro ht
        exact houtFreshSupport c.2.2 hco (mem_circuitWires_of_mem_targets _ _ ht)

    have hresult := modAdd_correct
      addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus st
      wiring.addLen wiring.redLen wiring.width wiring.addOK wiring.redOK wiring.selectOK
      wiring.redA wiring.selectX wiring.selectY wiring.modulusPos wiring.fit ha hb
      haddCarryFresh haddSumFresh hcin₁Fresh
      (by simpa [K] using hKNodup)
      (by simpa [X, K, wiring.redA] using hredAB)
      (by simpa [Y, K] using hredSB)
      (by simpa [K] using hredCarryB)
      (by simpa [K] using hredCinB)
      (by simpa [X, Y, wiring.redA] using hredAS)
      (by simpa [X, wiring.redA] using hredACarry)
      hredCarryFresh hredSumFresh hredBFresh hcin₂Fresh houtFresh

    have hrestore := modAdd_clean
      addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus st
      wiring.addOK wiring.redOK wiring.selectOK
      (by simpa [O] using houtFreshSupport)

    have hnodup' :
        (layout.lhs ++ (layout.rhs ++ (layout.out ++ layout.work))).Nodup := by
      simpa [RegisterLayout.allWires, List.append_assoc] using hvalid.2.2
    have hlhsOut : ∀ w ∈ layout.lhs, w ∉ layout.out := by
      intro w hw hwo
      exact (List.nodup_append.mp hnodup').2.2 w hw w (by simp [hwo]) rfl
    have htailNodup : (layout.rhs ++ (layout.out ++ layout.work)).Nodup :=
      (List.nodup_append.mp hnodup').2.1
    have hrhsOut : ∀ w ∈ layout.rhs, w ∉ layout.out := by
      intro w hw hwo
      exact (List.nodup_append.mp htailNodup).2.2 w hw w (by simp [hwo]) rfl
    have houtWorkNodup : (layout.out ++ layout.work).Nodup :=
      (List.nodup_append.mp htailNodup).2.1
    have hworkOut : ∀ w ∈ layout.work, w ∉ layout.out := by
      intro w hw hwo
      exact (List.nodup_append.mp houtWorkNodup).2.2 w hwo w hw rfl

    have hlhs : AgreesOn layout.lhs st (run program st) := by
      intro w hw
      exact hrestore w (hlhsOut w hw)
    have hrhs : AgreesOn layout.rhs st (run program st) := by
      intro w hw
      exact hrestore w (hrhsOut w hw)
    have hworkAfter : Clean layout.work (run program st) := by
      intro w hw
      rw [hrestore w (hworkOut w hw)]
      exact hworkClean w hw

    exact ⟨hlhs, hrhs, hresult, hworkAfter⟩

  · simpa [layout, RegisterLayout.allWires, modAddLayout,
      ModAddSupport.modAddAllWires] using
      (ModAddSupport.modAdd_usesOnly addCols redCols selectCols cin₁ couts₁ cin₂ couts₂
        modulus wiring.redA wiring.selectX wiring.selectY)

  · exact modAdd_tCount addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus
      wiring.addLen wiring.redLen wiring.width wiring.selectLen

  · exact modAdd_HPFree addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus

  · intro _
    exact modAdd_wellFormed addCols redCols selectCols cin₁ couts₁ cin₂ couts₂ modulus
      wiring.addOK wiring.redOK wiring.selectOK

end ShorECDLP
