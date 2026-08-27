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

`ModAddWiring` supplies the aligned registers, physical wire conditions, and
`2 * modulus <= 2^w`. For a valid `modAddLayout`, canonical inputs, and a clean output/work
area,

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

`modAdd_program_correct` and `modAdd_tCount` expose the final correctness and exact cost
directly for the same `modAdd` term. `modAdd_contract` packages those facts with locality and
physical-validity obligations for composition. Lower-level constant-addition and reduction
lemmas provide their proof.
-/

namespace ShorECDLP

open Classical

open Arithmetic
open scoped ArithmeticNotation

/-- **M1.3.1 — constant adder.** Load `c` into `constReg`, add it to `a`, then
unload it. The temporary constant register is restored by construction. -/
def addConst (a constReg sum : List Wire) (cin : Wire) (couts : List Wire)
    (c : Nat) : Circuit :=
  circuit! {
    loadConst constReg c;
    ripple a constReg sum cin couts;
    loadConst constReg c
  }

/-- Forward computation of the unreduced sum and the one-subtraction candidate. The exact
same `sum` register is the first ripple's output and the constant adder's input. -/
def modAddCompute (lhs rhs sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) : Circuit :=
  circuit! {
    ripple lhs rhs sum cin₁ couts₁;
    addConst sum constReg candidate cin₂ couts₂ (2 ^ sum.length - modulus)
  }

/-- Clean modular adder: compute both candidates, select into `out`, then reverse only the
candidate computation. The exact same `sum` and `candidate` registers feed the selector. -/
def modAdd (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) : Circuit :=
  let compute := modAddCompute lhs rhs sum constReg candidate
    cin₁ couts₁ cin₂ couts₂ modulus
  circuit! {
    compute;
    selectPoint (carryOut cin₂ couts₂) sum candidate out;
    compute.reverse
  }

/-- The carry-out wire lies among `cin :: couts`, so it avoids any register disjoint from both. -/
theorem carryOut_not_mem (bs : List Wire) :
    ∀ (cin : Wire) (couts : List Wire), cin ∉ bs → (∀ x ∈ couts, x ∉ bs) →
      carryOut cin couts ∉ bs
  | cin, [],      hcin, _      => by simpa [carryOut] using hcin
  | _,   co :: cs, _,   hcouts => by
      rw [carryOut]
      exact carryOut_not_mem bs co cs (hcouts co (List.mem_cons_self ..))
        (fun x hx => hcouts x (List.mem_cons_of_mem _ hx))

theorem addConst_correct
    (a constReg sum : List Wire) (cin : Wire) (couts : List Wire)
    (c : Nat) (st : BasisState)
    (hconstLen : constReg.length = a.length)
    (hwok : wiresOK a constReg sum cin couts)
    (hbnd : constReg.Nodup)
    (hAB : ∀ w ∈ a, w ∉ constReg)
    (hSB : ∀ w ∈ sum, w ∉ constReg)
    (hcoutB : ∀ x ∈ couts, x ∉ constReg)
    (hcinB : cin ∉ constReg)
    (hfc : ∀ x ∈ couts, st x = false)
    (hfs : ∀ w ∈ sum, st w = false)
    (hfb : ∀ w ∈ constReg, st w = false)
    (hfcin : st cin = false)
    (hc : c < 2 ^ a.length) :
    (⟪addConst a constReg sum cin couts c⟫ st)⟦ᵣsum⟧
      + 2 ^ a.length * bit (⟪addConst a constReg sum cin couts c⟫ st)
          (carryOut cin couts)
      = st⟦ᵣa⟧ + c := by
  have hcarryB : carryOut cin couts ∉ constReg :=
    carryOut_not_mem _ cin couts hcinB hcoutB
  rw [addConst, run_append, run_append]
  have hload : regValue constReg (run (loadConst constReg c) st) = c :=
    loadConst_correct _ c st hbnd hfb (by simpa [hconstLen] using hc)
  have hakeep : regValue a (run (loadConst constReg c) st) = regValue a st :=
    loadConst_regValue _ _ c st hAB
  have hcoutkeep : ∀ x ∈ couts, run (loadConst constReg c) st x = false :=
    fun x hx => loadConst_false x _ c st (hcoutB x hx) (hfc x hx)
  have hskeep : ∀ w ∈ sum, run (loadConst constReg c) st w = false :=
    fun w hw => loadConst_false w _ c st (hSB w hw) (hfs w hw)
  have hcinkeep : run (loadConst constReg c) st cin = false :=
    loadConst_false cin _ c st hcinB hfcin
  have hrip := ripple_correct a constReg sum cin couts
    (run (loadConst constReg c) st) hwok hcoutkeep hskeep
  rw [hload, hakeep] at hrip
  have hcinbit : bit (run (loadConst constReg c) st) cin = 0 := by
    rw [bit, hcinkeep]; rfl
  rw [hcinbit, Nat.add_zero] at hrip
  have hs_unload : regValue sum
      (run (loadConst constReg c)
        (run (ripple a constReg sum cin couts) (run (loadConst constReg c) st)))
      = regValue sum
        (run (ripple a constReg sum cin couts) (run (loadConst constReg c) st)) :=
    loadConst_regValue _ _ c _ hSB
  have hcarry_unload : bit (run (loadConst constReg c)
        (run (ripple a constReg sum cin couts) (run (loadConst constReg c) st)))
        (carryOut cin couts)
      = bit (run (ripple a constReg sum cin couts) (run (loadConst constReg c) st))
        (carryOut cin couts) := by
    rw [bit, bit, loadConst_other (carryOut cin couts) _ c _ hcarryB]
  rw [hs_unload, hcarry_unload, hrip]

/-- A constant adder changes only its sum and carry-output wires; its temporary constant
register is restored by the final `loadConst`. -/
theorem addConst_other (w : Wire) (a constReg sum : List Wire) (cin : Wire)
    (couts : List Wire) (c : Nat) (st : BasisState)
    (hb : w ∉ constReg) (hs : ∀ x ∈ sum, w ≠ x)
    (hc : ∀ x ∈ couts, w ≠ x) :
    run (addConst a constReg sum cin couts c) st w = st w := by
  rw [addConst, run_append, run_append,
    loadConst_other w _ c _ hb,
    ripple_other w a constReg sum cin couts _ hs hc,
    loadConst_other w _ c _ hb]

/-- The constant adder costs the same `21n` T as the underlying ripple (the loads are T-free).
Its `HPFree`/`WellFormed` land at M1.3.2, where they compose with `ripple_HPFree`/`_wellFormed`
into the deliverable modular adder's full contract. -/
theorem addConst_tCount (a constReg sum : List Wire) (cin : Wire)
    (couts : List Wire) (c : Nat)
    (hconst : constReg.length = a.length) (hsum : sum.length = a.length)
    (hcouts : couts.length = a.length) :
    tCount (addConst a constReg sum cin couts c) = 21 * a.length := by
  rw [addConst, tCount_append, tCount_append,
    ripple_tCount a constReg sum cin couts hconst hsum hcouts, loadConst_tCount]
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
theorem addConst_HPFree (a constReg sum : List Wire) (cin : Wire)
    (couts : List Wire) (c : Nat) : HPFree (addConst a constReg sum cin couts c) := by
  rw [addConst, hpFree_append, hpFree_append]
  exact ⟨⟨loadConst_HPFree _ _, ripple_HPFree _ _ _ _ _⟩, loadConst_HPFree _ _⟩

/-- The constant adder is well-formed whenever its ripple core is. -/
theorem addConst_wellFormed (a constReg sum : List Wire) (cin : Wire)
    (couts : List Wire) (c : Nat) (h : wiresOK a constReg sum cin couts) :
    CircuitWellFormed (addConst a constReg sum cin couts c) := by
  rw [addConst, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨loadConst_wellFormed _ _, ripple_wellFormed a constReg sum cin couts h⟩,
    loadConst_wellFormed _ _⟩

/-- **M1.3.2 — clean modular addition is correct.**

All six named registers have the same width. The second ripple reads the exact `sum` register
produced by the first, and the selector reads that same `sum` plus the exact `candidate`. The explicit
freshness/disjointness hypotheses are the gate-level layout obligations: the second stage's
work wires survive the first stage as zeroes, and the public output is outside the complete
compute circuit.  For canonical inputs and a width satisfying `2*modulus ≤ 2^width`, the
selected output is `(a+b) % modulus`. -/
theorem modAdd_correct
    (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (st : BasisState)
    (hsumLen : sum.length = lhs.length)
    (hconstLen : constReg.length = sum.length)
    (hcandidateLen : candidate.length = sum.length)
    (haddOK : wiresOK lhs rhs sum cin₁ couts₁)
    (hredOK : wiresOK sum constReg candidate cin₂ couts₂)
    (hselectOK : selectOK (carryOut cin₂ couts₂) sum candidate out)
    (hmod : 0 < modulus)
    (hfit : 2 * modulus ≤ 2 ^ lhs.length)
    (ha : st⟦ᵣlhs⟧ < modulus)
    (hb : st⟦ᵣrhs⟧ < modulus)
    (haddCarryFresh : ∀ w ∈ couts₁, st w = false)
    (haddSumFresh : ∀ w ∈ sum, st w = false)
    (hcin₁Fresh : st cin₁ = false)
    (hredBNodup : constReg.Nodup)
    (hredAB : ∀ w ∈ sum, w ∉ constReg)
    (hredSB : ∀ w ∈ candidate, w ∉ constReg)
    (hredCarryB : ∀ w ∈ couts₂, w ∉ constReg)
    (hredCinB : cin₂ ∉ constReg)
    (hredAS : ∀ w ∈ sum, w ∉ candidate)
    (hredACarry : ∀ w ∈ sum, w ∉ couts₂)
    (hredCarryFresh : ∀ w ∈ couts₂,
      st w = false ∧ w ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget)
    (hredSumFresh : ∀ w ∈ candidate,
      st w = false ∧ w ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget)
    (hredBFresh : ∀ w ∈ constReg,
      st w = false ∧ w ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget)
    (hcin₂Fresh : st cin₂ = false ∧
      cin₂ ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget)
    (houtFresh : ∀ w ∈ out,
      st w = false ∧
        w ∉ (modAddCompute lhs rhs sum constReg candidate
          cin₁ couts₁ cin₂ couts₂ modulus).map gateTarget) :
    (⟪modAdd lhs rhs out sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus⟫ st)⟦ᵣout⟧ =
      (st⟦ᵣlhs⟧ + st⟦ᵣrhs⟧) % modulus := by
  have hripple := ripple_correct lhs rhs sum cin₁ couts₁ st haddOK
    haddCarryFresh haddSumFresh
  have hcinbit : bit st cin₁ = 0 := by simp [bit, hcin₁Fresh]
  rw [hcinbit, Nat.add_zero] at hripple
  have hsumBound :
      regValue lhs st + regValue rhs st < 2 * modulus := by
    omega
  have hsumPow :
      regValue lhs st + regValue rhs st < 2 ^ lhs.length := by
    omega
  have hsum :
      regValue sum (run (ripple lhs rhs sum cin₁ couts₁) st) =
        regValue lhs st + regValue rhs st := by
    by_cases hc : run (ripple lhs rhs sum cin₁ couts₁) st (carryOut cin₁ couts₁)
    · simp [bit, hc] at hripple
      exfalso
      apply (Nat.not_le_of_lt hsumPow)
      rw [← hripple]
      omega
    · simpa [bit, hc] using hripple
  have hredCarryFresh' : ∀ w ∈ couts₂,
      run (ripple lhs rhs sum cin₁ couts₁) st w = false := by
    intro w hw
    rw [run_other_targets _ _ w (hredCarryFresh w hw).2, (hredCarryFresh w hw).1]
  have hredSumFresh' : ∀ w ∈ candidate,
      run (ripple lhs rhs sum cin₁ couts₁) st w = false := by
    intro w hw
    rw [run_other_targets _ _ w (hredSumFresh w hw).2, (hredSumFresh w hw).1]
  have hredBFresh' : ∀ w ∈ constReg,
      run (ripple lhs rhs sum cin₁ couts₁) st w = false := by
    intro w hw
    rw [run_other_targets _ _ w (hredBFresh w hw).2, (hredBFresh w hw).1]
  have hcin₂Fresh' : run (ripple lhs rhs sum cin₁ couts₁) st cin₂ = false := by
    rw [run_other_targets _ _ cin₂ hcin₂Fresh.2, hcin₂Fresh.1]
  have hconstBound : 2 ^ sum.length - modulus < 2 ^ sum.length := by
    rw [hsumLen]
    omega
  have hreduce := addConst_correct sum constReg candidate cin₂ couts₂
    (2 ^ sum.length - modulus) (run (ripple lhs rhs sum cin₁ couts₁) st)
    hconstLen hredOK hredBNodup hredAB hredSB hredCarryB hredCinB
    hredCarryFresh' hredSumFresh' hredBFresh' hcin₂Fresh' hconstBound
  have hcompute :
      run (modAddCompute lhs rhs sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus) st =
        run (addConst sum constReg candidate cin₂ couts₂ (2 ^ sum.length - modulus))
          (run (ripple lhs rhs sum cin₁ couts₁) st) := by
    rw [modAddCompute, run_append]
  have hsumPreserved :
      regValue sum
          (run (modAddCompute lhs rhs sum constReg candidate
            cin₁ couts₁ cin₂ couts₂ modulus) st) =
        regValue lhs st + regValue rhs st := by
    rw [hcompute]
    calc
      regValue sum
          (run (addConst sum constReg candidate cin₂ couts₂
              (2 ^ sum.length - modulus))
            (run (ripple lhs rhs sum cin₁ couts₁) st)) =
          regValue sum (run (ripple lhs rhs sum cin₁ couts₁) st) := by
              apply regValue_congr
              intro w hw
              exact addConst_other w sum constReg candidate cin₂ couts₂
                (2 ^ sum.length - modulus) _ (hredAB w hw)
                (fun x hx hEq => hredAS w hw (hEq ▸ hx))
                (fun x hx hEq => hredACarry w hw (hEq ▸ hx))
      _ = _ := hsum
  have hcandidate :
      regValue candidate
          (run (modAddCompute lhs rhs sum constReg candidate
            cin₁ couts₁ cin₂ couts₂ modulus) st) +
        2 ^ lhs.length *
          (if run (modAddCompute lhs rhs sum constReg candidate
              cin₁ couts₁ cin₂ couts₂ modulus) st
              (carryOut cin₂ couts₂) then 1 else 0) =
        (regValue lhs st + regValue rhs st) + (2 ^ lhs.length - modulus) := by
    rw [hcompute]
    rw [hsum] at hreduce
    simpa [bit, hsumLen] using hreduce
  have houtFresh' : ∀ w ∈ out,
      run (modAddCompute lhs rhs sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus) st w = false := by
    intro w hw
    rw [run_other_targets _ _ w (houtFresh w hw).2, (houtFresh w hw).1]
  have hselected := selectPoint_correct (carryOut cin₂ couts₂) sum candidate out
    (run (modAddCompute lhs rhs sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus) st)
    hselectOK houtFresh'
  rw [hsumPreserved] at hselected
  have hyBound :
      regValue candidate
          (run (modAddCompute lhs rhs sum constReg candidate
            cin₁ couts₁ cin₂ couts₂ modulus) st) <
        2 ^ lhs.length := by
    have h := regValue_lt_two_pow candidate
      (run (modAddCompute lhs rhs sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus) st)
    simpa [hcandidateLen, hsumLen] using h
  have hreduced := reduceOnce_select_eq_mod modulus (2 ^ lhs.length)
    (regValue lhs st + regValue rhs st)
    (regValue candidate
      (run (modAddCompute lhs rhs sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus) st))
    (run (modAddCompute lhs rhs sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus) st
      (carryOut cin₂ couts₂)) hmod hfit hsumBound hyBound hcandidate
  have hforward :
      regValue out
          (run (selectPoint (carryOut cin₂ couts₂) sum candidate out)
            (run (modAddCompute lhs rhs sum constReg candidate
              cin₁ couts₁ cin₂ couts₂ modulus) st)) =
        (regValue lhs st + regValue rhs st) % modulus :=
    hselected.trans hreduced
  rw [modAdd, run_append, run_append]
  calc
    regValue out
        (run (modAddCompute lhs rhs sum constReg candidate
            cin₁ couts₁ cin₂ couts₂ modulus).reverse
          (run (selectPoint (carryOut cin₂ couts₂) sum candidate out)
            (run (modAddCompute lhs rhs sum constReg candidate
              cin₁ couts₁ cin₂ couts₂ modulus) st))) =
      regValue out
        (run (selectPoint (carryOut cin₂ couts₂) sum candidate out)
          (run (modAddCompute lhs rhs sum constReg candidate
            cin₁ couts₁ cin₂ couts₂ modulus) st)) := by
            apply regValue_congr
            intro w hw
            apply run_other_targets
            simp only [List.map_reverse, List.mem_reverse]
            exact (houtFresh w hw).2
    _ = _ := hforward

theorem modAddCompute_tCount (lhs rhs sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (hrhs : rhs.length = lhs.length) (hsum : sum.length = lhs.length)
    (hcouts₁ : couts₁.length = lhs.length)
    (hconst : constReg.length = sum.length)
    (hcandidate : candidate.length = sum.length)
    (hcouts₂ : couts₂.length = sum.length) :
    tCount (modAddCompute lhs rhs sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus) = 42 * lhs.length := by
  rw [modAddCompute, tCount_append,
    ripple_tCount lhs rhs sum cin₁ couts₁ hrhs hsum hcouts₁,
    addConst_tCount sum constReg candidate cin₂ couts₂ _
      hconst hcandidate hcouts₂]
  omega

theorem modAdd_tCount (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (hrhs : rhs.length = lhs.length) (hsum : sum.length = lhs.length)
    (hcouts₁ : couts₁.length = lhs.length)
    (hconst : constReg.length = sum.length)
    (hcandidate : candidate.length = sum.length)
    (hcouts₂ : couts₂.length = sum.length)
    (hout : out.length = lhs.length) :
    tCount (modAdd lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus) = 91 * lhs.length := by
  rw [modAdd, tCount_append, tCount_append, tCount_reverse,
    modAddCompute_tCount lhs rhs sum constReg candidate cin₁ couts₁ cin₂ couts₂
      modulus hrhs hsum hcouts₁ hconst hcandidate hcouts₂,
    selectPoint_tCount _ _ _ _ hcandidate.symm (hsum.trans hout.symm), hout]
  omega

theorem modAddCompute_HPFree (lhs rhs sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) :
    HPFree (modAddCompute lhs rhs sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modAddCompute, hpFree_append]
  exact ⟨ripple_HPFree _ _ _ _ _, addConst_HPFree _ _ _ _ _ _⟩

theorem modAddCompute_wellFormed (lhs rhs sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (ha : wiresOK lhs rhs sum cin₁ couts₁)
    (hr : wiresOK sum constReg candidate cin₂ couts₂) :
    CircuitWellFormed (modAddCompute lhs rhs sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modAddCompute, circuitWellFormed_append]
  exact ⟨ripple_wellFormed _ _ _ _ _ ha, addConst_wellFormed _ _ _ _ _ _ hr⟩

theorem modAdd_HPFree (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) :
    HPFree (modAdd lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modAdd, hpFree_append, hpFree_append]
  have hc := modAddCompute_HPFree lhs rhs sum constReg candidate
    cin₁ couts₁ cin₂ couts₂ modulus
  exact ⟨⟨hc, selectPoint_HPFree _ _ _ _⟩, hpFree_reverse _ hc⟩

theorem modAdd_wellFormed (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) (modulus : Nat)
    (ha : wiresOK lhs rhs sum cin₁ couts₁)
    (hr : wiresOK sum constReg candidate cin₂ couts₂)
    (hs : selectOK (carryOut cin₂ couts₂) sum candidate out) :
    CircuitWellFormed (modAdd lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modAdd, circuitWellFormed_append, circuitWellFormed_append]
  have hc := modAddCompute_wellFormed lhs rhs sum constReg candidate
    cin₁ couts₁ cin₂ couts₂ modulus ha hr
  exact ⟨⟨hc, selectPoint_wellFormed _ _ _ _ hs⟩, wellFormed_reverse _ hc⟩

/-- The Bennett tail restores every non-output wire.  This is the reusable-work guarantee:
all arithmetic sum, constant-scratch, and carry wires return to their input values, while the
fresh selector output is retained.  The output must be outside the full compute support, not
merely outside its target list, because changing a later inverse control would spoil cleanup. -/
theorem modAdd_clean
    (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (st : BasisState)
    (ha : wiresOK lhs rhs sum cin₁ couts₁)
    (hr : wiresOK sum constReg candidate cin₂ couts₂)
    (hs : selectOK (carryOut cin₂ couts₂) sum candidate out)
    (hout : ∀ w ∈ out,
      w ∉ circuitWires (modAddCompute lhs rhs sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus)) :
    ∀ w, w ∉ out →
      run (modAdd lhs rhs out sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus) st w = st w := by
  let compute := modAddCompute lhs rhs sum constReg candidate
    cin₁ couts₁ cin₂ couts₂ modulus
  let selector := selectPoint (carryOut cin₂ couts₂) sum candidate out
  have hcomputeHP : HPFree compute :=
    modAddCompute_HPFree lhs rhs sum constReg candidate cin₁ couts₁ cin₂ couts₂ modulus
  have hcomputeWF : CircuitWellFormed compute :=
    modAddCompute_wellFormed lhs rhs sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus ha hr
  have hsupport : ∀ u ∈ circuitWires compute,
      run selector (run compute st) u = run compute st u := by
    intro u hu
    apply selectPoint_other (carryOut cin₂ couts₂) u sum candidate out _ hs
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
      selectPoint_other (carryOut cin₂ couts₂) w sum candidate out _ hs hw,
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

/-- All inputs, threaded carries, and sums that a ripple circuit may use. -/
def rippleFootprint (a b sum : List Wire) (cin : Wire) (couts : List Wire) : List Wire :=
  cin :: (couts ++ a ++ b ++ sum)

/-- A ripple circuit stays inside its named-register/carry footprint. -/
theorem ripple_usesOnly :
    ∀ (a b sum : List Wire) (cin : Wire) (couts : List Wire),
      CircuitUsesOnly (rippleFootprint a b sum cin couts)
        (ripple a b sum cin couts) := by
  intro a
  induction a with
  | nil =>
      intro b sum cin couts
      cases b <;> cases sum <;> cases couts <;> exact circuitUsesOnly_nil _
  | cons a as ih =>
      intro b sum cin couts
      cases b with
      | nil => exact circuitUsesOnly_nil _
      | cons b bs =>
          cases sum with
          | nil => exact circuitUsesOnly_nil _
          | cons s ss =>
              cases couts with
              | nil => exact circuitUsesOnly_nil _
              | cons co cs =>
                  rw [ripple, circuitUsesOnly_append]
                  constructor
                  · apply circuitUsesOnly_mono (fullAdder_usesOnly a b cin s co)
                    intro w hw
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
                    simp only [rippleFootprint, List.mem_cons, List.mem_append]
                    rcases hw with rfl | rfl | rfl | rfl | rfl <;> simp
                  · apply circuitUsesOnly_mono (ih bs ss co cs)
                    intro w hw
                    simp only [rippleFootprint, List.mem_cons, List.mem_append] at hw ⊢
                    rcases hw with hco | (((hcs | has) | hbs) | hss)
                    · subst w; simp
                    · simp [hcs]
                    · simp [has]
                    · simp [hbs]
                    · simp [hss]

/-- Constant addition has the same footprint as its ripple core: `constReg` is already a
named ripple input register. -/
theorem addConst_usesOnly (a constReg sum : List Wire)
    (cin : Wire) (couts : List Wire) (k : Nat) :
    CircuitUsesOnly (rippleFootprint a constReg sum cin couts)
      (addConst a constReg sum cin couts k) := by
  have hb : ∀ w ∈ constReg, w ∈ rippleFootprint a constReg sum cin couts := by
    intro w hw
    simp [rippleFootprint, hw]
  rw [addConst, circuitUsesOnly_append, circuitUsesOnly_append]
  exact ⟨⟨circuitUsesOnly_mono (Arithmetic.loadConst_usesOnly _ k) hb,
    ripple_usesOnly a constReg sum cin couts⟩,
    circuitUsesOnly_mono (Arithmetic.loadConst_usesOnly _ k) hb⟩

/-- The owner registers A/B/O followed by all modular-addition work registers. -/
def modAddAllWires
    (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) : List Wire :=
  lhs ++
  rhs ++
  out ++
  sum ++
  constReg ++
  candidate ++
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
    (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) :
    CircuitUsesOnly
      (modAddAllWires lhs rhs out sum constReg candidate cin₁ couts₁ cin₂ couts₂)
      (modAdd lhs rhs out sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus) := by
  let all := modAddAllWires lhs rhs out sum constReg candidate
    cin₁ couts₁ cin₂ couts₂
  have hadd : ∀ w ∈ rippleFootprint lhs rhs sum cin₁ couts₁, w ∈ all := by
    intro w hw
    simp only [rippleFootprint, List.mem_cons, List.mem_append] at hw
    simp only [all, modAddAllWires, List.mem_append, List.mem_singleton]
    rcases hw with hcin | (((hcouts | hlhs) | hrhs) | hsum)
    · subst w; simp
    · simp [hcouts]
    · simp [hlhs]
    · simp [hrhs]
    · simp [hsum]
  have hred : ∀ w ∈ rippleFootprint sum constReg candidate cin₂ couts₂, w ∈ all := by
    intro w hw
    simp only [rippleFootprint, List.mem_cons, List.mem_append] at hw
    simp only [all, modAddAllWires, List.mem_append, List.mem_singleton]
    rcases hw with hcin | (((hcouts | hsum) | hconst) | hcandidate)
    · subst w; simp
    · simp [hcouts]
    · simp [hsum]
    · simp [hconst]
    · simp [hcandidate]
  have hselect : ∀ w ∈ selectFootprint (carryOut cin₂ couts₂) sum candidate out,
      w ∈ all := by
    intro w hw
    simp only [selectFootprint, List.mem_cons, List.mem_append] at hw
    rcases hw with ((hflag | hsum) | hcandidate) | hout
    · subst w
      have hcarry := carryOut_mem_footprint cin₂ couts₂
      simp only [List.mem_cons] at hcarry
      rcases hcarry with hcarry | hcarry
      · rw [hcarry]
        simp [all, modAddAllWires]
      · simp [all, modAddAllWires, hcarry]
    · simp [all, modAddAllWires, hsum]
    · simp [all, modAddAllWires, hcandidate]
    · simp [all, modAddAllWires, hout]
  rw [modAdd, circuitUsesOnly_append, circuitUsesOnly_append]
  have hcompute : CircuitUsesOnly all
      (modAddCompute lhs rhs sum constReg candidate cin₁ couts₁ cin₂ couts₂ modulus) := by
    rw [modAddCompute, circuitUsesOnly_append]
    exact ⟨circuitUsesOnly_mono (ripple_usesOnly lhs rhs sum cin₁ couts₁) hadd,
      circuitUsesOnly_mono (addConst_usesOnly sum constReg candidate cin₂ couts₂ _) hred⟩
  exact ⟨⟨hcompute, circuitUsesOnly_mono (selectPoint_usesOnly _ _ _ _) hselect⟩,
    (circuitUsesOnly_reverse all _).2 hcompute⟩

/-- The compute/uncompute core excludes selector outputs from its declared support. -/
theorem modAddCompute_usesOnly
    (lhs rhs sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) :
    CircuitUsesOnly
      (lhs ++
       rhs ++
       sum ++
       constReg ++
       candidate ++
       [cin₁] ++ couts₁ ++ [cin₂] ++ couts₂)
      (modAddCompute lhs rhs sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus) := by
  let all :=
    lhs ++
    rhs ++
    sum ++
    constReg ++
    candidate ++
    [cin₁] ++ couts₁ ++ [cin₂] ++ couts₂
  have hadd : ∀ w ∈ rippleFootprint lhs rhs sum cin₁ couts₁, w ∈ all := by
    intro w hw
    simp only [rippleFootprint, List.mem_cons, List.mem_append] at hw
    simp only [all, List.mem_append, List.mem_singleton]
    rcases hw with hcin | (((hcouts | hlhs) | hrhs) | hsum)
    · subst w; simp
    · simp [hcouts]
    · simp [hlhs]
    · simp [hrhs]
    · simp [hsum]
  have hred : ∀ w ∈ rippleFootprint sum constReg candidate cin₂ couts₂, w ∈ all := by
    intro w hw
    simp only [rippleFootprint, List.mem_cons, List.mem_append] at hw
    simp only [all, List.mem_append, List.mem_singleton]
    rcases hw with hcin | (((hcouts | hsum) | hconst) | hcandidate)
    · subst w; simp
    · simp [hcouts]
    · simp [hsum]
    · simp [hconst]
    · simp [hcandidate]
  rw [modAddCompute, circuitUsesOnly_append]
  exact ⟨circuitUsesOnly_mono (ripple_usesOnly lhs rhs sum cin₁ couts₁) hadd,
    circuitUsesOnly_mono (addConst_usesOnly sum constReg candidate cin₂ couts₂ _) hred⟩

end ModAddSupport

/-! ## Clean modular-addition contract -/

/-- Public `A`, public `B`, public output `O`, followed by each owned work register exactly
once: unreduced sum `X`, loaded constant `K`, reduction candidate `Y`, then the two carry
banks and their carry-ins. The selector flag is the final wire of `couts₂`, so it is not
listed a second time. -/
def modAddLayout
    (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) :
    RegisterLayout where
  lhs := lhs
  rhs := rhs
  out := out
  work :=
    sum ++
    constReg ++
    candidate ++
    [cin₁] ++ couts₁ ++ [cin₂] ++ couts₂

/-- The genuine construction parameters of one concrete modular-adder instance.

All cross-register disjointness and stage-freshness facts are derived inside `modAdd_contract`
from `RegisterLayout.Valid`; callers do not have to restate consequences of its global
`Nodup` premise. -/
structure ModAddWiring
    (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) : Prop where
  rhsLen : rhs.length = lhs.length
  sumLen : sum.length = lhs.length
  addCarryLen : couts₁.length = lhs.length
  constLen : constReg.length = sum.length
  candidateLen : candidate.length = sum.length
  redCarryLen : couts₂.length = sum.length
  outLen : out.length = lhs.length
  addOK : wiresOK lhs rhs sum cin₁ couts₁
  redOK : wiresOK sum constReg candidate cin₂ couts₂
  selectOK : ShorECDLP.selectOK (carryOut cin₂ couts₂) sum candidate out
  modulusPos : 0 < modulus
  fit : 2 * modulus ≤ 2 ^ lhs.length

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
    (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (wiring : ModAddWiring lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus) :
    ModAddContract
      (modAdd lhs rhs out sum constReg candidate cin₁ couts₁ cin₂ couts₂ modulus)
      (modAddLayout lhs rhs out sum constReg candidate cin₁ couts₁ cin₂ couts₂)
      modulus (91 * lhs.length) := by
  let layout := modAddLayout lhs rhs out sum constReg candidate
    cin₁ couts₁ cin₂ couts₂
  let program := modAdd lhs rhs out sum constReg candidate
    cin₁ couts₁ cin₂ couts₂ modulus
  refine {
    correct := ?_
    usesOnly := ?_
    counted := ?_
    hpFree := ?_
    wellFormed := ?_
  }
  · intro st hvalid ha hb hclean
    dsimp only
    let A := lhs
    let B := rhs
    let O := out
    let X := sum
    let K := constReg
    let Y := candidate

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
    have haddSumFresh : ∀ w ∈ sum, st w = false := by
      intro w hw
      apply hworkClean w
      simp [layout, modAddLayout, hw]
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

    have htargetSupport : ∀ w ∈ (ripple lhs rhs sum cin₁ couts₁).map gateTarget,
        w ∈ ModAddSupport.rippleFootprint lhs rhs sum cin₁ couts₁ := by
      intro w hw
      exact (ModAddSupport.circuitUsesOnly_iff_support _ _).mp
        (ModAddSupport.ripple_usesOnly lhs rhs sum cin₁ couts₁) w
        (mem_circuitWires_of_mem_targets _ _ hw)

    have hnotRippleK : ∀ w ∈ K,
        w ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget := by
      intro w hwK hwTarget
      have hw := htargetSupport w hwTarget
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | (((hwC | hwA) | hwB) | hwX)
      · exact hAcrossK w hwK w (by simp) rfl
      · exact hAcrossK w hwK w (by simp [hwC]) rfl
      · exact hAcrossA w (by simpa [A] using hwA) w (by simp [K, hwK]) rfl
      · exact hAcrossB w (by simpa [B] using hwB) w (by simp [K, hwK]) rfl
      · exact hAcrossX w (by simpa [X] using hwX) w (by simp [K, hwK]) rfl
    have hnotRippleY : ∀ w ∈ Y,
        w ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget := by
      intro w hwY hwTarget
      have hw := htargetSupport w hwTarget
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | (((hwC | hwA) | hwB) | hwX)
      · exact hAcrossY w hwY w (by simp) rfl
      · exact hAcrossY w hwY w (by simp [hwC]) rfl
      · exact hAcrossA w (by simpa [A] using hwA) w (by simp [Y, hwY]) rfl
      · exact hAcrossB w (by simpa [B] using hwB) w (by simp [Y, hwY]) rfl
      · exact hAcrossX w (by simpa [X] using hwX) w (by simp [Y, hwY]) rfl
    have hnotRippleCin₂ : cin₂ ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget := by
      intro hwTarget
      have hw := htargetSupport cin₂ hwTarget
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append] at hw
      rcases hw with hEq | (((hwC | hwA) | hwB) | hwX)
      · exact hAcrossCin₁ cin₁ (by simp) cin₂ (by simp) hEq.symm
      · exact hAcrossCouts₁ cin₂ hwC cin₂ (by simp) rfl
      · exact hAcrossA cin₂ (by simpa [A] using hwA) cin₂ (by simp) rfl
      · exact hAcrossB cin₂ (by simpa [B] using hwB) cin₂ (by simp) rfl
      · exact hAcrossX cin₂ (by simpa [X] using hwX) cin₂ (by simp) rfl
    have hnotRippleCouts₂ : ∀ w ∈ couts₂,
        w ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget := by
      intro w hwC hwTarget
      have hw := htargetSupport w hwTarget
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | (((hwC₁ | hwA) | hwB) | hwX)
      · exact hAcrossCin₁ w (by simp) w (by simp [hwC]) rfl
      · exact hAcrossCouts₁ w hwC₁ w (by simp [hwC]) rfl
      · exact hAcrossA w (by simpa [A] using hwA) w (by simp [hwC]) rfl
      · exact hAcrossB w (by simpa [B] using hwB) w (by simp [hwC]) rfl
      · exact hAcrossX w (by simpa [X] using hwX) w (by simp [hwC]) rfl

    have hredCarryFresh : ∀ w ∈ couts₂,
        st w = false ∧ w ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget := by
      intro w hw
      constructor
      · apply hworkClean w
        simp [layout, modAddLayout, hw]
      · exact hnotRippleCouts₂ w hw
    have hredSumFresh : ∀ w ∈ candidate,
        st w = false ∧ w ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget := by
      intro w hw
      constructor
      · apply hworkClean w
        simp [layout, modAddLayout, hw]
      · exact hnotRippleY w (by simpa [Y] using hw)
    have hredBFresh : ∀ w ∈ constReg,
        st w = false ∧ w ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget := by
      intro w hw
      constructor
      · apply hworkClean w
        simp [layout, modAddLayout, hw]
      · exact hnotRippleK w (by simpa [K] using hw)
    have hcin₂Fresh : st cin₂ = false ∧
        cin₂ ∉ (ripple lhs rhs sum cin₁ couts₁).map gateTarget := by
      constructor
      · apply hworkClean cin₂
        simp [layout, modAddLayout]
      · exact hnotRippleCin₂

    have hcomputeSupport : ∀ w ∈ circuitWires
        (modAddCompute lhs rhs sum constReg candidate cin₁ couts₁ cin₂ couts₂ modulus),
        w ∈ A ++ (B ++ (X ++ (K ++ (Y ++
          ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂))))))) := by
      simpa [A, B, X, K, Y] using
        (ModAddSupport.circuitUsesOnly_iff_support _ _).mp
          (ModAddSupport.modAddCompute_usesOnly
            lhs rhs sum constReg candidate cin₁ couts₁ cin₂ couts₂ modulus)
    have houtFreshSupport : ∀ w ∈ O,
        w ∉ circuitWires
          (modAddCompute lhs rhs sum constReg candidate
            cin₁ couts₁ cin₂ couts₂ modulus) := by
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
    have houtFresh : ∀ w ∈ out,
        st w = false ∧
          w ∉ (modAddCompute lhs rhs sum constReg candidate
            cin₁ couts₁ cin₂ couts₂ modulus).map
            gateTarget := by
      intro w hw
      have hco : w ∈ O := by simpa [O] using hw
      constructor
      · exact hclean w (List.mem_append_left _ hco)
      · intro ht
        exact houtFreshSupport w hco (mem_circuitWires_of_mem_targets _ _ ht)

    have hresult := modAdd_correct
      lhs rhs out sum constReg candidate cin₁ couts₁ cin₂ couts₂ modulus st
      wiring.sumLen wiring.constLen wiring.candidateLen wiring.addOK wiring.redOK wiring.selectOK
      wiring.modulusPos wiring.fit ha hb
      haddCarryFresh haddSumFresh hcin₁Fresh
      (by simpa [K] using hKNodup)
      (by simpa [X, K] using hredAB)
      (by simpa [Y, K] using hredSB)
      (by simpa [K] using hredCarryB)
      (by simpa [K] using hredCinB)
      (by simpa [X, Y] using hredAS)
      (by simpa [X] using hredACarry)
      hredCarryFresh hredSumFresh hredBFresh hcin₂Fresh houtFresh

    have hrestore := modAdd_clean
      lhs rhs out sum constReg candidate cin₁ couts₁ cin₂ couts₂ modulus st
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
      (ModAddSupport.modAdd_usesOnly lhs rhs out sum constReg candidate
        cin₁ couts₁ cin₂ couts₂ modulus)

  · exact modAdd_tCount lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus wiring.rhsLen wiring.sumLen
      wiring.addCarryLen wiring.constLen wiring.candidateLen wiring.redCarryLen
      wiring.outLen

  · exact modAdd_HPFree lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus

  · intro _
    exact modAdd_wellFormed lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus wiring.addOK wiring.redOK wiring.selectOK

/-- Final direct correctness theorem for the exact clean modular-addition program.

The conclusion states input preservation, the modular sum, and restored workspace inline, so
callers do not need to project the semantic field from `modAdd_contract`. -/
theorem modAdd_program_correct
    (lhs rhs out sum constReg candidate : List Wire)
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (wiring : ModAddWiring lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus)
    (st : BasisState)
    (hvalid : (modAddLayout lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂).Valid)
    (ha : st⟦ᵣlhs⟧ < modulus)
    (hb : st⟦ᵣrhs⟧ < modulus)
    (hclean : clean(out ++ (modAddLayout lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂).work, st)) :
    let after := ⟪modAdd lhs rhs out sum constReg candidate
      cin₁ couts₁ cin₂ couts₂ modulus⟫ st
    AgreesOn lhs st after ∧
      AgreesOn rhs st after ∧
      after⟦ᵣout⟧ = (st⟦ᵣlhs⟧ + st⟦ᵣrhs⟧) % modulus ∧
      clean((modAddLayout lhs rhs out sum constReg candidate
        cin₁ couts₁ cin₂ couts₂).work, after) := by
  exact (modAdd_contract lhs rhs out sum constReg candidate
    cin₁ couts₁ cin₂ couts₂ modulus wiring).correct st hvalid ha hb hclean

end ShorECDLP
