import ShorECDLP.Submission.Arithmetic.RippleAdder

/-
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
-/

namespace ShorECDLP

open Classical

/-- Load the constant `c` (LSB-first) into wires `ws`: X each wire whose corresponding bit of
`c` is set. Self-inverse — running it again clears the register. -/
def loadConst : List Nat → Nat → Circuit
  | [],      _ => []
  | w :: ws, c => (if c % 2 = 1 then [Gate.X w] else []) ++ loadConst ws (c / 2)

/-- `loadConst` touches only its own wires: a wire outside `ws` is left unchanged. -/
theorem loadConst_other (w : Nat) :
    ∀ (ws : List Nat) (c : Nat) (st : BasisState), w ∉ ws →
      run (loadConst ws c) st w = st w := by
  intro ws
  induction ws with
  | nil => intro c st _; simp [loadConst]
  | cons v vs ih =>
      intro c st hw
      simp only [List.mem_cons, not_or] at hw
      obtain ⟨hwv, hwvs⟩ := hw
      rw [loadConst, run_append, ih (c / 2) _ hwvs]
      by_cases h : c % 2 = 1 <;>
        simp [h, run_cons, run_nil, applyGate, upd_other _ _ _ hwv]

/-- **M1.3.0 — `loadConst` is correct.** Loading `c < 2ⁿ` into `n` distinct, initially-`false`
wires makes the register hold exactly `c`. -/
theorem loadConst_correct :
    ∀ (ws : List Nat) (c : Nat) (st : BasisState),
      ws.Nodup → (∀ w ∈ ws, st w = false) → c < 2 ^ ws.length →
      regValue ws (run (loadConst ws c) st) = c := by
  intro ws
  induction ws with
  | nil =>
      intro c st _ _ hc
      simp only [List.length_nil, Nat.pow_zero, Nat.lt_one_iff] at hc
      subst hc; simp [loadConst]
  | cons v vs ih =>
      intro c st hnd hfree hc
      simp only [List.nodup_cons] at hnd
      obtain ⟨hv, hndvs⟩ := hnd
      simp only [List.length_cons, Nat.pow_succ] at hc
      have hc2 : c / 2 < 2 ^ vs.length := by omega
      have hfreevs : ∀ w ∈ vs, st w = false := fun w hw => hfree w (List.mem_cons_of_mem _ hw)
      rw [loadConst, run_append, regValue_cons]
      by_cases hodd : c % 2 = 1
      · -- odd: the load applies `X v`
        rw [if_pos hodd]
        have hst' : ∀ w ∈ vs, run [Gate.X v] st w = false := by
          intro w hw
          have hwv : w ≠ v := fun e => hv (e ▸ hw)
          simp [run_cons, run_nil, applyGate, upd_other _ _ _ hwv, hfreevs w hw]
        have hv' : run [Gate.X v] st v = true := by
          simp [run_cons, run_nil, applyGate, upd, hfree v (List.mem_cons_self ..)]
        have hvf : run (loadConst vs (c / 2)) (run [Gate.X v] st) v = run [Gate.X v] st v :=
          loadConst_other v vs (c / 2) _ hv
        rw [hvf, hv', ih (c / 2) (run [Gate.X v] st) hndvs hst' hc2]
        simp; omega
      · -- even: the load is empty on this wire
        rw [if_neg hodd, run_nil]
        have hvf : run (loadConst vs (c / 2)) st v = st v := loadConst_other v vs (c / 2) st hv
        rw [hvf, hfree v (List.mem_cons_self ..), ih (c / 2) st hndvs hfreevs hc2]
        simp; omega

/-- `regValue` of wires disjoint from the loaded register is unchanged by `loadConst`. -/
theorem loadConst_regValue (ws bs : List Nat) (c : Nat) (st : BasisState)
    (h : ∀ w ∈ ws, w ∉ bs) :
    regValue ws (run (loadConst bs c) st) = regValue ws st :=
  regValue_congr ws _ _ (fun w hw => loadConst_other w bs c st (h w hw))

/-- A wire outside the loaded register keeps its value (bit form) under `loadConst`. -/
theorem loadConst_false (w : Nat) (bs : List Nat) (c : Nat) (st : BasisState)
    (hw : w ∉ bs) (hf : st w = false) : run (loadConst bs c) st w = false := by
  rw [loadConst_other w bs c st hw, hf]

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

/-- `loadConst` is X-only, so it is T-free. -/
theorem loadConst_tCount (ws : List Nat) (c : Nat) : tCount (loadConst ws c) = 0 := by
  induction ws generalizing c with
  | nil => simp [loadConst]
  | cons w vs ih =>
      rw [loadConst, tCount_append, ih (c / 2)]
      by_cases h : c % 2 = 1 <;> simp [h, tCount, tCost]

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
  | .P _ t     => t

/-- All wires read or written by a primitive gate. -/
def gateWires : Gate → List Wire
  | .X t       => [t]
  | .H t       => [t]
  | .CX c t    => [c, t]
  | .CCX a b t => [a, b, t]
  | .P _ t     => [t]

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
  | P k target => exact hst w hw

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
  | P _ _ => rfl

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
  | P k t => simp at hc

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

/-- `loadConst` contains only `X` gates. -/
theorem loadConst_HPFree (ws : List Wire) (c : Nat) : HPFree (loadConst ws c) := by
  induction ws generalizing c with
  | nil => simp [loadConst]
  | cons w ws ih =>
      rw [loadConst, hpFree_append]
      by_cases h : c % 2 = 1 <;> simp [h, ih (c / 2)]

/-- `loadConst` is well-formed without side conditions because every gate is unary. -/
theorem loadConst_wellFormed (ws : List Wire) (c : Nat) :
    CircuitWellFormed (loadConst ws c) := by
  induction ws generalizing c with
  | nil => simp [loadConst]
  | cons w ws ih =>
      rw [loadConst, circuitWellFormed_append]
      by_cases h : c % 2 = 1 <;> simp [h, ih (c / 2), Gate.WellFormed]

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

/-- One bit of a reversible two-way selector.  With a fresh output it writes `x` when `flag=0`
and `y` when `flag=1`.  The middle CNOTs temporarily form `x XOR y` on `y`, allowing the
selection to use one Toffoli rather than two, and then restore `y`. -/
def selectBit (flag x y out : Wire) : Circuit :=
  [Gate.CX x out, Gate.CX x y, Gate.CCX flag y out, Gate.CX x y]

/-- Exact state action of one selector cell.  Only `out` changes; the temporary XOR on `y`
is uncomputed inside the cell. -/
theorem run_selectBit (flag x y out : Wire) (st : BasisState)
    (hxy : x ≠ y) (hxo : x ≠ out) (hyo : y ≠ out)
    (hfy : flag ≠ y) (hfo : flag ≠ out) :
    run (selectBit flag x y out) st =
      st[out ↦ Bool.xor (st out) (if st flag then st y else st x)] := by
  funext w
  by_cases hwo : w = out
  · subst w
    simp only [selectBit, run_cons, run_nil, applyGate, upd_same]
    simp [upd, hxo, hyo, hyo.symm, hfy, hfo]
    cases st flag <;> cases st x <;> cases st y <;> cases st out <;> rfl
  · simp only [selectBit, run_cons, run_nil, applyGate]
    by_cases hwy : w = y
    · subst w
      simp [upd, hxy, hxo, hyo]
    · simp [upd, hwo, hwy]

/-- Apply `selectBit` pointwise to aligned `(x,y,out)` columns. -/
def selectPoint (flag : Wire) : List (Wire × Wire × Wire) → Circuit
  | []          => []
  | (x,y,o)::cs => selectBit flag x y o ++ selectPoint flag cs

/-- Wire conditions needed by the selector.  Source/flag wires are outside the duplicate-free
output register, and the flag is distinct from both sources in every column. -/
def selectOK (flag : Wire) (cols : List (Wire × Wire × Wire)) : Prop :=
  let outs := cols.map (fun c => c.2.2)
  outs.Nodup ∧ flag ∉ outs ∧
    (∀ c ∈ cols,
      c.1 ∉ outs ∧ c.2.1 ∉ outs ∧ flag ≠ c.1 ∧ flag ≠ c.2.1 ∧ c.1 ≠ c.2.1)

/-- The selector's net action changes only its output register. -/
theorem selectPoint_other (flag w : Wire) :
    ∀ (cols : List (Wire × Wire × Wire)) (st : BasisState),
      selectOK flag cols → w ∉ cols.map (fun c => c.2.2) →
      run (selectPoint flag cols) st w = st w := by
  intro cols
  induction cols with
  | nil => intro st _ _; rfl
  | cons c cs ih =>
      intro st hok hw
      obtain ⟨x,y,o⟩ := c
      simp only [selectOK, List.map_cons, List.nodup_cons] at hok
      obtain ⟨⟨ho, houts⟩, hfo, hall⟩ := hok
      have hw' : w ≠ o ∧ w ∉ cs.map (fun d => d.2.2) := by
        constructor
        · intro e
          apply hw
          simp [e]
        · intro hm
          apply hw
          exact List.mem_cons_of_mem o hm
      have hhead := hall (x,y,o) (List.mem_cons_self ..)
      have hflagout : flag ≠ o := fun e => hfo (e ▸ List.mem_cons_self ..)
      have htail : selectOK flag cs := by
        simp only [selectOK]
        refine ⟨houts, ?_, ?_⟩
        · exact fun hf => hfo (List.mem_cons_of_mem _ hf)
        · intro d hd
          have hd' := hall d (List.mem_cons_of_mem _ hd)
          exact ⟨fun hm => hd'.1 (List.mem_cons_of_mem _ hm),
            fun hm => hd'.2.1 (List.mem_cons_of_mem _ hm), hd'.2.2⟩
      rw [selectPoint, run_append, ih _ htail hw'.2,
        run_selectBit flag x y o st hhead.2.2.2.2
          (Ne.symm (fun e => hhead.1 (e ▸ List.mem_cons_self ..)))
          (Ne.symm (fun e => hhead.2.1 (e ▸ List.mem_cons_self ..)))
          hhead.2.2.2.1 hflagout,
        upd_other _ _ _ hw'.1]

/-- With a fresh output register, the pointwise selector writes the `x` register when its
flag is false and the `y` register when its flag is true. -/
theorem selectPoint_correct (flag : Wire) :
    ∀ (cols : List (Wire × Wire × Wire)) (st : BasisState),
      selectOK flag cols → (∀ c ∈ cols, st c.2.2 = false) →
      regValue (cols.map (fun c => c.2.2)) (run (selectPoint flag cols) st) =
        if st flag then regValue (cols.map (fun c => c.2.1)) st
        else regValue (cols.map (fun c => c.1)) st := by
  intro cols
  induction cols with
  | nil => intro st _ _; simp [selectPoint]
  | cons c cs ih =>
      intro st hok hfree
      obtain ⟨x,y,o⟩ := c
      simp only [selectOK, List.map_cons, List.nodup_cons] at hok
      obtain ⟨⟨ho, houts⟩, hfo, hall⟩ := hok
      have hhead := hall (x,y,o) (List.mem_cons_self ..)
      have hflagout : flag ≠ o := fun e => hfo (e ▸ List.mem_cons_self ..)
      have htail : selectOK flag cs := by
        simp only [selectOK]
        refine ⟨houts, ?_, ?_⟩
        · exact fun hf => hfo (List.mem_cons_of_mem _ hf)
        · intro d hd
          have hd' := hall d (List.mem_cons_of_mem _ hd)
          exact ⟨fun hm => hd'.1 (List.mem_cons_of_mem _ hm),
            fun hm => hd'.2.1 (List.mem_cons_of_mem _ hm), hd'.2.2⟩
      have hcell := run_selectBit flag x y o st hhead.2.2.2.2
        (Ne.symm (fun e => hhead.1 (e ▸ List.mem_cons_self ..)))
        (Ne.symm (fun e => hhead.2.1 (e ▸ List.mem_cons_self ..)))
        hhead.2.2.2.1 hflagout
      have hotx : o ∉ cs.map (fun d => d.1) := by
        intro hm
        simp only [List.mem_map] at hm
        obtain ⟨d, hd, he⟩ := hm
        exact (hall d (List.mem_cons_of_mem _ hd)).1 (he ▸ List.mem_cons_self ..)
      have hoty : o ∉ cs.map (fun d => d.2.1) := by
        intro hm
        simp only [List.mem_map] at hm
        obtain ⟨d, hd, he⟩ := hm
        exact (hall d (List.mem_cons_of_mem _ hd)).2.1 (he ▸ List.mem_cons_self ..)
      have htailfree : ∀ d ∈ cs, run (selectBit flag x y o) st d.2.2 = false := by
        intro d hd
        rw [hcell, upd_other]
        · exact hfree d (List.mem_cons_of_mem _ hd)
        · intro he
          exact ho (he ▸ List.mem_map_of_mem hd)
      have hih := ih (run (selectBit flag x y o) st) htail htailfree
      have htailx : regValue (cs.map (fun d => d.1)) (run (selectBit flag x y o) st) =
          regValue (cs.map (fun d => d.1)) st := by
        rw [hcell, regValue_upd_not_mem _ _ _ _ hotx]
      have htaily : regValue (cs.map (fun d => d.2.1)) (run (selectBit flag x y o) st) =
          regValue (cs.map (fun d => d.2.1)) st := by
        rw [hcell, regValue_upd_not_mem _ _ _ _ hoty]
      have hflagcell : run (selectBit flag x y o) st flag = st flag := by
        rw [hcell, upd_other _ _ _ hflagout]
      rw [htaily, htailx, hflagcell] at hih
      have hout : run (selectPoint flag cs) (run (selectBit flag x y o) st) o =
          if st flag then st y else st x := by
        rw [selectPoint_other flag o cs _ htail ho, hcell, upd_same,
          hfree (x,y,o) (List.mem_cons_self ..)]
        simp
      rw [selectPoint, run_append, List.map_cons, regValue_cons, hout, hih]
      cases st flag <;> simp [regValue_cons]

/-- One selector cell has T-count `7` (one Toffoli). -/
theorem selectBit_tCount (flag x y out : Wire) : tCount (selectBit flag x y out) = 7 := rfl

/-- The selector costs `7` T per output bit. -/
theorem selectPoint_tCount (flag : Wire) (cols : List (Wire × Wire × Wire)) :
    tCount (selectPoint flag cols) = 7 * cols.length := by
  induction cols with
  | nil => simp [selectPoint]
  | cons c cs ih =>
      obtain ⟨x,y,o⟩ := c
      rw [selectPoint, tCount_append, selectBit_tCount, ih]
      simp [Nat.mul_succ, Nat.add_comm]

/-- The selector is an arithmetic circuit. -/
theorem selectPoint_HPFree (flag : Wire) (cols : List (Wire × Wire × Wire)) :
    HPFree (selectPoint flag cols) := by
  induction cols with
  | nil => simp [selectPoint]
  | cons c cs ih =>
      obtain ⟨x,y,o⟩ := c
      rw [selectPoint, hpFree_append]
      exact ⟨by simp [selectBit], ih⟩

/-- The selector is well-formed under `selectOK`. -/
theorem selectPoint_wellFormed (flag : Wire) (cols : List (Wire × Wire × Wire))
    (h : selectOK flag cols) : CircuitWellFormed (selectPoint flag cols) := by
  induction cols with
  | nil => simp [selectPoint]
  | cons c cs ih =>
      obtain ⟨x,y,o⟩ := c
      simp only [selectOK, List.map_cons, List.nodup_cons] at h
      obtain ⟨⟨ho, houts⟩, hfo, hall⟩ := h
      have hhead := hall (x,y,o) (List.mem_cons_self ..)
      have hflagout : flag ≠ o := fun e => hfo (e ▸ List.mem_cons_self ..)
      have htail : selectOK flag cs := by
        simp only [selectOK]
        refine ⟨houts, ?_, ?_⟩
        · exact fun hf => hfo (List.mem_cons_of_mem _ hf)
        · intro d hd
          have hd' := hall d (List.mem_cons_of_mem _ hd)
          exact ⟨fun hm => hd'.1 (List.mem_cons_of_mem _ hm),
            fun hm => hd'.2.1 (List.mem_cons_of_mem _ hm), hd'.2.2⟩
      rw [selectPoint, circuitWellFormed_append]
      constructor
      · simp only [selectBit, circuitWellFormed_cons, circuitWellFormed_nil,
          Gate.WellFormed, and_true]
        exact ⟨Ne.symm (fun e => hhead.1 (e ▸ List.mem_cons_self ..)),
          hhead.2.2.2.2,
          ⟨hhead.2.2.2.1, hflagout,
            Ne.symm (fun e => hhead.2.1 (e ▸ List.mem_cons_self ..))⟩,
          hhead.2.2.2.2⟩
      · exact ih htail

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

end ShorECDLP
