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
- **M1.3.2** — the modular adder `(a + b) mod p`, correctness against `Field.p`; here the
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

end ShorECDLP
