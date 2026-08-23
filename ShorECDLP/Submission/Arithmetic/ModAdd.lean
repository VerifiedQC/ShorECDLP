import ShorECDLP.Submission.Arithmetic.RippleAdder

/-
# Modular adder (M1.3) — `(a + b) mod p`

Naive/textbook construction: reuse the general `ripple` adder (M1.2) together with constant
loads, rather than specializing arithmetic to secp256k1's prime `p`. `loadConst` X-es a
constant into a register, so a register–register adder doubles as a constant adder; the
modular adder (later sub-step) adds `b`, conditionally subtracts the constant `p`, and
uncomputes — all over `ripple`.

Built up one sub-step per PR:
- **M1.3.0** (this PR) — `loadConst`: load a classical constant into a register.
- **M1.3.1** — constant adder `(a + c) mod 2ⁿ` (load ⇒ ripple ⇒ unload).
- **M1.3.2** — the modular adder `(a + b) mod p`, correctness against `Field.p`.
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

end ShorECDLP
