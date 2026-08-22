import ShorECDLP.Framework.Classical.Semantics
import ShorECDLP.Framework.CostModel

/-
# Reversible full-adder cell (M1, submission arithmetic)

The atom of the ripple-carry adder. Given input bits on wires `a, b, cin` and two fresh
(`|0⟩`) output wires `s` (sum) and `co` (carry-out), `fullAdder` writes
`s := a ⊕ b ⊕ cin` and `co := majority(a, b, cin)`. Correctness is proved against the
classical basis-state semantics; the T-count is the naive framework metric.
-/

namespace ShorECDLP

open Classical

/-- A reversible full-adder cell over `{CCX, CX}`. `s` and `co` must be fresh wires. -/
def fullAdder (a b cin s co : Nat) : Circuit :=
  [Gate.CCX a b co, Gate.CCX a cin co, Gate.CCX b cin co,
   Gate.CX a s, Gate.CX b s, Gate.CX cin s]

/-- The full-adder cell costs `3 · 7 = 21` T (three Toffolis; the CNOTs are free). -/
theorem fullAdder_tCount (a b cin s co : Nat) : tCount (fullAdder a b cin s co) = 21 := rfl

/-- Sum wire: with the output wires `s, co` fresh and distinct from the inputs, the adder
writes `a ⊕ b ⊕ cin` on `s`. -/
theorem fullAdder_sum (a b cin s co : Nat) (st : State) (hs : st s = false)
    (bs : b ≠ s) (cs : cin ≠ s)
    (ac : a ≠ co) (bc : b ≠ co) (cc : cin ≠ co) (sc : s ≠ co) :
    ⟪fullAdder a b cin s co⟫ st s
      = Bool.xor (Bool.xor (st a) (st b)) (st cin) := by
  simp only [fullAdder, run_cons, run_nil, applyGate, upd_same,
    upd_other _ _ _ bs, upd_other _ _ _ cs,
    upd_other _ _ _ ac, upd_other _ _ _ bc, upd_other _ _ _ cc,
    upd_other _ _ _ sc, hs]
  cases st a <;> cases st b <;> cases st cin <;> rfl

/-- Carry wire: with the output wires `s, co` fresh and distinct from the inputs, the adder
writes `majority(a, b, cin) = (a∧b) ⊕ (a∧cin) ⊕ (b∧cin)` on `co`. -/
theorem fullAdder_carry (a b cin s co : Nat) (st : State) (hco : st co = false)
    (bs : b ≠ s) (cs : cin ≠ s)
    (ac : a ≠ co) (bc : b ≠ co) (cc : cin ≠ co) (sc : s ≠ co) :
    ⟪fullAdder a b cin s co⟫ st co
      = Bool.xor (Bool.xor (st a && st b) (st a && st cin)) (st b && st cin) := by
  simp only [fullAdder, run_cons, run_nil, applyGate, upd_same,
    upd_other _ _ _ bs, upd_other _ _ _ cs,
    upd_other _ _ _ ac, upd_other _ _ _ bc, upd_other _ _ _ cc,
    upd_other _ _ _ sc.symm, hco]
  cases st a <;> cases st b <;> cases st cin <;> rfl

end ShorECDLP
