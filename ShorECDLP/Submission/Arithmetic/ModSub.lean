import ShorECDLP.Submission.Arithmetic.ModAdd

/-!
# Clean modular subtraction

This file supplies the missing field operation `(a - b) mod modulus`.  The construction is
the textbook two's-complement subtractor over the existing ripple adder:

```text
prepare(b, cin):
  X every bit of b                   -- bitwise complement
  X cin                              -- carry-in 1

subtractRaw(a, b; raw, noBorrow):
  prepare
  ripple(a, not b, 1; raw, noBorrow)
  reverse(prepare)                   -- restore b and cin

compute:
  subtractRaw
  addConst(raw, modulus; candidate)

modSub:
  compute
  selectPoint(noBorrow, candidate, raw; out)
  reverse(compute)
```

The first carry is `true` exactly when `a ≥ b`.  Thus the selector keeps `raw = a - b` in the
no-borrow branch, and otherwise keeps the low bits of `raw + modulus = a + modulus - b`.
The final reverse is Bennett cleanup: public inputs are restored, the answer remains in the
fresh output, and every owned work wire returns to zero.

For canonical inputs and `modulus < 2^width`, the public contract proves

```text
value(out, after) = (value(a) + modulus - value(b)) % modulus
tCount(modSub) = 91 * width
```

along with declared-wire locality, H/P-freedom, physical well-formedness, input preservation,
and exact work cleanup for the same circuit term.
-/

namespace ShorECDLP

open Classical
open Arithmetic

/-! ## Bitwise complement and the raw two's-complement subtraction -/

/-- Flip every bit of an LSB-first register. -/
def complementReg : List Wire → Circuit
  | [] => []
  | w :: ws => Gate.X w :: complementReg ws

/-- Complementing changes no wire outside the register. -/
theorem complementReg_other (w : Wire) :
    ∀ (ws : List Wire) (st : BasisState), w ∉ ws →
      run (complementReg ws) st w = st w := by
  intro ws
  induction ws with
  | nil => intro st _; rfl
  | cons x xs ih =>
      intro st hw
      simp only [List.mem_cons, not_or] at hw
      rw [complementReg, run_cons, ih (applyGate (Gate.X x) st) hw.2]
      exact upd_other st x (!st x) hw.1

/-- A complemented register is the width-bounded bitwise complement of its old value. -/
theorem complementReg_mem :
    ∀ (ws : List Wire) (st : BasisState), ws.Nodup →
      ∀ w ∈ ws, run (complementReg ws) st w = !st w := by
  intro ws
  induction ws with
  | nil => simp
  | cons x xs ih =>
      intro st hnd w hw
      obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
      simp only [List.mem_cons] at hw
      rw [complementReg, run_cons]
      rcases hw with hw | hw
      · subst w
        rw [complementReg_other x xs (applyGate (Gate.X x) st) hx]
        simp [applyGate, upd]
      · rw [ih (applyGate (Gate.X x) st) hxs w hw]
        have hwx : w ≠ x := fun e => hx (e ▸ hw)
        simp [applyGate, upd, hwx]

/-- Reading the pointwise Boolean complement gives `2^width - 1 - value`. -/
private theorem regValue_boolNot (ws : List Wire) (st : BasisState) :
    regValue ws (fun w => !st w) = 2 ^ ws.length - 1 - regValue ws st := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      rw [regValue_cons, regValue_cons, ih, List.length_cons, Nat.pow_succ]
      have hbound := regValue_lt_two_pow ws st
      cases st w <;> simp <;> omega

/-- Numeric action of bitwise complement on a duplicate-free register. -/
theorem regValue_complementReg (ws : List Wire) (st : BasisState) (hnd : ws.Nodup) :
    regValue ws (run (complementReg ws) st) =
      2 ^ ws.length - 1 - regValue ws st := by
  calc
    regValue ws (run (complementReg ws) st) = regValue ws (fun w => !st w) := by
      apply regValue_congr
      exact complementReg_mem ws st hnd
    _ = _ := regValue_boolNot ws st

@[simp]
theorem complementReg_tCount (ws : List Wire) : tCount (complementReg ws) = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [complementReg, tCost] using ih

@[simp]
theorem complementReg_HPFree (ws : List Wire) : HPFree (complementReg ws) := by
  induction ws with
  | nil => simp [complementReg]
  | cons w ws ih => simp [complementReg, ih]

theorem complementReg_wellFormed (ws : List Wire) :
    CircuitWellFormed (complementReg ws) := by
  induction ws with
  | nil => simp [complementReg]
  | cons w ws ih => simp [complementReg, Gate.WellFormed, ih]

theorem complementReg_usesOnly (ws : List Wire) :
    CircuitUsesOnly ws (complementReg ws) := by
  induction ws with
  | nil => intro g hg; simp [complementReg] at hg
  | cons w ws ih =>
      rw [complementReg]
      intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · simp [Gate.UsesOnly]
      · exact usesOnly_mono ih (fun x hx => List.mem_cons_of_mem w hx) g hg

/-- Prepare two's-complement subtraction by complementing `b` and setting the carry-in. -/
def subPrepare (cols : List (Wire × Wire × Wire)) (cin : Wire) : Circuit :=
  complementReg (cols.map (fun c => c.2.1)) ++ [Gate.X cin]

/-- Compute the width-bounded raw difference and a no-borrow carry, restoring `b` and `cin`. -/
def subRaw (cols : List (Wire × Wire × Wire)) (cin : Wire)
    (couts : List Wire) : Circuit :=
  let prepare := subPrepare cols cin
  prepare ++ ripple cols cin couts ++ prepare.reverse

def subRawFootprint (cols : List (Wire × Wire × Wire)) (cin : Wire)
    (couts : List Wire) : List Wire :=
  cols.map (fun c => c.1) ++
    (cols.map (fun c => c.2.1) ++
      (cols.map (fun c => c.2.2) ++ ([cin] ++ couts)))

/-- At positive width, the threaded final carry is one of the carry-bank wires. -/
theorem carryOut_mem_couts (cin : Wire) :
    ∀ (couts : List Wire), couts ≠ [] → carryOut cin couts ∈ couts := by
  intro couts
  induction couts generalizing cin with
  | nil => intro h; contradiction
  | cons co cs ih =>
      intro _
      cases cs with
      | nil => simp [carryOut]
      | cons co' cs =>
          rw [carryOut]
          exact List.mem_cons_of_mem co (ih co (by simp))

theorem subPrepare_usesOnly (cols : List (Wire × Wire × Wire)) (cin : Wire) :
    CircuitUsesOnly (cols.map (fun c => c.2.1) ++ [cin]) (subPrepare cols cin) := by
  rw [subPrepare]
  apply usesOnly_append
  · exact usesOnly_mono (complementReg_usesOnly _) (fun w hw => List.mem_append_left _ hw)
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp [Gate.UsesOnly]

theorem subRaw_usesOnly (cols : List (Wire × Wire × Wire)) (cin : Wire)
    (couts : List Wire) :
    CircuitUsesOnly (subRawFootprint cols cin couts) (subRaw cols cin couts) := by
  have hprep : CircuitUsesOnly (subRawFootprint cols cin couts) (subPrepare cols cin) :=
    usesOnly_mono (subPrepare_usesOnly cols cin) (by
      intro w hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · simp [subRawFootprint, hw]
      · subst w
        simp [subRawFootprint])
  have hripple : CircuitUsesOnly (subRawFootprint cols cin couts) (ripple cols cin couts) :=
    ModAddSupport.circuitUsesOnly_mono (ModAddSupport.ripple_usesOnly cols cin couts) (by
      intro w hw
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append,
        ModAddSupport.colsWires, List.mem_flatMap] at hw
      rcases hw with rfl | hw
      · simp [subRawFootprint]
      · rcases hw with hw | ⟨c, hc, hw⟩
        · simp [subRawFootprint, hw]
        · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
          rcases hw' with rfl | rfl | rfl <;>
            simp [subRawFootprint, List.mem_map_of_mem hc])
  rw [subRaw]
  exact usesOnly_append (usesOnly_append hprep hripple) (usesOnly_reverse hprep)

theorem subRaw_tCount (cols : List (Wire × Wire × Wire)) (cin : Wire)
    (couts : List Wire) (hlen : couts.length = cols.length) :
    tCount (subRaw cols cin couts) = 21 * cols.length := by
  rw [subRaw, tCount_append, tCount_append, tCount_reverse,
    ripple_tCount cols cin couts hlen]
  simp [subPrepare, tCount_append, tCost]

theorem subPrepare_HPFree (cols : List (Wire × Wire × Wire)) (cin : Wire) :
    HPFree (subPrepare cols cin) := by
  simp [subPrepare, hpFree_append]

theorem subPrepare_wellFormed (cols : List (Wire × Wire × Wire)) (cin : Wire) :
    CircuitWellFormed (subPrepare cols cin) := by
  simp [subPrepare, circuitWellFormed_append, complementReg_wellFormed, Gate.WellFormed]

theorem subRaw_HPFree (cols : List (Wire × Wire × Wire)) (cin : Wire)
    (couts : List Wire) : HPFree (subRaw cols cin couts) := by
  rw [subRaw, hpFree_append, hpFree_append]
  exact ⟨⟨subPrepare_HPFree cols cin, ripple_HPFree cols cin couts⟩,
    Arithmetic.hpFree_reverse (subPrepare_HPFree cols cin)⟩

theorem subRaw_wellFormed (cols : List (Wire × Wire × Wire)) (cin : Wire)
    (couts : List Wire) (h : wiresOK cols cin couts) :
    CircuitWellFormed (subRaw cols cin couts) := by
  rw [subRaw, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨subPrepare_wellFormed cols cin, ripple_wellFormed cols cin couts h⟩,
    Arithmetic.wellFormed_reverse (subPrepare_wellFormed cols cin)⟩

/-- Raw two's-complement subtraction identity.  The final carry is the no-borrow flag. -/
theorem subRaw_correct
    (cols : List (Wire × Wire × Wire)) (cin : Wire) (couts : List Wire)
    (st : BasisState)
    (hlen : couts.length = cols.length)
    (hwok : wiresOK cols cin couts)
    (hbNodup : (cols.map (fun c => c.2.1)).Nodup)
    (hcinB : cin ∉ cols.map (fun c => c.2.1))
    (hAOutside : ∀ w ∈ cols.map (fun c => c.1),
      w ∉ cols.map (fun c => c.2.1) ++ [cin])
    (hSOutside : ∀ w ∈ cols.map (fun c => c.2.2),
      w ∉ cols.map (fun c => c.2.1) ++ [cin])
    (hcoutsOutside : ∀ w ∈ couts,
      w ∉ cols.map (fun c => c.2.1) ++ [cin])
    (hcarryOutside : carryOut cin couts ∉ cols.map (fun c => c.2.1) ++ [cin])
    (hcarryFresh : ∀ w ∈ couts, st w = false)
    (hsumFresh : ∀ c ∈ cols, st c.2.2 = false)
    (hcinFresh : st cin = false) :
    regValue (cols.map (fun c => c.2.2)) (run (subRaw cols cin couts) st) +
        2 ^ cols.length * bit (run (subRaw cols cin couts) st) (carryOut cin couts) =
      regValue (cols.map (fun c => c.1)) st + 2 ^ cols.length -
        regValue (cols.map (fun c => c.2.1)) st := by
  let B := cols.map (fun c => c.2.1)
  let S := cols.map (fun c => c.2.2)
  let prepare := subPrepare cols cin
  let prepared := run prepare st
  have hprepareUses : CircuitUsesOnly (B ++ [cin]) prepare := by
    simpa [B, prepare] using subPrepare_usesOnly cols cin
  have hpreparedB : regValue B prepared = 2 ^ cols.length - 1 - regValue B st := by
    change regValue B (run (subPrepare cols cin) st) = _
    rw [subPrepare, run_append]
    calc
      regValue B (run [Gate.X cin] (run (complementReg B) st)) =
          regValue B (run (complementReg B) st) := by
        apply regValue_congr
        intro w hw
        have hwcin : w ≠ cin := fun e => hcinB (e ▸ hw)
        simp [run_cons, run_nil, applyGate, upd, hwcin]
      _ = 2 ^ B.length - 1 - regValue B st := regValue_complementReg B st hbNodup
      _ = _ := by simp [B]
  have hpreparedA : regValue (cols.map (fun c => c.1)) prepared =
      regValue (cols.map (fun c => c.1)) st := by
    apply regValue_congr
    intro w hw
    exact hprepareUses.preservesOutside st w (hAOutside w hw)
  have hpreparedCin : prepared cin = true := by
    change run (subPrepare cols cin) st cin = true
    rw [subPrepare, run_append]
    simp only [run_cons, run_nil, applyGate, upd_same]
    rw [complementReg_other cin B st hcinB, hcinFresh]
    rfl
  have hpreparedCarry : ∀ w ∈ couts, prepared w = false := by
    intro w hw
    exact Eq.trans (hprepareUses.preservesOutside st w (hcoutsOutside w hw))
      (hcarryFresh w hw)
  have hpreparedSum : ∀ c ∈ cols, prepared c.2.2 = false := by
    intro c hc
    apply Eq.trans (hprepareUses.preservesOutside st c.2.2 ?_) (hsumFresh c hc)
    exact hSOutside c.2.2 (List.mem_map_of_mem hc)
  have hripple := ripple_correct cols cin couts prepared hlen hwok
    hpreparedCarry hpreparedSum
  rw [hpreparedA, hpreparedB] at hripple
  have hcinBit : bit prepared cin = 1 := by simp [bit, hpreparedCin]
  rw [hcinBit] at hripple
  have hBbound : regValue B st < 2 ^ cols.length := by
    simpa [B] using regValue_lt_two_pow B st
  have hripple' :
      regValue S (run (ripple cols cin couts) prepared) +
          2 ^ cols.length * bit (run (ripple cols cin couts) prepared) (carryOut cin couts) =
        regValue (cols.map (fun c => c.1)) st + 2 ^ cols.length - regValue B st := by
    let a := regValue (cols.map (fun c => c.1)) st
    let b := regValue B st
    let M := 2 ^ cols.length
    have hbM : b < M := by simpa [b, M] using hBbound
    have hminus : M - 1 - b + 1 = M - b := by omega
    have haddSub : a + (M - b) = a + M - b := by omega
    calc
      regValue S (run (ripple cols cin couts) prepared) +
          M * bit (run (ripple cols cin couts) prepared) (carryOut cin couts) =
        a + (M - 1 - b) + 1 := by simpa [S, B, a, b, M] using hripple
      _ = a + ((M - 1 - b) + 1) := by omega
      _ = a + (M - b) := by rw [hminus]
      _ = a + M - b := haddSub
  have hreverseUses : CircuitUsesOnly (B ++ [cin]) prepare.reverse :=
    usesOnly_reverse hprepareUses
  have hsumKeep : regValue S
      (run prepare.reverse (run (ripple cols cin couts) prepared)) =
      regValue S (run (ripple cols cin couts) prepared) := by
    apply regValue_congr
    intro w hw
    exact hreverseUses.preservesOutside _ w (hSOutside w (by simpa [S] using hw))
  have hcarryKeep : bit
      (run prepare.reverse (run (ripple cols cin couts) prepared)) (carryOut cin couts) =
      bit (run (ripple cols cin couts) prepared) (carryOut cin couts) := by
    rw [bit, bit, hreverseUses.preservesOutside _ _ hcarryOutside]
  rw [subRaw, run_append, run_append, hsumKeep, hcarryKeep]
  simpa [S, B, prepare, prepared] using hripple'

/-! ## Modular correction, selection, and exact resource packages -/

/-- Forward computation of the raw difference and the `+ modulus` underflow candidate. -/
def modSubCompute (subCols addCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) : Circuit :=
  subRaw subCols cin₁ couts₁ ++ addConst addCols cin₂ couts₂ modulus

/-- Clean modular subtractor: compute, select by the no-borrow carry, then Bennett-uncompute. -/
def modSub (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) : Circuit :=
  let compute := modSubCompute subCols addCols cin₁ couts₁ cin₂ couts₂ modulus
  compute ++ selectPoint (carryOut cin₁ couts₁) selectCols ++ compute.reverse

/-- Arithmetic fact underlying the no-borrow selector. -/
theorem modSub_select_eq (modulus M a b raw candidate : Nat)
    (noBorrow overflow : Bool)
    (hmod : 0 < modulus) (hfit : modulus < M)
    (ha : a < modulus) (hb : b < modulus)
    (hraw : raw < M) (hcandidate : candidate < M)
    (hrawEq : raw + M * (if noBorrow then 1 else 0) = a + M - b)
    (hcandidateEq : candidate + M * (if overflow then 1 else 0) = raw + modulus) :
    (if noBorrow then raw else candidate) = (a + modulus - b) % modulus := by
  cases noBorrow with
  | false =>
      simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at hrawEq ⊢
      have hab : a < b := by omega
      have hresultLt : a + modulus - b < modulus := by omega
      cases overflow with
      | false => simp at hcandidateEq; omega
      | true =>
          simp only [if_true, Nat.mul_one] at hcandidateEq
          have hc : candidate = a + modulus - b := by omega
          rw [hc, Nat.mod_eq_of_lt hresultLt]
  | true =>
      simp only [if_true, Nat.mul_one] at hrawEq ⊢
      have hba : b ≤ a := by omega
      have hr : raw = a - b := by omega
      have hresult : a + modulus - b = (a - b) + modulus := by omega
      have hsmall : a - b < modulus := by omega
      rw [hr, hresult]
      simp [Nat.mod_eq_of_lt hsmall]

theorem modSubCompute_tCount (subCols addCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (hsub : couts₁.length = subCols.length)
    (hadd : couts₂.length = addCols.length) (hlen : addCols.length = subCols.length) :
    tCount (modSubCompute subCols addCols cin₁ couts₁ cin₂ couts₂ modulus) =
      42 * subCols.length := by
  rw [modSubCompute, tCount_append, subRaw_tCount _ _ _ hsub,
    addConst_tCount _ _ _ _ hadd]
  omega

theorem modSub_tCount (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (hsub : couts₁.length = subCols.length)
    (hadd : couts₂.length = addCols.length) (hlen₁ : addCols.length = subCols.length)
    (hlen₂ : selectCols.length = subCols.length) :
    tCount (modSub subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) =
      91 * subCols.length := by
  rw [modSub, tCount_append, tCount_append, tCount_reverse,
    modSubCompute_tCount _ _ _ _ _ _ _ hsub hadd hlen₁, selectPoint_tCount]
  omega

theorem modSubCompute_HPFree (subCols addCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) :
    HPFree (modSubCompute subCols addCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modSubCompute, hpFree_append]
  exact ⟨subRaw_HPFree _ _ _, addConst_HPFree _ _ _ _⟩

theorem modSubCompute_wellFormed (subCols addCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (hsub : wiresOK subCols cin₁ couts₁)
    (hadd : wiresOK addCols cin₂ couts₂) :
    CircuitWellFormed (modSubCompute subCols addCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modSubCompute, circuitWellFormed_append]
  exact ⟨subRaw_wellFormed _ _ _ hsub, addConst_wellFormed _ _ _ _ hadd⟩

theorem modSub_HPFree (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) :
    HPFree (modSub subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modSub, hpFree_append, hpFree_append]
  have hc := modSubCompute_HPFree subCols addCols cin₁ couts₁ cin₂ couts₂ modulus
  exact ⟨⟨hc, selectPoint_HPFree _ _⟩, Arithmetic.hpFree_reverse hc⟩

theorem modSub_wellFormed (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) (hsub : wiresOK subCols cin₁ couts₁)
    (hadd : wiresOK addCols cin₂ couts₂)
    (hselect : selectOK (carryOut cin₁ couts₁) selectCols) :
    CircuitWellFormed (modSub subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  rw [modSub, circuitWellFormed_append, circuitWellFormed_append]
  have hc := modSubCompute_wellFormed subCols addCols cin₁ couts₁ cin₂ couts₂ modulus hsub hadd
  exact ⟨⟨hc, selectPoint_wellFormed _ _ hselect⟩, Arithmetic.wellFormed_reverse hc⟩

/-! ## Declared layout, locality, and clean contract -/

/-- Public `A`, public `B`, public output `O`, then raw difference `X`, constant scratch `K`,
correction candidate `Y`, and both carry banks/carry-ins. -/
def modSubLayout
    (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) :
    RegisterLayout where
  lhs := subCols.map (fun c => c.1)
  rhs := subCols.map (fun c => c.2.1)
  out := selectCols.map (fun c => c.2.2)
  work :=
    subCols.map (fun c => c.2.2) ++
      (addCols.map (fun c => c.2.1) ++
        (addCols.map (fun c => c.2.2) ++
          ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂)))))

/-- Every wire used by the forward computation, excluding the fresh selector output. -/
def modSubActiveWires
    (subCols addCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) : List Wire :=
  subCols.map (fun c => c.1) ++
    (subCols.map (fun c => c.2.1) ++
      (subCols.map (fun c => c.2.2) ++
        (addCols.map (fun c => c.2.1) ++
          (addCols.map (fun c => c.2.2) ++
            ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂)))))))

/-- Public inputs/output and the complete owned workspace. -/
def modSubAllWires
    (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire) : List Wire :=
  subCols.map (fun c => c.1) ++
    (subCols.map (fun c => c.2.1) ++
      (selectCols.map (fun c => c.2.2) ++
        (subCols.map (fun c => c.2.2) ++
          (addCols.map (fun c => c.2.1) ++
            (addCols.map (fun c => c.2.2) ++
              ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂))))))))

/-- Genuine wiring obligations for one modular-subtraction instance.  Cross-register freshness is
derived from `modSubLayout.Valid` inside the contract rather than duplicated here. -/
structure ModSubWiring
    (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat) : Prop where
  subLen : couts₁.length = subCols.length
  addLen : couts₂.length = addCols.length
  width : addCols.length = subCols.length
  selectLen : selectCols.length = subCols.length
  subOK : wiresOK subCols cin₁ couts₁
  addOK : wiresOK addCols cin₂ couts₂
  selectOK : ShorECDLP.selectOK (carryOut cin₁ couts₁) selectCols
  addA : addCols.map (fun c => c.1) = subCols.map (fun c => c.2.2)
  selectCandidate : selectCols.map (fun c => c.1) = addCols.map (fun c => c.2.2)
  selectRaw : selectCols.map (fun c => c.2.1) = subCols.map (fun c => c.2.2)
  modulusPos : 0 < modulus
  fit : modulus < 2 ^ subCols.length

/-- The forward computation stays within the active (non-output) registers. -/
theorem modSubCompute_usesOnly
    (subCols addCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (haddA : addCols.map (fun c => c.1) = subCols.map (fun c => c.2.2)) :
    CircuitUsesOnly (modSubActiveWires subCols addCols cin₁ couts₁ cin₂ couts₂)
      (modSubCompute subCols addCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  let active := modSubActiveWires subCols addCols cin₁ couts₁ cin₂ couts₂
  have hsub : ∀ w ∈ subRawFootprint subCols cin₁ couts₁, w ∈ active := by
    intro w hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | rfl | hwC
    · simp [active, modSubActiveWires, hwA]
    · simp [active, modSubActiveWires, hwB]
    · simp [active, modSubActiveWires, hwX]
    · simp [active, modSubActiveWires]
    · simp [active, modSubActiveWires, hwC]
  have hadd : ∀ w ∈ ModAddSupport.rippleFootprint addCols cin₂ couts₂, w ∈ active := by
    intro w hw
    simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append,
      ModAddSupport.colsWires, List.mem_flatMap] at hw
    rcases hw with rfl | hw
    · simp [active, modSubActiveWires]
    · rcases hw with hw | ⟨c, hc, hw⟩
      · simp [active, modSubActiveWires, hw]
      · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
        rcases hw' with rfl | rfl | rfl
        · have hm : c.1 ∈ subCols.map (fun d => d.2.2) := by
            rw [← haddA]
            exact List.mem_map_of_mem hc
          simp [active, modSubActiveWires, hm]
        · simp [active, modSubActiveWires, List.mem_map_of_mem hc]
        · simp [active, modSubActiveWires, List.mem_map_of_mem hc]
  rw [modSubCompute]
  exact usesOnly_append
    (usesOnly_mono (subRaw_usesOnly subCols cin₁ couts₁) hsub)
    (usesOnly_mono (ModAddSupport.addConst_usesOnly addCols cin₂ couts₂ modulus) hadd)

/-- Every control and target of `modSub` belongs to its declared public/work layout. -/
theorem modSub_usesOnly
    (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (haddA : addCols.map (fun c => c.1) = subCols.map (fun c => c.2.2))
    (hselectCandidate : selectCols.map (fun c => c.1) = addCols.map (fun c => c.2.2))
    (hselectRaw : selectCols.map (fun c => c.2.1) = subCols.map (fun c => c.2.2)) :
    CircuitUsesOnly (modSubAllWires subCols addCols selectCols cin₁ couts₁ cin₂ couts₂)
      (modSub subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) := by
  let active := modSubActiveWires subCols addCols cin₁ couts₁ cin₂ couts₂
  let all := modSubAllWires subCols addCols selectCols cin₁ couts₁ cin₂ couts₂
  have hactive : ∀ w ∈ active, w ∈ all := by
    intro w hw
    simp only [active, modSubActiveWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwK | hwY | rfl | hwC₁ | rfl | hwC₂
    · simp [all, modSubAllWires, hwA]
    · simp [all, modSubAllWires, hwB]
    · simp [all, modSubAllWires, hwX]
    · simp [all, modSubAllWires, hwK]
    · simp [all, modSubAllWires, hwY]
    · simp [all, modSubAllWires]
    · simp [all, modSubAllWires, hwC₁]
    · simp [all, modSubAllWires]
    · simp [all, modSubAllWires, hwC₂]
  have hcompute : CircuitUsesOnly all
      (modSubCompute subCols addCols cin₁ couts₁ cin₂ couts₂ modulus) :=
    usesOnly_mono
      (modSubCompute_usesOnly subCols addCols cin₁ couts₁ cin₂ couts₂ modulus haddA)
      hactive
  have hselect : ∀ w ∈ selectFootprint (carryOut cin₁ couts₁) selectCols, w ∈ all := by
    intro w hw
    simp only [selectFootprint, List.mem_cons, List.mem_flatMap] at hw
    rcases hw with rfl | ⟨c, hc, hw⟩
    · have hcarry := ModAddSupport.carryOut_mem_footprint cin₁ couts₁
      simp only [List.mem_cons] at hcarry
      rcases hcarry with hcarry | hcarry
      · rw [hcarry]
        simp [all, modSubAllWires]
      · simp [all, modSubAllWires, hcarry]
    · have hw' : w = c.1 ∨ w = c.2.1 ∨ w = c.2.2 := by simpa using hw
      rcases hw' with rfl | rfl | rfl
      · have hm : c.1 ∈ addCols.map (fun d => d.2.2) := by
          rw [← hselectCandidate]
          exact List.mem_map_of_mem hc
        simp [all, modSubAllWires, hm]
      · have hm : c.2.1 ∈ subCols.map (fun d => d.2.2) := by
          rw [← hselectRaw]
          exact List.mem_map_of_mem hc
        simp [all, modSubAllWires, hm]
      · simp [all, modSubAllWires, List.mem_map_of_mem hc]
  rw [modSub]
  exact usesOnly_append
    (usesOnly_append hcompute
      (usesOnly_mono (selectPoint_usesOnly (carryOut cin₁ couts₁) selectCols) hselect))
    (usesOnly_reverse hcompute)

/-- Functional correctness of the exact clean modular-subtraction circuit term. -/
theorem modSub_correct
    (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (wiring : ModSubWiring subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus)
    (st : BasisState)
    (hvalid : (modSubLayout subCols addCols selectCols cin₁ couts₁ cin₂ couts₂).Valid)
    (ha : regValue (subCols.map (fun c => c.1)) st < modulus)
    (hb : regValue (subCols.map (fun c => c.2.1)) st < modulus)
    (hclean : Clean
      ((modSubLayout subCols addCols selectCols cin₁ couts₁ cin₂ couts₂).out ++
       (modSubLayout subCols addCols selectCols cin₁ couts₁ cin₂ couts₂).work) st) :
    regValue (selectCols.map (fun c => c.2.2))
        (run (modSub subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) st) =
      (regValue (subCols.map (fun c => c.1)) st + modulus -
        regValue (subCols.map (fun c => c.2.1)) st) % modulus := by
  let layout := modSubLayout subCols addCols selectCols cin₁ couts₁ cin₂ couts₂
  let A := subCols.map (fun c => c.1)
  let B := subCols.map (fun c => c.2.1)
  let O := selectCols.map (fun c => c.2.2)
  let X := subCols.map (fun c => c.2.2)
  let K := addCols.map (fun c => c.2.1)
  let Y := addCols.map (fun c => c.2.2)
  let rawState := run (subRaw subCols cin₁ couts₁) st
  let compute := modSubCompute subCols addCols cin₁ couts₁ cin₂ couts₂ modulus
  let computeState := run compute st

  have hnodup :
      (A ++ (B ++ (O ++ (X ++ (K ++ (Y ++
        ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂))))))))).Nodup := by
    simpa [A, B, O, X, K, Y, layout, modSubLayout, RegisterLayout.allWires,
      List.append_assoc] using hvalid.2.2
  rcases List.nodup_append.mp hnodup with ⟨hANodup, htailA, hAcrossA⟩
  rcases List.nodup_append.mp htailA with ⟨hBNodup, htailB, hAcrossB⟩
  rcases List.nodup_append.mp htailB with ⟨hONodup, htailO, hAcrossO⟩
  rcases List.nodup_append.mp htailO with ⟨hXNodup, htailX, hAcrossX⟩
  rcases List.nodup_append.mp htailX with ⟨hKNodup, htailK, hAcrossK⟩
  rcases List.nodup_append.mp htailK with ⟨hYNodup, htailY, hAcrossY⟩
  rcases List.nodup_append.mp htailY with ⟨_, htailCin₁, hAcrossCin₁⟩
  rcases List.nodup_append.mp htailCin₁ with
    ⟨hCouts₁Nodup, htailCouts₁, hAcrossCouts₁⟩

  have hworkClean : Clean layout.work st := by
    intro w hw
    exact hclean w (List.mem_append_right _ hw)
  have hwidthPos : 0 < subCols.length := by
    rcases Nat.eq_zero_or_pos subCols.length with hz | hpos
    · have hfit := wiring.fit
      simp [hz] at hfit
      omega
    · exact hpos
  have hcouts₁Nonempty : couts₁ ≠ [] := by
    intro hz
    have hlen := wiring.subLen
    simp [hz] at hlen
    omega
  have hflagMem : carryOut cin₁ couts₁ ∈ couts₁ :=
    carryOut_mem_couts cin₁ couts₁ hcouts₁Nonempty

  have hcin₁B : cin₁ ∉ B := by
    intro hwB
    exact hAcrossB cin₁ hwB cin₁ (by simp) rfl
  have hAOutside : ∀ w ∈ A, w ∉ B ++ [cin₁] := by
    intro w hwA hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hwB | hwCin
    · exact hAcrossA w hwA w (by simp [hwB]) rfl
    · exact hAcrossA w hwA cin₁ (by simp) hwCin
  have hXOutside : ∀ w ∈ X, w ∉ B ++ [cin₁] := by
    intro w hwX hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hwB | hwCin
    · exact hAcrossB w hwB w (by simp [hwX]) rfl
    · exact hAcrossX w hwX cin₁ (by simp) hwCin
  have hcouts₁Outside : ∀ w ∈ couts₁, w ∉ B ++ [cin₁] := by
    intro w hwC hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hwB | hwCin
    · exact hAcrossB w hwB w (by simp [hwC]) rfl
    · exact hAcrossCin₁ cin₁ (by simp) w (by simp [hwC]) hwCin.symm
  have hflagOutside : carryOut cin₁ couts₁ ∉ B ++ [cin₁] :=
    hcouts₁Outside _ hflagMem

  have hsubCarryFresh : ∀ w ∈ couts₁, st w = false := by
    intro w hw
    apply hworkClean w
    simp [layout, modSubLayout, hw]
  have hsubSumFresh : ∀ c ∈ subCols, st c.2.2 = false := by
    intro c hc
    apply hworkClean c.2.2
    simp [layout, modSubLayout, List.mem_map_of_mem hc]
  have hcin₁Fresh : st cin₁ = false := by
    apply hworkClean cin₁
    simp [layout, modSubLayout]
  have hraw := subRaw_correct subCols cin₁ couts₁ st
    wiring.subLen wiring.subOK (by simpa [B] using hBNodup)
    (by simpa [B] using hcin₁B)
    (by simpa [A, B] using hAOutside)
    (by simpa [X, B] using hXOutside)
    (by simpa [B] using hcouts₁Outside)
    (by simpa [B] using hflagOutside)
    hsubCarryFresh hsubSumFresh hcin₁Fresh

  have hnotSubK : ∀ w ∈ K, w ∉ subRawFootprint subCols cin₁ couts₁ := by
    intro w hwK hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwCin | hwC
    · exact hAcrossA w hwA w (by simp [hwK]) rfl
    · exact hAcrossB w hwB w (by simp [hwK]) rfl
    · exact hAcrossX w hwX w (by simp [hwK]) rfl
    · exact hAcrossK w hwK cin₁ (by simp) hwCin
    · exact hAcrossK w hwK w (by simp [hwC]) rfl
  have hnotSubY : ∀ w ∈ Y, w ∉ subRawFootprint subCols cin₁ couts₁ := by
    intro w hwY hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwCin | hwC
    · exact hAcrossA w hwA w (by simp [hwY]) rfl
    · exact hAcrossB w hwB w (by simp [hwY]) rfl
    · exact hAcrossX w hwX w (by simp [hwY]) rfl
    · exact hAcrossY w hwY cin₁ (by simp) hwCin
    · exact hAcrossY w hwY w (by simp [hwC]) rfl
  have hnotSubCin₂ : cin₂ ∉ subRawFootprint subCols cin₁ couts₁ := by
    intro hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwCin | hwC
    · exact hAcrossA cin₂ hwA cin₂ (by simp) rfl
    · exact hAcrossB cin₂ hwB cin₂ (by simp) rfl
    · exact hAcrossX cin₂ hwX cin₂ (by simp) rfl
    · subst cin₂
      exact hAcrossCin₁ cin₁ (by simp) cin₁ (by simp) rfl
    · exact hAcrossCouts₁ cin₂ hwC cin₂ (by simp) rfl
  have hnotSubCouts₂ : ∀ w ∈ couts₂, w ∉ subRawFootprint subCols cin₁ couts₁ := by
    intro w hwC₂ hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwCin | hwC₁
    · exact hAcrossA w hwA w (by simp [hwC₂]) rfl
    · exact hAcrossB w hwB w (by simp [hwC₂]) rfl
    · exact hAcrossX w hwX w (by simp [hwC₂]) rfl
    · exact hAcrossCin₁ cin₁ (by simp) w (by simp [hwC₂]) hwCin.symm
    · exact hAcrossCouts₁ w hwC₁ w (by simp [hwC₂]) rfl

  have hsubUses := subRaw_usesOnly subCols cin₁ couts₁
  have haddCarryFresh : ∀ w ∈ couts₂, rawState w = false := by
    intro w hw
    change run (subRaw subCols cin₁ couts₁) st w = false
    rw [hsubUses.preservesOutside st w (hnotSubCouts₂ w hw)]
    exact hworkClean w (by simp [layout, modSubLayout, hw])
  have haddSumFresh : ∀ c ∈ addCols, rawState c.2.2 = false := by
    intro c hc
    have hwY : c.2.2 ∈ Y := List.mem_map_of_mem hc
    change run (subRaw subCols cin₁ couts₁) st c.2.2 = false
    rw [hsubUses.preservesOutside st c.2.2 (hnotSubY c.2.2 hwY)]
    apply hworkClean c.2.2
    change c.2.2 ∈ X ++ (K ++ (Y ++ ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂)))))
    simp only [List.mem_append]
    exact Or.inr (Or.inr (Or.inl hwY))
  have haddBFresh : ∀ c ∈ addCols, rawState c.2.1 = false := by
    intro c hc
    have hwK : c.2.1 ∈ K := List.mem_map_of_mem hc
    change run (subRaw subCols cin₁ couts₁) st c.2.1 = false
    rw [hsubUses.preservesOutside st c.2.1 (hnotSubK c.2.1 hwK)]
    apply hworkClean c.2.1
    change c.2.1 ∈ X ++ (K ++ (Y ++ ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂)))))
    simp only [List.mem_append]
    exact Or.inr (Or.inl hwK)
  have hcin₂Fresh : rawState cin₂ = false := by
    change run (subRaw subCols cin₁ couts₁) st cin₂ = false
    rw [hsubUses.preservesOutside st cin₂ hnotSubCin₂]
    exact hworkClean cin₂ (by simp [layout, modSubLayout])

  have hXK : ∀ w ∈ X, w ∉ K := by
    intro w hwX hwK
    exact hAcrossX w hwX w (by simp [hwK]) rfl
  have hYK : ∀ w ∈ Y, w ∉ K := by
    intro w hwY hwK
    exact hAcrossK w hwK w (by simp [hwY]) rfl
  have hCouts₂K : ∀ w ∈ couts₂, w ∉ K := by
    intro w hwC hwK
    exact hAcrossK w hwK w (by simp [hwC]) rfl
  have hCin₂K : cin₂ ∉ K := by
    intro hwK
    exact hAcrossK cin₂ hwK cin₂ (by simp) rfl
  have hconstBound : modulus < 2 ^ addCols.length := by
    rw [wiring.width]
    exact wiring.fit
  have hcandidate := addConst_correct addCols cin₂ couts₂ modulus rawState
    wiring.addLen wiring.addOK (by simpa [K] using hKNodup)
    (by simpa [X, K, wiring.addA] using hXK)
    (by simpa [Y, K] using hYK)
    (by simpa [K] using hCouts₂K)
    (by simpa [K] using hCin₂K)
    haddCarryFresh haddSumFresh haddBFresh hcin₂Fresh hconstBound

  have hcomputeState : computeState =
      run (addConst addCols cin₂ couts₂ modulus) rawState := by
    simp [computeState, compute, modSubCompute, rawState, run_append]
  have hXY : ∀ w ∈ X, w ∉ Y := by
    intro w hwX hwY
    exact hAcrossX w hwX w (by simp [hwY]) rfl
  have hXCouts₂ : ∀ w ∈ X, w ∉ couts₂ := by
    intro w hwX hwC
    exact hAcrossX w hwX w (by simp [hwC]) rfl
  have hrawPreserved : regValue X computeState = regValue X rawState := by
    rw [hcomputeState]
    apply regValue_congr
    intro w hwX
    have hwAddA : w ∈ addCols.map (fun c => c.1) := by
      rw [wiring.addA]
      exact hwX
    exact addConst_other w addCols cin₂ couts₂ modulus rawState
      (hXK w hwX)
      (fun c hc he => hXY w hwX (he ▸ List.mem_map_of_mem hc))
      (fun c hc he => hXCouts₂ w hwX (he ▸ hc))
  have hFlagK : carryOut cin₁ couts₁ ∉ K := by
    intro hwK
    exact hAcrossK _ hwK _ (by simp [hflagMem]) rfl
  have hFlagY : ∀ c ∈ addCols, carryOut cin₁ couts₁ ≠ c.2.2 := by
    intro c hc he
    have hwY : c.2.2 ∈ Y := List.mem_map_of_mem hc
    exact hAcrossY c.2.2 hwY (carryOut cin₁ couts₁) (by simp [hflagMem]) he.symm
  have hFlagCouts₂ : ∀ w ∈ couts₂, carryOut cin₁ couts₁ ≠ w := by
    intro w hw he
    exact hAcrossCouts₁ _ hflagMem _ (by simp [hw]) he
  have hflagPreserved : computeState (carryOut cin₁ couts₁) =
      rawState (carryOut cin₁ couts₁) := by
    rw [hcomputeState]
    exact addConst_other (carryOut cin₁ couts₁) addCols cin₂ couts₂ modulus rawState
      (by simpa [K] using hFlagK) hFlagY hFlagCouts₂

  have hcandidateEq :
      regValue Y computeState + 2 ^ subCols.length *
          (if computeState (carryOut cin₂ couts₂) then 1 else 0) =
        regValue X rawState + modulus := by
    rw [hcomputeState]
    have hc := hcandidate
    rw [wiring.addA] at hc
    simpa [Y, X, bit, wiring.width] using hc
  have hrawEq :
      regValue X rawState + 2 ^ subCols.length *
          (if computeState (carryOut cin₁ couts₁) then 1 else 0) =
        regValue A st + 2 ^ subCols.length - regValue B st := by
    rw [hflagPreserved]
    simpa [X, A, B, rawState, bit] using hraw

  have hactiveUses :=
    modSubCompute_usesOnly subCols addCols cin₁ couts₁ cin₂ couts₂ modulus wiring.addA
  have houtActive : ∀ w ∈ O,
      w ∉ modSubActiveWires subCols addCols cin₁ couts₁ cin₂ couts₂ := by
    intro w hwO hw
    simp only [modSubActiveWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwK | hwY | hwCin₁ | hwC₁ | hwCin₂ | hwC₂
    · exact hAcrossA w hwA w (by simp [hwO]) rfl
    · exact hAcrossB w hwB w (by simp [hwO]) rfl
    · exact hAcrossO w hwO w (by
        simp only [List.mem_append]
        exact Or.inl hwX) rfl
    · exact hAcrossO w hwO w (by
        simp only [List.mem_append]
        exact Or.inr (Or.inl hwK)) rfl
    · exact hAcrossO w hwO w (by
        simp only [List.mem_append]
        exact Or.inr (Or.inr (Or.inl hwY))) rfl
    · exact hAcrossO w hwO cin₁ (by simp) hwCin₁
    · exact hAcrossO w hwO w (by simp [hwC₁]) rfl
    · exact hAcrossO w hwO cin₂ (by simp) hwCin₂
    · exact hAcrossO w hwO w (by simp [hwC₂]) rfl
  have houtFresh : ∀ c ∈ selectCols, computeState c.2.2 = false := by
    intro c hc
    have hwO : c.2.2 ∈ O := List.mem_map_of_mem hc
    change run compute st c.2.2 = false
    rw [hactiveUses.preservesOutside st c.2.2 (houtActive c.2.2 hwO)]
    exact hclean c.2.2 (List.mem_append_left _ (by simpa [layout, modSubLayout, O] using hwO))
  have hselected := selectPoint_correct (carryOut cin₁ couts₁) selectCols computeState
    wiring.selectOK houtFresh
  rw [wiring.selectCandidate, wiring.selectRaw, hrawPreserved] at hselected

  have hrawBound : regValue X rawState < 2 ^ subCols.length := by
    simpa [X] using regValue_lt_two_pow X rawState
  have hcandidateBound : regValue Y computeState < 2 ^ subCols.length := by
    have h := regValue_lt_two_pow Y computeState
    simpa [Y, wiring.width] using h
  have hselectedValue := modSub_select_eq modulus (2 ^ subCols.length)
    (regValue A st) (regValue B st) (regValue X rawState) (regValue Y computeState)
    (computeState (carryOut cin₁ couts₁)) (computeState (carryOut cin₂ couts₂))
    wiring.modulusPos wiring.fit
    (by simpa [A] using ha) (by simpa [B] using hb)
    hrawBound hcandidateBound hrawEq hcandidateEq
  have hforward : regValue O
      (run (selectPoint (carryOut cin₁ couts₁) selectCols) computeState) =
      (regValue A st + modulus - regValue B st) % modulus :=
    hselected.trans hselectedValue

  rw [modSub, run_append, run_append]
  calc
    regValue O
        (run compute.reverse
          (run (selectPoint (carryOut cin₁ couts₁) selectCols) computeState)) =
      regValue O (run (selectPoint (carryOut cin₁ couts₁) selectCols) computeState) := by
        apply regValue_congr
        intro w hwO
        exact (usesOnly_reverse hactiveUses).preservesOutside _ w (houtActive w hwO)
    _ = _ := by simpa [O, A, B] using hforward

/-- A valid declared layout places every fresh selector output outside the full forward
computation footprint. -/
theorem modSub_output_not_active
    (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (hvalid : (modSubLayout subCols addCols selectCols cin₁ couts₁ cin₂ couts₂).Valid) :
    ∀ w ∈ selectCols.map (fun c => c.2.2),
      w ∉ modSubActiveWires subCols addCols cin₁ couts₁ cin₂ couts₂ := by
  let A := subCols.map (fun c => c.1)
  let B := subCols.map (fun c => c.2.1)
  let O := selectCols.map (fun c => c.2.2)
  let X := subCols.map (fun c => c.2.2)
  let K := addCols.map (fun c => c.2.1)
  let Y := addCols.map (fun c => c.2.2)
  have hnodup :
      (A ++ (B ++ (O ++ (X ++ (K ++ (Y ++
        ([cin₁] ++ (couts₁ ++ ([cin₂] ++ couts₂))))))))).Nodup := by
    simpa [A, B, O, X, K, Y, modSubLayout, RegisterLayout.allWires,
      List.append_assoc] using hvalid.2.2
  rcases List.nodup_append.mp hnodup with ⟨_, htailA, hAcrossA⟩
  rcases List.nodup_append.mp htailA with ⟨_, htailB, hAcrossB⟩
  rcases List.nodup_append.mp htailB with ⟨_, _, hAcrossO⟩
  intro w hwO hw
  simp only [modSubActiveWires, List.mem_append, List.mem_singleton] at hw
  rcases hw with hwA | hwB | hwX | hwK | hwY | hwCin₁ | hwC₁ | hwCin₂ | hwC₂
  · exact hAcrossA w hwA w (by simp [O, hwO]) rfl
  · exact hAcrossB w hwB w (by simp [O, hwO]) rfl
  · exact hAcrossO w (by simpa [O] using hwO) w (by
      simp only [List.mem_append]
      exact Or.inl hwX) rfl
  · exact hAcrossO w (by simpa [O] using hwO) w (by
      simp only [List.mem_append]
      exact Or.inr (Or.inl hwK)) rfl
  · exact hAcrossO w (by simpa [O] using hwO) w (by
      simp only [List.mem_append]
      exact Or.inr (Or.inr (Or.inl hwY))) rfl
  · exact hAcrossO w (by simpa [O] using hwO) cin₁ (by simp) hwCin₁
  · exact hAcrossO w (by simpa [O] using hwO) w (by simp [hwC₁]) rfl
  · exact hAcrossO w (by simpa [O] using hwO) cin₂ (by simp) hwCin₂
  · exact hAcrossO w (by simpa [O] using hwO) w (by simp [hwC₂]) rfl

/-- Bennett cleanup: every non-output wire returns exactly to its input value. -/
theorem modSub_clean
    (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (wiring : ModSubWiring subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus)
    (st : BasisState)
    (hvalid : (modSubLayout subCols addCols selectCols cin₁ couts₁ cin₂ couts₂).Valid) :
    ∀ w, w ∉ selectCols.map (fun c => c.2.2) →
      run (modSub subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) st w = st w := by
  let active := modSubActiveWires subCols addCols cin₁ couts₁ cin₂ couts₂
  let compute := modSubCompute subCols addCols cin₁ couts₁ cin₂ couts₂ modulus
  let selector := selectPoint (carryOut cin₁ couts₁) selectCols
  have hcomputeUses : CircuitUsesOnly active compute := by
    simpa [active, compute] using
      modSubCompute_usesOnly subCols addCols cin₁ couts₁ cin₂ couts₂ modulus wiring.addA
  have hcomputeHP : HPFree compute := by
    simpa [compute] using
      modSubCompute_HPFree subCols addCols cin₁ couts₁ cin₂ couts₂ modulus
  have hcomputeWF : CircuitWellFormed compute := by
    simpa [compute] using modSubCompute_wellFormed
      subCols addCols cin₁ couts₁ cin₂ couts₂ modulus wiring.subOK wiring.addOK
  have houtActive : ∀ w ∈ selectCols.map (fun c => c.2.2), w ∉ active := by
    simpa [active] using
      modSub_output_not_active subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ hvalid
  have hactiveOut : ∀ w ∈ active, w ∉ selectCols.map (fun c => c.2.2) := by
    intro w hwActive hwOut
    exact houtActive w hwOut hwActive
  have hselectorAgree : ∀ w ∈ active,
      run selector (run compute st) w = run compute st w := by
    intro w hw
    exact selectPoint_other (carryOut cin₁ couts₁) w selectCols _ wiring.selectOK
      (hactiveOut w hw)
  have hreverseAgree : ∀ w ∈ active,
      run compute.reverse (run selector (run compute st)) w =
        run compute.reverse (run compute st) w :=
    Arithmetic.CircuitUsesOnly.run_congr
      (Arithmetic.usesOnly_reverse hcomputeUses) hselectorAgree
  have hcancel : run compute.reverse (run compute st) = st :=
    Arithmetic.run_reverse_cancel compute st hcomputeHP hcomputeWF
  intro w hwOut
  change run (compute ++ selector ++ compute.reverse) st w = st w
  rw [run_append, run_append]
  by_cases hwActive : w ∈ active
  · calc
      run compute.reverse (run selector (run compute st)) w =
          run compute.reverse (run compute st) w := hreverseAgree w hwActive
      _ = st w := congrFun hcancel w
  · calc
      run compute.reverse (run selector (run compute st)) w =
          run selector (run compute st) w :=
        (Arithmetic.usesOnly_reverse hcomputeUses).preservesOutside _ w hwActive
      _ = run compute st w := by
        change run (selectPoint (carryOut cin₁ couts₁) selectCols) (run compute st) w =
          run compute st w
        exact selectPoint_other (carryOut cin₁ couts₁) w selectCols _ wiring.selectOK hwOut
      _ = st w := hcomputeUses.preservesOutside st w hwActive

/-- **Clean modular-subtraction contract.** Correctness, exact cleanup, declared-wire locality,
exact cost, H/P-freedom, and well-formedness all refer to the same `modSub` circuit term. -/
theorem modSub_contract
    (subCols addCols selectCols : List (Wire × Wire × Wire))
    (cin₁ : Wire) (couts₁ : List Wire) (cin₂ : Wire) (couts₂ : List Wire)
    (modulus : Nat)
    (wiring : ModSubWiring subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus) :
    ModSubContract
      (modSub subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus)
      (modSubLayout subCols addCols selectCols cin₁ couts₁ cin₂ couts₂)
      modulus (91 * subCols.length) := by
  let layout := modSubLayout subCols addCols selectCols cin₁ couts₁ cin₂ couts₂
  let program := modSub subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus
  refine {
    correct := ?_
    usesOnly := ?_
    counted := ?_
    hpFree := ?_
    wellFormed := ?_
  }
  · intro st hvalid ha hb hclean
    dsimp only
    have hresult := modSub_correct subCols addCols selectCols cin₁ couts₁ cin₂ couts₂
      modulus wiring st hvalid ha hb hclean
    have hrestore := modSub_clean subCols addCols selectCols cin₁ couts₁ cin₂ couts₂
      modulus wiring st hvalid
    have hworkClean : Clean layout.work st := by
      intro w hw
      exact hclean w (List.mem_append_right _ hw)
    have hnodup :
        (layout.lhs ++ (layout.rhs ++ (layout.out ++ layout.work))).Nodup := by
      simpa [RegisterLayout.allWires, List.append_assoc] using hvalid.2.2
    have hlhsOut : ∀ w ∈ layout.lhs, w ∉ layout.out := by
      intro w hw hwo
      exact (List.nodup_append.mp hnodup).2.2 w hw w (by simp [hwo]) rfl
    have htailNodup : (layout.rhs ++ (layout.out ++ layout.work)).Nodup :=
      (List.nodup_append.mp hnodup).2.1
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
  · simpa [layout, RegisterLayout.allWires, modSubLayout, modSubAllWires,
      List.append_assoc] using
      modSub_usesOnly subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus
        wiring.addA wiring.selectCandidate wiring.selectRaw
  · exact modSub_tCount subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus
      wiring.subLen wiring.addLen wiring.width wiring.selectLen
  · exact modSub_HPFree subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus
  · intro _
    exact modSub_wellFormed subCols addCols selectCols cin₁ couts₁ cin₂ couts₂ modulus
      wiring.subOK wiring.addOK wiring.selectOK

end ShorECDLP
