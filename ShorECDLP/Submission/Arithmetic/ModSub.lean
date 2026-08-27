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

For canonical inputs and `modulus < 2^width`, `modSub_program_correct` proves directly

```text
value(out, after) = (value(a) + modulus - value(b)) % modulus
tCount(modSub) = 91 * width
```

along with declared-wire locality, H/P-freedom, physical well-formedness, input preservation,
and exact work cleanup for the same circuit term. `modSub_tCount` is its direct exact cost theorem;
`modSub_contract` packages the complete compositional interface.
-/

namespace ShorECDLP

open Classical
open Arithmetic
open scoped ArithmeticNotation

/-! ## Bitwise complement and the raw two's-complement subtraction -/

/-- Flip every bit of an LSB-first register. -/
def complementReg : List Wire → Circuit
  | [] => circuit! {}
  | w :: ws => circuit! {
      gate! Gate.X w;
      complementReg ws
    }

/-- Prepare two's-complement subtraction by complementing `rhs` and setting the carry-in. -/
def subPrepare (rhs : List Wire) (cin : Wire) : Circuit :=
  circuit! {
    complementReg rhs;
    gate! Gate.X cin
  }

/-- Compute the width-bounded raw difference and a no-borrow carry, restoring `rhs` and `cin`. -/
def subRaw (lhs rhs raw : List Wire) (cin : Wire) (couts : List Wire) : Circuit :=
  let prepare := subPrepare rhs cin
  circuit! {
    prepare;
    ripple lhs rhs raw cin couts;
    prepare.reverse
  }

/-- Complete syntactic footprint of raw subtraction. -/
def subRawFootprint (lhs rhs raw : List Wire) (cin : Wire)
    (couts : List Wire) : List Wire :=
  lhs ++ (rhs ++ (raw ++ ([cin] ++ couts)))

/-- Forward computation of the raw difference and the `+ modulus` underflow candidate. -/
def modSubCompute (lhs rhs raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat) : Circuit :=
  circuit! {
    subRaw lhs rhs raw cinSub coutsSub;
    addConst raw constReg candidate cinAdd coutsAdd modulus
  }

/-- Clean modular subtractor: compute, select by no-borrow, then Bennett-uncompute. -/
def modSub (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat) : Circuit :=
  let compute := modSubCompute lhs rhs raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd modulus
  circuit! {
    compute;
    selectPoint (carryOut cinSub coutsSub) candidate raw out;
    compute.reverse
  }

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

theorem subPrepare_usesOnly (rhs : List Wire) (cin : Wire) :
    CircuitUsesOnly (rhs ++ [cin]) (subPrepare rhs cin) := by
  rw [subPrepare]
  apply usesOnly_append
  · exact usesOnly_mono (complementReg_usesOnly _) (fun w hw => List.mem_append_left _ hw)
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp [Gate.UsesOnly]

theorem subRaw_usesOnly (lhs rhs raw : List Wire) (cin : Wire) (couts : List Wire) :
    CircuitUsesOnly (subRawFootprint lhs rhs raw cin couts)
      (subRaw lhs rhs raw cin couts) := by
  have hprep : CircuitUsesOnly (subRawFootprint lhs rhs raw cin couts)
      (subPrepare rhs cin) :=
    usesOnly_mono (subPrepare_usesOnly rhs cin) (by
      intro w hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · simp [subRawFootprint, hw]
      · subst w
        simp [subRawFootprint])
  have hripple : CircuitUsesOnly (subRawFootprint lhs rhs raw cin couts)
      (ripple lhs rhs raw cin couts) :=
    usesOnly_mono (ModAddSupport.ripple_usesOnly lhs rhs raw cin couts) (by
      intro w hw
      simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hw
      · simp [subRawFootprint]
      · rcases hw with ((hwC | hwA) | hwB) | hwRaw
        · simp [subRawFootprint, hwC]
        · simp [subRawFootprint, hwA]
        · simp [subRawFootprint, hwB]
        · simp [subRawFootprint, hwRaw])
  rw [subRaw]
  exact usesOnly_append (usesOnly_append hprep hripple) (usesOnly_reverse hprep)

theorem subRaw_tCount (lhs rhs raw : List Wire) (cin : Wire) (couts : List Wire)
    (hrhs : rhs.length = lhs.length) (hraw : raw.length = lhs.length)
    (hcouts : couts.length = lhs.length) :
    tCount (subRaw lhs rhs raw cin couts) = 21 * lhs.length := by
  rw [subRaw, tCount_append, tCount_append, tCount_reverse,
    ripple_tCount lhs rhs raw cin couts hrhs hraw hcouts]
  simp [subPrepare, tCount_append, tCost]

theorem subPrepare_HPFree (rhs : List Wire) (cin : Wire) :
    HPFree (subPrepare rhs cin) := by
  simp [subPrepare, hpFree_append]

theorem subPrepare_wellFormed (rhs : List Wire) (cin : Wire) :
    CircuitWellFormed (subPrepare rhs cin) := by
  simp [subPrepare, circuitWellFormed_append, complementReg_wellFormed, Gate.WellFormed]

theorem subRaw_HPFree (lhs rhs raw : List Wire) (cin : Wire) (couts : List Wire) :
    HPFree (subRaw lhs rhs raw cin couts) := by
  rw [subRaw, hpFree_append, hpFree_append]
  exact ⟨⟨subPrepare_HPFree rhs cin, ripple_HPFree lhs rhs raw cin couts⟩,
    Arithmetic.hpFree_reverse (subPrepare_HPFree rhs cin)⟩

theorem subRaw_wellFormed (lhs rhs raw : List Wire) (cin : Wire) (couts : List Wire)
    (h : wiresOK lhs rhs raw cin couts) :
    CircuitWellFormed (subRaw lhs rhs raw cin couts) := by
  rw [subRaw, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨subPrepare_wellFormed rhs cin, ripple_wellFormed lhs rhs raw cin couts h⟩,
    Arithmetic.wellFormed_reverse (subPrepare_wellFormed rhs cin)⟩

/-- Raw two's-complement subtraction identity.  The final carry is the no-borrow flag. -/
theorem subRaw_correct
    (lhs rhs raw : List Wire) (cin : Wire) (couts : List Wire) (st : BasisState)
    (hrhsLen : rhs.length = lhs.length)
    (hwok : wiresOK lhs rhs raw cin couts)
    (hrhsNodup : rhs.Nodup)
    (hcinRhs : cin ∉ rhs)
    (hLhsOutside : ∀ w ∈ lhs, w ∉ rhs ++ [cin])
    (hRawOutside : ∀ w ∈ raw, w ∉ rhs ++ [cin])
    (hcoutsOutside : ∀ w ∈ couts,
      w ∉ rhs ++ [cin])
    (hcarryOutside : carryOut cin couts ∉ rhs ++ [cin])
    (hcarryFresh : ∀ w ∈ couts, st w = false)
    (hrawFresh : ∀ w ∈ raw, st w = false)
    (hcinFresh : st cin = false) :
    regValue raw (run (subRaw lhs rhs raw cin couts) st) +
        2 ^ lhs.length * bit (run (subRaw lhs rhs raw cin couts) st) (carryOut cin couts) =
      regValue lhs st + 2 ^ lhs.length - regValue rhs st := by
  let prepare := subPrepare rhs cin
  let prepared := run prepare st
  have hprepareUses : CircuitUsesOnly (rhs ++ [cin]) prepare := by
    simpa [prepare] using subPrepare_usesOnly rhs cin
  have hpreparedRhs : regValue rhs prepared = 2 ^ lhs.length - 1 - regValue rhs st := by
    change regValue rhs (run (subPrepare rhs cin) st) = _
    rw [subPrepare, run_append]
    calc
      regValue rhs (run [Gate.X cin] (run (complementReg rhs) st)) =
          regValue rhs (run (complementReg rhs) st) := by
        apply regValue_congr
        intro w hw
        have hwcin : w ≠ cin := fun e => hcinRhs (e ▸ hw)
        simp [run_cons, run_nil, applyGate, upd, hwcin]
      _ = 2 ^ rhs.length - 1 - regValue rhs st :=
        regValue_complementReg rhs st hrhsNodup
      _ = _ := by rw [hrhsLen]
  have hpreparedLhs : regValue lhs prepared = regValue lhs st := by
    apply regValue_congr
    intro w hw
    exact hprepareUses.preservesOutside st w (hLhsOutside w hw)
  have hpreparedCin : prepared cin = true := by
    change run (subPrepare rhs cin) st cin = true
    rw [subPrepare, run_append]
    simp only [run_cons, run_nil, applyGate, upd_same]
    rw [complementReg_other cin rhs st hcinRhs, hcinFresh]
    rfl
  have hpreparedCarry : ∀ w ∈ couts, prepared w = false := by
    intro w hw
    exact Eq.trans (hprepareUses.preservesOutside st w (hcoutsOutside w hw))
      (hcarryFresh w hw)
  have hpreparedRaw : ∀ w ∈ raw, prepared w = false := by
    intro w hw
    exact Eq.trans (hprepareUses.preservesOutside st w (hRawOutside w hw))
      (hrawFresh w hw)
  have hripple := ripple_correct lhs rhs raw cin couts prepared hwok
    hpreparedCarry hpreparedRaw
  rw [hpreparedLhs, hpreparedRhs] at hripple
  have hcinBit : bit prepared cin = 1 := by simp [bit, hpreparedCin]
  rw [hcinBit] at hripple
  have hRhsBound : regValue rhs st < 2 ^ lhs.length := by
    rw [← hrhsLen]
    exact regValue_lt_two_pow rhs st
  have hripple' :
      regValue raw (run (ripple lhs rhs raw cin couts) prepared) +
          2 ^ lhs.length * bit (run (ripple lhs rhs raw cin couts) prepared)
            (carryOut cin couts) =
        regValue lhs st + 2 ^ lhs.length - regValue rhs st := by
    let a := regValue lhs st
    let b := regValue rhs st
    let M := 2 ^ lhs.length
    have hbM : b < M := by simpa [b, M] using hRhsBound
    have hminus : M - 1 - b + 1 = M - b := by omega
    have haddSub : a + (M - b) = a + M - b := by omega
    calc
      regValue raw (run (ripple lhs rhs raw cin couts) prepared) +
          M * bit (run (ripple lhs rhs raw cin couts) prepared) (carryOut cin couts) =
        a + (M - 1 - b) + 1 := by simpa [a, b, M] using hripple
      _ = a + ((M - 1 - b) + 1) := by omega
      _ = a + (M - b) := by rw [hminus]
      _ = a + M - b := haddSub
  have hreverseUses : CircuitUsesOnly (rhs ++ [cin]) prepare.reverse :=
    usesOnly_reverse hprepareUses
  have hrawKeep : regValue raw
      (run prepare.reverse (run (ripple lhs rhs raw cin couts) prepared)) =
      regValue raw (run (ripple lhs rhs raw cin couts) prepared) := by
    apply regValue_congr
    intro w hw
    exact hreverseUses.preservesOutside _ w (hRawOutside w hw)
  have hcarryKeep : bit
      (run prepare.reverse (run (ripple lhs rhs raw cin couts) prepared))
        (carryOut cin couts) =
      bit (run (ripple lhs rhs raw cin couts) prepared) (carryOut cin couts) := by
    rw [bit, bit, hreverseUses.preservesOutside _ _ hcarryOutside]
  rw [subRaw, run_append, run_append, hrawKeep, hcarryKeep]
  simpa [prepare, prepared] using hripple'

/-! ## Modular correction, selection, and exact resource packages -/

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

theorem modSubCompute_tCount (lhs rhs raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat)
    (hrhs : rhs.length = lhs.length) (hraw : raw.length = lhs.length)
    (hsub : coutsSub.length = lhs.length)
    (hconst : constReg.length = raw.length) (hcandidate : candidate.length = raw.length)
    (hadd : coutsAdd.length = raw.length) :
    tCount (modSubCompute lhs rhs raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus) = 42 * lhs.length := by
  rw [modSubCompute, tCount_append,
    subRaw_tCount lhs rhs raw cinSub coutsSub hrhs hraw hsub,
    addConst_tCount raw constReg candidate cinAdd coutsAdd modulus hconst hcandidate hadd]
  omega

theorem modSub_tCount (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat)
    (hrhs : rhs.length = lhs.length) (hraw : raw.length = lhs.length)
    (hsub : coutsSub.length = lhs.length)
    (hconst : constReg.length = raw.length) (hcandidate : candidate.length = raw.length)
    (hadd : coutsAdd.length = raw.length) (hout : out.length = lhs.length) :
    tCount (modSub lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus) = 91 * lhs.length := by
  have hcandidateOut : candidate.length = out.length := by omega
  rw [modSub, tCount_append, tCount_append, tCount_reverse,
    modSubCompute_tCount lhs rhs raw constReg candidate cinSub coutsSub cinAdd coutsAdd
      modulus hrhs hraw hsub hconst hcandidate hadd,
    selectPoint_tCount (carryOut cinSub coutsSub) candidate raw out
      hcandidate hcandidateOut]
  omega

theorem modSubCompute_HPFree (lhs rhs raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat) :
    HPFree (modSubCompute lhs rhs raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus) := by
  rw [modSubCompute, hpFree_append]
  exact ⟨subRaw_HPFree lhs rhs raw cinSub coutsSub,
    addConst_HPFree raw constReg candidate cinAdd coutsAdd modulus⟩

theorem modSubCompute_wellFormed (lhs rhs raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat) (hsub : wiresOK lhs rhs raw cinSub coutsSub)
    (hadd : wiresOK raw constReg candidate cinAdd coutsAdd) :
    CircuitWellFormed (modSubCompute lhs rhs raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus) := by
  rw [modSubCompute, circuitWellFormed_append]
  exact ⟨subRaw_wellFormed lhs rhs raw cinSub coutsSub hsub,
    addConst_wellFormed raw constReg candidate cinAdd coutsAdd modulus hadd⟩

theorem modSub_HPFree (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat) :
    HPFree (modSub lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus) := by
  rw [modSub, hpFree_append, hpFree_append]
  have hc := modSubCompute_HPFree lhs rhs raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd modulus
  exact ⟨⟨hc, selectPoint_HPFree _ _ _ _⟩, Arithmetic.hpFree_reverse hc⟩

theorem modSub_wellFormed (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat) (hsub : wiresOK lhs rhs raw cinSub coutsSub)
    (hadd : wiresOK raw constReg candidate cinAdd coutsAdd)
    (hselect : selectOK (carryOut cinSub coutsSub) candidate raw out) :
    CircuitWellFormed (modSub lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus) := by
  rw [modSub, circuitWellFormed_append, circuitWellFormed_append]
  have hc := modSubCompute_wellFormed lhs rhs raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd modulus hsub hadd
  exact ⟨⟨hc, selectPoint_wellFormed _ _ _ _ hselect⟩, Arithmetic.wellFormed_reverse hc⟩

/-! ## Declared layout, locality, and clean contract -/

/-- Public `A`, public `B`, public output `O`, then raw difference `X`, constant scratch `K`,
correction candidate `Y`, and both carry banks/carry-ins. -/
def modSubLayout
    (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire) :
    RegisterLayout where
  lhs := lhs
  rhs := rhs
  out := out
  work := raw ++ (constReg ++ (candidate ++
    ([cinSub] ++ (coutsSub ++ ([cinAdd] ++ coutsAdd)))))

/-- Every wire used by the forward computation, excluding the fresh selector output. -/
def modSubActiveWires
    (lhs rhs raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire) : List Wire :=
  lhs ++ (rhs ++ (raw ++ (constReg ++ (candidate ++
    ([cinSub] ++ (coutsSub ++ ([cinAdd] ++ coutsAdd)))))))

/-- Public inputs/output and the complete owned workspace. -/
def modSubAllWires
    (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire) : List Wire :=
  lhs ++ (rhs ++ (out ++ (raw ++ (constReg ++ (candidate ++
    ([cinSub] ++ (coutsSub ++ ([cinAdd] ++ coutsAdd))))))))

/-- Genuine wiring obligations for one modular-subtraction instance.  Cross-register freshness is
derived from `modSubLayout.Valid` inside the contract rather than duplicated here. -/
structure ModSubWiring
    (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat) : Prop where
  rhsLen : rhs.length = lhs.length
  rawLen : raw.length = lhs.length
  subLen : coutsSub.length = lhs.length
  constLen : constReg.length = raw.length
  candidateLen : candidate.length = raw.length
  addLen : coutsAdd.length = raw.length
  outLen : out.length = lhs.length
  subOK : wiresOK lhs rhs raw cinSub coutsSub
  addOK : wiresOK raw constReg candidate cinAdd coutsAdd
  selectOK : ShorECDLP.selectOK (carryOut cinSub coutsSub) candidate raw out
  modulusPos : 0 < modulus
  fit : modulus < 2 ^ lhs.length

/-- The forward computation stays within the active (non-output) registers. -/
theorem modSubCompute_usesOnly
    (lhs rhs raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat) :
    CircuitUsesOnly
      (modSubActiveWires lhs rhs raw constReg candidate cinSub coutsSub cinAdd coutsAdd)
      (modSubCompute lhs rhs raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus) := by
  let active := modSubActiveWires lhs rhs raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd
  have hsub : ∀ w ∈ subRawFootprint lhs rhs raw cinSub coutsSub, w ∈ active := by
    intro w hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwRaw | hwCin | hwCouts
    · simp [active, modSubActiveWires, hwA]
    · simp [active, modSubActiveWires, hwB]
    · simp [active, modSubActiveWires, hwRaw]
    · simp [active, modSubActiveWires, hwCin]
    · simp [active, modSubActiveWires, hwCouts]
  have hadd : ∀ w ∈ ModAddSupport.rippleFootprint raw constReg candidate cinAdd coutsAdd,
      w ∈ active := by
    intro w hw
    simp only [ModAddSupport.rippleFootprint, List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | ((hwCouts | hwRaw) | hwConst) | hwCandidate
    · simp [active, modSubActiveWires]
    · simp [active, modSubActiveWires, hwCouts]
    · simp [active, modSubActiveWires, hwRaw]
    · simp [active, modSubActiveWires, hwConst]
    · simp [active, modSubActiveWires, hwCandidate]
  rw [modSubCompute]
  exact usesOnly_append
    (usesOnly_mono (subRaw_usesOnly lhs rhs raw cinSub coutsSub) hsub)
    (usesOnly_mono
      (ModAddSupport.addConst_usesOnly raw constReg candidate cinAdd coutsAdd modulus) hadd)

/-- Every control and target of `modSub` belongs to its declared public/work layout. -/
theorem modSub_usesOnly
    (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat) :
    CircuitUsesOnly
      (modSubAllWires lhs rhs out raw constReg candidate cinSub coutsSub cinAdd coutsAdd)
      (modSub lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus) := by
  let active := modSubActiveWires lhs rhs raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd
  let all := modSubAllWires lhs rhs out raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd
  have hactive : ∀ w ∈ active, w ∈ all := by
    intro w hw
    simp only [active, modSubActiveWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwLhs | hwRhs | hwRaw | hwConst | hwCandidate |
        hwCinSub | hwCoutsSub | hwCinAdd | hwCoutsAdd
    · simp [all, modSubAllWires, hwLhs]
    · simp [all, modSubAllWires, hwRhs]
    · simp [all, modSubAllWires, hwRaw]
    · simp [all, modSubAllWires, hwConst]
    · simp [all, modSubAllWires, hwCandidate]
    · simp [all, modSubAllWires, hwCinSub]
    · simp [all, modSubAllWires, hwCoutsSub]
    · simp [all, modSubAllWires, hwCinAdd]
    · simp [all, modSubAllWires, hwCoutsAdd]
  have hcompute : CircuitUsesOnly all
      (modSubCompute lhs rhs raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus) :=
    usesOnly_mono
      (modSubCompute_usesOnly lhs rhs raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus)
      hactive
  have hselect : ∀ w ∈ selectFootprint (carryOut cinSub coutsSub) candidate raw out,
      w ∈ all := by
    intro w hw
    simp only [selectFootprint, List.mem_cons, List.mem_append] at hw
    rcases hw with ((hwFlag | hwCandidate) | hwRaw) | hwOut
    · subst w
      by_cases hcouts : coutsSub = []
      · simp [hcouts, carryOut, all, modSubAllWires]
      · have hcarry : carryOut cinSub coutsSub ∈ coutsSub :=
          carryOut_mem_couts cinSub coutsSub hcouts
        exact hactive _ (by simp [active, modSubActiveWires, hcarry])
    · simp [all, modSubAllWires, hwCandidate]
    · simp [all, modSubAllWires, hwRaw]
    · simp [all, modSubAllWires, hwOut]
  rw [modSub]
  exact usesOnly_append
    (usesOnly_append hcompute
      (usesOnly_mono
        (selectPoint_usesOnly (carryOut cinSub coutsSub) candidate raw out) hselect))
    (usesOnly_reverse hcompute)

/-- Functional correctness of the exact clean modular-subtraction circuit term. -/
theorem modSub_correct
    (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat)
    (wiring : ModSubWiring lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus)
    (st : BasisState)
    (hvalid : (modSubLayout lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd).Valid)
    (ha : st⟦ᵣlhs⟧ < modulus)
    (hb : st⟦ᵣrhs⟧ < modulus)
    (hclean : clean(
      ((modSubLayout lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd).out ++
       (modSubLayout lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd).work), st)) :
    (⟪modSub lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus⟫ st)⟦ᵣout⟧ =
      (st⟦ᵣlhs⟧ + modulus - st⟦ᵣrhs⟧) % modulus := by
  let layout := modSubLayout lhs rhs out raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd
  let A := lhs
  let B := rhs
  let O := out
  let X := raw
  let K := constReg
  let Y := candidate
  let rawState := run (subRaw lhs rhs raw cinSub coutsSub) st
  let compute := modSubCompute lhs rhs raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd modulus
  let computeState := run compute st

  have hnodup :
      (A ++ (B ++ (O ++ (X ++ (K ++ (Y ++
        ([cinSub] ++ (coutsSub ++ ([cinAdd] ++ coutsAdd))))))))).Nodup := by
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
  have hwidthPos : 0 < lhs.length := by
    rcases Nat.eq_zero_or_pos lhs.length with hz | hpos
    · have hfit := wiring.fit
      simp [hz] at hfit
      omega
    · exact hpos
  have hcoutsSubNonempty : coutsSub ≠ [] := by
    intro hz
    have hlen := wiring.subLen
    simp [hz] at hlen
    omega
  have hflagMem : carryOut cinSub coutsSub ∈ coutsSub :=
    carryOut_mem_couts cinSub coutsSub hcoutsSubNonempty

  have hcinSubB : cinSub ∉ B := by
    intro hwB
    exact hAcrossB cinSub hwB cinSub (by simp) rfl
  have hAOutside : ∀ w ∈ A, w ∉ B ++ [cinSub] := by
    intro w hwA hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hwB | hwCin
    · exact hAcrossA w hwA w (by simp [hwB]) rfl
    · exact hAcrossA w hwA cinSub (by simp) hwCin
  have hXOutside : ∀ w ∈ X, w ∉ B ++ [cinSub] := by
    intro w hwX hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hwB | hwCin
    · exact hAcrossB w hwB w (by simp [hwX]) rfl
    · exact hAcrossX w hwX cinSub (by simp) hwCin
  have hcoutsSubOutside : ∀ w ∈ coutsSub, w ∉ B ++ [cinSub] := by
    intro w hwC hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hwB | hwCin
    · exact hAcrossB w hwB w (by simp [hwC]) rfl
    · exact hAcrossCin₁ cinSub (by simp) w (by simp [hwC]) hwCin.symm
  have hflagOutside : carryOut cinSub coutsSub ∉ B ++ [cinSub] :=
    hcoutsSubOutside _ hflagMem

  have hsubCarryFresh : ∀ w ∈ coutsSub, st w = false := by
    intro w hw
    apply hworkClean w
    simp [layout, modSubLayout, hw]
  have hsubRawFresh : ∀ w ∈ raw, st w = false := by
    intro w hw
    apply hworkClean w
    simp [layout, modSubLayout, hw]
  have hcinSubFresh : st cinSub = false := by
    apply hworkClean cinSub
    simp [layout, modSubLayout]
  have hraw := subRaw_correct lhs rhs raw cinSub coutsSub st
    wiring.rhsLen wiring.subOK (by simpa [B] using hBNodup)
    (by simpa [B] using hcinSubB)
    (by simpa [A, B] using hAOutside)
    (by simpa [X, B] using hXOutside)
    (by simpa [B] using hcoutsSubOutside)
    (by simpa [B] using hflagOutside)
    hsubCarryFresh hsubRawFresh hcinSubFresh

  have hnotSubK : ∀ w ∈ K, w ∉ subRawFootprint lhs rhs raw cinSub coutsSub := by
    intro w hwK hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwCin | hwC
    · exact hAcrossA w hwA w (by simp [hwK]) rfl
    · exact hAcrossB w hwB w (by simp [hwK]) rfl
    · exact hAcrossX w hwX w (by simp [hwK]) rfl
    · exact hAcrossK w hwK cinSub (by simp) hwCin
    · exact hAcrossK w hwK w (by simp [hwC]) rfl
  have hnotSubY : ∀ w ∈ Y, w ∉ subRawFootprint lhs rhs raw cinSub coutsSub := by
    intro w hwY hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwCin | hwC
    · exact hAcrossA w hwA w (by simp [hwY]) rfl
    · exact hAcrossB w hwB w (by simp [hwY]) rfl
    · exact hAcrossX w hwX w (by simp [hwY]) rfl
    · exact hAcrossY w hwY cinSub (by simp) hwCin
    · exact hAcrossY w hwY w (by simp [hwC]) rfl
  have hnotSubCinAdd : cinAdd ∉ subRawFootprint lhs rhs raw cinSub coutsSub := by
    intro hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwCin | hwC
    · exact hAcrossA cinAdd hwA cinAdd (by simp) rfl
    · exact hAcrossB cinAdd hwB cinAdd (by simp) rfl
    · exact hAcrossX cinAdd hwX cinAdd (by simp) rfl
    · subst cinAdd
      exact hAcrossCin₁ cinSub (by simp) cinSub (by simp) rfl
    · exact hAcrossCouts₁ cinAdd hwC cinAdd (by simp) rfl
  have hnotSubCoutsAdd : ∀ w ∈ coutsAdd,
      w ∉ subRawFootprint lhs rhs raw cinSub coutsSub := by
    intro w hwC₂ hw
    simp only [subRawFootprint, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwCin | hwC₁
    · exact hAcrossA w hwA w (by simp [hwC₂]) rfl
    · exact hAcrossB w hwB w (by simp [hwC₂]) rfl
    · exact hAcrossX w hwX w (by simp [hwC₂]) rfl
    · exact hAcrossCin₁ cinSub (by simp) w (by simp [hwC₂]) hwCin.symm
    · exact hAcrossCouts₁ w hwC₁ w (by simp [hwC₂]) rfl

  have hsubUses := subRaw_usesOnly lhs rhs raw cinSub coutsSub
  have haddCarryFresh : ∀ w ∈ coutsAdd, rawState w = false := by
    intro w hw
    change run (subRaw lhs rhs raw cinSub coutsSub) st w = false
    rw [hsubUses.preservesOutside st w (hnotSubCoutsAdd w hw)]
    exact hworkClean w (by simp [layout, modSubLayout, hw])
  have haddSumFresh : ∀ w ∈ candidate, rawState w = false := by
    intro w hwY
    change run (subRaw lhs rhs raw cinSub coutsSub) st w = false
    rw [hsubUses.preservesOutside st w (hnotSubY w (by simpa [Y] using hwY))]
    exact hworkClean w (by simp [layout, modSubLayout, hwY])
  have haddConstFresh : ∀ w ∈ constReg, rawState w = false := by
    intro w hwK
    change run (subRaw lhs rhs raw cinSub coutsSub) st w = false
    rw [hsubUses.preservesOutside st w (hnotSubK w (by simpa [K] using hwK))]
    exact hworkClean w (by simp [layout, modSubLayout, hwK])
  have hcinAddFresh : rawState cinAdd = false := by
    change run (subRaw lhs rhs raw cinSub coutsSub) st cinAdd = false
    rw [hsubUses.preservesOutside st cinAdd hnotSubCinAdd]
    exact hworkClean cinAdd (by simp [layout, modSubLayout])

  have hXK : ∀ w ∈ X, w ∉ K := by
    intro w hwX hwK
    exact hAcrossX w hwX w (by simp [hwK]) rfl
  have hYK : ∀ w ∈ Y, w ∉ K := by
    intro w hwY hwK
    exact hAcrossK w hwK w (by simp [hwY]) rfl
  have hCoutsAddK : ∀ w ∈ coutsAdd, w ∉ K := by
    intro w hwC hwK
    exact hAcrossK w hwK w (by simp [hwC]) rfl
  have hCinAddK : cinAdd ∉ K := by
    intro hwK
    exact hAcrossK cinAdd hwK cinAdd (by simp) rfl
  have hconstBound : modulus < 2 ^ raw.length := by
    rw [wiring.rawLen]
    exact wiring.fit
  have hcandidate := addConst_correct raw constReg candidate cinAdd coutsAdd modulus rawState
    wiring.constLen wiring.addOK (by simpa [K] using hKNodup)
    (by simpa [X, K] using hXK)
    (by simpa [Y, K] using hYK)
    (by simpa [K] using hCoutsAddK)
    (by simpa [K] using hCinAddK)
    haddCarryFresh haddSumFresh haddConstFresh hcinAddFresh hconstBound

  have hcomputeState : computeState =
      run (addConst raw constReg candidate cinAdd coutsAdd modulus) rawState := by
    simp [computeState, compute, modSubCompute, rawState, run_append]
  have hXY : ∀ w ∈ X, w ∉ Y := by
    intro w hwX hwY
    exact hAcrossX w hwX w (by simp [hwY]) rfl
  have hXCoutsAdd : ∀ w ∈ X, w ∉ coutsAdd := by
    intro w hwX hwC
    exact hAcrossX w hwX w (by simp [hwC]) rfl
  have hrawPreserved : regValue X computeState = regValue X rawState := by
    rw [hcomputeState]
    apply regValue_congr
    intro w hwX
    exact addConst_other w raw constReg candidate cinAdd coutsAdd modulus rawState
      (by simpa [K] using hXK w hwX)
      (fun x hx he => by
        subst x
        exact hXY w hwX (by simpa [Y] using hx))
      (fun x hx he => by
        subst x
        exact hXCoutsAdd w hwX hx)
  have hFlagK : carryOut cinSub coutsSub ∉ K := by
    intro hwK
    exact hAcrossK _ hwK _ (by simp [hflagMem]) rfl
  have hFlagY : ∀ w ∈ candidate, carryOut cinSub coutsSub ≠ w := by
    intro w hwY he
    exact hAcrossY w (by simpa [Y] using hwY) (carryOut cinSub coutsSub)
      (by simp [hflagMem]) he.symm
  have hFlagCoutsAdd : ∀ w ∈ coutsAdd, carryOut cinSub coutsSub ≠ w := by
    intro w hw he
    exact hAcrossCouts₁ _ hflagMem _ (by simp [hw]) he
  have hflagPreserved : computeState (carryOut cinSub coutsSub) =
      rawState (carryOut cinSub coutsSub) := by
    rw [hcomputeState]
    exact addConst_other (carryOut cinSub coutsSub) raw constReg candidate cinAdd coutsAdd
      modulus rawState (by simpa [K] using hFlagK) hFlagY hFlagCoutsAdd

  have hcandidateEq :
      regValue Y computeState + 2 ^ lhs.length *
          (if computeState (carryOut cinAdd coutsAdd) then 1 else 0) =
        regValue X rawState + modulus := by
    rw [hcomputeState]
    have hc := hcandidate
    simpa [Y, X, bit, wiring.rawLen] using hc
  have hrawEq :
      regValue X rawState + 2 ^ lhs.length *
          (if computeState (carryOut cinSub coutsSub) then 1 else 0) =
        regValue A st + 2 ^ lhs.length - regValue B st := by
    rw [hflagPreserved]
    simpa [X, A, B, rawState, bit] using hraw

  have hactiveUses :=
    modSubCompute_usesOnly lhs rhs raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus
  have houtActive : ∀ w ∈ O,
      w ∉ modSubActiveWires lhs rhs raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd := by
    intro w hwO hw
    simp only [modSubActiveWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with hwA | hwB | hwX | hwK | hwY | hwCinSub | hwCSub | hwCinAdd | hwCAdd
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
    · exact hAcrossO w hwO cinSub (by simp) hwCinSub
    · exact hAcrossO w hwO w (by simp [hwCSub]) rfl
    · exact hAcrossO w hwO cinAdd (by simp) hwCinAdd
    · exact hAcrossO w hwO w (by simp [hwCAdd]) rfl
  have houtFresh : ∀ w ∈ out, computeState w = false := by
    intro w hwO
    change run compute st w = false
    rw [hactiveUses.preservesOutside st w (houtActive w (by simpa [O] using hwO))]
    exact hclean w (List.mem_append_left _ (by simpa [layout, modSubLayout] using hwO))
  have hselected := selectPoint_correct (carryOut cinSub coutsSub)
    candidate raw out computeState wiring.selectOK houtFresh
  have hrawPreserved' : regValue raw computeState = regValue raw rawState := by
    simpa [X] using hrawPreserved
  rw [hrawPreserved'] at hselected

  have hrawBound : regValue X rawState < 2 ^ lhs.length := by
    simpa [X, wiring.rawLen] using regValue_lt_two_pow X rawState
  have hcandidateBound : regValue Y computeState < 2 ^ lhs.length := by
    have h := regValue_lt_two_pow Y computeState
    simpa [Y, wiring.candidateLen, wiring.rawLen] using h
  have hselectedValue := modSub_select_eq modulus (2 ^ lhs.length)
    (regValue A st) (regValue B st) (regValue X rawState) (regValue Y computeState)
    (computeState (carryOut cinSub coutsSub)) (computeState (carryOut cinAdd coutsAdd))
    wiring.modulusPos wiring.fit
    (by simpa [A] using ha) (by simpa [B] using hb)
    hrawBound hcandidateBound hrawEq hcandidateEq
  have hselected' : regValue O
      (run (selectPoint (carryOut cinSub coutsSub) candidate raw out) computeState) =
      if computeState (carryOut cinSub coutsSub) then regValue X rawState
      else regValue Y computeState := by
    simpa [O, X, Y] using hselected
  have hforward : regValue O
      (run (selectPoint (carryOut cinSub coutsSub) candidate raw out) computeState) =
      (regValue A st + modulus - regValue B st) % modulus :=
    hselected'.trans hselectedValue

  rw [modSub, run_append, run_append]
  calc
    regValue O
        (run compute.reverse
          (run (selectPoint (carryOut cinSub coutsSub) candidate raw out) computeState)) =
      regValue O
        (run (selectPoint (carryOut cinSub coutsSub) candidate raw out) computeState) := by
        apply regValue_congr
        intro w hwO
        exact (usesOnly_reverse hactiveUses).preservesOutside _ w (houtActive w hwO)
    _ = _ := by simpa [O, A, B] using hforward

/-- A valid declared layout places every fresh selector output outside the full forward
computation footprint. -/
theorem modSub_output_not_active
    (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (hvalid : (modSubLayout lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd).Valid) :
    ∀ w ∈ out,
      w ∉ modSubActiveWires lhs rhs raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd := by
  let A := lhs
  let B := rhs
  let O := out
  let X := raw
  let K := constReg
  let Y := candidate
  have hnodup :
      (A ++ (B ++ (O ++ (X ++ (K ++ (Y ++
        ([cinSub] ++ (coutsSub ++ ([cinAdd] ++ coutsAdd))))))))).Nodup := by
    simpa [A, B, O, X, K, Y, modSubLayout, RegisterLayout.allWires,
      List.append_assoc] using hvalid.2.2
  rcases List.nodup_append.mp hnodup with ⟨_, htailA, hAcrossA⟩
  rcases List.nodup_append.mp htailA with ⟨_, htailB, hAcrossB⟩
  rcases List.nodup_append.mp htailB with ⟨_, _, hAcrossO⟩
  intro w hwO hw
  simp only [modSubActiveWires, List.mem_append, List.mem_singleton] at hw
  rcases hw with hwA | hwB | hwX | hwK | hwY | hwCinSub | hwCSub | hwCinAdd | hwCAdd
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
  · exact hAcrossO w (by simpa [O] using hwO) cinSub (by simp) hwCinSub
  · exact hAcrossO w (by simpa [O] using hwO) w (by simp [hwCSub]) rfl
  · exact hAcrossO w (by simpa [O] using hwO) cinAdd (by simp) hwCinAdd
  · exact hAcrossO w (by simpa [O] using hwO) w (by simp [hwCAdd]) rfl

/-- Bennett cleanup: every non-output wire returns exactly to its input value. -/
theorem modSub_clean
    (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat)
    (wiring : ModSubWiring lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus)
    (st : BasisState)
    (hvalid : (modSubLayout lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd).Valid) :
    ∀ w, w ∉ out →
      run (modSub lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus) st w = st w := by
  let active := modSubActiveWires lhs rhs raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd
  let compute := modSubCompute lhs rhs raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd modulus
  let selector := selectPoint (carryOut cinSub coutsSub) candidate raw out
  have hcomputeUses : CircuitUsesOnly active compute := by
    simpa [active, compute] using
      modSubCompute_usesOnly lhs rhs raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus
  have hcomputeHP : HPFree compute := by
    simpa [compute] using
      modSubCompute_HPFree lhs rhs raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus
  have hcomputeWF : CircuitWellFormed compute := by
    simpa [compute] using modSubCompute_wellFormed
      lhs rhs raw constReg candidate cinSub coutsSub cinAdd coutsAdd
        modulus wiring.subOK wiring.addOK
  have houtActive : ∀ w ∈ out, w ∉ active := by
    simpa [active] using
      modSub_output_not_active lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd hvalid
  have hactiveOut : ∀ w ∈ active, w ∉ out := by
    intro w hwActive hwOut
    exact houtActive w hwOut hwActive
  have hselectorAgree : ∀ w ∈ active,
      run selector (run compute st) w = run compute st w := by
    intro w hw
    exact selectPoint_other (carryOut cinSub coutsSub) w candidate raw out _
      wiring.selectOK (hactiveOut w hw)
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
        change run (selectPoint (carryOut cinSub coutsSub) candidate raw out)
          (run compute st) w = run compute st w
        exact selectPoint_other (carryOut cinSub coutsSub) w candidate raw out _
          wiring.selectOK hwOut
      _ = st w := hcomputeUses.preservesOutside st w hwActive

/-- **Clean modular-subtraction contract.** Correctness, exact cleanup, declared-wire locality,
exact cost, H/P-freedom, and well-formedness all refer to the same `modSub` circuit term. -/
theorem modSub_contract
    (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat)
    (wiring : ModSubWiring lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus) :
    ModSubContract
      (modSub lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus)
      (modSubLayout lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd)
      modulus (91 * lhs.length) := by
  let layout := modSubLayout lhs rhs out raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd
  let program := modSub lhs rhs out raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd modulus
  refine {
    correct := ?_
    usesOnly := ?_
    counted := ?_
    hpFree := ?_
    wellFormed := ?_
  }
  · intro st hvalid ha hb hclean
    dsimp only
    have hresult := modSub_correct lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus wiring st hvalid ha hb hclean
    have hrestore := modSub_clean lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus wiring st hvalid
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
      modSub_usesOnly lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd modulus
  · exact modSub_tCount lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus wiring.rhsLen wiring.rawLen wiring.subLen
        wiring.constLen wiring.candidateLen wiring.addLen wiring.outLen
  · exact modSub_HPFree lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus
  · intro _
    exact modSub_wellFormed lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus wiring.subOK wiring.addOK wiring.selectOK

/-- Final direct correctness theorem for the exact clean modular-subtraction program.

The conclusion states input preservation, the canonical modular difference, and restored
workspace inline, so callers do not need to project the semantic field from `modSub_contract`. -/
theorem modSub_program_correct
    (lhs rhs out raw constReg candidate : List Wire)
    (cinSub : Wire) (coutsSub : List Wire) (cinAdd : Wire) (coutsAdd : List Wire)
    (modulus : Nat)
    (wiring : ModSubWiring lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus)
    (st : BasisState)
    (hvalid : (modSubLayout lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd).Valid)
    (ha : st⟦ᵣlhs⟧ < modulus)
    (hb : st⟦ᵣrhs⟧ < modulus)
    (hclean : clean(out ++ (modSubLayout lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd).work, st)) :
    let after := ⟪modSub lhs rhs out raw constReg candidate
      cinSub coutsSub cinAdd coutsAdd modulus⟫ st
    AgreesOn lhs st after ∧
      AgreesOn rhs st after ∧
      after⟦ᵣout⟧ = (st⟦ᵣlhs⟧ + modulus - st⟦ᵣrhs⟧) % modulus ∧
      clean((modSubLayout lhs rhs out raw constReg candidate
        cinSub coutsSub cinAdd coutsAdd).work, after) := by
  exact (modSub_contract lhs rhs out raw constReg candidate
    cinSub coutsSub cinAdd coutsAdd modulus wiring).correct st hvalid ha hb hclean

end ShorECDLP
