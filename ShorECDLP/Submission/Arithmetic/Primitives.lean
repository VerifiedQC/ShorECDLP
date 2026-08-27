import ShorECDLP.Submission.Arithmetic.Contracts
import ShorECDLP.Submission.Arithmetic.RippleAdder

/-!
# Reusable clean reversible-circuit primitives

This module contains the small, implementation-neutral leaves shared by the arithmetic
milestones: constant loading, reversible two-way selection, aligned register copying,
circuit-support composition, and cancellation of a well-formed H/P-free circuit by its reverse.
Keeping them here prevents the modular arithmetic layers from growing divergent local copies or
depending on a concrete higher-level arithmetic construction for a generic circuit primitive.

## Programs (syntax-sugared)

```text
loadConst(ws, c):
  for i in 0 .. ws.length - 1:
    if bit(c, i) = 1: X ws[i]

selectBit(flag, x, y; clean out):
  CX x out; CX x y; CCX flag y out; CX x y
  -- out = (flag ? y : x), while x and y are restored

selectPoint(flag, xs, ys, outs):
  for aligned (x, y, out): selectBit(flag, x, y; out)

copyReg(src; clean dst):
  for aligned (s, d): CX s d
```

The module also supplies the generic inverse program `c.reverse` for any well-formed H/P-free
circuit `c`.

## Specifications

```text
ws.Nodup, clean ws, and c < 2^|ws| -> value(ws, run(loadConst(ws,c), st)) = c
selectOK(flag, xs, ys, outs) and clean outs
  -> selectPoint stores (flag ? value(ys) : value(xs)) in outs
equal-length disjoint src/dst and clean dst -> copyReg stores value(src) in dst
HPFree(c) and CircuitWellFormed(c) -> run(c.reverse, run(c, st)) = st
```

Each primitive additionally exposes exact T-count, support/locality, H/P-free, and
well-formedness lemmas. Program definitions precede their correctness results; the shared
support and cancellation proof tools are collected after the leaf programs.
-/

namespace ShorECDLP

open Classical
open scoped ArithmeticNotation

/-! ## Constant loading -/

/-- Load the constant `c` (LSB-first) into wires `ws`: X each wire whose corresponding bit of
`c` is set. Self-inverse — running it again clears the register. -/
def loadConst : List Wire → Nat → Circuit
  | [],      _ => circuit! {}
  | w :: ws, c => circuit! {
      (if c % 2 = 1 then circuit! { gate! Gate.X w } else circuit! {});
      loadConst ws (c / 2)
    }

/-- One bit of a reversible two-way selector. With a fresh output it writes `x` when `flag=0`
and `y` when `flag=1`. -/
def selectBit (flag x y out : Wire) : Circuit :=
  circuit! {
    gate! Gate.CX x out;
    gate! Gate.CX x y;
    gate! Gate.CCX flag y out;
    gate! Gate.CX x y
  }

/-- Apply `selectBit` pointwise to three aligned, LSB-first registers. -/
def selectPoint (flag : Wire) : List Wire → List Wire → List Wire → Circuit
  | x :: xs, y :: ys, out :: outs =>
      circuit! {
        selectBit flag x y out;
        selectPoint flag xs ys outs
      }
  | _, _, _ => circuit! {}

/-- Wire conditions needed by the selector. The three lists are aligned registers; source and
flag wires stay outside the duplicate-free output register, and the two sources in each bit
position are distinct. -/
def selectOK (flag : Wire) : List Wire → List Wire → List Wire → Prop
  | [], [], [] => True
  | x :: xs, y :: ys, out :: outs =>
      x ≠ y ∧ x ≠ out ∧ y ≠ out ∧
      flag ≠ x ∧ flag ≠ y ∧ flag ≠ out ∧
      out ∉ outs ∧ x ∉ outs ∧ y ∉ outs ∧
      (∀ x' ∈ xs, x' ≠ out) ∧ (∀ y' ∈ ys, y' ≠ out) ∧
      selectOK flag xs ys outs
  | _, _, _ => False

namespace Arithmetic

/-- CNOT-copy aligned source bits into a clean destination register. -/
def copyReg : List Wire → List Wire → Circuit
  | s :: src, d :: dst => circuit! {
      gate! Gate.CX s d;
      copyReg src dst
    }
  | _, _ => circuit! {}

end Arithmetic

/-- `loadConst` touches only its own wires: a wire outside `ws` is left unchanged. -/
theorem loadConst_other (w : Wire) :
    ∀ (ws : List Wire) (c : Nat) (st : BasisState), w ∉ ws →
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
    ∀ (ws : List Wire) (c : Nat) (st : BasisState),
      ws.Nodup → (∀ w ∈ ws, st w = false) → c < 2 ^ ws.length →
      (⟪loadConst ws c⟫ st)⟦ᵣws⟧ = c := by
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
theorem loadConst_regValue (ws bs : List Wire) (c : Nat) (st : BasisState)
    (h : ∀ w ∈ ws, w ∉ bs) :
    (⟪loadConst bs c⟫ st)⟦ᵣws⟧ = st⟦ᵣws⟧ :=
  regValue_congr ws _ _ (fun w hw => loadConst_other w bs c st (h w hw))

/-- A wire outside the loaded register keeps its value (bit form) under `loadConst`. -/
theorem loadConst_false (w : Wire) (bs : List Wire) (c : Nat) (st : BasisState)
    (hw : w ∉ bs) (hf : st w = false) : run (loadConst bs c) st w = false := by
  rw [loadConst_other w bs c st hw, hf]

/-- `loadConst` is X-only, so it is T-free. -/
theorem loadConst_tCount (ws : List Wire) (c : Nat) : tCount (loadConst ws c) = 0 := by
  induction ws generalizing c with
  | nil => simp [loadConst]
  | cons w vs ih =>
      rw [loadConst, tCount_append, ih (c / 2)]
      by_cases h : c % 2 = 1 <;> simp [h, tCount, tCost]

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

/-! ## Reversible two-way selection -/

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

/-- The selector's net action changes only its output register. -/
theorem selectPoint_other (flag w : Wire) :
    ∀ (xs ys outs : List Wire) (st : BasisState),
      selectOK flag xs ys outs → w ∉ outs →
      run (selectPoint flag xs ys outs) st w = st w := by
  intro xs
  induction xs with
  | nil =>
      intro ys outs st hok _
      cases ys <;> cases outs <;> simp [selectPoint, selectOK] at hok ⊢
  | cons x xs ih =>
      intro ys outs st hok hw
      cases ys with
      | nil => simp [selectOK] at hok
      | cons y ys =>
          cases outs with
          | nil => simp [selectOK] at hok
          | cons out outs =>
              rcases hok with
                ⟨hxy, hxo, hyo, _, hfy, hfo, _, _, _, _, _, htail⟩
              have hwo : w ≠ out := by
                intro h
                exact hw (h ▸ List.mem_cons_self ..)
              have hwouts : w ∉ outs := fun h => hw (List.mem_cons_of_mem _ h)
              rw [selectPoint, run_append, ih ys outs _ htail hwouts,
                run_selectBit flag x y out st hxy hxo hyo hfy hfo,
                upd_other _ _ _ hwo]

/-- With a fresh output register, the pointwise selector writes `xs` when its flag is false and
`ys` when its flag is true. -/
theorem selectPoint_correct (flag : Wire) :
    ∀ (xs ys outs : List Wire) (st : BasisState),
      selectOK flag xs ys outs → clean(outs, st) →
      (⟪selectPoint flag xs ys outs⟫ st)⟦ᵣouts⟧ =
        if st flag then st⟦ᵣys⟧ else st⟦ᵣxs⟧ := by
  intro xs
  induction xs with
  | nil =>
      intro ys outs st hok _
      cases ys <;> cases outs <;> simp [selectPoint, selectOK] at hok ⊢
  | cons x xs ih =>
      intro ys outs st hok hclean
      cases ys with
      | nil => simp [selectOK] at hok
      | cons y ys =>
          cases outs with
          | nil => simp [selectOK] at hok
          | cons out outs =>
              rcases hok with
                ⟨hxy, hxo, hyo, _, hfy, hfo, hout, hxouts, hyouts,
                  hxsout, hysout, htail⟩
              have hcell := run_selectBit flag x y out st hxy hxo hyo hfy hfo
              have houtxs : out ∉ xs := by
                intro h
                exact hxsout out h rfl
              have houtys : out ∉ ys := by
                intro h
                exact hysout out h rfl
              have htailclean : Clean outs (run (selectBit flag x y out) st) := by
                intro w hw
                rw [hcell, upd_other]
                · exact hclean w (List.mem_cons_of_mem _ hw)
                · intro h
                  exact hout (h ▸ hw)
              have hih := ih ys outs (run (selectBit flag x y out) st) htail htailclean
              have htailx : regValue xs (run (selectBit flag x y out) st) =
                  regValue xs st := by
                rw [hcell, regValue_upd_not_mem _ _ _ _ houtxs]
              have htaily : regValue ys (run (selectBit flag x y out) st) =
                  regValue ys st := by
                rw [hcell, regValue_upd_not_mem _ _ _ _ houtys]
              have hflagcell : run (selectBit flag x y out) st flag = st flag := by
                rw [hcell, upd_other _ _ _ hfo]
              rw [htaily, htailx, hflagcell] at hih
              have houtvalue :
                  run (selectPoint flag xs ys outs) (run (selectBit flag x y out) st) out =
                    if st flag then st y else st x := by
                rw [selectPoint_other flag out xs ys outs _ htail hout,
                  hcell, upd_same, hclean out (List.mem_cons_self ..)]
                simp
              rw [selectPoint, run_append, regValue_cons, houtvalue, hih]
              cases st flag <;> simp [regValue_cons]

/-- One selector cell has T-count `7` (one Toffoli). -/
theorem selectBit_tCount (flag x y out : Wire) : tCount (selectBit flag x y out) = 7 := rfl

/-- The selector costs `7` T per output bit whenever its three registers are aligned. -/
theorem selectPoint_tCount (flag : Wire) :
    ∀ (xs ys outs : List Wire), xs.length = ys.length → xs.length = outs.length →
      tCount (selectPoint flag xs ys outs) = 7 * outs.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys outs hxy hxo
      cases ys <;> cases outs <;> simp [selectPoint] at hxy hxo ⊢
  | cons x xs ih =>
      intro ys outs hxy hxo
      cases ys with
      | nil => simp at hxy
      | cons y ys =>
          cases outs with
          | nil => simp at hxo
          | cons out outs =>
              have hxy' : xs.length = ys.length := by simpa using hxy
              have hxo' : xs.length = outs.length := by simpa using hxo
              rw [selectPoint, tCount_append, selectBit_tCount,
                ih ys outs hxy' hxo']
              simp [Nat.mul_succ, Nat.add_comm]

/-- The selector is an arithmetic circuit. -/
theorem selectPoint_HPFree (flag : Wire) :
    ∀ (xs ys outs : List Wire), HPFree (selectPoint flag xs ys outs) := by
  intro xs
  induction xs with
  | nil => intro ys outs; simp [selectPoint]
  | cons x xs ih =>
      intro ys outs
      cases ys <;> cases outs <;> simp [selectPoint, selectBit, ih]

/-- The selector is well-formed under `selectOK`. -/
theorem selectPoint_wellFormed (flag : Wire) :
    ∀ (xs ys outs : List Wire), selectOK flag xs ys outs →
      CircuitWellFormed (selectPoint flag xs ys outs) := by
  intro xs
  induction xs with
  | nil =>
      intro ys outs h
      cases ys <;> cases outs <;> simp [selectPoint, selectOK] at h ⊢
  | cons x xs ih =>
      intro ys outs h
      cases ys with
      | nil => simp [selectOK] at h
      | cons y ys =>
          cases outs with
          | nil => simp [selectOK] at h
          | cons out outs =>
              rcases h with
                ⟨hxy, hxo, hyo, _, hfy, hfo, _, _, _, _, _, htail⟩
              rw [selectPoint, circuitWellFormed_append]
              constructor
              · simp only [selectBit, circuitWellFormed_cons, circuitWellFormed_nil,
                  Gate.WellFormed, and_true]
                exact ⟨hxo, hxy, ⟨hfy, hfo, hyo⟩, hxy⟩
              · exact ih ys outs htail

/-! ## Register copying -/

namespace Arithmetic

theorem Clean.mono {xs ys : List Wire} {st : BasisState} (h : Clean xs st)
    (hsub : ∀ w ∈ ys, w ∈ xs) : Clean ys st := by
  intro w hw
  exact h w (hsub w hw)

theorem Clean.regValue_eq_zero {ws : List Wire} {st : BasisState} (h : Clean ws st) :
    regValue ws st = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      rw [regValue_cons, h w (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem w hx))]
      simp

theorem AgreesOn.regValue {ws : List Wire} {before after : BasisState}
    (h : AgreesOn ws before after) : regValue ws after = regValue ws before :=
  regValue_congr ws after before h

@[simp]
theorem copyReg_tCount (src dst : List Wire) : tCount (copyReg src dst) = 0 := by
  induction src generalizing dst with
  | nil => simp [copyReg]
  | cons s src ih =>
      cases dst with
      | nil => simp [copyReg]
      | cons d dst => simp [copyReg, ih, tCost]

@[simp]
theorem copyReg_HPFree (src dst : List Wire) : HPFree (copyReg src dst) := by
  induction src generalizing dst with
  | nil => simp [copyReg]
  | cons s src ih =>
      cases dst with
      | nil => simp [copyReg]
      | cons d dst => simp [copyReg, ih]

theorem copyReg_usesOnly (src dst ws : List Wire)
    (hsrc : ∀ w ∈ src, w ∈ ws) (hdst : ∀ w ∈ dst, w ∈ ws) :
    CircuitUsesOnly ws (copyReg src dst) := by
  intro g hg
  induction src generalizing dst with
  | nil => simp [copyReg] at hg
  | cons s src ih =>
      cases dst with
      | nil => simp [copyReg] at hg
      | cons d dst =>
          simp only [copyReg, List.mem_cons] at hg
          cases hg with
          | inl heq =>
              subst g
              exact ⟨hsrc s (List.mem_cons_self ..), hdst d (List.mem_cons_self ..)⟩
          | inr htail =>
              exact ih dst (fun w hw => hsrc w (List.mem_cons_of_mem _ hw))
                (fun w hw => hdst w (List.mem_cons_of_mem _ hw)) htail

/-- Copying changes only destination wires. -/
theorem copyReg_other (w : Wire) :
    ∀ (src dst : List Wire) (st : BasisState), w ∉ dst →
      run (copyReg src dst) st w = st w := by
  intro src
  induction src with
  | nil => intro dst st _; simp [copyReg]
  | cons s src ih =>
      intro dst st hw
      cases dst with
      | nil => simp [copyReg]
      | cons d dst =>
          simp only [List.mem_cons, not_or] at hw
          rw [copyReg, run_cons, ih dst (applyGate (Gate.CX s d) st) hw.2]
          exact upd_other st d (Bool.xor (st d) (st s)) hw.1

/-- CNOT-copy correctness on duplicate-free, disjoint aligned registers. -/
theorem copyReg_correct :
    ∀ (src dst : List Wire) (st : BasisState),
      dst.length = src.length → (src ++ dst).Nodup → clean(dst, st) →
      (⟪copyReg src dst⟫ st)⟦ᵣdst⟧ = st⟦ᵣsrc⟧ := by
  intro src
  induction src with
  | nil =>
      intro dst st hlen _ _
      have : dst = [] := List.length_eq_zero_iff.mp hlen
      subst dst
      rfl
  | cons s src ih =>
      intro dst st hlen hnd hclean
      cases dst with
      | nil => simp at hlen
      | cons d dst =>
          have hlenTail : dst.length = src.length := by simpa using hlen
          obtain ⟨hsrcNd, hdstNd, hcross⟩ := List.nodup_append.mp hnd
          obtain ⟨_, hsrcTailNd⟩ := List.nodup_cons.mp hsrcNd
          obtain ⟨hdDst, hdstTailNd⟩ := List.nodup_cons.mp hdstNd
          have htailNd : (src ++ dst).Nodup := List.nodup_append.mpr
            ⟨hsrcTailNd, hdstTailNd,
              fun a ha b hb => hcross a (List.mem_cons_of_mem s ha) b (List.mem_cons_of_mem d hb)⟩
          have hdSrc : d ∉ src := by
            intro hd
            exact (hcross d (List.mem_cons_of_mem s hd) d (List.mem_cons_self ..)) rfl
          let st₁ := applyGate (Gate.CX s d) st
          have hcleanTail : Clean dst st₁ := by
            intro w hw
            change st[d ↦ Bool.xor (st d) (st s)] w = false
            have hwd : w ≠ d := by
              intro e
              subst w
              exact hdDst hw
            rw [upd_other _ _ _ hwd]
            exact hclean w (List.mem_cons_of_mem d hw)
          have hih := ih dst st₁ hlenTail htailNd hcleanTail
          have hsrcKeep : regValue src st₁ = regValue src st := by
            exact regValue_upd_not_mem src st d (Bool.xor (st d) (st s)) hdSrc
          have hdFinal : run (copyReg src dst) st₁ d = st s := by
            rw [copyReg_other d src dst st₁ hdDst]
            simp [st₁, applyGate, hclean d (List.mem_cons_self ..)]
          rw [copyReg, run_cons, regValue_cons, hdFinal, hih, hsrcKeep, regValue_cons]

theorem copyReg_wellFormed :
    ∀ (src dst : List Wire), (src ++ dst).Nodup → CircuitWellFormed (copyReg src dst) := by
  intro src
  induction src with
  | nil => intro dst _; simp [copyReg]
  | cons s src ih =>
      intro dst hnd
      cases dst with
      | nil => simp [copyReg]
      | cons d dst =>
          obtain ⟨hsrcNd, hdstNd, hcross⟩ := List.nodup_append.mp hnd
          obtain ⟨_, hsrcTailNd⟩ := List.nodup_cons.mp hsrcNd
          obtain ⟨_, hdstTailNd⟩ := List.nodup_cons.mp hdstNd
          have htailNd : (src ++ dst).Nodup := List.nodup_append.mpr
            ⟨hsrcTailNd, hdstTailNd,
              fun a ha b hb => hcross a (List.mem_cons_of_mem s ha) b (List.mem_cons_of_mem d hb)⟩
          rw [copyReg, circuitWellFormed_cons]
          exact ⟨hcross s (List.mem_cons_self ..) d (List.mem_cons_self ..), ih dst htailNd⟩

theorem usesOnly_append {ws : List Wire} {c₁ c₂ : Circuit}
    (h₁ : CircuitUsesOnly ws c₁) (h₂ : CircuitUsesOnly ws c₂) :
    CircuitUsesOnly ws (c₁ ++ c₂) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h₁ g hg
  · exact h₂ g hg

theorem usesOnly_mono {xs ys : List Wire} {c : Circuit}
    (h : CircuitUsesOnly xs c) (hsub : ∀ w ∈ xs, w ∈ ys) : CircuitUsesOnly ys c := by
  intro g hg
  have hgate := h g hg
  cases g <;> simp_all [Gate.UsesOnly]

theorem usesOnly_reverse {ws : List Wire} {c : Circuit}
    (h : CircuitUsesOnly ws c) : CircuitUsesOnly ws c.reverse := by
  intro g hg
  exact h g (by simpa using hg)

/-- Loading a constant only touches its declared register. -/
theorem loadConst_usesOnly (ws : List Wire) (c : Nat) :
    CircuitUsesOnly ws (loadConst ws c) := by
  induction ws generalizing c with
  | nil => exact fun g hg => by simp [loadConst] at hg
  | cons w ws ih =>
      rw [loadConst]
      by_cases h : c % 2 = 1
      · rw [if_pos h]
        exact usesOnly_append
          (by simp [CircuitUsesOnly, Gate.UsesOnly])
          (usesOnly_mono (ih (c / 2)) (fun x hx => List.mem_cons_of_mem w hx))
      · rw [if_neg h]
        simpa using usesOnly_mono (ih (c / 2)) (fun x hx => List.mem_cons_of_mem w hx)

/-- One selector cell uses exactly its flag, two sources, and output. -/
theorem selectBit_usesOnly (flag x y out : Wire) :
    CircuitUsesOnly [flag, x, y, out] (selectBit flag x y out) := by
  simp [CircuitUsesOnly, selectBit, Gate.UsesOnly]

/-- Full syntactic footprint of a pointwise selector. -/
def selectFootprint (flag : Wire) (xs ys outs : List Wire) : List Wire :=
  flag :: xs ++ ys ++ outs

/-- A pointwise selector reads and writes only its declared footprint. -/
theorem selectPoint_usesOnly (flag : Wire) :
    ∀ (xs ys outs : List Wire),
      CircuitUsesOnly (selectFootprint flag xs ys outs) (selectPoint flag xs ys outs) := by
  intro xs
  induction xs with
  | nil => intro ys outs g hg; simp [selectPoint] at hg
  | cons x xs ih =>
      intro ys outs
      cases ys with
      | nil => intro g hg; simp [selectPoint] at hg
      | cons y ys =>
          cases outs with
          | nil => intro g hg; simp [selectPoint] at hg
          | cons out outs =>
              rw [selectPoint]
              apply usesOnly_append
              · apply usesOnly_mono (selectBit_usesOnly flag x y out)
                intro w hw
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
                simp only [selectFootprint, List.mem_cons, List.mem_append]
                rcases hw with rfl | rfl | rfl | rfl <;> simp
              · apply usesOnly_mono (ih ys outs)
                intro w hw
                simp only [selectFootprint, List.mem_cons, List.mem_append] at hw ⊢
                rcases hw with ((hflag | hxs) | hys) | houts
                · subst w
                  simp
                · exact Or.inl (Or.inl (Or.inr (Or.inr hxs)))
                · exact Or.inl (Or.inr (Or.inr hys))
                · exact Or.inr (Or.inr houts)

theorem hpFree_reverse {c : Circuit} (h : HPFree c) : HPFree c.reverse := by
  intro g hg
  exact h g (by simpa using hg)

theorem wellFormed_reverse {c : Circuit} (h : CircuitWellFormed c) :
    CircuitWellFormed c.reverse := by
  intro g hg
  exact h g (by simpa using hg)

theorem tCount_reverse (c : Circuit) : tCount c.reverse = tCount c := by
  simp [tCount]

/-- A circuit's values on its declared support depend only on the initial values there. -/
theorem CircuitUsesOnly.run_congr {ws : List Wire} {c : Circuit}
    (hc : CircuitUsesOnly ws c) {st₁ st₂ : BasisState}
    (hst : ∀ w ∈ ws, st₁ w = st₂ w) :
    ∀ w ∈ ws, run c st₁ w = run c st₂ w := by
  induction c generalizing st₁ st₂ with
  | nil => exact hst
  | cons g c ih =>
      rw [run_cons, run_cons]
      apply ih (fun g' hg' => hc g' (List.mem_cons_of_mem g hg'))
      intro w hw
      have hg := hc g (List.mem_cons_self ..)
      cases g with
      | X t =>
          simp only [Gate.UsesOnly] at hg
          by_cases hwt : w = t
          · subst w
            simp [applyGate, upd, hst t hg]
          · simp [applyGate, upd, hwt, hst w hw]
      | H _ => exact hst w hw
      | CX control target =>
          simp only [Gate.UsesOnly] at hg
          by_cases hwt : w = target
          · subst w
            simp [applyGate, upd, hst target hg.2, hst control hg.1]
          · simp [applyGate, upd, hwt, hst w hw]
      | CCX control₁ control₂ target =>
          simp only [Gate.UsesOnly] at hg
          by_cases hwt : w = target
          · subst w
            simp [applyGate, upd, hst target hg.2.2, hst control₁ hg.1,
              hst control₂ hg.2.1]
          · simp [applyGate, upd, hwt, hst w hw]
      | P _ _ _ => exact hst w hw

/-- A well-formed classical primitive gate is self-inverse. -/
theorem applyGate_twice (g : Gate) (st : BasisState)
    (hc : IsClassicalGate g) (hwf : g.WellFormed) : applyGate g (applyGate g st) = st := by
  funext w
  cases g with
  | X t =>
      by_cases h : w = t
      · subst w; simp [applyGate, upd]
      · simp [applyGate, upd, h]
  | H _ => simp at hc
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
  | P _ _ _ => simp at hc

/-- Reversing a well-formed H/P-free circuit cancels its classical action. -/
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

end Arithmetic
end ShorECDLP
