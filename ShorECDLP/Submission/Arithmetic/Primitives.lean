import ShorECDLP.Submission.Arithmetic.Contracts
import ShorECDLP.Submission.Arithmetic.RippleAdder

/-
# Reusable clean reversible-circuit primitives

This module contains the small, implementation-neutral leaves shared by the arithmetic
milestones: constant loading, reversible two-way selection, aligned register copying,
circuit-support composition, and cancellation of a well-formed H/P-free circuit by its reverse.
Keeping them here prevents the modular arithmetic layers from growing divergent local copies or
depending on a concrete higher-level arithmetic construction for a generic circuit primitive.
-/

namespace ShorECDLP

open Classical

/-! ## Constant loading -/

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

/-- `loadConst` is X-only, so it is T-free. -/
theorem loadConst_tCount (ws : List Nat) (c : Nat) : tCount (loadConst ws c) = 0 := by
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

/-- CNOT-copy aligned source bits into a clean destination register. -/
def copyReg : List Wire → List Wire → Circuit
  | s :: src, d :: dst => Gate.CX s d :: copyReg src dst
  | _, _ => []

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
      dst.length = src.length → (src ++ dst).Nodup → Clean dst st →
      regValue dst (run (copyReg src dst) st) = regValue src st := by
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
def selectFootprint (flag : Wire) (cols : List (Wire × Wire × Wire)) : List Wire :=
  flag :: cols.flatMap (fun c => [c.1, c.2.1, c.2.2])

/-- A pointwise selector reads and writes only its declared footprint. -/
theorem selectPoint_usesOnly (flag : Wire) :
    ∀ cols : List (Wire × Wire × Wire),
      CircuitUsesOnly (selectFootprint flag cols) (selectPoint flag cols) := by
  intro cols
  induction cols with
  | nil => exact fun g hg => by simp [selectPoint] at hg
  | cons head rest ih =>
      obtain ⟨x,y,o⟩ := head
      rw [selectPoint]
      apply usesOnly_append
      · apply usesOnly_mono (selectBit_usesOnly flag x y o)
        intro w hw
        simp only [List.mem_cons] at hw
        simp only [selectFootprint, List.flatMap_cons, List.mem_cons, List.mem_append,
          List.mem_flatMap]
        rcases hw with rfl | rfl | rfl | rfl | hw
        · simp
        · simp
        · simp
        · simp
        · contradiction
      · apply usesOnly_mono ih
        intro w hw
        simp only [selectFootprint, List.flatMap_cons, List.mem_cons, List.mem_append,
          List.mem_flatMap] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (Or.inr hw)

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
      | P _ _ => exact hst w hw

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
  | P _ _ => simp at hc

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
