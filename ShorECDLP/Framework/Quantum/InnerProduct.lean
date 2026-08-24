import ShorECDLP.Framework.Quantum.Semantics
import ShorECDLP.Framework.InstructionSet
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul

/-!
# Inner product on finite-support quantum states
-/

namespace ShorECDLP.Quantum

noncomputable section


/-! ## Inner product -/
/--
The finite-support complex inner product
-/
def inner (ψ φ : State) : ℂ :=
  ψ.sum fun s a => (starRingEnd ℂ) a * φ s

/-! ## Inner products of basis kets -/

@[simp]
theorem inner_ket_self (s : BasisState) :
    inner (ket s) (ket s) = 1 := by
  classical
  simp [inner, ket]

@[simp]
theorem inner_ket_ne
    {s t : BasisState}
    (h : s ≠ t) :
    inner (ket s) (ket t) = 0 := by
  classical
  simp [inner, ket, h]

/-! ## Zero -/

@[simp]
theorem inner_zero_left (φ : State) :
    inner 0 φ = 0 := by
  simp [inner]

@[simp]
theorem inner_zero_right (ψ : State) :
    inner ψ 0 = 0 := by
  simp [inner]

/-! ## Additivity -/
/--
The inner product is additive in its first argument.
-/
theorem inner_add_left
    (ψ₁ ψ₂ φ : State) :
    inner (ψ₁ + ψ₂) φ =
      inner ψ₁ φ + inner ψ₂ φ := by
  classical
  unfold inner
  rw [Finsupp.sum_add_index']
  · intro s
    simp
  · intro s a b
    simp [add_mul]

/--
The inner product is additive in its second argument.
-/
theorem inner_add_right
    (ψ φ₁ φ₂ : State) :
    inner ψ (φ₁ + φ₂) =
      inner ψ φ₁ + inner ψ φ₂ := by
  classical
  simp [inner, mul_add]

/-! ## Scalar multiplication -/
/--
The inner product is conjugate-linear in its first argument.
-/
theorem inner_smul_left
    (a : ℂ)
    (ψ φ : State) :
    inner (a • ψ) φ =
      (starRingEnd ℂ) a * inner ψ φ := by
  unfold inner
  rw [Finsupp.sum_smul_index']
  · simp only [smul_eq_mul, map_mul]
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro s hs
    simp [mul_assoc]
  · intro s
    simp

/--
The inner product is linear in its second argument.
-/
theorem inner_smul_right
    (a : ℂ)
    (ψ φ : State) :
    inner ψ (a • φ) =
      a * inner ψ φ := by
  unfold inner
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro s hs
  simp [mul_left_comm]

/-! ## Useful combined rules -/
theorem inner_add_add
    (ψ₁ ψ₂ φ₁ φ₂ : State) :
    inner (ψ₁ + ψ₂) (φ₁ + φ₂) =
      inner ψ₁ φ₁ +
      inner ψ₁ φ₂ +
      inner ψ₂ φ₁ +
      inner ψ₂ φ₂ := by
  rw [inner_add_left]
  rw [inner_add_right, inner_add_right]
  ring

theorem inner_smul_smul
    (a b : ℂ)
    (ψ φ : State) :
    inner (a • ψ) (b • φ) =
      (starRingEnd ℂ) a * b * inner ψ φ := by
  rw [inner_smul_left]
  rw [inner_smul_right]
  ring

/-! ## Squared norm / Born mass -/
/--
Squared ℓ² norm of a quantum state.

For a normalized quantum state this is `1`. This is the quantity preserved
by unitary circuits and used as total probability mass in the Born rule.
-/
def normSq (ψ : State) : ℝ :=
  (inner ψ ψ).re

@[simp]
theorem normSq_ket (s : BasisState) :
    normSq (ket s) = 1 := by
  simp [normSq]

@[simp]
theorem normSq_zero :
    normSq (0 : State) = 0 := by
  simp [normSq]

/-! ## Preservation predicates -/
/--
A complex-linear map preserves the quantum inner product.
-/
def PreservesInner
    (U : State →ₗ[ℂ] State) : Prop :=
  ∀ ψ φ, inner (U ψ) (U φ) = inner ψ φ

/--
A complex-linear map preserves squared norm / total Born mass.
-/
def PreservesNormSq
    (U : State →ₗ[ℂ] State) : Prop :=
  ∀ ψ, normSq (U ψ) = normSq ψ

/--
Inner-product preservation implies squared-norm preservation.
-/
theorem PreservesInner.preservesNormSq
    {U : State →ₗ[ℂ] State}
    (hU : PreservesInner U) :
    PreservesNormSq U := by
  intro ψ
  unfold normSq
  have h := hU ψ ψ
  exact congrArg Complex.re h

/-! ## Identity and composition -/

theorem preservesInner_id :
    PreservesInner
      (LinearMap.id : State →ₗ[ℂ] State) := by
  intro ψ φ
  rfl

/--
Inner-product-preserving maps remain inner-product-preserving under
composition.
-/
theorem PreservesInner.comp
    {U V : State →ₗ[ℂ] State}
    (hU : PreservesInner U)
    (hV : PreservesInner V) :
    PreservesInner (V.comp U) := by
  intro ψ φ
  change inner (V (U ψ)) (V (U φ)) = inner ψ φ
  rw [hV]
  exact hU ψ φ


theorem preservesNormSq_id :
    PreservesNormSq
      (LinearMap.id : State →ₗ[ℂ] State) :=
  preservesInner_id.preservesNormSq


theorem PreservesNormSq.comp
    {U V : State →ₗ[ℂ] State}
    (hU : PreservesNormSq U)
    (hV : PreservesNormSq V) :
    PreservesNormSq (V.comp U) := by
  intro ψ
  change normSq (V (U ψ)) = normSq ψ
  rw [hV]
  exact hU ψ

/-! ============================================================
    Well-formedness needed for unitarity
============================================================ -/


/-! ============================================================
    Basis extension theorem
============================================================ -/

/--
It is enough to check preservation of inner products on computational
basis kets.

Every `State` is a finite complex linear combination of such kets.
-/
theorem preservesInner_of_kets
    (U : State →ₗ[ℂ] State)
    (hU : ∀ s t : BasisState, inner (U (ket s)) (U (ket t)) = inner (ket s) (ket t)) :
    PreservesInner U := by
  intro ψ
  induction ψ using Finsupp.induction_linear with
  | zero =>
      intro φ
      simp [inner_zero_left]

  | add ψ₁ ψ₂ ih₁ ih₂ =>
      intro φ

      rw [U.map_add]
      rw [inner_add_left]
      rw [ih₁ φ, ih₂ φ]
      rw [inner_add_left]

  | single s a =>
      intro φ

      induction φ using Finsupp.induction_linear with
      | zero =>
          simp [inner_zero_right]

      | add φ₁ φ₂ ih₁ ih₂ =>
          rw [U.map_add]
          rw [inner_add_right]
          rw [ih₁, ih₂]
          rw [inner_add_right]

      | single t b =>
          have hs :
              Finsupp.single s a =
                a • ket s := by
            ext x
            simp [ket]

          have ht :
              Finsupp.single t b =
                b • ket t := by
            ext x
            simp [ket]
          rw [hs, ht, U.map_smul, U.map_smul,
            inner_smul_smul, inner_smul_smul, hU s t]


/-! ============================================================
    Basis-state permutations for X, CX, CCX
============================================================ -/

private def xBasis
    (t : Wire)
    (s : BasisState) : BasisState :=
  s[t ↦ !s t]


private def cxBasis
    (c t : Wire)
    (s : BasisState) : BasisState :=
  s[t ↦ Bool.xor (s t) (s c)]


private def ccxBasis
    (a b t : Wire)
    (s : BasisState) : BasisState :=
  s[t ↦ Bool.xor (s t) (s a && s b)]


/-! ### X -/

private theorem xBasis_involutive
    (t : Wire) :
    Function.Involutive (xBasis t) := by
  intro s
  funext i

  by_cases hi : i = t
  · subst i
    simp [xBasis]

  · simp [xBasis, upd, hi]


private theorem xBasis_injective
    (t : Wire) :
    Function.Injective (xBasis t) :=
  (xBasis_involutive t).injective


/-! ### CX -/

private theorem cxBasis_involutive
    (c t : Wire)
    (hct : c ≠ t) :
    Function.Involutive (cxBasis c t) := by
  intro s
  funext i

  by_cases hi : i = t
  · subst i

    cases hc : s c <;>
      cases ht : s t <;>
      simp [cxBasis, upd, hct, hc, ht]

  · simp [cxBasis, upd, hi]


private theorem cxBasis_injective
    (c t : Wire)
    (hct : c ≠ t) :
    Function.Injective (cxBasis c t) :=
  (cxBasis_involutive c t hct).injective


/-! ### CCX -/

private theorem ccxBasis_involutive
    (a b t : Wire)
    (hat : a ≠ t)
    (hbt : b ≠ t) :
    Function.Involutive (ccxBasis a b t) := by
  intro s
  funext i

  by_cases hi : i = t
  · subst i

    cases hab : (s a && s b) <;>
      cases ht : s t <;>
      simp [ccxBasis, upd, hat, hbt, hab, ht]

  · simp [ccxBasis, upd, hi]


private theorem ccxBasis_injective
    (a b t : Wire)
    (hat : a ≠ t)
    (hbt : b ≠ t) :
    Function.Injective (ccxBasis a b t) :=
  (ccxBasis_involutive a b t hat hbt).injective


/-!
An injective relabelling of computational basis states preserves
basis-ket inner products.
-/
private theorem inner_ket_injective_map
    (f : BasisState → BasisState)
    (hf : Function.Injective f)
    (s t : BasisState) :
    inner (ket (f s)) (ket (f t)) =
      inner (ket s) (ket t) := by
  by_cases h : s = t
  · subst t
    simp

  · have h' : f s ≠ f t := by
      intro hft
      exact h (hf hft)

    simp [h, h']


/-! ============================================================
    X preserves inner products
============================================================ -/

private theorem applyGate_X_preserves_ket_inner
    (t : Wire)
    (s u : BasisState) :
    inner
        (applyGate (.X t) (ket s))
        (applyGate (.X t) (ket u))
      =
    inner (ket s) (ket u) := by
  rw [applyGate_X_ket, applyGate_X_ket]

  simpa [xBasis] using
    inner_ket_injective_map
      (xBasis t)
      (xBasis_injective t)
      s u


theorem applyGate_X_preservesInner
    (t : Wire) :
    PreservesInner (applyGate (.X t)) :=
  preservesInner_of_kets
    (applyGate (.X t))
    (applyGate_X_preserves_ket_inner t)


/-! ============================================================
    CX preserves inner products
============================================================ -/

private theorem applyGate_CX_preserves_ket_inner
    (c t : Wire)
    (hct : c ≠ t)
    (s u : BasisState) :
    inner
        (applyGate (.CX c t) (ket s))
        (applyGate (.CX c t) (ket u))
      =
    inner (ket s) (ket u) := by
  rw [applyGate_CX_ket, applyGate_CX_ket]

  simpa [cxBasis] using
    inner_ket_injective_map
      (cxBasis c t)
      (cxBasis_injective c t hct)
      s u


theorem applyGate_CX_preservesInner
    (c t : Wire)
    (hct : c ≠ t) :
    PreservesInner (applyGate (.CX c t)) :=
  preservesInner_of_kets
    (applyGate (.CX c t))
    (applyGate_CX_preserves_ket_inner c t hct)


/-! ============================================================
    CCX preserves inner products
============================================================ -/

private theorem applyGate_CCX_preserves_ket_inner
    (a b t : Wire)
    (hat : a ≠ t)
    (hbt : b ≠ t)
    (s u : BasisState) :
    inner
        (applyGate (.CCX a b t) (ket s))
        (applyGate (.CCX a b t) (ket u))
      =
    inner (ket s) (ket u) := by
  rw [applyGate_CCX_ket, applyGate_CCX_ket]

  simpa [ccxBasis] using
    inner_ket_injective_map
      (ccxBasis a b t)
      (ccxBasis_injective a b t hat hbt)
      s u


theorem applyGate_CCX_preservesInner
    (a b t : Wire)
    (hat : a ≠ t)
    (hbt : b ≠ t) :
    PreservesInner (applyGate (.CCX a b t)) :=
  preservesInner_of_kets
    (applyGate (.CCX a b t))
    (applyGate_CCX_preserves_ket_inner a b t hat hbt)


/-! ============================================================
    Phase gate
============================================================ -/

/--
The phase used by `P dir k` has modulus one, expressed in the algebraic form
needed by the inner product.
-/
private theorem phaseCoeff_star_mul
    (dir : PhaseDir)
    (k : Nat) :
    (starRingEnd ℂ) (phaseCoeff dir k) *
        phaseCoeff dir k
      = 1 := by
  have hnorm : Complex.normSq (phaseCoeff dir k) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have hnorm' : ‖phaseCoeff dir k‖ = 1 := by
      unfold phaseCoeff
      simp
    rw [hnorm']
    norm_num
  have hnormC : ((Complex.normSq (phaseCoeff dir k) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hnorm
  rw [Complex.normSq_eq_conj_mul_self] at hnormC
  simpa using hnormC


private theorem applyGate_P_preserves_ket_inner
    (dir : PhaseDir)
    (k : Nat)
    (t : Wire)
    (s u : BasisState) :
    inner
        (applyGate (.P dir k t) (ket s))
        (applyGate (.P dir k t) (ket u))
      =
    inner (ket s) (ket u) := by
  rw [applyGate_P_ket, applyGate_P_ket]
  rw [inner_smul_smul]

  by_cases hsu : s = u
  · subst u

    by_cases hb : s t
    · simp [hb, phaseCoeff_star_mul]

    · simp [hb]

  · simp [hsu]


theorem applyGate_P_preservesInner
    (dir : PhaseDir)
    (k : Nat)
    (t : Wire) :
    PreservesInner (applyGate (.P dir k t)) :=
  preservesInner_of_kets
    (applyGate (.P dir k t))
    (applyGate_P_preserves_ket_inner dir k t)


/-! ============================================================
    Hadamard
============================================================ -/

/--
The common `1 / √2` Hadamard coefficient.
-/
private def hCoeff : ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)


private def hSign (b : Bool) : ℂ :=
  if b then -1 else 1


private theorem applyGate_H_ket'
    (t : Wire)
    (s : BasisState) :
    applyGate (.H t) (ket s)
      =
    hCoeff • ket (s[t ↦ false]) +
      (hCoeff * hSign (s t)) •
        ket (s[t ↦ true]) := by
  simpa [hCoeff, hSign] using
    applyGate_H_ket t s


/-!
`|1/√2|² = 1/2`.
-/
private theorem hCoeff_star_mul :
    (starRingEnd ℂ) hCoeff * hCoeff =
      (1 / 2 : ℂ) := by
  have hsqrt_ne :
      Real.sqrt 2 ≠ 0 := by
    positivity

  have hr :
      (Real.sqrt 2)⁻¹ *
          (Real.sqrt 2)⁻¹
        =
      (1 / 2 : ℝ) := by
    field_simp [hsqrt_ne]

    have hsqrt :
        Real.sqrt 2 * Real.sqrt 2 =
          (2 : ℝ) := by
      exact Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)

    nlinarith

  have hc :=
    congrArg (fun x : ℝ => (x : ℂ)) hr

  simpa [hCoeff] using hc


private theorem hWeighted_star_mul
    (b : Bool) :
    (starRingEnd ℂ) (hCoeff * hSign b) *
        (hCoeff * hSign b)
      =
    (1 / 2 : ℂ) := by
  cases b <;>
    simp [hSign, hCoeff_star_mul]


private theorem hWeighted_star_mul_of_ne
    {b₁ b₂ : Bool}
    (h : b₁ ≠ b₂) :
    (starRingEnd ℂ) (hCoeff * hSign b₁) *
        (hCoeff * hSign b₂)
      =
    -(1 / 2 : ℂ) := by
  cases b₁ <;>
    cases b₂ <;>
    simp_all [hSign, hCoeff_star_mul]


private theorem hCoeff_mul_star :
    hCoeff * (starRingEnd ℂ) hCoeff =
      (1 / 2 : ℂ) := by
  rw [mul_comm]
  exact hCoeff_star_mul


private theorem hWeighted_expanded_self
    (b : Bool) :
    hCoeff *
        (hSign b *
          ((starRingEnd ℂ) hCoeff *
            (starRingEnd ℂ) (hSign b)))
      =
    (1 / 2 : ℂ) := by
  cases b <;>
    simp [hSign, hCoeff_mul_star, mul_comm]


private theorem hWeighted_expanded_ne
    {b₁ b₂ : Bool}
    (h : b₁ ≠ b₂) :
    hCoeff *
        (hSign b₂ *
          ((starRingEnd ℂ) hCoeff *
            (starRingEnd ℂ) (hSign b₁)))
      =
    -(1 / 2 : ℂ) := by
  cases b₁ <;>
    cases b₂ <;>
    simp_all [hSign, hCoeff_mul_star, mul_comm]


/-! ### Small facts about updating one wire -/

private theorem update_false_ne_update_true
    (s u : BasisState)
    (t : Wire) :
    s[t ↦ false] ≠ u[t ↦ true] := by
  intro h
  have ht := congrFun h t
  simp at ht


private theorem update_true_ne_update_false
    (s u : BasisState)
    (t : Wire) :
    s[t ↦ true] ≠ u[t ↦ false] := by
  intro h
  have ht := congrFun h t
  simp at ht


private theorem update_true_eq_of_update_false_eq
    {s u : BasisState}
    {t : Wire}
    (h :
      s[t ↦ false] =
        u[t ↦ false]) :
    s[t ↦ true] =
      u[t ↦ true] := by
  funext i

  by_cases hi : i = t
  · subst i
    simp

  · have h' := congrFun h i
    simpa [upd, hi] using h'


private theorem update_true_ne_of_update_false_ne
    {s u : BasisState}
    {t : Wire}
    (h :
      s[t ↦ false] ≠
        u[t ↦ false]) :
    s[t ↦ true] ≠
      u[t ↦ true] := by
  intro htrue
  apply h

  funext i

  by_cases hi : i = t
  · subst i
    simp

  · have h' := congrFun htrue i
    simpa [upd, hi] using h'


private theorem state_eq_of_update_false_eq_of_bit_eq
    {s u : BasisState}
    {t : Wire}
    (hrest :
      s[t ↦ false] =
        u[t ↦ false])
    (hbit :
      s t = u t) :
    s = u := by
  funext i

  by_cases hi : i = t
  · subst i
    exact hbit

  · have h' := congrFun hrest i
    simpa [upd, hi] using h'


/-!
The two Hadamard images of computational basis states form an
orthonormal family.
-/
private theorem applyGate_H_preserves_ket_inner
    (t : Wire)
    (s u : BasisState) :
    inner
        (applyGate (.H t) (ket s))
        (applyGate (.H t) (ket u))
      =
    inner (ket s) (ket u) := by
  rw [applyGate_H_ket', applyGate_H_ket']

  simp only [
    inner_add_left,
    inner_add_right,
    inner_smul_smul
  ]

  have h01 :
      s[t ↦ false] ≠
        u[t ↦ true] :=
    update_false_ne_update_true s u t

  have h10 :
      s[t ↦ true] ≠
        u[t ↦ false] :=
    update_true_ne_update_false s u t

  by_cases hrest :
      s[t ↦ false] =
        u[t ↦ false]

  · have hset :
        s[t ↦ true] =
          u[t ↦ true] :=
      update_true_eq_of_update_false_eq hrest

    by_cases hsu : s = u

    · subst u

      simp [
        update_false_ne_update_true,
        update_true_ne_update_false,
        hCoeff_mul_star,
        hWeighted_expanded_self,
        map_mul,
        mul_assoc,
        mul_comm,
        mul_left_comm
      ]
      norm_num

    · have hbit :
          s t ≠ u t := by
        intro hbit
        exact hsu
          (state_eq_of_update_false_eq_of_bit_eq
            hrest hbit)

      simp [
        hrest,
        hset,
        hsu,
        hCoeff_mul_star,
        hWeighted_expanded_ne hbit,
        update_false_ne_update_true,
        update_true_ne_update_false,
        map_mul,
        mul_assoc,
        mul_comm,
        mul_left_comm
      ]

  · have hset :
        s[t ↦ true] ≠
          u[t ↦ true] :=
      update_true_ne_of_update_false_ne hrest

    have hsu : s ≠ u := by
      intro hsu
      subst u
      exact hrest rfl

    simp [
      hrest,
      hset,
      h01,
      h10,
      hsu
    ]


theorem applyGate_H_preservesInner
    (t : Wire) :
    PreservesInner (applyGate (.H t)) :=
  preservesInner_of_kets
    (applyGate (.H t))
    (applyGate_H_preserves_ket_inner t)


/-! ============================================================
    Primitive adjoints cancel
============================================================ -/

private theorem hCoeff_mul_self :
    ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) =
      (1 / 2 : ℂ) := by
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by
    positivity
  have hr :
      (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    field_simp [hsqrt_ne]
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) :=
      Real.mul_self_sqrt (by norm_num)
    nlinarith
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa using hc

private theorem upd_twice
    (s : BasisState) (t : Wire) (a b : Bool) :
    s[t ↦ a][t ↦ b] = s[t ↦ b] := by
  funext i
  by_cases hi : i = t
  · subst i
    simp
  · simp [upd, hi]

private theorem upd_eq_self
    (s : BasisState) (t : Wire) (b : Bool)
    (h : s t = b) :
    s[t ↦ b] = s := by
  funext i
  by_cases hi : i = t
  · subst i
    simpa using h.symm
  · simp [upd, hi]

private theorem applyGate_H_twice_ket
    (t : Wire) (s : BasisState) :
    applyGate (.H t) (applyGate (.H t) (ket s)) = ket s := by
  rw [applyGate_H_ket, applyGate_add, applyGate_smul, applyGate_smul,
    applyGate_H_ket, applyGate_H_ket]
  by_cases hb : s t
  · have hs1 : s[t ↦ true] = s := upd_eq_self s t true hb
    simp [hb, upd_twice, hs1, smul_smul]
    rw [hCoeff_mul_self]
    module
  · have hb' : s t = false := Bool.eq_false_of_not_eq_true hb
    have hs0 : s[t ↦ false] = s := upd_eq_self s t false hb'
    simp [hb, upd_twice, hs0, smul_smul]
    rw [hCoeff_mul_self]
    module

private theorem applyGate_adjoint_applyGate_ket
    (g : Gate) (hg : g.WellFormed) (s : BasisState) :
    applyGate g.adjoint (applyGate g (ket s)) = ket s := by
  cases g with
  | X t =>
      simp only [Gate.adjoint]
      rw [applyGate_X_ket, applyGate_X_ket]
      simpa [xBasis] using congrArg ket (xBasis_involutive t s)
  | H t =>
      exact applyGate_H_twice_ket t s
  | CX c t =>
      simp only [Gate.adjoint]
      rw [applyGate_CX_ket, applyGate_CX_ket]
      simpa [cxBasis] using congrArg ket (cxBasis_involutive c t hg s)
  | CCX a b t =>
      simp only [Gate.adjoint]
      rw [applyGate_CCX_ket, applyGate_CCX_ket]
      simpa [ccxBasis] using
        congrArg ket (ccxBasis_involutive a b t hg.2.1 hg.2.2 s)
  | P dir k t =>
      simp only [Gate.adjoint]
      rw [applyGate_P_ket, applyGate_smul, applyGate_P_ket]
      by_cases hb : s t
      · simp only [hb, if_pos, smul_smul]
        change
          (phaseCoeff dir k * phaseCoeff dir.adjoint k) • ket s = ket s
        rw [phaseCoeff_mul_adjoint]
        simp
      · simp [hb]

/-- Applying a well-formed primitive and then its adjoint is the identity
on every finitely supported quantum state. -/
theorem applyGate_adjoint_applyGate
    (g : Gate) (hg : g.WellFormed) (psi : State) :
    applyGate g.adjoint (applyGate g psi) = psi := by
  induction psi using Finsupp.induction_linear with
  | zero => simp
  | add psi phi ihpsi ihphi =>
      rw [applyGate_add, applyGate_add, ihpsi, ihphi]
  | single s a =>
      have hs : Finsupp.single s a = a • ket s := by
        ext x
        simp [ket]
      rw [hs, applyGate_smul, applyGate_smul,
        applyGate_adjoint_applyGate_ket g hg s]

/-- Applying the adjoint first and then the original well-formed primitive
is also the identity. -/
theorem applyGate_applyGate_adjoint
    (g : Gate) (hg : g.WellFormed) (psi : State) :
    applyGate g (applyGate g.adjoint psi) = psi := by
  have hadj : g.adjoint.WellFormed :=
    (Gate.wellFormed_adjoint g).2 hg
  have h := applyGate_adjoint_applyGate g.adjoint hadj psi
  rw [Gate.adjoint_adjoint] at h
  exact h


/-! ============================================================
    Every well-formed primitive gate preserves the inner product
============================================================ -/

theorem applyGate_preservesInner
    (g : Gate)
    (hg : Gate.WellFormed g) :
    PreservesInner (applyGate g) := by
  cases g with

  | X t =>
      exact applyGate_X_preservesInner t

  | H t =>
      exact applyGate_H_preservesInner t

  | CX c t =>
      exact applyGate_CX_preservesInner c t hg

  | CCX a b t =>
      exact
        applyGate_CCX_preservesInner
          a b t hg.2.1 hg.2.2

  | P dir k t =>
      exact applyGate_P_preservesInner dir k t


/--
Every well-formed primitive gate preserves squared norm.
-/
theorem applyGate_preservesNormSq
    (g : Gate)
    (hg : Gate.WellFormed g) :
    PreservesNormSq (applyGate g) :=
  (applyGate_preservesInner g hg).preservesNormSq


/-! ============================================================
    Circuit preservation
============================================================ -/

/--
Every well-formed circuit preserves the quantum inner product.
-/
theorem run_preservesInner
    (c : Circuit)
    (hc : CircuitWellFormed c) :
    PreservesInner (run c) := by
  induction c with

  | nil =>
      exact preservesInner_id

  | cons g c ih =>
      have hg :
          Gate.WellFormed g :=
        ((circuitWellFormed_cons g c).mp hc).1

      have hc' :
          CircuitWellFormed c :=
        ((circuitWellFormed_cons g c).mp hc).2

      have hgate :
          PreservesInner (applyGate g) :=
        applyGate_preservesInner g hg

      have hrest :
          PreservesInner (run c) :=
        ih hc'

      simpa [run] using
        hgate.comp hrest


/-! ============================================================
    Circuit adjoints cancel
============================================================ -/

/-- Running a well-formed circuit and then its adjoint is the identity. -/
theorem run_adjoint_run
    (c : Circuit) (hc : CircuitWellFormed c) (psi : State) :
    run (Circuit.adjoint c) (run c psi) = psi := by
  induction c generalizing psi with
  | nil => simp
  | cons g c ih =>
      have hg : g.WellFormed :=
        ((circuitWellFormed_cons g c).mp hc).1
      have hc' : CircuitWellFormed c :=
        ((circuitWellFormed_cons g c).mp hc).2
      rw [run_cons, circuit_adjoint_cons, run_append, run_singleton]
      rw [ih hc']
      exact applyGate_adjoint_applyGate g hg psi

/-- Running a well-formed circuit adjoint and then the original circuit is
also the identity. -/
theorem run_run_adjoint
    (c : Circuit) (hc : CircuitWellFormed c) (psi : State) :
    run c (run (Circuit.adjoint c) psi) = psi := by
  have hadj : CircuitWellFormed (Circuit.adjoint c) :=
    (circuitWellFormed_adjoint c).2 hc
  have h := run_adjoint_run (Circuit.adjoint c) hadj psi
  simpa using h


/--
Every well-formed circuit preserves total Born mass / squared norm.
-/
theorem run_preservesNormSq
    (c : Circuit)
    (hc : CircuitWellFormed c) :
    PreservesNormSq (run c) :=
  (run_preservesInner c hc).preservesNormSq


/--
Pointwise form, often more convenient downstream.
-/
theorem normSq_run
    (c : Circuit)
    (hc : CircuitWellFormed c)
    (ψ : State) :
    normSq (run c ψ) =
      normSq ψ :=
  run_preservesNormSq c hc ψ


/--
In particular, running a well-formed circuit on a computational basis
state produces a normalized quantum state.
-/
theorem normSq_run_ket
    (c : Circuit)
    (hc : CircuitWellFormed c)
    (s : BasisState) :
    normSq (run c (ket s)) = 1 := by
  rw [normSq_run c hc]
  simp

end
end ShorECDLP.Quantum
