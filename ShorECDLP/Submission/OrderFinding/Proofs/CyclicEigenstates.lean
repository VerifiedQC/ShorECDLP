import ShorECDLP.Submission.OrderFinding.Defs
import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Main
import Mathlib.Analysis.Fourier.ZMod

namespace ShorECDLP.Quantum.OrderFinding

open PhaseEstimation
open scoped BigOperators

noncomputable def pointEigenstate
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (pointReg : List Wire)
    (s : BasisState)
    (k : Fin r) : State :=
  (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
    ∑ j : Fin r,
      eigenvalue
          (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ)) •
        ket
          (writeReg pointReg
            (enc.encode (j.val • P)).val s)

theorem writeReg_eq_setReg
    (r : List Wire) (y : Nat) (s : BasisState) :
    writeReg r y s = setReg r y s := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [writeReg, setReg]
      have hbit : y.testBit 0 = (y % 2 == 1) := by
        rw [Nat.testBit_zero]
        by_cases h : y % 2 = 1 <;> simp [h]
      rw [hbit]
      exact ih (y := y / 2) (s := s[w ↦ (y % 2 == 1)])

theorem setReg_not_mem
    (r : List Wire) (y : Nat) (s : BasisState)
    {i : Wire} (hi : i ∉ r) :
    setReg r y s i = s i := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hi
      simp only [setReg]
      rw [ih (y := y / 2) (s := s[w ↦ (y % 2 == 1)]) hi.2]
      exact upd_other s w _ hi.1

theorem regValue_setReg_of_lt
    (r : List Wire) (y : Nat) (s : BasisState)
    (hnd : r.Nodup)
    (hy : y < 2 ^ r.length) :
    regValue r (setReg r y s) = y := by
  induction r generalizing y s with
  | nil =>
      simp only [List.length_nil, pow_zero] at hy
      have : y = 0 := by omega
      subst y
      rfl
  | cons w ws ih =>
      have hw : w ∉ ws := (List.nodup_cons.mp hnd).1
      have hws : ws.Nodup := (List.nodup_cons.mp hnd).2
      have hpow : 2 ^ (w :: ws).length = 2 * 2 ^ ws.length := by
        simp [pow_succ, Nat.mul_comm]
      have hy' : y / 2 < 2 ^ ws.length := by
        rw [hpow] at hy
        omega
      simp only [setReg]
      rw [regValue_cons]
      rw [setReg_not_mem ws (y / 2) (s[w ↦ (y % 2 == 1)]) hw]
      rw [upd_same]
      rw [ih (y := y / 2) (s := s[w ↦ (y % 2 == 1)]) hws hy']
      have hmod : y % 2 < 2 := Nat.mod_lt _ (by omega)
      have hdiv := Nat.mod_add_div y 2
      by_cases hodd : y % 2 = 1
      · simp [hodd]
        omega
      · have heven : y % 2 = 0 := by omega
        simp [heven]
        omega

theorem regValue_writeReg_of_lt
    (r : List Wire) (y : Nat) (s : BasisState)
    (hnd : r.Nodup)
    (hy : y < 2 ^ r.length) :
    regValue r (writeReg r y s) = y := by
  rw [writeReg_eq_setReg]
  exact regValue_setReg_of_lt r y s hnd hy

theorem writeReg_regValue
    (r : List Wire) (s : BasisState)
    (hnd : r.Nodup) :
    writeReg r (regValue r s) s = s := by
  induction r generalizing s with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ ws := (List.nodup_cons.mp hnd).1
      have hws : ws.Nodup := (List.nodup_cons.mp hnd).2
      cases hs : s w
      · have hreg :
          regValue (w :: ws) s = 2 * regValue ws s := by
          simp [regValue_cons, hs]
        rw [hreg]
        simp only [writeReg]
        have hbit :
            (2 * regValue ws s).testBit 0 = false := by
          rw [Nat.testBit_zero]
          simp
        rw [hbit]
        have htail :
            regValue ws (s[w ↦ false]) = regValue ws s :=
          regValue_upd_not_mem ws s w false hw
        have hi :=
          ih (s := s[w ↦ false]) hws
        rw [htail] at hi
        have hsame : s[w ↦ false] = s := by
          funext i
          by_cases hiw : i = w
          · subst i
            simp [upd, hs]
          · simp [upd, hiw]
        simpa [hsame] using hi
      · have hreg :
          regValue (w :: ws) s = 1 + 2 * regValue ws s := by
          simp [regValue_cons, hs]
        rw [hreg]
        simp only [writeReg]
        have hbit :
            (1 + 2 * regValue ws s).testBit 0 = true := by
          rw [Nat.testBit_zero]
          simp
        rw [hbit]
        have hdiv : (1 + 2 * regValue ws s) / 2 = regValue ws s := by
          omega
        rw [hdiv]
        have htail :
            regValue ws (s[w ↦ true]) = regValue ws s :=
          regValue_upd_not_mem ws s w true hw
        have hi :=
          ih (s := s[w ↦ true]) hws
        rw [htail] at hi
        have hsame : s[w ↦ true] = s := by
          funext i
          by_cases hiw : i = w
          · subst i
            simp [upd, hs]
          · simp [upd, hiw]
        simpa [hsame] using hi

 theorem pointBasis_injective
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (pointReg : List Wire)
    (s : BasisState)
    (horder : addOrderOf P = r)
    (hwidth : pointReg.length = w)
    (hnd : pointReg.Nodup) :
    Function.Injective
      (fun j : Fin r =>
        writeReg pointReg
          (enc.encode (j.val • P)).val s) := by
  intro j t h
  have hjlt :
      (enc.encode (j.val • P)).val < 2 ^ pointReg.length := by
    rw [hwidth]
    exact (enc.encode (j.val • P)).isLt
  have htlt :
      (enc.encode (t.val • P)).val < 2 ^ pointReg.length := by
    rw [hwidth]
    exact (enc.encode (t.val • P)).isLt
  have hval :
      (enc.encode (j.val • P)).val =
        (enc.encode (t.val • P)).val := by
    have :=
      congrArg (regValue pointReg) h
    rw [
      regValue_writeReg_of_lt pointReg
        (enc.encode (j.val • P)).val s hnd hjlt,
      regValue_writeReg_of_lt pointReg
        (enc.encode (t.val • P)).val s hnd htlt
    ] at this
    exact this
  have henc :
      enc.encode (j.val • P) =
        enc.encode (t.val • P) := by
    apply Fin.ext
    exact hval
  have hpoint :
      j.val • P = t.val • P :=
    enc.injective henc
  have hj : j.val < addOrderOf P := by
    simp[horder]
  have ht : t.val < addOrderOf P := by
    simp[horder]
  have hnat :
      j.val = t.val :=
    nsmul_injOn_Iio_addOrderOf hj ht hpoint
  exact Fin.ext hnat

 theorem inner_pointBasis
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (pointReg : List Wire)
    (s : BasisState)
    (horder : addOrderOf P = r)
    (hwidth : pointReg.length = w)
    (hnd : pointReg.Nodup)
    (j t : Fin r) :
    inner
        (ket
          (writeReg pointReg
            (enc.encode (j.val • P)).val s))
        (ket
          (writeReg pointReg
            (enc.encode (t.val • P)).val s)) =
      if j = t then 1 else 0 := by
  by_cases h : j = t
  · subst t
    simp
  · have hne :
      writeReg pointReg
          (enc.encode (j.val • P)).val s ≠
        writeReg pointReg
          (enc.encode (t.val • P)).val s := by
      intro heq
      exact h (pointBasis_injective
        enc P pointReg s horder hwidth hnd heq)
    simp [h, hne]

 theorem eigenvalue_add
    (x y : ℝ) :
    eigenvalue (x + y) =
      eigenvalue x * eigenvalue y := by
  unfold eigenvalue
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

 theorem eigenvalue_neg
    (x : ℝ) :
    eigenvalue (-x) = (eigenvalue x)⁻¹ := by
  unfold eigenvalue
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

 theorem star_eigenvalue
    (x : ℝ) :
    starRingEnd ℂ (eigenvalue x) =
      eigenvalue (-x) := by
  unfold eigenvalue
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

 theorem eigenvalue_int_div_eq_stdAddChar
    {r : ℕ}
    [NeZero r]
    (z : ℤ) :
    eigenvalue ((z : ℝ) / (r : ℝ)) =
      ZMod.stdAddChar (z : ZMod r) := by
  rw [ZMod.stdAddChar_coe]
  unfold eigenvalue
  congr 1
  push_cast
  ring

 theorem sum_stdAddChar_mul
    {r : ℕ}
    [NeZero r]
    (t : ZMod r) :
    (∑ j : ZMod r, ZMod.stdAddChar (t * j)) =
      if t = 0 then (r : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp only [ht, if_true, zero_mul, AddChar.map_zero_eq_one,
      Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · simp only [if_neg ht]
    exact
      AddChar.sum_eq_zero_of_ne_one
        (ZMod.isPrimitive_stdAddChar r ht)

 theorem character_sum
    {r : ℕ}
    (hr : Nat.Prime r)
    (k l : Fin r) :
    (∑ j : Fin r,
        starRingEnd ℂ
            (eigenvalue
              (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ))) *
          eigenvalue
            (-((l.val * j.val : ℕ) : ℝ) / (r : ℝ))) =
      if k = l then (r : ℂ) else 0 := by
  have hr0 : 0 < r := hr.pos
  letI : NeZero r := ⟨Nat.ne_of_gt hr0⟩
  have hterm :
      ∀ j : Fin r,
        starRingEnd ℂ
            (eigenvalue
              (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ))) *
          eigenvalue
            (-((l.val * j.val : ℕ) : ℝ) / (r : ℝ)) =
        ZMod.stdAddChar
          (((k.val : ZMod r) - (l.val : ZMod r)) * (j.val : ZMod r)) := by
    intro j
    rw [star_eigenvalue]
    rw [← eigenvalue_add]
    calc
      eigenvalue
          (-(-↑(k.val * j.val : ℕ) / ↑r) +
            -↑(l.val * j.val : ℕ) / ↑r) =
        eigenvalue ((((k.val : ℤ) - (l.val : ℤ)) * (j.val : ℤ) : ℤ) /
            (r : ℝ)) := by
          congr 1
          push_cast
          ring
      _ = ZMod.stdAddChar
          (((((k.val : ℤ) - (l.val : ℤ)) * (j.val : ℤ) : ℤ) : ZMod r)) := by
          rw [eigenvalue_int_div_eq_stdAddChar]
      _ = ZMod.stdAddChar
          (((k.val : ZMod r) - (l.val : ZMod r)) * (j.val : ZMod r)) := by
          congr 1
          push_cast
          ring
  simp_rw [hterm]
  rw [Fintype.sum_equiv (ZMod.finEquiv r).toEquiv]
  · have h :=
      sum_stdAddChar_mul
        ((k.val : ZMod r) - (l.val : ZMod r))
    rw [h]
    by_cases hkl : k = l
    · subst l
      simp
    · have hne :
        (k.val : ZMod r) - (l.val : ZMod r) ≠ 0 := by
        intro hz
        have hz' :
            (k.val : ZMod r) = (l.val : ZMod r) := sub_eq_zero.mp hz
        have hklt := k.isLt
        have hllt := l.isLt
        have hv :
            k.val = l.val := by
          rw [ZMod.natCast_eq_natCast_iff'] at hz'
          simpa [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hllt] using hz'
        exact hkl (Fin.ext hv)
      simp [hkl, hne]
  · intro j
    have hjcast :
        (j.val : ZMod r) = (ZMod.finEquiv r).toEquiv j := by
      apply ZMod.val_injective r
      cases r with
      | zero => exact False.elim (Nat.not_lt_zero _ j.isLt)
      | succ n =>
          cases j with
          | mk val hlt =>
              simp [ZMod.finEquiv, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
              change val = val
              rfl
    rw [hjcast]

 theorem inner_sum_left
    {ι : Type*} [Fintype ι]
    (f : ι → State)
    (φ : State) :
    inner (∑ i, f i) φ =
      ∑ i, inner (f i) φ := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp [ha, inner_add_left, ih]

 theorem inner_sum_right
    {ι : Type*} [Fintype ι]
    (ψ : State)
    (f : ι → State) :
    inner ψ (∑ i, f i) =
      ∑ i, inner ψ (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp [ha, inner_add_right, ih]

theorem pointEigenstate_orthonormal
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (pointReg : List Wire)
    (s : BasisState)
    (hr : Nat.Prime r)
    (horder : addOrderOf P = r)
    (hwidth : pointReg.length = w)
    (hnd : pointReg.Nodup)
    (k l : Fin r) :
    inner
        (pointEigenstate enc P pointReg s k)
        (pointEigenstate enc P pointReg s l) =
      if k = l then 1 else 0 := by
  have hr0 : 0 < r := hr.pos
  have hsqrt : Real.sqrt r ≠ 0 := by
    positivity
  unfold pointEigenstate
  rw [inner_smul_smul]
  rw [inner_sum_left]
  simp_rw [inner_sum_right]
  simp_rw [inner_smul_smul]
  simp_rw [inner_pointBasis enc P pointReg s horder hwidth hnd]
  simp only [mul_ite, mul_one, mul_zero]
  simp
  have hchar := character_sum hr k l
  simp only [Nat.cast_mul] at hchar
  rw [hchar]
  by_cases hkl : k = l
  · subst l
    simp only [if_true]
    have hsqrt_sq :
        Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) = r := by
      rw [Real.mul_self_sqrt]
      positivity
    have hcR :
        (Real.sqrt (r : ℝ))⁻¹ *
            (Real.sqrt (r : ℝ))⁻¹ * (r : ℝ) = 1 := by
      field_simp [hsqrt]
      nlinarith [hsqrt_sq]
    exact_mod_cast hcR
  · simp [hkl]

 theorem character_sum_zero_index
    {r : ℕ}
    (hr : Nat.Prime r)
    (j : Fin r) :
    (∑ k : Fin r,
        eigenvalue
          (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ))) =
      if j.val = 0 then (r : ℂ) else 0 := by
  have hr0 : 0 < r := hr.pos
  letI : NeZero r := ⟨Nat.ne_of_gt hr0⟩
  have hterm :
      ∀ k : Fin r,
        eigenvalue
            (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ)) =
          ZMod.stdAddChar
            (-((j.val : ZMod r) * (k.val : ZMod r))) := by
    intro k
    calc
      eigenvalue (-↑(k.val * j.val : ℕ) / ↑r) =
        eigenvalue ((-((k.val : ℤ) * (j.val : ℤ)) : ℤ) / (r : ℝ)) := by
          congr 1
          push_cast
          ring
      _ = ZMod.stdAddChar
          (((-((k.val : ℤ) * (j.val : ℤ)) : ℤ) : ZMod r)) := by
          rw [eigenvalue_int_div_eq_stdAddChar]
      _ = ZMod.stdAddChar
          (-((j.val : ZMod r) * (k.val : ZMod r))) := by
          congr 1
          push_cast
          ring
  simp_rw [hterm]
  rw [Fintype.sum_equiv (ZMod.finEquiv r).toEquiv]
  · have h :=
      sum_stdAddChar_mul
        (-(j.val : ZMod r))
    rw [h]
    by_cases hj : j.val = 0
    · simp [hj]
    · have hjz :
        -(j.val : ZMod r) ≠ 0 := by
        intro hz
        have hz' : (j.val : ZMod r) = 0 := by
          simpa using neg_eq_zero.mp hz
        have :
            j.val % r = 0 := by
          rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff'] at hz'
          simpa using hz'
        have hval : j.val = 0 := by
          simpa [Nat.mod_eq_of_lt j.isLt] using this
        exact hj hval
      simp [hj, hjz]
  · intro k
    have hkcast :
        (k.val : ZMod r) = (ZMod.finEquiv r).toEquiv k := by
      apply ZMod.val_injective r
      cases r with
      | zero => exact False.elim (Nat.not_lt_zero _ k.isLt)
      | succ n =>
          cases k with
          | mk val hlt =>
              simp [ZMod.finEquiv, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
              change val = val
              rfl
    rw [hkcast]
    rw [neg_mul]

theorem ket_eq_pointEigenstate_average
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (pointReg : List Wire)
    (s : BasisState)
    (hr : Nat.Prime r)
    (_horder : addOrderOf P = r)
    (hwidth : pointReg.length = w)
    (hnd : pointReg.Nodup)
    (hzero :
      regValue pointReg s = (enc.encode (0 : G)).val) :
    ket s =
      (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
        ∑ k : Fin r,
          pointEigenstate enc P pointReg s k := by
  have hr0 : 0 < r := hr.pos
  have hsqrt : Real.sqrt r ≠ 0 := by
    positivity
  have henc0lt :
      (enc.encode (0 : G)).val < 2 ^ pointReg.length := by
    rw [hwidth]
    exact (enc.encode (0 : G)).isLt
  have hwrite0 :
      writeReg pointReg (enc.encode (0 : G)).val s = s := by
    rw [← hzero]
    exact writeReg_regValue pointReg s hnd
  unfold pointEigenstate
  rw [Finset.smul_sum]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Eq.symm
  calc
    ∑ j : Fin r,
      ∑ k : Fin r,
        (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
          (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
            (eigenvalue
                (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ)) •
              ket
                (writeReg pointReg
                  (enc.encode (j.val • P)).val s))
        =
      ∑ j : Fin r,
        (((((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
            (((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
            ∑ k : Fin r,
              eigenvalue
                (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ))) •
          ket
            (writeReg pointReg
              (enc.encode (j.val • P)).val s)) := by
          apply Finset.sum_congr rfl
          intro j _
          simp_rw [smul_smul]
          rw [← Finset.sum_smul]
          apply congrArg
            (fun z : ℂ =>
              z • ket
                (writeReg pointReg
                  (enc.encode (j.val • P)).val s))
          simp [Finset.mul_sum, mul_assoc]
    _ =
      (((((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
          (r : ℂ)) •
        ket
          (writeReg pointReg
            (enc.encode (0 • P)).val s)) := by
          rw [Finset.sum_eq_single ⟨0, hr0⟩]
          · rw [character_sum_zero_index hr ⟨0, hr0⟩]
            simp
          · intro j _ hj
            rw [character_sum_zero_index hr j]
            have hj0 : j.val ≠ 0 := by
              intro h
              apply hj
              exact Fin.ext h
            simp [hj0]
          · simp
    _ = ket s := by
      simp only [zero_nsmul, hwrite0]
      have hsqrt_sq :
          Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) = r := by
        rw [Real.mul_self_sqrt]
        positivity
      have hc :
          ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
              (((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
              (r : ℂ)) = 1 := by
        have hcR :
            (Real.sqrt (r : ℝ))⁻¹ *
                (Real.sqrt (r : ℝ))⁻¹ * (r : ℝ) = 1 := by
          field_simp [hsqrt]
          nlinarith [hsqrt_sq]
        exact_mod_cast hcR
      rw [hc, one_smul]

end ShorECDLP.Quantum.OrderFinding
