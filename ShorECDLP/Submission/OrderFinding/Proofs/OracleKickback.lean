import ShorECDLP.Submission.OrderFinding.Proofs.CyclicEigenstates

namespace ShorECDLP.Quantum.OrderFinding

open PhaseEstimation
open scoped BigOperators

theorem pointEigenstate_shift
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (pointReg : List Wire)
    (s : BasisState)
    (hr : Nat.Prime r)
    (horder : addOrderOf P = r)
    (t : ℕ)
    (k : Fin r) :
    (∑ j : Fin r,
        eigenvalue
            (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ)) •
          ket
            (writeReg pointReg
              (enc.encode (j.val • P + t • P)).val s)) =
      eigenvalue
          (((k.val * t : ℕ) : ℝ) / (r : ℝ)) •
        ∑ j : Fin r,
          eigenvalue
              (-((k.val * j.val : ℕ) : ℝ) / (r : ℝ)) •
            ket
              (writeReg pointReg
                (enc.encode (j.val • P)).val s) := by
  classical
  letI : NeZero r := ⟨hr.ne_zero⟩

  let shift : Fin r → Fin r :=
    fun j => ⟨(j.val + t) % r, Nat.mod_lt _ hr.pos⟩

  have hshift_inj : Function.Injective shift := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change (i.val + t) % r = (j.val + t) % r at hv
    have hz :
        ((i.val + t : ℕ) : ZMod r) =
          ((j.val + t : ℕ) : ZMod r) := by
      have hz' :
          (((i.val + t) % r : ℕ) : ZMod r) =
            (((j.val + t) % r : ℕ) : ZMod r) :=
        congrArg (fun n : ℕ => (n : ZMod r)) hv
      simpa only [ZMod.natCast_mod] using hz'
    have hz' :
        (i.val : ZMod r) + (t : ZMod r) =
          (j.val : ZMod r) + (t : ZMod r) := by
      simpa only [Nat.cast_add] using hz
    have hij' : (i.val : ZMod r) = (j.val : ZMod r) :=
      add_right_cancel hz'
    have hm :=
      (ZMod.natCast_eq_natCast_iff' i.val j.val r).mp hij'
    simpa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hm

  have hshift_surj : Function.Surjective shift :=
    (Finite.injective_iff_surjective.mp hshift_inj)

  let e : Fin r ≃ Fin r :=
    Equiv.ofBijective shift ⟨hshift_inj, hshift_surj⟩

  have heval (j : Fin r) :
      (e j).val = (j.val + t) % r := by
    rfl

  have hshiftZ (j : Fin r) :
      ((e j).val : ZMod r) =
        (j.val : ZMod r) + (t : ZMod r) := by
    calc
      ((e j).val : ZMod r) =
          (((j.val + t) % r : ℕ) : ZMod r) := by
            rw [heval]
      _ = ((j.val + t : ℕ) : ZMod r) := by
            rw [ZMod.natCast_mod]
      _ = (j.val : ZMod r) + (t : ZMod r) := by
            push_cast
            rfl

  have hpoint (j : Fin r) :
      j.val • P + t • P = (e j).val • P := by
    calc
      j.val • P + t • P = (j.val + t) • P := by
        rw [add_nsmul]
      _ = ((j.val + t) % addOrderOf P) • P := by
        symm
        exact mod_addOrderOf_nsmul P (j.val + t)
      _ = ((j.val + t) % r) • P := by
        rw [horder]
      _ = (e j).val • P := by
        rw [heval]

  have hphase_pos (n : ℕ) :
      eigenvalue ((n : ℝ) / (r : ℝ)) =
        ZMod.stdAddChar (n : ZMod r) := by
    simpa using
      eigenvalue_int_div_eq_stdAddChar (r := r) (n : ℤ)

  have hphase_neg (n : ℕ) :
      eigenvalue (-(n : ℝ) / (r : ℝ)) =
        ZMod.stdAddChar (-(n : ZMod r)) := by
    simpa using
      eigenvalue_int_div_eq_stdAddChar (r := r) (-(n : ℤ))

  rw [Finset.smul_sum]

  refine Fintype.sum_equiv e _ _ fun j => ?_

  rw [hpoint j, smul_smul]

  congr 1

  rw [
    hphase_neg,
    hphase_pos,
    hphase_neg,
    ← AddChar.map_add_eq_mul
  ]

  congr 1

  push_cast
  rw [hshiftZ j]
  ring

private theorem labelState_ket
    (reg : List Wire) (x : ℕ) (s : BasisState) :
    labelState reg x (ket s) =
      ket (writeReg reg x s) := by
  classical
  simp [labelState, ket]

private theorem upd_comm
    (s : BasisState) (i j : Wire) (bi bj : Bool)
    (h : i ≠ j) :
    (s[i ↦ bi])[j ↦ bj] = (s[j ↦ bj])[i ↦ bi] := by
  funext x
  by_cases hxi : x = i
  · subst x
    simp [upd, h]
  · by_cases hxj : x = j
    · subst x
      simp [upd, hxi]
    · simp [upd, hxi, hxj]

private theorem writeReg_apply_not_mem
    (reg : List Wire) (x : ℕ) (s : BasisState)
    {q : Wire} (hq : q ∉ reg) :
    writeReg reg x s q = s q := by
  induction reg generalizing x s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hq
      simp only [writeReg]
      rw [ih (x := x / 2) (s := s[w ↦ x.testBit 0]) hq.2]
      exact upd_other s w _ hq.1

private theorem writeReg_upd_not_mem
    (reg : List Wire) (x : ℕ) (s : BasisState)
    (q : Wire) (b : Bool) (hq : q ∉ reg) :
    writeReg reg x s[q ↦ b] =
      (writeReg reg x s)[q ↦ b] := by
  induction reg generalizing x s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hq
      simp only [writeReg]
      rw [upd_comm s q w b (x.testBit 0) hq.1]
      exact ih (x := x / 2)
        (s := s[w ↦ x.testBit 0]) hq.2

private theorem writeReg_comm_of_disjoint
    (r₁ r₂ : List Wire) (x y : ℕ) (s : BasisState)
    (h : List.Disjoint r₁ r₂) :
    writeReg r₁ x (writeReg r₂ y s) =
      writeReg r₂ y (writeReg r₁ x s) := by
  induction r₁ generalizing x s with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ r₂ := by
        intro hw
        aesop
      have hws : List.Disjoint ws r₂ := by
        intro a ha b
        aesop
      simp only [writeReg]
      rw [← writeReg_upd_not_mem r₂ y s w (x.testBit 0) hw]
      exact ih (x := x / 2) (s := s[w ↦ x.testBit 0]) hws

private theorem writeReg_overwrite
    (reg : List Wire) (x y : ℕ) (s : BasisState)
    (hnd : reg.Nodup) :
    writeReg reg y (writeReg reg x s) =
      writeReg reg y s := by
  induction reg generalizing x y s with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ ws := (List.nodup_cons.mp hnd).1
      have hws : ws.Nodup := (List.nodup_cons.mp hnd).2
      simp only [writeReg]
      rw [← writeReg_upd_not_mem ws (x / 2)
        (s[w ↦ x.testBit 0]) w (y.testBit 0) hw]
      rw [ih (x := x / 2) (y := y / 2)
        (s := (s[w ↦ x.testBit 0])[w ↦ y.testBit 0]) hws]
      congr 1
      funext q
      by_cases hq : q = w
      · subst q
        simp
      · simp [upd, hq]

private theorem regValue_writeReg_disjoint
    (r₁ r₂ : List Wire) (x : ℕ) (s : BasisState)
    (h : List.Disjoint r₁ r₂) :
    regValue r₁ (writeReg r₂ x s) =
      regValue r₁ s := by
  induction r₁ with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ r₂ := by
        intro hw
        aesop
      have hws : List.Disjoint ws r₂ := by
        intro a ha b
        aesop
      rw [regValue_cons, regValue_cons]
      rw [writeReg_apply_not_mem r₂ x s hw]
      rw [ih hws]

private theorem clean_writeReg_disjoint
    (work reg : List Wire) (x : ℕ) (s : BasisState)
    (hclean : Clean work s)
    (h : List.Disjoint work reg) :
    Clean work (writeReg reg x s) := by
  intro q hq
  rw [writeReg_apply_not_mem reg x s]
  · exact hclean q hq
  · intro hqr
    aesop
private theorem eigenvalue_add_kickback
    (x y : ℝ) :
    eigenvalue (x + y) =
      eigenvalue x * eigenvalue y := by
  unfold eigenvalue
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem eigenvalue_add_one
    (x : ℝ) :
    eigenvalue (x + 1) = eigenvalue x := by
  unfold eigenvalue
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨1, ?_⟩
  push_cast
  ring

private theorem eigenvalue_add_nat
    (x : ℝ) :
    ∀ n : ℕ, eigenvalue (x + n) = eigenvalue x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        eigenvalue (x + (↑(n + 1) : ℝ)) =
            eigenvalue ((x + (n : ℝ)) + 1) := by
              congr 1
              push_cast
              ring
        _ = eigenvalue (x + (n : ℝ)) :=
          eigenvalue_add_one _
        _ = eigenvalue x := ih

private theorem eigenvalue_mod_div
    (n r : ℕ)
    (hr : 0 < r) :
    eigenvalue (((n % r : ℕ) : ℝ) / (r : ℝ)) =
      eigenvalue ((n : ℝ) / (r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hdecomp :
      ((n % r : ℕ) : ℝ) / (r : ℝ) + (n / r : ℕ) =
        (n : ℝ) / (r : ℝ) := by
    have h := Nat.mod_add_div n r
    have hR :
        (((n % r : ℕ) : ℝ) +
          (r : ℝ) * ((n / r : ℕ) : ℝ)) = n := by
      exact_mod_cast h
    field_simp [ne_of_gt hrR]
    nlinarith
  calc
    eigenvalue (((n % r : ℕ) : ℝ) / (r : ℝ)) =
        eigenvalue
          (((n % r : ℕ) : ℝ) / (r : ℝ) + (n / r : ℕ)) := by
            symm
            exact eigenvalue_add_nat _ _
    _ = eigenvalue ((n : ℝ) / (r : ℝ)) := by rw [hdecomp]

private theorem kickback_phase_eq
    {r d : ℕ}
    (hr : 0 < r)
    (k : Fin r)
    (a b : ℕ) :
    eigenvalue
        (((k.val * (a + b * d) : ℕ) : ℝ) / (r : ℝ)) =
      eigenvalue ((k.val : ℝ) / (r : ℝ)) ^ a *
        eigenvalue
          ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) ^ b := by
  rw [eigenvalue_mod_div (k.val * d) r hr]
  rw [eigenvalue_pow_eq_eigenvalue_mul,
    eigenvalue_pow_eq_eigenvalue_mul]
  rw [← eigenvalue_add_kickback]
  congr 1
  push_cast
  field_simp [Nat.ne_of_gt hr]

private theorem labelState_pointEigenstate
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState)
    (a b : ℕ)
    (k : Fin r)
    (hap : List.Disjoint aReg pointReg)
    (hbp : List.Disjoint bReg pointReg) :
    labelState bReg b
        (labelState aReg a
          (pointEigenstate enc P pointReg s k)) =
      pointEigenstate enc P pointReg
        (writeReg bReg b (writeReg aReg a s)) k := by
  classical
  unfold pointEigenstate
  rw [map_smul, map_smul]
  congr 1
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [labelState_ket, labelState_ket]
  rw [writeReg_comm_of_disjoint
    aReg pointReg a
    (enc.encode (j.val • P)).val s hap]
  rw [writeReg_comm_of_disjoint
    bReg pointReg b
    (enc.encode (j.val • P)).val
    (writeReg aReg a s) hbp]

private theorem oracle_pointEigenstate_kickback_raw
    {G : Type*} [AddCommGroup G]
    {w r d precision : ℕ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (hsetting : ECDLPSetting P Q r d)
    (hspec :
      ECDLPOracleSpec enc oracle P Q
        aReg bReg pointReg oracleWork)
    (hsetup :
      OrderFindingSetup enc aReg bReg pointReg oracleWork
        qftAncilla precision s)
    (a b : Fin (2 ^ precision))
    (k : Fin r) :
    oracle
      (pointEigenstate enc P pointReg
        (writeReg bReg b.val (writeReg aReg a.val s)) k) =
      eigenvalue
          (((k.val * (a.val + b.val * d) : ℕ) : ℝ) /
            (r : ℝ)) •
        pointEigenstate enc P pointReg
          (writeReg bReg b.val (writeReg aReg a.val s)) k := by
  classical
  let sab :=
    writeReg bReg b.val (writeReg aReg a.val s)

  have hmainWork := List.nodup_append.mp hspec.registers_nodup
  have habPoint := List.nodup_append.mp hmainWork.1
  have habRegs := List.nodup_append.mp habPoint.1

  have haNodup : aReg.Nodup := habRegs.1
  have hbNodup : bReg.Nodup := habRegs.2.1
  have hpNodup : pointReg.Nodup := habPoint.2.1

  have hab : List.Disjoint aReg bReg := by
    intro x hx hy
    exact (habRegs.2.2 x hx x hy) rfl

  have hap : List.Disjoint aReg pointReg := by
    intro x hx hy
    exact (habPoint.2.2 x (by simp [hx]) x hy) rfl

  have haw : List.Disjoint aReg oracleWork := by
    intro x hx hy
    exact (hmainWork.2.2 x (by simp [hx]) x hy) rfl

  have hbp : List.Disjoint bReg pointReg := by
    intro x hx hy
    exact (habPoint.2.2 x (by simp [hx]) x hy) rfl

  have hbw : List.Disjoint bReg oracleWork := by
    intro x hx hy
    exact (hmainWork.2.2 x (by simp [hx]) x hy) rfl

  have hpw : List.Disjoint pointReg oracleWork := by
    intro x hx hy
    exact (hmainWork.2.2 x (by simp [hx]) x hy) rfl

  have haSab :
      regValue aReg sab = a.val := by
    dsimp [sab]
    rw [regValue_writeReg_disjoint aReg bReg b.val
      (writeReg aReg a.val s) hab]
    exact regValue_writeReg_of_lt
      aReg a.val s haNodup
      (by simp [hsetup.a_width])

  have hbSab :
      regValue bReg sab = b.val := by
    dsimp [sab]
    exact regValue_writeReg_of_lt
      bReg b.val (writeReg aReg a.val s) hbNodup
      (by simp [hsetup.b_width])

  have hcleanSab :
      Clean oracleWork sab := by
    dsimp [sab]
    exact clean_writeReg_disjoint
      oracleWork bReg b.val
      (writeReg aReg a.val s)
      (clean_writeReg_disjoint
        oracleWork aReg a.val s
        hsetup.oracleWork_zero haw.symm)
      hbw.symm

  unfold pointEigenstate
  rw [map_smul, map_sum]
  simp_rw [map_smul]

  have horacle :
      ∀ j : Fin r,
        oracle
            (ket
              (writeReg pointReg
                (enc.encode (j.val • P)).val sab)) =
          ket
            (writeReg pointReg
              (enc.encode
                (j.val • P +
                  (a.val + b.val * d) • P)).val sab) := by
    intro j

    have hp :
        regValue pointReg
            (writeReg pointReg
              (enc.encode (j.val • P)).val sab) =
          (enc.encode (j.val • P)).val := by
      exact regValue_writeReg_of_lt
        pointReg
        (enc.encode (j.val • P)).val
        sab hpNodup
        (by
          rw [hspec.point_width]
          exact (enc.encode (j.val • P)).isLt)

    have ha :
        regValue aReg
            (writeReg pointReg
              (enc.encode (j.val • P)).val sab) =
          a.val := by
      rw [regValue_writeReg_disjoint
        aReg pointReg _ sab hap]
      exact haSab

    have hb :
        regValue bReg
            (writeReg pointReg
              (enc.encode (j.val • P)).val sab) =
          b.val := by
      rw [regValue_writeReg_disjoint
        bReg pointReg _ sab hbp]
      exact hbSab

    have hc :
        Clean oracleWork
          (writeReg pointReg
            (enc.encode (j.val • P)).val sab) := by
      exact clean_writeReg_disjoint
        oracleWork pointReg _ sab
        hcleanSab hpw.symm

    have h :=
      hspec.onKet
        (writeReg pointReg
          (enc.encode (j.val • P)).val sab)
        a.val b.val (j.val • P) ha hb hp hc

    rw [writeReg_overwrite
      pointReg
      (enc.encode (j.val • P)).val
      (enc.encode
        (j.val • P +
          ecdlpFunction P Q a.val b.val)).val
      sab hpNodup] at h

    simpa [ecdlpFunction, hsetting.Q_eq,
      mul_nsmul, add_nsmul, Nat.mul_comm] using h

  dsimp [sab] at horacle
  simp only [horacle]

  rw [pointEigenstate_shift
    enc P pointReg sab
    hsetting.prime_order hsetting.order_P
    (a.val + b.val * d) k]

  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem oracle_pointEigenstate_kickback
    {G : Type*} [AddCommGroup G]
    {w r d precision : ℕ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (hsetting : ECDLPSetting P Q r d)
    (hspec :
      ECDLPOracleSpec enc oracle P Q
        aReg bReg pointReg oracleWork)
    (hsetup :
      OrderFindingSetup enc aReg bReg pointReg oracleWork
        qftAncilla precision s)
    (a b : Fin (2 ^ precision))
    (k : Fin r) :
    oracle
        (labelState bReg b.val
          (labelState aReg a.val
            (pointEigenstate enc P pointReg s k))) =
      (eigenvalue
          ((k.val : ℝ) / (r : ℝ)) ^ a.val *
        eigenvalue
          ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) ^ b.val) •
        labelState bReg b.val
          (labelState aReg a.val
            (pointEigenstate enc P pointReg s k)) := by
  classical

  have hmainWork := List.nodup_append.mp hspec.registers_nodup
  have habPoint := List.nodup_append.mp hmainWork.1
  have habRegs := List.nodup_append.mp habPoint.1

  have hap : List.Disjoint aReg pointReg := by
    intro x hx hy
    exact (habPoint.2.2 x (by simp [hx]) x hy) rfl

  have hbp : List.Disjoint bReg pointReg := by
    intro x hx hy
    exact (habPoint.2.2 x (by simp [hx]) x hy) rfl

  have hlabel :=
    labelState_pointEigenstate
      enc P aReg bReg pointReg s
      a.val b.val k hap hbp

  rw [hlabel]

  rw [oracle_pointEigenstate_kickback_raw
    enc oracle P Q
    aReg bReg pointReg oracleWork
    qftAncilla s
    hsetting hspec hsetup a b k]

  rw [kickback_phase_eq
    hsetting.prime_order.pos k a.val b.val]

theorem labelState_pointEigenstate_comm
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState)
    (a b : ℕ)
    (k : Fin r)
    (hab : List.Disjoint aReg bReg)
    (hap : List.Disjoint aReg pointReg)
    (hbp : List.Disjoint bReg pointReg) :
    labelState bReg b
        (labelState aReg a
          (pointEigenstate enc P pointReg s k)) =
      labelState aReg a
        (labelState bReg b
          (pointEigenstate enc P pointReg s k)) := by
  rw [labelState_pointEigenstate
    enc P aReg bReg pointReg s a b k hap hbp]
  rw [labelState_pointEigenstate
    enc P bReg aReg pointReg s b a k hbp hap]
  apply congrArg
    (fun t : BasisState => pointEigenstate enc P pointReg t k)
  exact writeReg_comm_of_disjoint
    bReg aReg b a s hab.symm
