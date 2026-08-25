import ShorECDLP.Submission.OrderFinding.Proofs.FourierSampling
import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Proofs.Approximations

namespace ShorECDLP.Quantum.OrderFinding

open PhaseEstimation
open scoped BigOperators

private theorem writeReg_not_mem
    (r : List Wire) (y : Nat) (s : BasisState)
    {i : Wire} (hi : i ∉ r) :
    writeReg r y s i = s i := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hi
      simp only [writeReg]
      rw [ih (y := y / 2) (s := s[w ↦ y.testBit 0]) hi.2]
      exact upd_other s w _ hi.1

private theorem regValue_writeReg_disjoint
    (r₁ r₂ : List Wire)
    (y : Nat)
    (s : BasisState)
    (h : List.Disjoint r₁ r₂) :
    regValue r₁ (writeReg r₂ y s) = regValue r₁ s := by
  induction r₁ with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ r₂ := by
        intro hwr
        exact (List.disjoint_left.mp h) (by simp) hwr
      have hws : List.Disjoint ws r₂ := by
        rw [List.disjoint_left]
        intro x hx hxr
        exact (List.disjoint_left.mp h) (by simp [hx]) hxr
      rw [regValue_cons, regValue_cons]
      rw [writeReg_not_mem r₂ y s hw]
      rw [ih hws]

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

private theorem register_parts
    {aReg bReg pointReg work : List Wire}
    (h : (aReg ++ bReg ++ pointReg ++ work).Nodup) :
    aReg.Nodup ∧ bReg.Nodup ∧ pointReg.Nodup ∧
      List.Disjoint aReg bReg ∧
      List.Disjoint aReg pointReg ∧
      List.Disjoint bReg pointReg := by
  have hmainWork := List.nodup_append.mp h
  have habPoint := List.nodup_append.mp hmainWork.1
  have habRegs := List.nodup_append.mp habPoint.1
  refine ⟨habRegs.1, habRegs.2.1, habPoint.2.1, ?_, ?_, ?_⟩
  · intro x hxa hxb
    exact (habRegs.2.2 x hxa x hxb) rfl
  · intro x hxa hxp
    exact (habPoint.2.2 x (by simp [hxa]) x hxp) rfl
  · intro x hxb hxp
    exact (habPoint.2.2 x (by simp [hxb]) x hxp) rfl

private theorem writeReg_overwrite_local
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

private theorem writeReg_zero_eq_of_regValue_zero
    (reg : List Wire) (s : BasisState)
    (hzero : regValue reg s = 0) :
    writeReg reg 0 s = s := by
  induction reg generalizing s with
  | nil => rfl
  | cons w ws ih =>
      have hwfalse : s w = false := by
        cases hw : s w
        · rfl
        · rw [regValue_cons, hw] at hzero
          simp at hzero
      have htail : regValue ws s = 0 := by
        rw [regValue_cons, hwfalse] at hzero
        omega
      simp only [writeReg, Nat.zero_testBit, Nat.zero_div]
      have hsame : s[w ↦ false] = s := by
        funext q
        by_cases hq : q = w
        · subst q
          simp [upd, hwfalse]
        · simp [upd, hq]
      have hi := ih (s := s) htail
      simpa [hsame] using hi

private theorem labelState_eq_mapDomain
    (reg : List Wire)
    (value : Nat)
    (psi : State) :
    labelState reg value psi =
      Finsupp.mapDomain (writeReg reg value) psi := by
  classical
  unfold labelState
  rw [Finsupp.linearCombination_apply]
  unfold Finsupp.mapDomain
  apply Finsupp.sum_congr
  intro s _
  simp [ket]

private theorem writeReg_injOn_support_zero
    (reg : List Wire)
    (value : Nat)
    (psi : State)
    (hzero : ∀ s, psi s ≠ 0 → regValue reg s = 0)
    (hnd : reg.Nodup) :
    Set.InjOn (writeReg reg value) ↑psi.support := by
  intro s hs t ht hst
  have hs0 : regValue reg s = 0 :=
    hzero s (Finsupp.mem_support_iff.mp hs)
  have ht0 : regValue reg t = 0 :=
    hzero t (Finsupp.mem_support_iff.mp ht)
  have h := congrArg (writeReg reg 0) hst
  rw [writeReg_overwrite_local reg value 0 s hnd,
    writeReg_overwrite_local reg value 0 t hnd,
    writeReg_zero_eq_of_regValue_zero reg s hs0,
    writeReg_zero_eq_of_regValue_zero reg t ht0] at h
  exact h

private theorem state_normSq_eq_support_sum
    (ψ : State) :
    normSq ψ =
      ∑ s ∈ ψ.support, Complex.normSq (ψ s) := by
  classical
  have hinner :
      inner ψ ψ =
        ((∑ s ∈ ψ.support, Complex.normSq (ψ s) : ℝ) : ℂ) := by
    unfold inner
    change
      (∑ s ∈ ψ.support,
        (starRingEnd ℂ) (ψ s) * ψ s) =
      ((∑ s ∈ ψ.support, Complex.normSq (ψ s) : ℝ) : ℂ)
    push_cast
    apply Finset.sum_congr rfl
    intro s _
    exact (Complex.normSq_eq_conj_mul_self).symm
  unfold normSq
  rw [hinner]
  simp

private theorem state_normSq_smul
    (c : ℂ)
    (ψ : State) :
    normSq (c • ψ) =
      Complex.normSq c * normSq ψ := by
  unfold normSq
  rw [inner_smul_smul]
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

private def jointFilter
    (aReg bReg : List Wire)
    (a b : Nat)
    (ψ : State) : State :=
  Finsupp.filter
    (fun s =>
      regValue aReg s = a ∧ regValue bReg s = b)
    ψ

private theorem jointRegisterProbability_eq_normSq_filter
    (aReg bReg : List Wire)
    (a b : Nat)
    (ψ : State) :
    jointRegisterProbability aReg bReg a b ψ =
      normSq (jointFilter aReg bReg a b ψ) := by
  classical
  unfold jointRegisterProbability jointFilter
  rw [state_normSq_eq_support_sum]
  rw [Finsupp.support_filter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h :
      regValue aReg s = a ∧ regValue bReg s = b
  · simp [h]
  · simp [h]

private theorem jointFilter_smul
    (aReg bReg : List Wire)
    (a b : Nat)
    (c : ℂ)
    (ψ : State) :
    jointFilter aReg bReg a b (c • ψ) =
      c • jointFilter aReg bReg a b ψ := by
  classical
  ext s
  by_cases h :
      regValue aReg s = a ∧ regValue bReg s = b <;>
    simp [jointFilter, h]

private theorem jointFilter_sum
    {ι : Type*} [Fintype ι]
    (aReg bReg : List Wire)
    (a b : Nat)
    (f : ι → State) :
    jointFilter aReg bReg a b (∑ i, f i) =
      ∑ i, jointFilter aReg bReg a b (f i) := by
  classical
  ext s
  by_cases h :
      regValue aReg s = a ∧ regValue bReg s = b <;>
    simp [jointFilter, h, Finset.sum_apply]

private theorem jointFilter_labelPair
    (aReg bReg : List Wire)
    (precision : Nat)
    (haWidth : aReg.length = precision)
    (hbWidth : bReg.length = precision)
    (haNodup : aReg.Nodup)
    (hbNodup : bReg.Nodup)
    (hab : List.Disjoint aReg bReg)
    (a b x y : Fin (2 ^ precision))
    (ψ : State) :
    jointFilter aReg bReg a.val b.val
        (labelState bReg y.val
          (labelState aReg x.val ψ)) =
      if x = a ∧ y = b then
        labelState bReg y.val
          (labelState aReg x.val ψ)
      else 0 := by
  classical
  unfold jointFilter
  by_cases hxy : x = a ∧ y = b
  · rw [if_pos hxy]
    apply (Finsupp.filter_eq_self_iff _ _).mpr
    intro t ht
    have htmem :
        t ∈
          (labelState bReg y.val
            (labelState aReg x.val ψ)).support :=
      Finsupp.mem_support_iff.mpr ht
    rw [labelState_eq_mapDomain] at htmem
    have htimg := Finsupp.mapDomain_support htmem
    rcases Finset.mem_image.mp htimg with ⟨u, hu, rfl⟩
    rw [labelState_eq_mapDomain] at hu
    have huimg := Finsupp.mapDomain_support hu
    rcases Finset.mem_image.mp huimg with ⟨v, hv, rfl⟩
    have hx :
        regValue aReg
            (writeReg bReg y.val
              (writeReg aReg x.val v)) =
          x.val := by
      rw [regValue_writeReg_disjoint aReg bReg _ _ hab]
      apply regValue_writeReg_of_lt
      · exact haNodup
      · simp [haWidth]
    have hy :
        regValue bReg
            (writeReg bReg y.val
              (writeReg aReg x.val v)) =
          y.val := by
      apply regValue_writeReg_of_lt
      · exact hbNodup
      · simp [hbWidth]
    rcases hxy with ⟨rfl, rfl⟩
    exact ⟨hx, hy⟩
  · rw [if_neg hxy]
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro t htval
    by_contra ht
    have htmem :
        t ∈
          (labelState bReg y.val
            (labelState aReg x.val ψ)).support :=
      Finsupp.mem_support_iff.mpr ht
    rw [labelState_eq_mapDomain] at htmem
    have htimg := Finsupp.mapDomain_support htmem
    rcases Finset.mem_image.mp htimg with ⟨u, hu, rfl⟩
    rw [labelState_eq_mapDomain] at hu
    have huimg := Finsupp.mapDomain_support hu
    rcases Finset.mem_image.mp huimg with ⟨v, hv, rfl⟩
    have hx :
        regValue aReg
            (writeReg bReg y.val
              (writeReg aReg x.val v)) =
          x.val := by
      rw [regValue_writeReg_disjoint aReg bReg _ _ hab]
      apply regValue_writeReg_of_lt
      · exact haNodup
      · simp [haWidth]
    have hy :
        regValue bReg
            (writeReg bReg y.val
              (writeReg aReg x.val v)) =
          y.val := by
      apply regValue_writeReg_of_lt
      · exact hbNodup
      · simp [hbWidth]
    apply hxy
    constructor
    · apply Fin.ext
      exact hx.symm.trans htval.1
    · apply Fin.ext
      exact hy.symm.trans htval.2

noncomputable def characterWeight
    (r precision d : ℕ)
    (k : Fin r)
    (a b : Fin (2 ^ precision)) : ℝ :=
  Complex.normSq
      (qpeAmplitude precision
        ((k.val : ℝ) / (r : ℝ)) a.val) *
    Complex.normSq
      (qpeAmplitude precision
        ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ))
        b.val)

private def RegisterZero
    (reg : List Wire)
    (ψ : State) : Prop :=
  ∀ s, ψ s ≠ 0 → regValue reg s = 0

private theorem normSq_labelState_clean
    (reg : List Wire)
    (psi : State)
    (value : Nat)
    (hzero : RegisterZero reg psi)
    (hnd : reg.Nodup) :
    normSq (labelState reg value psi) = normSq psi := by
  classical
  let f : BasisState → BasisState := writeReg reg value
  have hinj : Set.InjOn f ↑psi.support := by
    simpa [f] using
      writeReg_injOn_support_zero reg value psi hzero hnd
  rw [labelState_eq_mapDomain]
  change normSq (Finsupp.mapDomain f psi) = normSq psi
  rw [state_normSq_eq_support_sum, state_normSq_eq_support_sum]
  rw [Finsupp.mapDomain_support_of_injOn psi hinj]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finsupp.mapDomain_apply' (↑psi.support) (f := f) psi
    Set.Subset.rfl hinj hs]

private theorem registerZero_ket
    (reg : List Wire)
    (s : BasisState)
    (hzero : regValue reg s = 0) :
    RegisterZero reg (ket s) := by
  intro t ht
  by_cases h : t = s
  · subst t
    exact hzero
  · have hz : ket s t = 0 := ket_ne (fun hst => h hst.symm)
    exact (ht hz).elim

private theorem registerZero_smul
    (reg : List Wire)
    (c : ℂ)
    (ψ : State)
    (hψ : RegisterZero reg ψ) :
    RegisterZero reg (c • ψ) := by
  intro s hs
  apply hψ s
  intro hz
  apply hs
  simp [hz]

private theorem registerZero_sum
    {ι : Type*} [Fintype ι]
    (reg : List Wire)
    (f : ι → State)
    (hf : ∀ i, RegisterZero reg (f i)) :
    RegisterZero reg (∑ i, f i) := by
  classical
  intro s hs
  by_contra hreg
  have hz : ∀ i, f i s = 0 := by
    intro i
    by_contra hi
    exact hreg (hf i s hi)
  apply hs
  simp [Finset.sum_apply, hz]

private theorem pointEigenstate_registerZero
    {G : Type*} [AddCommGroup G]
    {w r : Nat}
    (enc : PointEncoding G w)
    (P : G)
    (pointReg reg : List Wire)
    (s : BasisState)
    (hdisj : List.Disjoint reg pointReg)
    (hzero : regValue reg s = 0)
    (k : Fin r) :
    RegisterZero reg
      (pointEigenstate enc P pointReg s k) := by
  unfold pointEigenstate
  apply registerZero_smul
  apply registerZero_sum
  intro j
  apply registerZero_smul
  apply registerZero_ket
  rw [regValue_writeReg_disjoint reg pointReg _ _ hdisj]
  exact hzero

private theorem registerZero_labelState_disjoint
    (reg labelReg : List Wire)
    (value : Nat)
    (ψ : State)
    (hzero : RegisterZero reg ψ)
    (hdisj : List.Disjoint reg labelReg) :
    RegisterZero reg (labelState labelReg value ψ) := by
  classical
  intro t ht
  have htmem :
      t ∈ (labelState labelReg value ψ).support :=
    Finsupp.mem_support_iff.mpr ht
  rw [labelState_eq_mapDomain] at htmem
  have htimg := Finsupp.mapDomain_support htmem
  rcases Finset.mem_image.mp htimg with ⟨u, hu, rfl⟩
  rw [regValue_writeReg_disjoint reg labelReg _ _ hdisj]
  exact hzero u (Finsupp.mem_support_iff.mp hu)

private theorem inner_finset_sum_left
    {ι : Type*}
    (S : Finset ι)
    (f : ι → State)
    (φ : State) :
    inner (∑ i ∈ S, f i) φ =
      ∑ i ∈ S, inner (f i) φ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      simp [hi, inner_add_left, ih]

private theorem inner_finset_sum_right
    {ι : Type*}
    (S : Finset ι)
    (ψ : State)
    (f : ι → State) :
    inner ψ (∑ i ∈ S, f i) =
      ∑ i ∈ S, inner ψ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      simp [hi, inner_add_right, ih]

private theorem normSq_orthonormal_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → State)
    (c : ι → ℂ)
    (hv :
      ∀ i j,
        inner (v i) (v j) =
          if i = j then 1 else 0) :
    normSq (∑ i, c i • v i) =
      ∑ i, Complex.normSq (c i) := by
  have hinner :
      inner
          (∑ i, c i • v i)
          (∑ i, c i • v i) =
        ∑ i, (Complex.normSq (c i) : ℂ) := by
    rw [inner_finset_sum_left Finset.univ]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_finset_sum_right Finset.univ]
    rw [Finset.sum_eq_single i]
    · rw [inner_smul_smul, hv i i]
      simp [Complex.normSq_eq_conj_mul_self]
    · intro j _ hji
      rw [inner_smul_smul, hv i j]
      simp [Ne.symm hji]
    · simp
  unfold normSq
  rw [hinner]
  simp

private theorem jointRegisterProbability_fourierState_eq_character_average
    {G : Type*} [AddCommGroup G]
    {w r d precision : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (s : BasisState)
    (hsetting : ECDLPSetting P (d • P) r d)
    (hspecNodup :
      (aReg ++ bReg ++ pointReg ++ oracleWork).Nodup)
    (hpointWidth : pointReg.length = w)
    (haWidth : aReg.length = precision)
    (hbWidth : bReg.length = precision)
    (haZero : regValue aReg s = 0)
    (hbZero : regValue bReg s = 0)
    (a b : Fin (2 ^ precision)) :
    jointRegisterProbability aReg bReg a.val b.val
        (orderFindingFourierState
          (r := r) (d := d) (precision := precision)
          enc P aReg bReg pointReg s) =
      ((r : ℝ)⁻¹) *
        ∑ k : Fin r,
          characterWeight r precision d k a b := by
  classical

  obtain ⟨haN, hbN, hpN, hab, hap, hbp⟩ :=
    register_parts hspecNodup

  let coeff : Fin r → ℂ :=
    fun k =>
      qpeAmplitude precision
          ((k.val : ℝ) / (r : ℝ)) a.val *
        qpeAmplitude precision
          ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ))
          b.val

  let χ : State :=
    ∑ k : Fin r,
      coeff k • pointEigenstate enc P pointReg s k

  have hfilter :
      jointFilter aReg bReg a.val b.val
          (orderFindingFourierState
            (r := r) (d := d) (precision := precision)
            enc P aReg bReg pointReg s) =
        (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
          ∑ k : Fin r,
            coeff k •
              labelState bReg b.val
                (labelState aReg a.val
                  (pointEigenstate enc P pointReg s k)) := by
    unfold orderFindingFourierState
    rw [jointFilter_smul]
    simp_rw [jointFilter_sum, jointFilter_smul]
    simp_rw [
      jointFilter_labelPair
        aReg bReg precision
        haWidth hbWidth haN hbN hab a b
    ]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp [coeff]
      · intro y _ hy
        simp [hy]
      · simp
    · intro x _ hx
      simp [hx]
    · simp

  have hfactor :
      (∑ k : Fin r,
          coeff k •
            labelState bReg b.val
              (labelState aReg a.val
                (pointEigenstate enc P pointReg s k))) =
        labelState bReg b.val
          (labelState aReg a.val χ) := by
    dsimp [χ]
    simp only [map_sum, map_smul]

  have hχa : RegisterZero aReg χ := by
    dsimp [χ]
    apply registerZero_sum
    intro k
    apply registerZero_smul
    exact pointEigenstate_registerZero
      enc P pointReg aReg s hap haZero k

  have hχb : RegisterZero bReg χ := by
    dsimp [χ]
    apply registerZero_sum
    intro k
    apply registerZero_smul
    exact pointEigenstate_registerZero
      enc P pointReg bReg s hbp hbZero k

  have hχbAfterA :
      RegisterZero bReg
        (labelState aReg a.val χ) :=
    registerZero_labelState_disjoint
      bReg aReg a.val χ hχb hab.symm

  have hlabelNorm :
      normSq
          (labelState bReg b.val
            (labelState aReg a.val χ)) =
        normSq χ := by
    rw [
      normSq_labelState_clean
        bReg (labelState aReg a.val χ)
        b.val hχbAfterA hbN
    ]
    rw [
      normSq_labelState_clean
        aReg χ a.val hχa haN
    ]

  have hχnorm :
      normSq χ =
        ∑ k : Fin r, Complex.normSq (coeff k) := by
    dsimp [χ]
    apply normSq_orthonormal_sum
    intro k l
    exact pointEigenstate_orthonormal
      enc P pointReg s
      hsetting.prime_order hsetting.order_P
      hpointWidth hpN k l

  have hrR : (r : ℝ) ≠ 0 := by
    exact_mod_cast hsetting.prime_order.ne_zero

  have hsqrt :
      Real.sqrt (r : ℝ) ≠ 0 := by
    positivity

  have hc :
      Complex.normSq
          ((((Real.sqrt r)⁻¹ : ℝ) : ℂ)) =
        (r : ℝ)⁻¹ := by
    simp only [Complex.normSq_ofReal]
    field_simp [hsqrt, hrR]
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]

  rw [jointRegisterProbability_eq_normSq_filter]
  rw [hfilter]
  rw [state_normSq_smul]
  rw [hfactor, hlabelNorm, hχnorm, hc]
  simp [coeff, characterWeight, Complex.normSq_mul]

theorem jointRegisterProbability_orderFinding_eq_character_average
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
    (a b : Fin (2 ^ precision)) :
    jointRegisterProbability
        aReg bReg a.val b.val
        (orderFinding aReg bReg qftAncilla oracle (ket s)) =
      ((r : ℝ)⁻¹) *
        ∑ k : Fin r,
          characterWeight r precision d k a b := by
  rw [
    orderFinding_eq_fourierState
      enc oracle P Q
      aReg bReg pointReg oracleWork
      qftAncilla s hsetting hspec hsetup
  ]
  have hsetting' :
      ECDLPSetting P (d • P) r d := by
    exact {
      prime_order := hsetting.prime_order
      order_P := hsetting.order_P
      Q_eq := rfl
    }
  exact
    jointRegisterProbability_fourierState_eq_character_average
      enc P aReg bReg pointReg oracleWork s
      hsetting'
      hspec.registers_nodup
      hspec.point_width
      hsetup.a_width
      hsetup.b_width
      hsetup.a_zero
      hsetup.b_zero
      a b

private theorem qpeAmplitude_peak_lower_bound
    (precision : Nat)
    (phase : ℝ)
    (value : Fin (2 ^ precision))
    (hnear :
      circularDistance precision phase value ≤
        (1 : ℝ) / (2 * (2 ^ precision : Nat))) :
    (4 : ℝ) / Real.pi ^ 2 ≤
      Complex.normSq
        (qpeAmplitude precision phase value.val) := by
  unfold qpeAmplitude
  apply geometric_phase_average_lower_bound
  · positivity
  · simpa [circularDistance] using hnear

theorem jointRegisterProbability_character_peak_lower_bound
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
    (k : Fin r)
    (a b : Fin (2 ^ precision))
    (ha :
      circularDistance precision
          ((k.val : ℝ) / (r : ℝ)) a ≤
        (1 : ℝ) / (2 * (2 ^ precision : Nat)))
    (hb :
      circularDistance precision
          ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) b ≤
        (1 : ℝ) / (2 * (2 ^ precision : Nat))) :
    ((r : ℝ)⁻¹) *
        ((4 : ℝ) / Real.pi ^ 2) ^ 2 ≤
      jointRegisterProbability
        aReg bReg a.val b.val
        (orderFinding aReg bReg qftAncilla oracle (ket s)) := by
  classical

  let A :=
    Complex.normSq
      (qpeAmplitude precision
        ((k.val : ℝ) / (r : ℝ)) a.val)

  let B :=
    Complex.normSq
      (qpeAmplitude precision
        ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ))
        b.val)

  let c : ℝ := (4 : ℝ) / Real.pi ^ 2

  have hA : c ≤ A := by
    dsimp [c, A]
    exact qpeAmplitude_peak_lower_bound
      precision ((k.val : ℝ) / (r : ℝ)) a ha

  have hB : c ≤ B := by
    dsimp [c, B]
    exact qpeAmplitude_peak_lower_bound
      precision
        ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ))
        b hb

  have hc : 0 ≤ c := by
    dsimp [c]
    positivity

  have hAB :
      c ^ 2 ≤ characterWeight r precision d k a b := by
    have hmul : c * c ≤ A * B :=
      mul_le_mul hA hB hc (by
        dsimp [A]
        exact Complex.normSq_nonneg _)
    simpa [c, A, B, characterWeight, pow_two] using hmul

  have hsum :
      characterWeight r precision d k a b ≤
        ∑ j : Fin r,
          characterWeight r precision d j a b := by
    simpa using
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin r)))
        (a := k)
        (f := fun j : Fin r => characterWeight r precision d j a b)
        (by
          intro j _
          unfold characterWeight
          exact mul_nonneg
            (Complex.normSq_nonneg _)
            (Complex.normSq_nonneg _))
        (by simp)

  have hinv : 0 ≤ (r : ℝ)⁻¹ := by
    positivity

  calc
    ((r : ℝ)⁻¹) * c ^ 2
        ≤ ((r : ℝ)⁻¹) *
            characterWeight r precision d k a b :=
      mul_le_mul_of_nonneg_left hAB hinv
    _ ≤ ((r : ℝ)⁻¹) *
          ∑ j : Fin r,
            characterWeight r precision d j a b :=
      mul_le_mul_of_nonneg_left hsum hinv
    _ =
        jointRegisterProbability
          aReg bReg a.val b.val
          (orderFinding
            aReg bReg qftAncilla oracle (ket s)) := by
      symm
      exact
        jointRegisterProbability_orderFinding_eq_character_average
          enc oracle P Q
          aReg bReg pointReg oracleWork
          qftAncilla s hsetting hspec hsetup a b
