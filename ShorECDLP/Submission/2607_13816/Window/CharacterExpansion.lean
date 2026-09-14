import ShorECDLP.Submission.«2607_13816».Window.Kernel
/-! Character expansion of physical point kets and normalized finite word sums. -/

namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1 Quantum.PhaseEstimation Quantum.OrderFinding
open scoped BigOperators
noncomputable section
private theorem shifted_cyclicState {r : Nat} (hr : Nat.Prime r) (t : Nat)
    (basis : Fin r → State) (k : Fin r) :
    cyclicState (fun j => basis (cyclicShift hr.pos t j)) k=
      eigenvalue (((k.val*t:Nat):ℝ)/(r:ℝ)) • cyclicState basis k := by
  letI : NeZero r := ⟨hr.ne_zero⟩
  let e : Fin r ≃ Fin r := Equiv.ofBijective (cyclicShift hr.pos t)
    ⟨cyclicShift_injective hr.pos t,Finite.injective_iff_surjective.mp (cyclicShift_injective hr.pos t)⟩
  have hz (j : Fin r) : ((e j).val:ZMod r)=(j.val:ZMod r)+(t:ZMod r) := by
    change (((j.val+t)%r:Nat):ZMod r)=_
    simp only [ZMod.natCast_mod,Nat.cast_add]
  have hp (n : Nat) : eigenvalue ((n:ℝ)/(r:ℝ))=ZMod.stdAddChar (n:ZMod r) := by
    simpa using eigenvalue_int_div_eq_stdAddChar (r:=r) (n:ℤ)
  have hn (n : Nat) : eigenvalue (-(n:ℝ)/(r:ℝ))=ZMod.stdAddChar (-(n:ZMod r)) := by
    simpa using eigenvalue_int_div_eq_stdAddChar (r:=r) (-(n:ℤ))
  unfold cyclicState
  rw [smul_comm _ (((Real.sqrt r)⁻¹:ℝ):ℂ)]
  apply congrArg (fun ψ : State => (((Real.sqrt r)⁻¹:ℝ):ℂ) • ψ)
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv e _ _ fun j => ?_
  rw [smul_smul]
  have hc : eigenvalue (-((k.val*j.val:Nat):ℝ)/(r:ℝ))=
    eigenvalue (((k.val*t:Nat):ℝ)/(r:ℝ))*eigenvalue (-((k.val*(e j).val:Nat):ℝ)/(r:ℝ)) := by
    rw [hn,hp,hn,← AddChar.map_add_eq_mul]
    congr 1
    push_cast
    rw [hz]
    ring
  rw [hc]
  rfl

/-- Expand a point ket in the cyclic character basis of its prime-order orbit. -/
theorem pointKet_character_expansion {r : Nat} (hr : Nat.Prime r) (P : Point)
    (horder : addOrderOf P=r) (s : BasisState) (t : Nat) :
    ket (pointWrite (t • P) s)=
      (((Real.sqrt r)⁻¹:ℝ):ℂ) • ∑ k : Fin r,
        eigenvalue (((k.val*t:Nat):ℝ)/(r:ℝ)) • pointCyclicState P s k := by
  have h := cyclicState_average hr (fun j => pointCyclicBasis P s (cyclicShift hr.pos t j))
  simp_rw [shifted_cyclicState hr t (pointCyclicBasis P s)] at h
  have hm := mod_addOrderOf_nsmul P t
  rw [horder] at hm
  simpa only [pointCyclicState,pointCyclicBasis,cyclicShift,Nat.zero_add,hm] using h.symm
private theorem bitWord_eq (bs : List Bool) : boolWordToNat bs=fourierWordLSB bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [boolWordToNat,fourierWordLSB,ih]

private theorem outcome_words_perm (n : Nat) :
    ((fourierOutcomes n).map fourierWordLSB).Perm (List.range (2^n)) := by
  have hn : ((fourierOutcomes n).map fourierWordLSB).Nodup :=
    (fourierOutcomes_nodup n).map_on (by
      intro a ha b hb hv
      exact fourierWordLSB_injective a b
        (((fourierOutcomes_mem _ _).mp ha).trans ((fourierOutcomes_mem _ _).mp hb).symm) hv)
  apply (List.perm_ext_iff_of_nodup hn List.nodup_range).mpr
  intro k
  simp only [List.mem_map,List.mem_range]
  constructor
  · rintro ⟨bs,hbs,rfl⟩
    simpa only [(fourierOutcomes_mem _ _).mp hbs] using fourierWordLSB_lt bs
  · intro hk
    obtain ⟨bs,hlen,hv⟩ := fourierWordLSB_surjective n k hk
    exact ⟨bs,(fourierOutcomes_mem _ _).mpr hlen,hv⟩

private theorem sum_map_range (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum=∑ x∈Finset.range n, f x := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,ih,Finset.sum_range_succ]

/-- Enumerating fixed-width bit words enumerates the geometric sum exactly once. -/
theorem phaseWord_geometric_sum (n : Nat) (z : ℂ) :
    ((fourierOutcomes n).map (fun bs => z^boolWordToNat bs)).sum=
      ∑ x ∈ Finset.range (2^n), z^x := by
  have h := (outcome_words_perm n).map (fun x => z^x)
  have he := h.sum_eq
  simpa only [List.map_map,Function.comp_def,bitWord_eq,sum_map_range] using he

private theorem phase_normalization_square (n : Nat) :
    ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^n) * ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^n)=((2^n:Nat):ℂ)⁻¹ := by
  have hh : ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^2)=(2:ℂ)⁻¹ := by
    have h : ((Real.sqrt 2)⁻¹)^2=(2:ℝ)⁻¹ := by
      rw [inv_pow,Real.sq_sqrt (by norm_num)]
    rw [←Complex.ofReal_pow,h,Complex.ofReal_inv]
    norm_num
  rw [←pow_two,←pow_mul,Nat.mul_comm n 2,pow_mul,hh,inv_pow]
  norm_cast

private theorem weighted_kernel_power (phase : ℝ) (n v : Nat) (out : List Bool)
    (hlen : out.length=n) :
    dyadicFourierKernel .inverse n v (fourierWordLSB out)*eigenvalue (phase*v)=
      eigenvalue (phase-(fourierWordLSB out:ℝ)/(2^n:Nat))^v := by
  rw [←hlen,←phaseProductRoot_nil]
  simp only [phaseProductRoot,fourierHistoryAngle,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,mul_one,mul_pow,dyadicFourierKernel]
  rw [eigenvalue_pow_eq_eigenvalue_mul,←pow_mul]
  rw [Nat.mul_comm (fourierWordLSB out) v,mul_comm phase (v:ℝ),mul_comm]

/-- Input and output Hadamard factors normalize the weighted physical word sum. -/
theorem phaseWord_weighted_sum (phase : ℝ) (n : Nat) (out : List Bool) (hlen : out.length=n) :
    ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^n) * ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^n) *
      ((fourierOutcomes n).map (fun bs =>
        dyadicFourierKernel .inverse n (boolWordToNat bs) (fourierWordLSB out)*
          eigenvalue (phase*boolWordToNat bs))).sum=
      paperPhaseAmplitude n phase (fourierWordLSB out) := by
  rw [phase_normalization_square]
  simp_rw [weighted_kernel_power phase n _ out hlen]
  rw [phaseWord_geometric_sum]
  rfl

end
end ShorECDLP.Paper2607_13816
