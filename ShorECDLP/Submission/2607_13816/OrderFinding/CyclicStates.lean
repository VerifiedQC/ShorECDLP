import ShorECDLP.Math.CyclicCharacters
import ShorECDLP.Framework.Quantum.InnerProduct
namespace ShorECDLP.Paper2607_13816
open ShorECDLP.Quantum ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
private theorem cyclic_inner_sum_left {ι : Type*} [Fintype ι] (f : ι → State) (φ : State) :
    inner (∑ i, f i) φ = ∑ i, inner (f i) φ := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, inner_add_left, ih]
private theorem cyclic_inner_sum_right {ι : Type*} [Fintype ι] (ψ : State) (f : ι → State) :
    inner ψ (∑ i, f i) = ∑ i, inner ψ (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, inner_add_right, ih]
def cyclicState {r : Nat} (basis : Fin r → State) (k : Fin r) : State :=
  (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • ∑ j : Fin r,
    eigenvalue (-((k.val*j.val:Nat):ℝ)/(r:ℝ)) • basis j
private theorem cyclic_normalization {r : Nat} (hr : 0<r) :
    ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (r:ℂ))=1 := by
  have hs : Real.sqrt (r:ℝ) ≠ 0 := by positivity
  have hs2 : Real.sqrt (r:ℝ)*Real.sqrt (r:ℝ)=(r:ℝ) := Real.mul_self_sqrt (by positivity)
  have h : (Real.sqrt (r:ℝ))⁻¹*(Real.sqrt (r:ℝ))⁻¹*(r:ℝ)=1 := by
    field_simp [hs]
    nlinarith [hs2]
  exact_mod_cast h
theorem cyclicState_orthonormal {r : Nat} (hr : Nat.Prime r) (basis : Fin r → State)
    (hb : ∀ j l, inner (basis j) (basis l)=if j=l then 1 else 0) (k l : Fin r) :
    inner (cyclicState basis k) (cyclicState basis l)=if k=l then 1 else 0 := by
  classical
  unfold cyclicState
  rw [inner_smul_smul,cyclic_inner_sum_left]
  simp_rw [cyclic_inner_sum_right,inner_smul_smul,hb]
  simp only [mul_ite,mul_one,mul_zero]
  simp
  have hc := character_sum hr k l
  simp only [Nat.cast_mul] at hc
  rw [hc]
  by_cases h : k=l
  · subst l
    simp only [if_true]
    simpa using cyclic_normalization hr.pos
  · simp [h]
theorem cyclicState_average {r : Nat} (hr : Nat.Prime r) (basis : Fin r → State) :
    (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • ∑ k : Fin r, cyclicState basis k = basis ⟨0,hr.pos⟩ := by
  classical
  unfold cyclicState
  simp_rw [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  have he (j : Fin r) :
    (∑ k : Fin r, ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
      ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) * eigenvalue (-((k.val*j.val:Nat):ℝ)/(r:ℝ)))) • basis j) =
    (if j.val=0 then (1:ℂ) else 0) • basis j := by
    rw [← Finset.sum_smul]
    simp_rw [← mul_assoc]
    rw [← Finset.mul_sum, character_sum_zero_index hr j]
    split
    · rw [cyclic_normalization hr.pos]
    · simp
  simp_rw [he]
  rw [Finset.sum_eq_single ⟨0,hr.pos⟩]
  · simp
  · intro j _ hj
    have hn : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [hn]
  · simp
theorem cyclicState_mass {r : Nat} (hr : Nat.Prime r) (basis : Fin r → State)
    (hb : ∀ j l, inner (basis j) (basis l)=if j=l then 1 else 0) (a : Fin r → ℂ) :
    normSq (∑ k : Fin r, a k • cyclicState basis k)=∑ k : Fin r, Complex.normSq (a k) := by
  classical
  unfold normSq
  rw [cyclic_inner_sum_left]
  simp_rw [cyclic_inner_sum_right,inner_smul_smul,cyclicState_orthonormal hr basis hb]
  simp only [mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  simp

end
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open ShorECDLP.Quantum ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section
def cyclicShift {r : Nat} (hr : 0<r) (t : Nat) (j : Fin r) : Fin r :=
  ⟨(j.val+t)%r,Nat.mod_lt _ hr⟩
theorem cyclicShift_injective {r : Nat} (hr : 0<r) (t : Nat) :
    Function.Injective (cyclicShift hr t) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (i.val+t)%r=(j.val+t)%r at hv
  have hz : ((i.val+t:Nat):ZMod r)=((j.val+t:Nat):ZMod r) := by
    have hh := congrArg (fun n : Nat => (n:ZMod r)) hv
    simpa only [ZMod.natCast_mod] using hh
  simp only [Nat.cast_add,add_left_inj] at hz
  have hm := (ZMod.natCast_eq_natCast_iff' i.val j.val r).mp hz
  simpa [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hm

theorem cyclicState_shift {r : Nat} (hr : Nat.Prime r) (t : Nat)
    (basis : Fin r → State) (T : State →ₗ[ℂ] State)
    (hT : ∀ j, T (basis j)=basis (cyclicShift hr.pos t j)) (k : Fin r) :
    T (cyclicState basis k)=eigenvalue (((k.val*t:Nat):ℝ)/(r:ℝ)) • cyclicState basis k := by
  classical
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
  rw [map_smul, map_sum, smul_comm _ (((Real.sqrt r)⁻¹:ℝ):ℂ)]
  congr 1
  simp_rw [map_smul,hT]
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
end
end ShorECDLP.Paper2607_13816
