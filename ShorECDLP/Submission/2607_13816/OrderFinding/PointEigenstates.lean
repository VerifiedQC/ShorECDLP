import ShorECDLP.Submission.«2607_13816».Arithmetic.PointTotal
import ShorECDLP.Submission.«2607_13816».OrderFinding.CyclicStates
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Classical Quantum
noncomputable section
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩
theorem pointWrite_frame (P : Secp256k1.Point) (s : BasisState) (w : Wire) (hw : w∉pointLogicalWires) :
    pointWrite P s w=s w := by simp only [pointWrite,if_neg hw]
theorem pointWrite_word (P : Secp256k1.Point) (s : BasisState) :
    wireValues pointLogicalWires (pointWrite P s)=pointCoordinateWord (fig14PointEncoding P) := by
  have he : wireValues pointLogicalWires (pointWrite P s)=
      wireValues pointLogicalWires (wordPattern pointLogicalWires (pointCoordinateWord (fig14PointEncoding P))) := by
    apply List.map_congr_left
    intro w hw
    simp only [pointWrite,if_pos hw]
  rw [he,wordPattern_read _ _ pointLogicalWires_nodup (by simp [pointLogicalWires,pointCorrectionX,pointCorrectionYInf])]
private theorem pointWrite_fields (P : Secp256k1.Point) (s : BasisState) :
    wireValues (List.range' 263 256) (pointWrite P s)=constantBits 256 (fig14PointEncoding P).2.1.val ∧
    wireValues (List.range' 580 256) (pointWrite P s)=constantBits 256 (fig14PointEncoding P).2.2.val ∧
    pointWrite P s 838=(fig14PointEncoding P).1 := by
  have h := pointWrite_word P s
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,wireValues,List.map_append,
    List.map_cons,List.map_nil,pointCoordinateWord,← List.append_assoc] at h
  have ha := List.append_inj h (by simp)
  have hb := List.append_inj ha.1 (by simp)
  exact ⟨hb.1,hb.2,by simpa using ha.2⟩
theorem pointWrite_coordinates (P : Secp256k1.Point) (s : BasisState) :
    pointStateCoordinates (pointWrite P s)=fig14PointEncoding P := by
  obtain ⟨hx,hy,hi⟩ := pointWrite_fields P s
  have hxlt : (fig14PointEncoding P).2.1.val<2^256 := (ZMod.val_lt _).trans (by decide +kernel)
  have hylt : (fig14PointEncoding P).2.2.val<2^256 := (ZMod.val_lt _).trans (by decide +kernel)
  simp only [pointStateCoordinates,hx,hy,hi,boolWordToNat_constantBits,Nat.mod_eq_of_lt hxlt,
    Nat.mod_eq_of_lt hylt,ZMod.natCast_zmod_val,Prod.mk.eta]
theorem pointWrite_valid (P : Secp256k1.Point) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (pointWrite P s) := by
  obtain ⟨hx,hy,_⟩ := pointWrite_fields P s
  have hxlt : (fig14PointEncoding P).2.1.val<2^256 := (ZMod.val_lt _).trans (by decide +kernel)
  have hylt : (fig14PointEncoding P).2.2.val<2^256 := (ZMod.val_lt _).trans (by decide +kernel)
  refine ⟨?_,?_,?_,?_⟩
  · intro w hw
    rw [pointWrite_frame]
    · exact hs.1 w hw
    · simp only [List.mem_append,List.mem_range'_1] at hw
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
      intro hp
      rcases hp with hp | hp | hp
      · omega
      · omega
      · subst w; norm_num at hw
  · rw [pointWrite_frame P s 837 (by decide +kernel)]
    exact hs.2.1
  · rw [hx,boolWordToNat_constantBits,Nat.mod_eq_of_lt hxlt]
    exact ZMod.val_lt _
  · rw [hy,boolWordToNat_constantBits,Nat.mod_eq_of_lt hylt]
    exact ZMod.val_lt _
theorem pointWrite_overwrite (P Q : Secp256k1.Point) (s : BasisState) :
    pointWrite P (pointWrite Q s)=pointWrite P s := by
  funext w
  by_cases hw : w∈pointLogicalWires <;> simp [pointWrite,hw]
theorem pointWrite_injective (s : BasisState) : Function.Injective (fun P : Secp256k1.Point => pointWrite P s) := by
  intro P Q h
  apply fig14PointEncoding_injective
  have hh := congrArg pointStateCoordinates h
  simpa only [pointWrite_coordinates] using hh
def pointCyclicBasis {r : Nat} (P : Secp256k1.Point) (s : BasisState) (j : Fin r) : State :=
  ket (pointWrite (j.val • P) s)
theorem pointCyclicBasis_orthonormal {r : Nat} (P : Secp256k1.Point) (s : BasisState)
    (horder : addOrderOf P=r) (j l : Fin r) :
    inner (pointCyclicBasis P s j) (pointCyclicBasis P s l)=if j=l then 1 else 0 := by
  classical
  by_cases h : j=l
  · subst l; simp [pointCyclicBasis]
  · have hn : pointWrite (j.val • P) s ≠ pointWrite (l.val • P) s := by
      intro he
      have hp := pointWrite_injective s he
      have hj : j.val<addOrderOf P := by simp [horder]
      have hl : l.val<addOrderOf P := by simp [horder]
      exact h (Fin.ext (nsmul_injOn_Iio_addOrderOf hj hl hp))
    simp [pointCyclicBasis,h,hn]
theorem pointCyclicBasis_shift {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hq : s 836=true) (t : Nat) (j : Fin r) :
    Finsupp.lmapDomain ℂ ℂ (pointAddState (t • P)) (pointCyclicBasis P s j)=
      pointCyclicBasis P s (cyclicShift hr.pos t j) := by
  have he := pointAddState_correct (t • P) (j.val • P) (pointWrite (j.val • P) s)
    (pointWrite_valid _ s hs) (pointWrite_coordinates _ s)
  rw [pointWrite_frame _ s 836 (by decide +kernel),hq,if_pos rfl,pointWrite_overwrite] at he
  have hp : j.val • P + t • P=(cyclicShift hr.pos t j).val • P := by
    rw [← add_nsmul]
    change (j.val+t) • P=((j.val+t)%r) • P
    have hm := mod_addOrderOf_nsmul P (j.val+t)
    rw [horder] at hm
    exact hm.symm
  rw [hp] at he
  simpa only [pointCyclicBasis,ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,one_smul] using congrArg (fun u => Finsupp.single u (1:ℂ)) he

def pointCyclicState {r : Nat} (P : Secp256k1.Point) (s : BasisState) (k : Fin r) : State :=
  cyclicState (pointCyclicBasis P s) k

theorem pointCyclicState_shift {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hq : s 836=true) (t : Nat) (k : Fin r) :
    Finsupp.lmapDomain ℂ ℂ (pointAddState (t • P)) (pointCyclicState P s k)=
      ShorECDLP.Quantum.PhaseEstimation.eigenvalue (((k.val*t:Nat):ℝ)/(r:ℝ)) • pointCyclicState P s k :=
  cyclicState_shift hr t _ _ (pointCyclicBasis_shift hr P horder s hs hq t) k

theorem pointCyclicState_supported {r : Nat} (P : Secp256k1.Point) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (k : Fin r) :
    SupportedOn Secp256k1ZeroAllowedInputValid (pointCyclicState P s k) := by
  classical
  intro u hu
  by_contra hn
  apply hu
  have hz (j : Fin r) : pointCyclicBasis P s j u=0 := by
    have hh := supportedOn_ket _ _ (pointWrite_valid (j.val • P) s hs)
    by_contra h
    exact hn (hh u h)
  simp [pointCyclicState,cyclicState,Finsupp.smul_apply,hz]
theorem pointCyclicState_disabled {r : Nat} (P : Secp256k1.Point) (C : Secp256k1.Point)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=false) (k : Fin r) :
    Finsupp.lmapDomain ℂ ℂ (pointAddState C) (pointCyclicState P s k)=pointCyclicState P s k := by
  have he (j : Fin r) : pointAddState C (pointWrite (j.val • P) s)=pointWrite (j.val • P) s := by
    have hh := pointAddState_correct C (j.val • P) (pointWrite (j.val • P) s)
      (pointWrite_valid _ s hs) (pointWrite_coordinates _ s)
    simpa only [pointWrite_frame _ s 836 (by decide +kernel),hq,Bool.false_eq_true,if_false] using hh
  simp only [pointCyclicState,cyclicState,map_smul,map_sum,pointCyclicBasis,ket,
    Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,he]
theorem pointAddProgram_eigenstate {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (t : Nat) (k : Fin r) :
    ∃ cs : List ℂ, List.Forall₂
      (fun branch c => branch.kraus (pointCyclicState P s k)=
        c • ((if s 836 then ShorECDLP.Quantum.PhaseEstimation.eigenvalue (((k.val*t:Nat):ℝ)/(r:ℝ)) else 1) •
          pointCyclicState P s k)) (pointAddProgram (t • P)).run cs ∧
      (cs.map Complex.normSq).sum=1 := by
  obtain ⟨cs,hcs,hm⟩ := coherent_on_supported_state (pointAddProgram_coherent (t • P))
    (pointCyclicState_supported P s hs k)
  refine ⟨cs,?_,hm⟩
  apply hcs.imp
  intro branch c hc
  rw [hc]
  cases hq : s 836
  · rw [pointCyclicState_disabled P (t • P) s hs hq k]
    simp
  · rw [pointCyclicState_shift hr P horder s hs hq t k]
    simp

end
end ShorECDLP.Paper2607_13816
