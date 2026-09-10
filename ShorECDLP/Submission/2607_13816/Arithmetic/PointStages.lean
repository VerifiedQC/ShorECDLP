import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedResources
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantModularCoherent
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularNegate
import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareSubtract
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

/-! Fixed shared-layout stages for Figure 14. Arithmetic, complete frame restoration,
and canonical readiness are proved on the same layouts used by the coherent circuits. -/


private theorem point_X_update (s t : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hx : boolWordToNat (wireValues (List.range' 263 256) t)<ShorECDLP.p)
    (hframe : ∀ w, w ∉ List.range' 263 256 → t w=s w) : Secp256k1ZeroAllowedInputValid t := by
  refine ⟨?_,?_,hx,?_⟩
  · intro w hw
    rw [hframe w (by simp at hw ⊢; omega)]
    exact hs.1 w hw
  · rw [hframe 837 (by decide +kernel)]
    exact hs.2.1
  · have he : wireValues (List.range' 580 256) t=wireValues (List.range' 580 256) s := by
      apply List.map_congr_left
      intro w hw
      exact hframe w (by simp at hw ⊢; omega)
    rw [he]
    exact hs.2.2.2
private theorem point_Y_update (s t : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hy : boolWordToNat (wireValues (List.range' 580 256) t)<ShorECDLP.p)
    (hframe : ∀ w, w ∉ List.range' 580 256 → t w=s w) : Secp256k1ZeroAllowedInputValid t := by
  refine ⟨?_,?_,?_,hy⟩
  · intro w hw
    rw [hframe w (by simp at hw ⊢; omega)]
    exact hs.1 w hw
  · rw [hframe 837 (by decide +kernel)]
    exact hs.2.1
  · have he : wireValues (List.range' 263 256) t=wireValues (List.range' 263 256) s := by
      apply List.map_congr_left
      intro w hw
      exact hframe w (by simp at hw ⊢; omega)
    rw [he]
    exact hs.2.2.1

def fig14ConstantX (k : Nat) : AdaptiveCircuit :=
  uncontrolledConstantModularAdd (List.range' 263 256) (List.range' 7 256) (constantBits 256 k)
    secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559
def fig14ConstantXState (k : Nat) : BasisState → BasisState :=
  uncontrolledConstantModularAddIdealState (List.range' 263 256) (constantBits 256 k)
    secp256k1ReductionConstantBits ShorECDLP.p 559

private theorem point_bits_value (k : Nat) (hk : k<ShorECDLP.p) : boolWordToNat (constantBits 256 k)=k := by
  rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt]
  exact hk.trans (by decide +kernel)

theorem fig14ConstantXState_correct (k : Nat) (hk : k<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    boolWordToNat (wireValues (List.range' 263 256) (fig14ConstantXState k s))=
      (boolWordToNat (wireValues (List.range' 263 256) s)+k)%ShorECDLP.p ∧
    (∀ w, w ∉ List.range' 263 256 → fig14ConstantXState k s w=s w) := by
  have h := uncontrolledConstantModularAddIdealState_correct (List.range' 263 256)
    (constantBits 256 k) secp256k1ReductionConstantBits ShorECDLP.p 559 s
    (by simp) (by simp [secp256k1ReductionConstantBits]) (List.nodup_range') (by decide +kernel)
    (hs.1 559 (by decide +kernel)) (by decide +kernel) (by rw [point_bits_value k hk]; exact hk)
    hs.2.2.1 (by rw [secp256k1ReductionConstant_value]; decide +kernel)
  simpa only [point_bits_value k hk] using h

theorem fig14ConstantXState_ready (k : Nat) (hk : k<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (fig14ConstantXState k s) := by
  have hh := fig14ConstantXState_correct k hk s hs
  exact point_X_update s _ hs (by rw [hh.1]; exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos) hh.2
private theorem point_constantX_layout :
    ([558,560,561,559]++List.range' 263 256++List.range' 7 256).Nodup := by decide +kernel
private theorem point_const_valid_X (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    ConstantModularValid (List.range' 263 256) ShorECDLP.p 558 560 561 559 s :=
  ⟨hs.1 558 (by decide +kernel),hs.1 560 (by decide +kernel),hs.1 561 (by decide +kernel),
    hs.1 559 (by decide +kernel),hs.2.2.1⟩
private theorem coherent_strengthen {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State} {Valid Stronger : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid) (hsub : ∀ s, Stronger s → Valid s) :
    CoherentlyImplementsOn program ideal Stronger := by
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (hsub s hs)),hm⟩

theorem fig14ConstantX_coherent (k : Nat) :
    CoherentlyImplementsOn (fig14ConstantX k) (Finsupp.lmapDomain ℂ ℂ (fig14ConstantXState k))
      Secp256k1ZeroAllowedInputValid := by
  apply coherent_strengthen
    (uncontrolledConstantModularAdd_coherent (List.range' 263 256) (List.range' 7 256)
      (constantBits 256 k) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559
      (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp) (by simp)
      point_constantX_layout ShorECDLP.Secp256k1.p_prime.pos)
  exact point_const_valid_X
def fig14ControlledConstantX (k : Nat) : AdaptiveCircuit :=
  controlledConstantModularAdd (List.range' 263 256) (List.range' 7 256) (constantBits 256 k)
    secp256k1ReductionConstantBits ShorECDLP.p 836 558 560 561 559
def fig14ControlledConstantXState (k : Nat) : BasisState → BasisState :=
  constantModularAddIdealState (List.range' 263 256) (constantBits 256 k)
    secp256k1ReductionConstantBits ShorECDLP.p 836 559

theorem fig14ControlledConstantXState_correct (k : Nat) (hk : k<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    boolWordToNat (wireValues (List.range' 263 256) (fig14ControlledConstantXState k s))=
      (boolWordToNat (wireValues (List.range' 263 256) s)+(if s 836 then k else 0))%ShorECDLP.p ∧
    (∀ w, w ∉ List.range' 263 256 → fig14ControlledConstantXState k s w=s w) := by
  have h := constantModularAddIdealState_correct (List.range' 263 256)
    (constantBits 256 k) secp256k1ReductionConstantBits ShorECDLP.p 836 559 s
    (by simp) (by simp [secp256k1ReductionConstantBits]) (List.nodup_range') (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (hs.1 559 (by decide +kernel)) (by decide +kernel) (by rw [point_bits_value k hk]; exact hk)
    hs.2.2.1 (by rw [secp256k1ReductionConstant_value]; decide +kernel)
  simpa only [point_bits_value k hk] using h

theorem fig14ControlledConstantXState_ready (k : Nat) (hk : k<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (fig14ControlledConstantXState k s) := by
  have hh := fig14ControlledConstantXState_correct k hk s hs
  exact point_X_update s _ hs (by rw [hh.1]; exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos) hh.2
private theorem point_controlledConstantX_layout :
    ([836,558,560,561,559]++List.range' 263 256++List.range' 7 256).Nodup := by decide +kernel
theorem fig14ControlledConstantX_coherent (k : Nat) :
    CoherentlyImplementsOn (fig14ControlledConstantX k) (Finsupp.lmapDomain ℂ ℂ (fig14ControlledConstantXState k))
      Secp256k1ZeroAllowedInputValid := by
  apply coherent_strengthen
    (controlledConstantModularAdd_coherent (List.range' 263 256) (List.range' 7 256)
      (constantBits 256 k) secp256k1ReductionConstantBits ShorECDLP.p 836 558 560 561 559
      (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp) (by simp)
      point_controlledConstantX_layout ShorECDLP.Secp256k1.p_prime.pos)
  exact point_const_valid_X
def fig14ControlledConstantY (k : Nat) : AdaptiveCircuit :=
  controlledConstantModularAdd (List.range' 580 256) (List.range' 7 256) (constantBits 256 k)
    secp256k1ReductionConstantBits ShorECDLP.p 836 558 560 561 559
def fig14ControlledConstantYState (k : Nat) : BasisState → BasisState :=
  constantModularAddIdealState (List.range' 580 256) (constantBits 256 k)
    secp256k1ReductionConstantBits ShorECDLP.p 836 559

theorem fig14ControlledConstantYState_correct (k : Nat) (hk : k<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    boolWordToNat (wireValues (List.range' 580 256) (fig14ControlledConstantYState k s))=
      (boolWordToNat (wireValues (List.range' 580 256) s)+(if s 836 then k else 0))%ShorECDLP.p ∧
    (∀ w, w ∉ List.range' 580 256 → fig14ControlledConstantYState k s w=s w) := by
  have h := constantModularAddIdealState_correct (List.range' 580 256)
    (constantBits 256 k) secp256k1ReductionConstantBits ShorECDLP.p 836 559 s
    (by simp) (by simp [secp256k1ReductionConstantBits]) (List.nodup_range') (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (hs.1 559 (by decide +kernel)) (by decide +kernel) (by rw [point_bits_value k hk]; exact hk)
    hs.2.2.2 (by rw [secp256k1ReductionConstant_value]; decide +kernel)
  simpa only [point_bits_value k hk] using h

theorem fig14ControlledConstantYState_ready (k : Nat) (hk : k<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (fig14ControlledConstantYState k s) := by
  have hh := fig14ControlledConstantYState_correct k hk s hs
  exact point_Y_update s _ hs (by rw [hh.1]; exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos) hh.2
private theorem point_controlledConstantY_layout :
    ([836,558,560,561,559]++List.range' 580 256++List.range' 7 256).Nodup := by decide +kernel
private theorem point_const_valid_Y (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    ConstantModularValid (List.range' 580 256) ShorECDLP.p 558 560 561 559 s :=
  ⟨hs.1 558 (by decide +kernel),hs.1 560 (by decide +kernel),hs.1 561 (by decide +kernel),
    hs.1 559 (by decide +kernel),hs.2.2.2⟩
theorem fig14ControlledConstantY_coherent (k : Nat) :
    CoherentlyImplementsOn (fig14ControlledConstantY k) (Finsupp.lmapDomain ℂ ℂ (fig14ControlledConstantYState k))
      Secp256k1ZeroAllowedInputValid := by
  apply coherent_strengthen
    (controlledConstantModularAdd_coherent (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 k) secp256k1ReductionConstantBits ShorECDLP.p 836 558 560 561 559
      (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp) (by simp)
      point_controlledConstantY_layout ShorECDLP.Secp256k1.p_prime.pos)
  exact point_const_valid_Y

theorem fig14Division_ready (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (zeroAllowedDivisionOutputState s) := by
  apply point_Y_update s _ hs
  · rw [zeroAllowedDivisionOutputState_word s hs]
    exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  · intro w hw
    simp only [zeroAllowedDivisionOutputState_frame s hs,if_neg hw]

theorem fig14Multiplication_ready (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (zeroAllowedMultiplicationOutputState s) := by
  apply point_Y_update s _ hs
  · rw [zeroAllowedMultiplicationOutputState_word s hs]
    exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  · intro w hw
    simp only [zeroAllowedMultiplicationOutputState_frame s hs,if_neg hw]

/-- The controlled negation stage uses the same clean helpers and dirty accumulator
as the constant additions; label 836 carries the arbitrary point control. -/
def fig14Negate : AdaptiveCircuit :=
  controlledModularNegate (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 558 560 561 559
def fig14NegateState : BasisState → BasisState :=
  modularNegateIdealState (List.range' 263 256) (constantBits 256 ShorECDLP.p) 836 559

private theorem point_modulus : boolWordToNat (constantBits 256 ShorECDLP.p)=ShorECDLP.p := by
  rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt (by decide +kernel)]

theorem fig14NegateState_correct (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    boolWordToNat (wireValues (List.range' 263 256) (fig14NegateState s))=
      (if s 836 then (ShorECDLP.p-boolWordToNat (wireValues (List.range' 263 256) s))%ShorECDLP.p
       else boolWordToNat (wireValues (List.range' 263 256) s)) ∧
    (∀ w, w ∉ List.range' 263 256 → fig14NegateState s w=s w) := by
  exact modularNegateIdealState_correct _ _ ShorECDLP.p 836 559 s
    (by simp) (by simp) (List.nodup_range') (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (hs.1 559 (by decide +kernel)) (by decide +kernel) hs.2.2.1 point_modulus

theorem fig14NegateState_ready (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (fig14NegateState s) := by
  have hh := fig14NegateState_correct s hs
  apply point_X_update s _ hs _ hh.2
  rw [hh.1]
  split
  · exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  · exact hs.2.2.1

theorem fig14Negate_coherent :
    CoherentlyImplementsOn fig14Negate (Finsupp.lmapDomain ℂ ℂ fig14NegateState)
      Secp256k1ZeroAllowedInputValid := by
  apply coherent_strengthen
    (controlledModularNegate_coherent (List.range' 263 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) ShorECDLP.p 836 558 560 561 559
      (by simp) (by simp) (by simp) point_controlledConstantX_layout ShorECDLP.Secp256k1.p_prime.pos)
  exact point_const_valid_X

/-- Figure 14's square-subtraction uses Y as both multiplicands and restores
its clean accumulator before the following field multiplication. -/
def fig14SquareSubtract : AdaptiveCircuit :=
  squareSubtract (List.range' 263 256) (List.range' 580 256) (7::List.range' 8 255)
    secp256k1ReductionConstantBits (constantBits 256 ShorECDLP.p) ShorECDLP.p 836 558 559 561 562 560
def fig14SquareSubtractState : BasisState → BasisState :=
  squareSubtractIdealState (List.range' 263 256) (List.range' 580 256) (7::List.range' 8 255)
    secp256k1ReductionConstantBits (constantBits 256 ShorECDLP.p) ShorECDLP.p 836 558 559 560
private theorem point_square_layout :
    ([558,559,561,562,560]++List.range' 580 256++(7::List.range' 8 255)).Nodup := by decide +kernel
private theorem point_subtract_layout :
    ([836,558,560,561,559]++(7::List.range' 8 255)++List.range' 263 256).Nodup := by decide +kernel
private theorem point_square_external :
    ∀ w ∈ List.range' 580 256++[558,559,561,562,560], w ∉ List.range' 263 256 := by
  intro w hw
  simp at hw ⊢
  omega
private theorem point_square_valid (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    SquareSubtractValid (List.range' 263 256) (List.range' 580 256) (7::List.range' 8 255)
      ShorECDLP.p 558 559 561 562 560 s := by
  refine ⟨?_,hs.1 558 (by decide +kernel),hs.1 559 (by decide +kernel),
    hs.1 561 (by decide +kernel),hs.1 562 (by decide +kernel),hs.1 560 (by decide +kernel),hs.2.2.1,hs.2.2.2⟩
  intro w hw
  apply hs.1 w
  dsimp only [Wire] at *
  simp at hw ⊢
  omega

theorem fig14SquareSubtractState_correct (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    boolWordToNat (wireValues (List.range' 263 256) (fig14SquareSubtractState s))=
      (boolWordToNat (wireValues (List.range' 263 256) s)+ShorECDLP.p-
        (if s 836 then (boolWordToNat (wireValues (List.range' 580 256) s)*
          boolWordToNat (wireValues (List.range' 580 256) s))%ShorECDLP.p else 0))%ShorECDLP.p ∧
    (∀ w, w ∉ List.range' 263 256 → fig14SquareSubtractState s w=s w) := by
  have hv := point_square_valid s hs
  have hh := squareSubtract_correct (List.range' 263 256) (List.range' 580 256) 7 (List.range' 8 255)
    secp256k1ReductionConstantBits (constantBits 256 ShorECDLP.p) ShorECDLP.p 836 558 559 561 562 560 s
    (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp)
    point_square_layout point_subtract_layout point_square_external hv.1 hv.2.1 hv.2.2.1
    hv.2.2.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2.1 (by decide +kernel) (by decide +kernel)
    hs.2.2.1 hs.2.2.2 (by simpa only [List.length_cons,List.length_range'] using secp256k1ReductionConstant_value) point_modulus
  exact ⟨hh.1,hh.2.1⟩

theorem fig14SquareSubtractState_ready (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (fig14SquareSubtractState s) := by
  have hh := fig14SquareSubtractState_correct s hs
  exact point_X_update s _ hs (by rw [hh.1]; exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos) hh.2

theorem fig14SquareSubtract_coherent :
    CoherentlyImplementsOn fig14SquareSubtract (Finsupp.lmapDomain ℂ ℂ fig14SquareSubtractState)
      Secp256k1ZeroAllowedInputValid := by
  apply coherent_strengthen
    (squareSubtract_coherent (List.range' 263 256) (List.range' 580 256) 7 (List.range' 8 255)
      secp256k1ReductionConstantBits (constantBits 256 ShorECDLP.p) ShorECDLP.p 836 558 559 561 562 560
      (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp)
      point_square_layout point_subtract_layout point_square_external (by decide +kernel) (by decide +kernel)
      (by simpa only [List.length_cons,List.length_range'] using secp256k1ReductionConstant_value) point_modulus)
  exact point_square_valid
end ShorECDLP.Paper2607_13816
