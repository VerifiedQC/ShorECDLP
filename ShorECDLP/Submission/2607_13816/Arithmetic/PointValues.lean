import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCircuit
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private def pointX (s : BasisState) : Nat := boolWordToNat (wireValues (List.range' 263 256) s)
private def pointY (s : BasisState) : Nat := boolWordToNat (wireValues (List.range' 580 256) s)
private theorem frame_X (s t : BasisState)
    (hf : ∀ w, w ∉ List.range' 263 256 → t w=s w) : pointY t=pointY s ∧ t 836=s 836 := by
  refine ⟨?_,hf 836 (by decide +kernel)⟩
  change boolWordToNat _=boolWordToNat _
  congr 1
  apply List.map_congr_left
  intro w hw
  exact hf w (by simp at hw ⊢; omega)
private theorem frame_Y (s t : BasisState)
    (hf : ∀ w, w ∉ List.range' 580 256 → t w=s w) : pointX t=pointX s ∧ t 836=s 836 := by
  refine ⟨?_,hf 836 (by decide +kernel)⟩
  change boolWordToNat _=boolWordToNat _
  congr 1
  apply List.map_congr_left
  intro w hw
  exact hf w (by simp at hw ⊢; omega)
private theorem constantX_values (k : Nat) (hk : k<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    pointX (fig14ConstantXState k s)=(pointX s+k)%ShorECDLP.p ∧
    pointY (fig14ConstantXState k s)=pointY s ∧ fig14ConstantXState k s 836=s 836 := by
  have hh := fig14ConstantXState_correct k hk s hs
  exact ⟨hh.1,frame_X s _ hh.2⟩
private theorem constantCX_values (k : Nat) (hk : k<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    pointX (fig14ControlledConstantXState k s)=(pointX s+(if s 836 then k else 0))%ShorECDLP.p ∧
    pointY (fig14ControlledConstantXState k s)=pointY s ∧ fig14ControlledConstantXState k s 836=s 836 := by
  have hh := fig14ControlledConstantXState_correct k hk s hs
  exact ⟨hh.1,frame_X s _ hh.2⟩
private theorem constantY_values (k : Nat) (hk : k<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    pointX (fig14ControlledConstantYState k s)=pointX s ∧
    pointY (fig14ControlledConstantYState k s)=(pointY s+(if s 836 then k else 0))%ShorECDLP.p ∧
    fig14ControlledConstantYState k s 836=s 836 := by
  have hh := fig14ControlledConstantYState_correct k hk s hs
  have he := frame_Y s _ hh.2
  exact ⟨he.1,hh.1,he.2⟩
private theorem division_values (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    pointX (zeroAllowedDivisionOutputState s)=pointX s ∧
    pointY (zeroAllowedDivisionOutputState s)=
      (pointY s*paperInverse ShorECDLP.p (if pointX s=0 then 1 else pointX s))%ShorECDLP.p ∧
    zeroAllowedDivisionOutputState s 836=s 836 := by
  have he := frame_Y s (zeroAllowedDivisionOutputState s) (by
    intro w hw
    simp only [zeroAllowedDivisionOutputState_frame s hs,if_neg hw])
  exact ⟨he.1,zeroAllowedDivisionOutputState_word s hs,he.2⟩
private theorem multiplication_values (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    pointX (zeroAllowedMultiplicationOutputState s)=pointX s ∧
    pointY (zeroAllowedMultiplicationOutputState s)=
      (pointY s*(if pointX s=0 then 1 else pointX s))%ShorECDLP.p ∧
    zeroAllowedMultiplicationOutputState s 836=s 836 := by
  have he := frame_Y s (zeroAllowedMultiplicationOutputState s) (by
    intro w hw
    simp only [zeroAllowedMultiplicationOutputState_frame s hs,if_neg hw])
  exact ⟨he.1,zeroAllowedMultiplicationOutputState_word s hs,he.2⟩
private theorem square_values (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    pointX (fig14SquareSubtractState s)=
      (pointX s+ShorECDLP.p-(if s 836 then (pointY s*pointY s)%ShorECDLP.p else 0))%ShorECDLP.p ∧
    pointY (fig14SquareSubtractState s)=pointY s ∧ fig14SquareSubtractState s 836=s 836 := by
  have hh := fig14SquareSubtractState_correct s hs
  exact ⟨hh.1,frame_X s _ hh.2⟩
private theorem negate_values (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    pointX (fig14NegateState s)=(if s 836 then (ShorECDLP.p-pointX s)%ShorECDLP.p else pointX s) ∧
    pointY (fig14NegateState s)=pointY s ∧ fig14NegateState s 836=s 836 := by
  have hh := fig14NegateState_correct s hs
  exact ⟨hh.1,frame_X s _ hh.2⟩

/-- Arithmetic value of the Figure 14 coordinate permutation, including both
explicit zero-as-one extensions. It is not a total point-addition specification. -/
def fig14CoordinateValues (x₂ y₂ : Nat) (enabled : Bool) (x y : Nat) : Nat × Nat :=
  let a := (x+(ShorECDLP.p-x₂)%ShorECDLP.p)%ShorECDLP.p
  let b := (y+(if enabled then (ShorECDLP.p-y₂)%ShorECDLP.p else 0))%ShorECDLP.p
  let u := (b*paperInverse ShorECDLP.p (if a=0 then 1 else a))%ShorECDLP.p
  let v := (a+ShorECDLP.p-(if enabled then (u*u)%ShorECDLP.p else 0))%ShorECDLP.p
  let w := (v+(if enabled then (3*x₂)%ShorECDLP.p else 0))%ShorECDLP.p
  let z := (u*(if w=0 then 1 else w))%ShorECDLP.p
  let r := if enabled then (ShorECDLP.p-w)%ShorECDLP.p else w
  ((r+x₂%ShorECDLP.p)%ShorECDLP.p,
    (z+(if enabled then (ShorECDLP.p-y₂)%ShorECDLP.p else 0))%ShorECDLP.p)

theorem fig14CoordinateState_values (x₂ y₂ : Nat) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) :
    (boolWordToNat (wireValues (List.range' 263 256) (fig14CoordinateState x₂ y₂ s)),
      boolWordToNat (wireValues (List.range' 580 256) (fig14CoordinateState x₂ y₂ s)))=
      fig14CoordinateValues x₂ y₂ (s 836)
        (boolWordToNat (wireValues (List.range' 263 256) s))
        (boolWordToNat (wireValues (List.range' 580 256) s)) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  let s1 := (fig14ConstantXState ((ShorECDLP.p-x₂)%ShorECDLP.p)) s
  have h1 : Secp256k1ZeroAllowedInputValid s1 := fig14ConstantXState_ready _ (hk _) s hs
  have v1 := constantX_values ((ShorECDLP.p-x₂)%ShorECDLP.p) (hk (ShorECDLP.p-x₂)) s hs
  let s2 := (fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)) s1
  have h2 : Secp256k1ZeroAllowedInputValid s2 := fig14ControlledConstantYState_ready _ (hk _) s1 h1
  have v2 := constantY_values ((ShorECDLP.p-y₂)%ShorECDLP.p) (hk (ShorECDLP.p-y₂)) s1 h1
  let s3 := (zeroAllowedDivisionOutputState) s2
  have h3 : Secp256k1ZeroAllowedInputValid s3 := fig14Division_ready s2 h2
  have v3 := division_values s2 h2
  let s4 := (fig14SquareSubtractState) s3
  have h4 : Secp256k1ZeroAllowedInputValid s4 := fig14SquareSubtractState_ready s3 h3
  have v4 := square_values s3 h3
  let s5 := (fig14ControlledConstantXState ((3*x₂)%ShorECDLP.p)) s4
  have h5 : Secp256k1ZeroAllowedInputValid s5 := fig14ControlledConstantXState_ready _ (hk _) s4 h4
  have v5 := constantCX_values ((3*x₂)%ShorECDLP.p) (hk (3*x₂)) s4 h4
  let s6 := (zeroAllowedMultiplicationOutputState) s5
  have h6 : Secp256k1ZeroAllowedInputValid s6 := fig14Multiplication_ready s5 h5
  have v6 := multiplication_values s5 h5
  let s7 := (fig14NegateState) s6
  have h7 : Secp256k1ZeroAllowedInputValid s7 := fig14NegateState_ready s6 h6
  have v7 := negate_values s6 h6
  let s8 := (fig14ConstantXState (x₂%ShorECDLP.p)) s7
  have h8 : Secp256k1ZeroAllowedInputValid s8 := fig14ConstantXState_ready _ (hk _) s7 h7
  have v8 := constantX_values ((x₂)%ShorECDLP.p) (hk (x₂)) s7 h7
  let s9 := (fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)) s8
  have v9 := constantY_values ((ShorECDLP.p-y₂)%ShorECDLP.p) (hk (ShorECDLP.p-y₂)) s8 h8
  change (pointX s9,pointY s9)=fig14CoordinateValues x₂ y₂ (s 836) (pointX s) (pointY s)
  dsimp only [s1,s2,s3,s4,s5,s6,s7,s8,s9] at v1 v2 v3 v4 v5 v6 v7 v8 v9 ⊢
  simp only [v9.1,v9.2.1,v8.1,v8.2.1,v8.2.2,v7.1,v7.2.1,v7.2.2,v6.1,v6.2.1,v6.2.2,v5.1,v5.2.1,v5.2.2,v4.1,v4.2.1,v4.2.2,v3.1,v3.2.1,v3.2.2,v2.1,v2.2.1,v2.2.2,v1.1,v1.2.1,v1.2.2]
  rfl

private theorem effective_inverse (a : Nat) (ha : a<ShorECDLP.p) :
    (paperInverse ShorECDLP.p (if a=0 then 1 else a)*(if a=0 then 1 else a))%ShorECDLP.p=1 := by
  have he : 1≤(if a=0 then 1 else a) := by split <;> omega
  have hp : (if a=0 then 1 else a)<ShorECDLP.p := by
    split
    · exact ShorECDLP.Secp256k1.p_prime.one_lt
    · exact ha
  have hh := paperRun_inverse_mod_prime ShorECDLP.Secp256k1.p_prime he hp
  have hv := congrArg ZMod.val hh
  simpa only [← Nat.cast_mul,ZMod.val_natCast,ZMod.val_one] using hv

theorem fig14CoordinateValues_disabled (x₂ y₂ x y : Nat)
    (hx₂ : x₂<ShorECDLP.p) (hx : x<ShorECDLP.p) (hy : y<ShorECDLP.p) :
    fig14CoordinateValues x₂ y₂ false x y=(x,y) := by
  let a := (x+(ShorECDLP.p-x₂)%ShorECDLP.p)%ShorECDLP.p
  have ha : a<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  have hm : ((y*paperInverse ShorECDLP.p (if a=0 then 1 else a))%ShorECDLP.p*
      (if a=0 then 1 else a))%ShorECDLP.p=y := by
    rw [Nat.mod_mul_mod,Nat.mul_assoc,Nat.mul_mod,effective_inverse a ha,
      Nat.mul_one,Nat.mod_mod,Nat.mod_eq_of_lt hy]
  have hrestore : (a+x₂%ShorECDLP.p)%ShorECDLP.p=x := by
    calc
      (a+x₂%ShorECDLP.p)%ShorECDLP.p = (x+(ShorECDLP.p-x₂)+x₂)%ShorECDLP.p := by
        simp only [a,Nat.add_mod,Nat.mod_mod]
      _ = x := by
        rw [Nat.add_assoc,Nat.sub_add_cancel (Nat.le_of_lt hx₂),Nat.add_mod_right,Nat.mod_eq_of_lt hx]
  simp only [fig14CoordinateValues,Bool.false_eq_true,if_false,Nat.add_zero,Nat.mod_eq_of_lt hy,
    Nat.sub_zero,Nat.add_mod_right,Nat.mod_mod]
  change ((a+x₂%ShorECDLP.p)%ShorECDLP.p,
    (((y*paperInverse ShorECDLP.p (if a=0 then 1 else a))%ShorECDLP.p*
      (if a=0 then 1 else a))%ShorECDLP.p))=(x,y)
  rw [hrestore,hm]

attribute [local irreducible] fig14CoordinateState fig14CoordinateProgram

private theorem point_frame_ext (s t : BasisState)
    (hx : boolWordToNat (wireValues (List.range' 263 256) s)=boolWordToNat (wireValues (List.range' 263 256) t))
    (hy : boolWordToNat (wireValues (List.range' 580 256) s)=boolWordToNat (wireValues (List.range' 580 256) t))
    (hf : ∀ w, w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → s w=t w) : s=t := by
  have hX : wireValues (List.range' 263 256) s=wireValues (List.range' 263 256) t :=
    boolWordToNat_injective_of_length (by simp [wireValues]) hx
  have hY : wireValues (List.range' 580 256) s=wireValues (List.range' 580 256) t :=
    boolWordToNat_injective_of_length (by simp [wireValues]) hy
  funext w
  by_cases hwX : w ∈ List.range' 263 256
  · exact List.map_inj_left.mp hX w hwX
  · by_cases hwY : w ∈ List.range' 580 256
    · exact List.map_inj_left.mp hY w hwY
    · exact hf w hwX hwY

/-- Turning off the point control makes the whole coordinate permutation the
identity, even when either intermediate field multiplier is zero. -/
theorem fig14CoordinateState_disabled (x₂ y₂ : Nat) (hx₂ : x₂<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=false) :
    fig14CoordinateState x₂ y₂ s=s := by
  have hh := fig14CoordinateState_values x₂ y₂ s hs
  rw [hq,fig14CoordinateValues_disabled x₂ y₂ _ _ hx₂ hs.2.2.1 hs.2.2.2] at hh
  have hX := congrArg (fun v : Nat × Nat => v.1) hh
  have hY := congrArg (fun v : Nat × Nat => v.2) hh
  exact point_frame_ext (fig14CoordinateState x₂ y₂ s) s hX hY
    (fig14CoordinateState_frame x₂ y₂ s hs)

/-- The actual circuit is coherently the identity on the disabled-control subspace. -/
theorem fig14CoordinateProgram_disabled (x₂ y₂ : Nat) (hx₂ : x₂<ShorECDLP.p) :
    CoherentlyImplementsOn (fig14CoordinateProgram x₂ y₂) (LinearMap.id : State →ₗ[ℂ] State)
      (fun s => Secp256k1ZeroAllowedInputValid s ∧ s 836=false) := by
  obtain ⟨cs,ha,hm⟩ := fig14CoordinateProgram_coherent x₂ y₂
  refine ⟨cs,ha.imp ?_,hm⟩
  intro b c hb s hs
  have h := hb s hs.1
  have he : (Finsupp.lmapDomain ℂ ℂ (fig14CoordinateState x₂ y₂)) (ket s)=ket s := by
    have hket (f : BasisState → BasisState) : (Finsupp.lmapDomain ℂ ℂ f) (ket s)=ket (f s) := by simp [ket]
    rw [hket,fig14CoordinateState_disabled x₂ y₂ hx₂ s hs.1 hs.2]
  simpa only [he,LinearMap.id_apply] using h
end ShorECDLP.Paper2607_13816
