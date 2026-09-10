import ShorECDLP.Submission.«2607_13816».Arithmetic.PointGeneric
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩
private def effectiveFactor {F : Type*} [Field F] [DecidableEq F] (x : F) : F :=
  if x=0 then 1 else x
private theorem effectiveFactor_ne_zero {F : Type*} [Field F] [DecidableEq F] (x : F) :
    effectiveFactor x≠0 := by
  unfold effectiveFactor
  split
  · exact one_ne_zero
  · assumption
private def fieldShiftX {F : Type*} [Field F] (k : F) : (F × F) ≃ (F × F) where
  toFun p := (p.1+k,p.2)
  invFun p := (p.1-k,p.2)
  left_inv := by intro p; ext <;> simp
  right_inv := by intro p; ext <;> simp
private def fieldShiftY {F : Type*} [Field F] (k : F) : (F × F) ≃ (F × F) where
  toFun p := (p.1,p.2+k)
  invFun p := (p.1,p.2-k)
  left_inv := by intro p; ext <;> simp
  right_inv := by intro p; ext <;> simp
private def fieldDivide {F : Type*} [Field F] [DecidableEq F] : (F × F) ≃ (F × F) where
  toFun p := (p.1,p.2*(effectiveFactor p.1)⁻¹)
  invFun p := (p.1,p.2*effectiveFactor p.1)
  left_inv := by intro p; ext <;> simp [effectiveFactor_ne_zero]
  right_inv := by intro p; ext <;> simp [effectiveFactor_ne_zero]
private def fieldSquareSubtract {F : Type*} [Field F] : (F × F) ≃ (F × F) where
  toFun p := (p.1-p.2*p.2,p.2)
  invFun p := (p.1+p.2*p.2,p.2)
  left_inv := by intro p; ext <;> simp
  right_inv := by intro p; ext <;> simp
private def fieldNegateX {F : Type*} [Field F] : (F × F) ≃ (F × F) where
  toFun p := (-p.1,p.2)
  invFun p := (-p.1,p.2)
  left_inv := by intro p; ext <;> simp
  right_inv := by intro p; ext <;> simp

/-- A field-coordinate permutation for the enabled Figure 14 stages. Both
potentially zero factors are explicitly replaced by one before inversion or multiplication. -/
noncomputable def fig14CoordinateEquiv (x₂ y₂ : ZMod ShorECDLP.p) :
    (ZMod ShorECDLP.p × ZMod ShorECDLP.p) ≃ (ZMod ShorECDLP.p × ZMod ShorECDLP.p) :=
  ((((((((fieldShiftX (-x₂)).trans (fieldShiftY (-y₂))).trans fieldDivide).trans
    fieldSquareSubtract).trans (fieldShiftX (3*x₂))).trans fieldDivide.symm).trans
    fieldNegateX).trans (fieldShiftX x₂)).trans (fieldShiftY (-y₂))

private theorem coordinateEquiv_apply (x₂ y₂ x y : ZMod ShorECDLP.p) :
    fig14CoordinateEquiv x₂ y₂ (x,y)=
      let a := x-x₂
      let b := y-y₂
      let u := b*(effectiveFactor a)⁻¹
      let v := a-u*u
      let w := v+3*x₂
      let z := u*effectiveFactor w
      (-w+x₂,z-y₂) := by
  simp only [fig14CoordinateEquiv,Equiv.trans_apply,fieldShiftX,fieldShiftY,fieldDivide,
    fieldSquareSubtract,fieldNegateX,Equiv.coe_fn_mk,Equiv.symm,sub_eq_add_neg]

private theorem cast_effective (a : Nat) (ha : a<ShorECDLP.p) :
    ((if a=0 then 1 else a : Nat) : ZMod ShorECDLP.p)=effectiveFactor (a : ZMod ShorECDLP.p) := by
  by_cases hz : a=0
  · simp [hz,effectiveFactor]
  · have hn : (a : ZMod ShorECDLP.p)≠0 := by
      intro h
      apply hz
      have hv := congrArg ZMod.val h
      simpa [Nat.mod_eq_of_lt ha] using hv
    simp [hz,hn,effectiveFactor]
private theorem cast_effective_inverse (a : Nat) (ha : a<ShorECDLP.p) :
    (paperInverse ShorECDLP.p (if a=0 then 1 else a) : ZMod ShorECDLP.p)=
      (effectiveFactor (a : ZMod ShorECDLP.p))⁻¹ := by
  have he : 1≤(if a=0 then 1 else a) := by split <;> omega
  have hp : (if a=0 then 1 else a)<ShorECDLP.p := by
    split
    · exact ShorECDLP.Secp256k1.p_prime.one_lt
    · exact ha
  have hh := eq_inv_of_mul_eq_one_left (paperRun_inverse_mod_prime ShorECDLP.Secp256k1.p_prime he hp)
  rw [cast_effective a ha] at hh
  exact hh

private theorem cast_point_offset (x c : Nat) (hc : c<ShorECDLP.p) :
    (((x+(ShorECDLP.p-c)%ShorECDLP.p)%ShorECDLP.p : Nat) : ZMod ShorECDLP.p)=
      (x : ZMod ShorECDLP.p)-(c : ZMod ShorECDLP.p) := by
  simp [Nat.cast_sub hc.le,sub_eq_add_neg]
private theorem cast_point_subtract (a b : Nat) (hb : b<ShorECDLP.p) :
    (((a+ShorECDLP.p-b)%ShorECDLP.p : Nat) : ZMod ShorECDLP.p)=
      (a : ZMod ShorECDLP.p)-(b : ZMod ShorECDLP.p) := by
  have hle : b≤a+ShorECDLP.p := by omega
  simp [Nat.cast_sub hle]
private theorem equiv_from_steps (x₂ y₂ x y a b u v w z : Nat)
    (hx₂ : x₂<ShorECDLP.p) (hy₂ : y₂<ShorECDLP.p)
    (ha_def : a=(x+(ShorECDLP.p-x₂)%ShorECDLP.p)%ShorECDLP.p)
    (hb_def : b=(y+(ShorECDLP.p-y₂)%ShorECDLP.p)%ShorECDLP.p)
    (hu_def : u=(b*paperInverse ShorECDLP.p (if a=0 then 1 else a))%ShorECDLP.p)
    (hv_def : v=(a+ShorECDLP.p-(u*u)%ShorECDLP.p)%ShorECDLP.p)
    (hw_def : w=(v+(3*x₂)%ShorECDLP.p)%ShorECDLP.p)
    (hz_def : z=(u*(if w=0 then 1 else w))%ShorECDLP.p) :
    (((((ShorECDLP.p-w)%ShorECDLP.p+x₂%ShorECDLP.p)%ShorECDLP.p : Nat) : ZMod ShorECDLP.p),
      (((z+(ShorECDLP.p-y₂)%ShorECDLP.p)%ShorECDLP.p : Nat) : ZMod ShorECDLP.p))=
      fig14CoordinateEquiv x₂ y₂ (x,y) := by
  have hp (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  have ha : (a : ZMod ShorECDLP.p)=(x : ZMod ShorECDLP.p)-x₂ := by
    rw [ha_def]; exact cast_point_offset x x₂ hx₂
  have hb : (b : ZMod ShorECDLP.p)=(y : ZMod ShorECDLP.p)-y₂ := by
    rw [hb_def]; exact cast_point_offset y y₂ hy₂
  have hal : a<ShorECDLP.p := by rw [ha_def]; exact hp _
  have hwl : w<ShorECDLP.p := by rw [hw_def]; exact hp _
  have hu : (u : ZMod ShorECDLP.p)=(b : ZMod ShorECDLP.p)*(effectiveFactor (a : ZMod ShorECDLP.p))⁻¹ := by
    rw [hu_def]
    simp only [ZMod.natCast_mod,Nat.cast_mul,cast_effective_inverse a hal]
  have hv : (v : ZMod ShorECDLP.p)=(a : ZMod ShorECDLP.p)-(u : ZMod ShorECDLP.p)*u := by
    rw [hv_def,cast_point_subtract a ((u*u)%ShorECDLP.p) (hp _)]
    simp only [ZMod.natCast_mod,Nat.cast_mul]
  have hw : (w : ZMod ShorECDLP.p)=(v : ZMod ShorECDLP.p)+3*x₂ := by
    rw [hw_def]
    simp only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hz : (z : ZMod ShorECDLP.p)=(u : ZMod ShorECDLP.p)*effectiveFactor (w : ZMod ShorECDLP.p) := by
    rw [hz_def]
    simp only [ZMod.natCast_mod,Nat.cast_mul,cast_effective w hwl]
  have hncast : ((ShorECDLP.p-w : Nat) : ZMod ShorECDLP.p)=-(w : ZMod ShorECDLP.p) := by
    rw [Nat.cast_sub hwl.le,ZMod.natCast_self,zero_sub]
  rw [cast_point_offset z y₂ hy₂,coordinateEquiv_apply]
  simp only [ZMod.natCast_mod,Nat.cast_add,hncast,hz,hw,hv,hu,hb,ha]

/-- The complete enabled coordinate formula is a permutation of field-coordinate
pairs, including all zero-factor cases. -/
theorem fig14CoordinateValues_equiv (x₂ y₂ x y : Nat)
    (hx₂ : x₂<ShorECDLP.p) (hy₂ : y₂<ShorECDLP.p) :
    (((fig14CoordinateValues x₂ y₂ true x y).1 : ZMod ShorECDLP.p),
      ((fig14CoordinateValues x₂ y₂ true x y).2 : ZMod ShorECDLP.p))=
      fig14CoordinateEquiv x₂ y₂ (x,y) := by
  let a := (x+(ShorECDLP.p-x₂)%ShorECDLP.p)%ShorECDLP.p
  let b := (y+(ShorECDLP.p-y₂)%ShorECDLP.p)%ShorECDLP.p
  let u := (b*paperInverse ShorECDLP.p (if a=0 then 1 else a))%ShorECDLP.p
  let v := (a+ShorECDLP.p-(u*u)%ShorECDLP.p)%ShorECDLP.p
  let w := (v+(3*x₂)%ShorECDLP.p)%ShorECDLP.p
  let z := (u*(if w=0 then 1 else w))%ShorECDLP.p
  have hh := equiv_from_steps x₂ y₂ x y a b u v w z hx₂ hy₂ rfl rfl rfl rfl rfl rfl
  simpa only [fig14CoordinateValues,Bool.true_eq,if_true,a,b,u,v,w,z] using hh

attribute [local irreducible] fig14CoordinateState

/-- The actual enabled circuit implements the field permutation even on zero factors. -/
theorem fig14CoordinateState_equiv (x₂ y₂ : Nat)
    (hx₂ : x₂<ShorECDLP.p) (hy₂ : y₂<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=true) :
    ((boolWordToNat (wireValues (List.range' 263 256) (fig14CoordinateState x₂ y₂ s)) : ZMod ShorECDLP.p),
      (boolWordToNat (wireValues (List.range' 580 256) (fig14CoordinateState x₂ y₂ s)) : ZMod ShorECDLP.p))=
      fig14CoordinateEquiv x₂ y₂
        (boolWordToNat (wireValues (List.range' 263 256) s),boolWordToNat (wireValues (List.range' 580 256) s)) := by
  have hv := fig14CoordinateState_values x₂ y₂ s hs
  rw [hq] at hv
  have he := congrArg (fun v : Nat × Nat => ((v.1 : ZMod ShorECDLP.p),(v.2 : ZMod ShorECDLP.p))) hv
  exact he.trans (fig14CoordinateValues_equiv x₂ y₂ _ _ hx₂ hy₂)

/-- No two valid enabled inputs collide, including complete external states and
all exceptional coordinate pairs. -/
theorem fig14CoordinateState_injectiveOn (x₂ y₂ : Nat)
    (hx₂ : x₂<ShorECDLP.p) (hy₂ : y₂<ShorECDLP.p) :
    Set.InjOn (fig14CoordinateState x₂ y₂)
      {s | Secp256k1ZeroAllowedInputValid s ∧ s 836=true} := by
  intro s hs t ht heq
  have hvs := fig14CoordinateState_equiv x₂ y₂ hx₂ hy₂ s hs.1 hs.2
  have hvt := fig14CoordinateState_equiv x₂ y₂ hx₂ hy₂ t ht.1 ht.2
  have hout := congrArg (fun u : BasisState =>
    ((boolWordToNat (wireValues (List.range' 263 256) u) : ZMod ShorECDLP.p),
      (boolWordToNat (wireValues (List.range' 580 256) u) : ZMod ShorECDLP.p))) heq
  have hi := (fig14CoordinateEquiv x₂ y₂).injective (hvs.symm.trans (hout.trans hvt))
  have hx := congrArg (fun v : ZMod ShorECDLP.p × ZMod ShorECDLP.p => ZMod.val v.1) hi
  have hy := congrArg (fun v : ZMod ShorECDLP.p × ZMod ShorECDLP.p => ZMod.val v.2) hi
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hs.1.2.2.1,Nat.mod_eq_of_lt ht.1.2.2.1] at hx
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hs.1.2.2.2,Nat.mod_eq_of_lt ht.1.2.2.2] at hy
  have hX : wireValues (List.range' 263 256) s=wireValues (List.range' 263 256) t :=
    boolWordToNat_injective_of_length (by simp [wireValues]) hx
  have hY : wireValues (List.range' 580 256) s=wireValues (List.range' 580 256) t :=
    boolWordToNat_injective_of_length (by simp [wireValues]) hy
  funext w
  by_cases hwX : w ∈ List.range' 263 256
  · exact List.map_inj_left.mp hX w hwX
  · by_cases hwY : w ∈ List.range' 580 256
    · exact List.map_inj_left.mp hY w hwY
    · calc
        s w = fig14CoordinateState x₂ y₂ s w := (fig14CoordinateState_frame x₂ y₂ s hs.1 w hwX hwY).symm
        _ = fig14CoordinateState x₂ y₂ t w := congrFun heq w
        _ = t w := fig14CoordinateState_frame x₂ y₂ t ht.1 w hwX hwY
end ShorECDLP.Paper2607_13816
