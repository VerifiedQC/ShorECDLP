import ShorECDLP.Submission.«2607_13816».Arithmetic.PointValues
import ShorECDLP.Math.EllipticCurve.AffineFormula
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩
private theorem cast_offset (x c : Nat) (hc : c<ShorECDLP.p) :
    (((x+(ShorECDLP.p-c)%ShorECDLP.p)%ShorECDLP.p : Nat) : ZMod ShorECDLP.p)=
      (x : ZMod ShorECDLP.p)-(c : ZMod ShorECDLP.p) := by
  simp [Nat.cast_sub hc.le,sub_eq_add_neg]
private theorem cast_subtract (a b : Nat) (hb : b<ShorECDLP.p) :
    (((a+ShorECDLP.p-b)%ShorECDLP.p : Nat) : ZMod ShorECDLP.p)=
      (a : ZMod ShorECDLP.p)-(b : ZMod ShorECDLP.p) := by
  have hle : b≤a+ShorECDLP.p := by omega
  simp [Nat.cast_sub hle]
private theorem cast_inverse (a : Nat) (ha : a<ShorECDLP.p) (hn : a≠0) :
    (paperInverse ShorECDLP.p a : ZMod ShorECDLP.p)=(a : ZMod ShorECDLP.p)⁻¹ := by
  have hi := paperRun_inverse_mod_prime ShorECDLP.Secp256k1.p_prime (x:=a) (by omega) ha
  exact eq_inv_of_mul_eq_one_left hi

private theorem field_square_shift {F : Type*} [Field F] (x x₂ l : F) :
    x-x₂-l*l+3*x₂=x₂-(l^2-x-x₂) := by ring
private theorem field_finish_X {F : Type*} [Field F] (x₂ xo : F) :
    -(x₂-xo)+x₂=xo := by ring
private theorem field_finish_Y {F : Type*} [Field F] (x y x₂ y₂ xo l : F)
    (hl : l*(x-x₂)=y-y₂) : l*(x₂-xo)-y₂=l*(x-xo)-y := by
  linear_combination -hl

private theorem generic_from_steps (x₂ y₂ x y a b u v w z : Nat)
    (hx₂ : x₂<ShorECDLP.p) (hy₂ : y₂<ShorECDLP.p)
    (hden : (x : ZMod ShorECDLP.p)≠(x₂ : ZMod ShorECDLP.p))
    (hsecond : (x₂ : ZMod ShorECDLP.p)≠ShorECDLP.Secp256k1.genericX x y x₂ y₂)
    (ha_def : a=(x+(ShorECDLP.p-x₂)%ShorECDLP.p)%ShorECDLP.p)
    (hb_def : b=(y+(ShorECDLP.p-y₂)%ShorECDLP.p)%ShorECDLP.p)
    (hu_def : u=(b*paperInverse ShorECDLP.p (if a=0 then 1 else a))%ShorECDLP.p)
    (hv_def : v=(a+ShorECDLP.p-(u*u)%ShorECDLP.p)%ShorECDLP.p)
    (hw_def : w=(v+(3*x₂)%ShorECDLP.p)%ShorECDLP.p)
    (hz_def : z=(u*(if w=0 then 1 else w))%ShorECDLP.p) :
    ((((ShorECDLP.p-w)%ShorECDLP.p+x₂%ShorECDLP.p)%ShorECDLP.p : Nat) : ZMod ShorECDLP.p)=
      ShorECDLP.Secp256k1.genericX x y x₂ y₂ ∧
    (((z+(ShorECDLP.p-y₂)%ShorECDLP.p)%ShorECDLP.p : Nat) : ZMod ShorECDLP.p)=
      ShorECDLP.Secp256k1.genericY x y x₂ y₂ := by
  let l : ZMod ShorECDLP.p := ((y : ZMod ShorECDLP.p)-y₂)*((x : ZMod ShorECDLP.p)-x₂)⁻¹
  have hp (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  have ha : (a : ZMod ShorECDLP.p)=(x : ZMod ShorECDLP.p)-x₂ := by rw [ha_def]; exact cast_offset x x₂ hx₂
  have hb : (b : ZMod ShorECDLP.p)=(y : ZMod ShorECDLP.p)-y₂ := by rw [hb_def]; exact cast_offset y y₂ hy₂
  have hal : a<ShorECDLP.p := by rw [ha_def]; exact hp _
  have han : a≠0 := by
    intro h
    have hh : (x : ZMod ShorECDLP.p)-x₂=0 := by rw [← ha,h,Nat.cast_zero]
    exact hden (sub_eq_zero.mp hh)
  have hu : (u : ZMod ShorECDLP.p)=l := by
    rw [hu_def]
    rw [if_neg han]
    simp only [Nat.cast_mul,ZMod.natCast_mod,cast_inverse a hal han,ha,hb,l]
  have hv : (v : ZMod ShorECDLP.p)=(a : ZMod ShorECDLP.p)-l*l := by
    rw [show (v : ZMod ShorECDLP.p)=(a : ZMod ShorECDLP.p)-((u*u)%ShorECDLP.p : Nat) from
      by rw [hv_def]; exact cast_subtract a ((u*u)%ShorECDLP.p) (hp _)]
    simp only [ZMod.natCast_mod,Nat.cast_mul,hu]
  have hw : (w : ZMod ShorECDLP.p)=(x₂ : ZMod ShorECDLP.p)-ShorECDLP.Secp256k1.genericX x y x₂ y₂ := by
    rw [hw_def]
    simp only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hv,ha]
    change (x : ZMod ShorECDLP.p)-x₂-l*l+3*x₂=(x₂ : ZMod ShorECDLP.p)-(l^2-x-x₂)
    exact field_square_shift _ _ _
  have hwn : w≠0 := by
    intro h
    have hh : (x₂ : ZMod ShorECDLP.p)-ShorECDLP.Secp256k1.genericX x y x₂ y₂=0 := by
      rw [← hw,h,Nat.cast_zero]
    exact hsecond (sub_eq_zero.mp hh)
  have hz : (z : ZMod ShorECDLP.p)=l*(w : ZMod ShorECDLP.p) := by
    rw [hz_def]
    simp only [if_neg hwn,ZMod.natCast_mod,Nat.cast_mul,hu]
  have hsl : l*((x : ZMod ShorECDLP.p)-x₂)=(y : ZMod ShorECDLP.p)-y₂ := by
    dsimp only [l]
    rw [mul_assoc,inv_mul_cancel₀ (sub_ne_zero.mpr hden),mul_one]
  have hwl : w<ShorECDLP.p := by rw [hw_def]; exact hp _
  have hncast : ((ShorECDLP.p-w : Nat) : ZMod ShorECDLP.p)=-(w : ZMod ShorECDLP.p) := by
    rw [Nat.cast_sub hwl.le,ZMod.natCast_self,zero_sub]
  constructor
  · simp only [ZMod.natCast_mod,Nat.cast_add,hncast,hw]
    exact field_finish_X _ _
  · rw [cast_offset z y₂ hy₂,hz,hw]
    change l*((x₂ : ZMod ShorECDLP.p)-ShorECDLP.Secp256k1.genericX x y x₂ y₂)-y₂=
      l*((x : ZMod ShorECDLP.p)-ShorECDLP.Secp256k1.genericX x y x₂ y₂)-y
    exact field_finish_Y _ _ _ _ _ _ hsl

/-- On the nonexceptional affine domain, the actual coordinate formula is the
usual addition formula. The second excluded zero factor is explicit. -/
theorem fig14CoordinateValues_generic (x₂ y₂ x y : Nat)
    (hx₂ : x₂<ShorECDLP.p) (hy₂ : y₂<ShorECDLP.p)
    (hden : (x : ZMod ShorECDLP.p)≠(x₂ : ZMod ShorECDLP.p))
    (hsecond : (x₂ : ZMod ShorECDLP.p)≠ShorECDLP.Secp256k1.genericX x y x₂ y₂) :
    ((fig14CoordinateValues x₂ y₂ true x y).1 : ZMod ShorECDLP.p)=ShorECDLP.Secp256k1.genericX x y x₂ y₂ ∧
    ((fig14CoordinateValues x₂ y₂ true x y).2 : ZMod ShorECDLP.p)=ShorECDLP.Secp256k1.genericY x y x₂ y₂ := by
  let a := (x+(ShorECDLP.p-x₂)%ShorECDLP.p)%ShorECDLP.p
  let b := (y+(ShorECDLP.p-y₂)%ShorECDLP.p)%ShorECDLP.p
  let u := (b*paperInverse ShorECDLP.p (if a=0 then 1 else a))%ShorECDLP.p
  let v := (a+ShorECDLP.p-(u*u)%ShorECDLP.p)%ShorECDLP.p
  let w := (v+(3*x₂)%ShorECDLP.p)%ShorECDLP.p
  let z := (u*(if w=0 then 1 else w))%ShorECDLP.p
  have hh := generic_from_steps x₂ y₂ x y a b u v w z hx₂ hy₂ hden hsecond rfl rfl rfl rfl rfl rfl
  simpa only [fig14CoordinateValues,Bool.true_eq,if_true,a,b,u,v,w,z] using hh

attribute [local irreducible] fig14CoordinateState

/-- The actual enabled coordinate circuit agrees with the affine addition
formula wherever both source multipliers are nonzero. -/
theorem fig14CoordinateState_generic (x₂ y₂ : Nat)
    (hx₂ : x₂<ShorECDLP.p) (hy₂ : y₂<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=true)
    (hden : (boolWordToNat (wireValues (List.range' 263 256) s) : ZMod ShorECDLP.p)≠x₂)
    (hsecond : (x₂ : ZMod ShorECDLP.p)≠ShorECDLP.Secp256k1.genericX
      (boolWordToNat (wireValues (List.range' 263 256) s))
      (boolWordToNat (wireValues (List.range' 580 256) s)) x₂ y₂) :
    (boolWordToNat (wireValues (List.range' 263 256) (fig14CoordinateState x₂ y₂ s)) : ZMod ShorECDLP.p)=
      ShorECDLP.Secp256k1.genericX (boolWordToNat (wireValues (List.range' 263 256) s))
        (boolWordToNat (wireValues (List.range' 580 256) s)) x₂ y₂ ∧
    (boolWordToNat (wireValues (List.range' 580 256) (fig14CoordinateState x₂ y₂ s)) : ZMod ShorECDLP.p)=
      ShorECDLP.Secp256k1.genericY (boolWordToNat (wireValues (List.range' 263 256) s))
        (boolWordToNat (wireValues (List.range' 580 256) s)) x₂ y₂ := by
  have hv := fig14CoordinateState_values x₂ y₂ s hs
  rw [hq] at hv
  have hg := fig14CoordinateValues_generic x₂ y₂ _ _ hx₂ hy₂ hden hsecond
  have hX := congrArg (fun v : Nat × Nat => (v.1 : ZMod ShorECDLP.p)) hv
  have hY := congrArg (fun v : Nat × Nat => (v.2 : ZMod ShorECDLP.p)) hv
  exact ⟨hX.trans hg.1,hY.trans hg.2⟩
end ShorECDLP.Paper2607_13816
