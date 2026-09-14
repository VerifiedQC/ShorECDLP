import ShorECDLP.Submission.«2607_13816».Window.CharacterExpansion
import ShorECDLP.Submission.«2607_13816».OrderFinding.PhysicalPair
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1 Quantum.PhaseEstimation Quantum.OrderFinding
open scoped BigOperators
noncomputable section
private theorem list_sum_fin {α : Type} {r : Nat} (xs : List α) (f : α → Fin r → State) :
    (xs.map (fun x => ∑ k, f x k)).sum = ∑ k, (xs.map (fun x => f x k)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Finset.sum_add_distrib]
private theorem list_sum_smul {α : Type} (xs : List α) (f : α → ℂ) (v : State) :
    (xs.map (fun x => f x • v)).sum = (xs.map f).sum • v := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_smul]
private theorem scalar_list_sum {α : Type} (c : ℂ) (xs : List α) (f : α → State) :
    c • (xs.map f).sum = (xs.map (fun x => c • f x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, smul_add]
private theorem list_sum_mul {α : Type} (xs : List α) (f : α → ℂ) (c : ℂ) :
    (xs.map (fun x => f x * c)).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_mul]
/-- Fourier-weighted orbit sums diagonalize in the cyclic character basis. -/
theorem weighted_point_character_sum {r : Nat} (hr : Nat.Prime r) (P : Point)
    (horder : addOrderOf P = r) (s : BasisState) (xs ys : List Nat)
    (f g : Nat → ℂ) (d : Nat) :
    (xs.map (fun a => (ys.map (fun b => (f a * g b) •
      ket (pointWrite ((a+d*b) • P) s))).sum)).sum =
    (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • ∑ k : Fin r,
      (((xs.map (fun a => f a * eigenvalue (((k.val:ℝ)/(r:ℝ))*a))).sum) *
       ((ys.map (fun b => g b * eigenvalue (((k.val*d:Nat):ℝ)/(r:ℝ)*b))).sum)) •
        pointCyclicState P s k := by
  have he (k a b : Nat) : eigenvalue (((k*(a+d*b):Nat):ℝ)/(r:ℝ)) =
      eigenvalue (((k:ℝ)/(r:ℝ))*a) * eigenvalue (((k*d:Nat):ℝ)/(r:ℝ)*b) := by
    rw [←eigenvalue_add]
    congr 1
    push_cast
    ring
  have hex (a b : Nat) : (f a * g b) • ket (pointWrite ((a+d*b) • P) s) =
      (((Real.sqrt r)⁻¹:ℝ):ℂ) • ∑ k : Fin r,
        (f a * g b * (eigenvalue (((k.val:ℝ)/(r:ℝ))*a) *
          eigenvalue (((k.val*d:Nat):ℝ)/(r:ℝ)*b))) • pointCyclicState P s k := by
    rw [pointKet_character_expansion hr P horder s, smul_comm]
    apply congrArg (fun v : State => (((Real.sqrt r)⁻¹:ℝ):ℂ) • v)
    simp only [Finset.smul_sum, smul_smul, he]
  simp_rw [hex]
  simp_rw [←scalar_list_sum, list_sum_fin]
  apply congrArg (fun v : State => (((Real.sqrt r)⁻¹:ℝ):ℂ) • v)
  apply Finset.sum_congr rfl
  intro k hk
  have hc (a b : Nat) : f a * g b *
      (eigenvalue (((k.val:ℝ)/(r:ℝ))*a) * eigenvalue (((k.val*d:Nat):ℝ)/(r:ℝ)*b)) =
      (f a * eigenvalue (((k.val:ℝ)/(r:ℝ))*a)) * (g b * eigenvalue (((k.val*d:Nat):ℝ)/(r:ℝ)*b)) := by ring
  simp_rw [hc, ←smul_smul, ←scalar_list_sum]
  simp only [smul_smul, list_sum_smul]
  simp only [←mul_assoc, list_sum_mul]

/-- The normalized double Fourier sum has the product phase amplitudes. -/
theorem normalized_point_character_sum {r : Nat} (hr : Nat.Prime r) (P : Point)
    (horder : addOrderOf P = r) (s : BasisState) (n d : Nat) (x y : List Bool)
    (hx : x.length=n) (hy : y.length=n) :
    let N : ℂ := ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^n) * ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^n)
    (N*N) • ((fourierOutcomes n).map (fun a => ((fourierOutcomes n).map (fun b =>
      (dyadicFourierKernel .inverse n (boolWordToNat a) (fourierWordLSB x) *
       dyadicFourierKernel .inverse n (boolWordToNat b) (fourierWordLSB y)) •
       ket (pointWrite ((boolWordToNat a+d*boolWordToNat b) • P) s))).sum)).sum =
    (((Real.sqrt r)⁻¹:ℝ):ℂ) • ∑ k : Fin r,
      (paperPhaseAmplitude n ((k.val:ℝ)/(r:ℝ)) (fourierWordLSB x) *
       paperPhaseAmplitude n (((k.val*d:Nat):ℝ)/(r:ℝ)) (fourierWordLSB y)) •
        pointCyclicState P s k := by
  dsimp only
  have hw := weighted_point_character_sum hr P horder s
    ((fourierOutcomes n).map boolWordToNat) ((fourierOutcomes n).map boolWordToNat)
    (fun a => dyadicFourierKernel .inverse n a (fourierWordLSB x))
    (fun b => dyadicFourierKernel .inverse n b (fourierWordLSB y)) d
  simp only [List.map_map, Function.comp_def] at hw
  rw [hw, smul_comm]
  apply congrArg (fun v : State => (((Real.sqrt r)⁻¹:ℝ):ℂ) • v)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_smul]
  have ha := phaseWord_weighted_sum ((k.val:ℝ)/(r:ℝ)) n x hx
  have hb := phaseWord_weighted_sum (((k.val*d:Nat):ℝ)/(r:ℝ)) n y hy
  rw [←ha, ←hb]
  congr 1
  ring

/-- The normalized point Fourier sum has exactly the uniform character-mixture mass. -/
theorem normalized_point_character_mass {r : Nat} (hr : Nat.Prime r) (P : Point)
    (horder : addOrderOf P=r) (s : BasisState) (n d : Nat) (x y : List Bool)
    (hx : x.length=n) (hy : y.length=n)
    (out : Fin (2^n) × Fin (2^n)) (hox : fourierWordLSB x=out.1.val)
    (hoy : fourierWordLSB y=out.2.val) :
    let N : ℂ := ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^n) * ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^n)
    normSq ((N*N) • ((fourierOutcomes n).map (fun a => ((fourierOutcomes n).map (fun b =>
      (dyadicFourierKernel .inverse n (boolWordToNat a) (fourierWordLSB x) *
       dyadicFourierKernel .inverse n (boolWordToNat b) (fourierWordLSB y)) •
       ket (pointWrite ((boolWordToNat a+d*boolWordToNat b) • P) s))).sum)).sum) =
    paperPairMass r n d out := by
  dsimp only
  rw [normalized_point_character_sum hr P horder s n d x y hx hy]
  rw [Finset.smul_sum]
  simp only [smul_smul, pointCyclicState]
  rw [cyclicState_mass hr _ (pointCyclicBasis_orthonormal P s horder)]
  have hn : Complex.normSq ((((Real.sqrt r)⁻¹:ℝ):ℂ))=1/(r:ℝ) := by
    simp [Complex.normSq_ofReal]
  have he (k : Fin r) : paperPhaseAmplitude n (((k.val*d:Nat):ℝ)/(r:ℝ)) out.2.val =
      paperPhaseAmplitude n ((((d*k.val)%r:Nat):ℝ)/(r:ℝ)) out.2.val := by
    rw [Nat.mul_comm k.val d]
    exact paperPhaseAmplitude_mod n r (d*k.val) out.2.val hr.pos
  simp_rw [Complex.normSq_mul, hn, hox, hoy, he]
  rw [←Finset.mul_sum]
  rfl

private theorem double_sum_normalize (xs ys : List (List Bool)) (f g : List Bool → ℂ)
    (c : ℂ) (P Q : Point) (d : Nat) (hQ : Q=d • P) (s : BasisState) :
    c • (xs.map (fun a => (ys.map (fun b => (c*f a*g b) •
      ket (pointWrite (boolWordToNat a • P+boolWordToNat b • Q) s))).sum)).sum =
    (c*c) • (xs.map (fun a => (ys.map (fun b => (f a*g b) •
      ket (pointWrite ((boolWordToNat a+d*boolWordToNat b) • P) s))).sum)).sum := by
  rw [←smul_smul c c]
  apply congrArg (fun v : State => c • v)
  rw [scalar_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [scalar_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  rw [smul_smul]
  have hpoint : boolWordToNat a • P+boolWordToNat b • Q =
      (boolWordToNat a+d*boolWordToNat b) • P := by
    rw [hQ, ←mul_nsmul, add_nsmul]
  rw [hpoint, mul_assoc]

/-- The actual windowed circuit's observed pair has the character-mixture probability. -/
theorem windowTrialOutputMass_character_mixture {r : Nat} (hr : Nat.Prime r)
    (P Q : Point) (hP : P≠0) (hQ : Q≠0) (hrP : order • P=0) (hrQ : order • Q=0)
    (horder : addOrderOf P=r) (d : Nat) (hQd : Q=d • P)
    (x y : List Bool) (hx : x.length=257) (hy : y.length=257)
    (out : Fin (2^257) × Fin (2^257)) (hox : fourierWordLSB x=out.1.val)
    (hoy : fourierWordLSB y=out.2.val) :
    windowTrialOutputMass P Q hP hQ hrP hrQ x y=paperPairMass r 257 d out := by
  rw [windowTrialOutputMass_point_sum P Q hP hQ hrP hrQ x y hx hy]
  rw [double_sum_normalize _ _ _ _ _ P Q d hQd zeroBasisState]
  have hp : ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^514)=
      ((((Real.sqrt 2)⁻¹:ℝ):ℂ)^257)*((((Real.sqrt 2)⁻¹:ℝ):ℂ)^257) := by
    rw [←pow_add]
  rw [hp]
  exact normalized_point_character_mass hr P horder zeroBasisState 257 d x y hx hy out hox hoy

end
end ShorECDLP.Paper2607_13816
