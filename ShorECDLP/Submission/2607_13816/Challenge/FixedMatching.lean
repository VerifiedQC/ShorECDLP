import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCorrection
namespace ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Repeated inputs are safe: their already-corrected pair contributes an identity swap. -/
theorem fixedMatching_correct {α β : Type*} [DecidableEq α]
    (F T : β → α) (hF : Function.Injective F) (hT : Function.Injective T)
    (inputs : List β) : ∀ x ∈ inputs,
    finiteMatchingPermutation (inputs.map fun y => (F y, T y)) (F x) = T x := by
  classical
  induction inputs with
  | nil => simp
  | cons y ys ih =>
    intro x hx
    simp only [List.map_cons, finiteMatchingPermutation, Equiv.trans_apply]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact Equiv.swap_apply_left _ _
    · rw [ih x hmem]
      by_cases hxy : x = y
      · subst y
        rw [ih x hmem]
        simp
      · apply Equiv.swap_apply_of_ne_of_ne
        · intro he
          have he' := (ih x hmem).trans he
          exact hxy (hF ((finiteMatchingPermutation (ys.map fun z => (F z, T z))).injective he'))
        · exact fun he => hxy (hT he)

/-- A fixed list of candidates can replace Q-dependent deduplication. -/
theorem fixedMatching_comp {α β : Type*} [DecidableEq α]
    (F T : β → α) (hF : Function.Injective F) (hT : Function.Injective T)
    (inputs : List β) (hgood : ∀ x, x ∉ inputs → F x = T x) : ∀ x,
    finiteMatchingPermutation (inputs.map fun y => (F y, T y)) (F x) = T x := by
  classical
  intro x
  by_cases hx : x ∈ inputs
  · exact fixedMatching_correct F T hF hT inputs x hx
  · rw [finiteMatchingPermutation_frame _ (F x) ?_ ?_, hgood x hx]
    · simp only [List.map_map, Function.comp_def, List.mem_map]
      rintro ⟨y, hy, he⟩
      exact hx ((hF he) ▸ hy)
    · simp only [List.map_map, Function.comp_def, List.mem_map]
      rintro ⟨y, hy, he⟩
      exact hx ((hT (he.trans (hgood x hx))) ▸ hy)


open ShorECDLP ShorECDLP.Secp256k1
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

def fixedExceptionInputs (C : Point) : List Point := [0, C, -C, -(C+C)]

/-- Semantic reference only: these endpoint values still require on-circuit computation. -/
def fixedExceptionPairs {x y : Fp} (hC : curve.toAffine.Nonsingular x y) :
    List ((Bool × (Fp × Fp)) × (Bool × (Fp × Fp))) :=
  (fixedExceptionInputs (.some hC)).map fun P =>
    (fig14EncodedEquiv x y (fig14PointEncoding P), fig14PointEncoding (P + .some hC))

def fixedExceptionSwaps {x y : Fp} (hC : curve.toAffine.Nonsingular x y) :=
  finiteMatchingSwaps (fixedExceptionPairs hC)

theorem fixedExceptionSwaps_length {x y : Fp} (hC : curve.toAffine.Nonsingular x y) :
    (fixedExceptionSwaps hC).length = 4 := by
  rw [fixedExceptionSwaps, finiteMatchingSwaps_length, fixedExceptionPairs, List.length_map]
  rfl

theorem fixedExceptionSwaps_correct {x y : Fp} (hC : curve.toAffine.Nonsingular x y) (P : Point) :
    runFiniteSwaps (fixedExceptionSwaps hC) (fig14EncodedEquiv x y (fig14PointEncoding P)) =
      fig14PointEncoding (P + .some hC) := by
  rw [fixedExceptionSwaps, finiteMatchingSwaps_apply]
  apply fixedMatching_comp
    (fun Q => fig14EncodedEquiv x y (fig14PointEncoding Q))
    (fun Q => fig14PointEncoding (Q + .some hC))
    ((fig14EncodedEquiv x y).injective.comp fig14PointEncoding_injective)
    (fun _ _ h => add_right_cancel (fig14PointEncoding_injective h))
    (fixedExceptionInputs (.some hC))
  intro Q hQ
  exact fig14EncodedEquiv_nonexceptional hC Q
    (by simpa [fixedExceptionInputs, fig14ExceptionalPoints] using hQ)

end ShorECDLP.Paper2607_13816.ChallengeMigration
