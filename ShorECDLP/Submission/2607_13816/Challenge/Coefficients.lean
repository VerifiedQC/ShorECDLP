import ShorECDLP.Challenge.Template
import ShorECDLP.Submission.«2607_13816».Window.OddTables
import ShorECDLP.Submission.«2607_13816».Window.ScalarWindows
import ShorECDLP.Submission.«2607_13816».Window.FirstWindowReplacement

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Challenge ShorECDLP.Secp256k1

/-- Canonical public coefficients; the problem instance is never an input. -/
def coefficients (a b : Nat) : PointCoeff :=
  ⟨⟨a % order, Nat.mod_lt _ (by decide)⟩,
   ⟨b % order, Nat.mod_lt _ (by decide)⟩⟩

theorem coefficients_point (a b : Nat) (Q : Point) (hQ : order • Q = 0) :
    constantPoint Q (coefficients a b) = a • G + b • Q := by
  unfold constantPoint coefficients
  dsimp
  rw [← nsmul_eq_mod_nsmul a generator_nsmul_eq_zero,
      ← nsmul_eq_mod_nsmul b hQ]

end ShorECDLP.Paper2607_13816.ChallengeMigration

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Challenge ShorECDLP.Secp256k1

theorem signedDigit_as_nsmul (P : Point) (hr : order • P = 0) (a : Nat) :
    signedWindowDigit 16 a • P = (a + (order - 32768)) • P := by
  have hl : 32768 ≤ order := by decide
  have hz : (order - 32768) • P + 32768 • P = 0 := by
    rw [← add_nsmul, Nat.sub_add_cancel hl, hr]
  have he := eq_neg_of_add_eq_zero_left hz
  change ((a : Int) - ((32768 : Nat) : Int)) • P = _
  rw [sub_zsmul]
  simp only [natCast_zsmul]
  rw [add_nsmul, he]
end ShorECDLP.Paper2607_13816.ChallengeMigration

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Challenge ShorECDLP.Secp256k1

def firstWindowCoefficients (i : Nat) : PointCoeff :=
  coefficients
    (65535 * radixGeometric 16 * ((order+1)/2) +
      (i + (order-32768)) * 2^(16*15) + ((order+1)/2) * 2^(16*15))
    (65535 * radixGeometric 13 * ((order+1)/2))

theorem firstWindowTable_coefficients (P Q : Point) (hr : order • P = 0) (i : Nat) :
    firstWindowTable (axisWindowOffset P 16 + axisWindowOffset Q 13)
      ((2^(16*15)) • P) i =
    (65535 * radixGeometric 16 * ((order+1)/2) +
      (i + (order-32768)) * 2^(16*15) + ((order+1)/2) * 2^(16*15)) • P +
    (65535 * radixGeometric 13 * ((order+1)/2)) • Q := by
  have hw : order • ((2^(16*15)) • P) = 0 := by
    rw [smul_comm, hr]
    exact nsmul_zero _
  rw [firstWindowTable, signedDigit_as_nsmul _ hw]
  simp only [axisWindowOffset, signedWindowHalfPoint, add_nsmul, mul_smul]
  abel

theorem firstWindowCoefficients_point (i : Nat) (Q : Point) (hQ : order • Q = 0) :
    constantPoint Q (firstWindowCoefficients i) =
      firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
        ((2^(16*15)) • G) i :=
  (coefficients_point _ _ Q hQ).trans
    (firstWindowTable_coefficients G Q generator_nsmul_eq_zero i).symm
end ShorECDLP.Paper2607_13816.ChallengeMigration
