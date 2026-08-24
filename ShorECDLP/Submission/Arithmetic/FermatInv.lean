import ShorECDLP.Submission.Arithmetic.Contracts
import ShorECDLP.Submission.Field

/-
# Fermat inversion from modular exponentiation (M1.6)

This is the thin correctness closure for field inversion.  It consumes the exact circuit term
already packaged by `ModExpContract`, fixes its preserved exponent register to `p - 2`, and
identifies the circuit output with inversion in `Fp` using `fermat_inv`.  It defines no second
exponentiation circuit and imports none of M1.5's private schedule or workspace.
-/

namespace ShorECDLP
namespace FermatInv

open Classical

/-- A correct modular-exponentiation circuit computes the secp256k1 field inverse when its
exponent input is `p - 2`.  The base and exponent registers are preserved and private work is
restored exactly as promised by the same `ModExpContract` term. -/
theorem correct [Fact (Nat.Prime p)] {program : Circuit} {layout : RegisterLayout} {cost : Nat}
    (spec : ModExpContract program layout p cost) (st : BasisState)
    (hlayout : layout.Valid) (hbase : regValue layout.lhs st < p)
    (hexponent : regValue layout.rhs st = p - 2)
    (hclean : Clean (layout.out ++ layout.work) st)
    (hnonzero : ((regValue layout.lhs st : Nat) : Fp) ≠ 0) :
    let after := run program st
    AgreesOn layout.lhs st after ∧
      AgreesOn layout.rhs st after ∧
      ((regValue layout.out after : Nat) : Fp) =
        ((regValue layout.lhs st : Nat) : Fp)⁻¹ ∧
      Clean layout.work after := by
  have hp2 : 2 ≤ p := (Fact.out (p := Nat.Prime p)).two_le
  have hexponentBound : regValue layout.rhs st < p := by
    rw [hexponent]
    omega
  obtain ⟨hlhs, hrhs, hout, hwork⟩ :=
    spec.correct st hlayout hbase hexponentBound hclean
  let after := run program st
  have houtPow :
      ((regValue layout.out after : Nat) : Fp) =
        ((regValue layout.lhs st : Nat) : Fp) ^ (p - 2) := by
    rw [hout, hexponent]
    simp
  exact ⟨hlhs, hrhs, houtPow.trans (fermat_inv _ hnonzero), hwork⟩

end FermatInv
end ShorECDLP
