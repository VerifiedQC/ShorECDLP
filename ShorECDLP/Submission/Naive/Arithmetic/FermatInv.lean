import ShorECDLP.Submission.Naive.Arithmetic.Contracts
import ShorECDLP.Math.Field

/-!
# Fermat inversion from modular exponentiation (M1.6)

This is the thin correctness closure for field inversion.  It consumes the exact circuit term
already packaged by `ModExpContract`, fixes its preserved exponent register to `p - 2`, and
identifies the circuit output with inversion in `Fp` using `fermat_inv`.  It defines no second
exponentiation circuit and imports none of M1.5's private schedule or workspace.

## Program (syntax-sugared)

This file defines **no new circuit**. Its program is any supplied modular-exponentiation circuit
already certified by `ModExpContract`:

```text
program := supplied ModExp program
value(layout.rhs, before) := p - 2
after := run program before
```

## Specification

Under `[Fact (Nat.Prime p)]`, a canonical nonzero base, exponent `p - 2`, a valid layout, and
clean output/work registers,

```text
value(layout.out, after) as Fp = (value(layout.lhs, before) as Fp)^(-1)
layout.lhs and layout.rhs are preserved
layout.work is clean in after
```

The same supplied `program`, layout, cleanup guarantee, and cost remain those of the input
`ModExpContract`; `FermatInv.correct` is only the final field-theory proof.
-/

namespace ShorECDLP
namespace FermatInv

open Classical
open scoped ArithmeticNotation

/-- A correct modular-exponentiation circuit computes the secp256k1 field inverse when its
exponent input is `p - 2`.  The base and exponent registers are preserved and private work is
restored exactly as promised by the same `ModExpContract` term. -/
theorem correct [Fact (Nat.Prime p)] {program : Circuit} {layout : RegisterLayout} {cost : Nat}
    (spec : ModExpContract program layout p cost) (st : BasisState)
    (hlayout : layout.Valid) (hbase : st⟦ᵣlayout.lhs⟧ < p)
    (hexponent : st⟦ᵣlayout.rhs⟧ = p - 2)
    (hclean : clean(layout.out ++ layout.work, st))
    (hnonzero : ((st⟦ᵣlayout.lhs⟧ : Nat) : Fp) ≠ 0) :
    let after := run program st
    AgreesOn layout.lhs st after ∧
      AgreesOn layout.rhs st after ∧
      ((after⟦ᵣlayout.out⟧ : Nat) : Fp) =
        ((st⟦ᵣlayout.lhs⟧ : Nat) : Fp)⁻¹ ∧
      clean(layout.work, after) := by
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
