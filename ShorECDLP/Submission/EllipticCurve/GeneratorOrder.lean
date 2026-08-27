import ShorECDLP.Submission.EllipticCurve.AffineFormula
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.ReduceModChar

/-!
# secp256k1 primality and generator-order certificate layer

This module contains Lucas/Pratt-style certificates for the two published prime constants
used by the concrete secp256k1 specialization.  The generator-order certificate replays
the affine scalar multiplication for the published order and generator, then uses primality
and `G_ne_zero` to identify the additive order exactly.
-/

namespace ShorECDLP
namespace Secp256k1

private theorem lucasFromFactors (n a : Nat) (factors : List Nat)
    (ha : (a : ZMod n) ^ (n - 1) = 1)
    (hn1 : n - 1 ≠ 0)
    (hprod : factors.prod = n - 1)
    (hprime : ∀ q ∈ factors, Nat.Prime q)
    (hpow : ∀ q ∈ factors, (a : ZMod n) ^ ((n - 1) / q) ≠ 1) :
    Nat.Prime n := by
  apply lucas_primality n (a : ZMod n) ha
  intro q hq hqdiv
  have hmemPF : q ∈ Nat.primeFactorsList (n - 1) :=
    (Nat.mem_primeFactorsList_iff_dvd hn1 hq).mpr hqdiv
  have hperm : List.Perm factors (Nat.primeFactorsList (n - 1)) :=
    Nat.primeFactorsList_unique hprod hprime
  exact hpow q (hperm.symm.mem_iff.mp hmemPF)

/-- Certificate subprime `13`. -/
private theorem prime_cert_01 : Nat.Prime 13 := by
  apply lucasFromFactors 13 2 [2, 2, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `17`. -/
private theorem prime_cert_02 : Nat.Prime 17 := by
  apply lucasFromFactors 17 3 [2, 2, 2, 2]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 := by simpa using hq
    rcases hcases with rfl
    · exact Nat.prime_two
  · intro q hq
    have hcases : q = 2 := by simpa using hq
    rcases hcases with rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `19`. -/
private theorem prime_cert_03 : Nat.Prime 19 := by
  apply lucasFromFactors 19 2 [2, 3, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `23`. -/
private theorem prime_cert_04 : Nat.Prime 23 := by
  apply lucasFromFactors 23 5 [2, 11]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_eleven
  · intro q hq
    have hcases : q = 2 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `29`. -/
private theorem prime_cert_05 : Nat.Prime 29 := by
  apply lucasFromFactors 29 2 [2, 2, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `31`. -/
private theorem prime_cert_06 : Nat.Prime 31 := by
  apply lucasFromFactors 31 3 [2, 3, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `37`. -/
private theorem prime_cert_07 : Nat.Prime 37 := by
  apply lucasFromFactors 37 2 [2, 2, 3, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `41`. -/
private theorem prime_cert_08 : Nat.Prime 41 := by
  apply lucasFromFactors 41 6 [2, 2, 2, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `53`. -/
private theorem prime_cert_09 : Nat.Prime 53 := by
  apply lucasFromFactors 53 2 [2, 2, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `59`. -/
private theorem prime_cert_10 : Nat.Prime 59 := by
  apply lucasFromFactors 59 2 [2, 29]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 29 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_05
  · intro q hq
    have hcases : q = 2 ∨ q = 29 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `67`. -/
private theorem prime_cert_11 : Nat.Prime 67 := by
  apply lucasFromFactors 67 2 [2, 3, 11]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `73`. -/
private theorem prime_cert_12 : Nat.Prime 73 := by
  apply lucasFromFactors 73 5 [2, 2, 2, 3, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `83`. -/
private theorem prime_cert_13 : Nat.Prime 83 := by
  apply lucasFromFactors 83 2 [2, 41]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_08
  · intro q hq
    have hcases : q = 2 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `97`. -/
private theorem prime_cert_14 : Nat.Prime 97 := by
  apply lucasFromFactors 97 5 [2, 2, 2, 2, 2, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `101`. -/
private theorem prime_cert_15 : Nat.Prime 101 := by
  apply lucasFromFactors 101 2 [2, 2, 5, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `103`. -/
private theorem prime_cert_16 : Nat.Prime 103 := by
  apply lucasFromFactors 103 5 [2, 3, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `109`. -/
private theorem prime_cert_17 : Nat.Prime 109 := by
  apply lucasFromFactors 109 6 [2, 2, 3, 3, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `113`. -/
private theorem prime_cert_18 : Nat.Prime 113 := by
  apply lucasFromFactors 113 3 [2, 2, 2, 2, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `131`. -/
private theorem prime_cert_19 : Nat.Prime 131 := by
  apply lucasFromFactors 131 2 [2, 5, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `149`. -/
private theorem prime_cert_20 : Nat.Prime 149 := by
  apply lucasFromFactors 149 2 [2, 2, 37]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 37 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_07
  · intro q hq
    have hcases : q = 2 ∨ q = 37 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `199`. -/
private theorem prime_cert_21 : Nat.Prime 199 := by
  apply lucasFromFactors 199 3 [2, 3, 3, 11]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `239`. -/
private theorem prime_cert_22 : Nat.Prime 239 := by
  apply lucasFromFactors 239 7 [2, 7, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `271`. -/
private theorem prime_cert_23 : Nat.Prime 271 := by
  apply lucasFromFactors 271 6 [2, 3, 3, 3, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `293`. -/
private theorem prime_cert_24 : Nat.Prime 293 := by
  apply lucasFromFactors 293 2 [2, 2, 73]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 73 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_12
  · intro q hq
    have hcases : q = 2 ∨ q = 73 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `419`. -/
private theorem prime_cert_25 : Nat.Prime 419 := by
  apply lucasFromFactors 419 2 [2, 11, 19]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 11 ∨ q = 19 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_eleven
    · exact prime_cert_03
  · intro q hq
    have hcases : q = 2 ∨ q = 11 ∨ q = 19 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `443`. -/
private theorem prime_cert_26 : Nat.Prime 443 := by
  apply lucasFromFactors 443 2 [2, 13, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 13 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_01
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 13 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `461`. -/
private theorem prime_cert_27 : Nat.Prime 461 := by
  apply lucasFromFactors 461 2 [2, 2, 5, 23]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 23 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_04
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 23 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `631`. -/
private theorem prime_cert_28 : Nat.Prime 631 := by
  apply lucasFromFactors 631 3 [2, 3, 3, 5, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `797`. -/
private theorem prime_cert_29 : Nat.Prime 797 := by
  apply lucasFromFactors 797 2 [2, 2, 199]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 199 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_21
  · intro q hq
    have hcases : q = 2 ∨ q = 199 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `887`. -/
private theorem prime_cert_30 : Nat.Prime 887 := by
  apply lucasFromFactors 887 5 [2, 443]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_26
  · intro q hq
    have hcases : q = 2 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `971`. -/
private theorem prime_cert_31 : Nat.Prime 971 := by
  apply lucasFromFactors 971 6 [2, 5, 97]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 97 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_14
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 97 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `1373`. -/
private theorem prime_cert_32 : Nat.Prime 1373 := by
  apply lucasFromFactors 1373 2 [2, 2, 7, 7, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `1409`. -/
private theorem prime_cert_33 : Nat.Prime 1409 := by
  apply lucasFromFactors 1409 3 [2, 2, 2, 2, 2, 2, 2, 11]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_eleven
  · intro q hq
    have hcases : q = 2 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `1627`. -/
private theorem prime_cert_34 : Nat.Prime 1627 := by
  apply lucasFromFactors 1627 3 [2, 3, 271]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 271 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_23
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 271 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `1871`. -/
private theorem prime_cert_35 : Nat.Prime 1871 := by
  apply lucasFromFactors 1871 14 [2, 5, 11, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 11 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact Nat.prime_eleven
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 11 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `2011`. -/
private theorem prime_cert_36 : Nat.Prime 2011 := by
  apply lucasFromFactors 2011 3 [2, 3, 5, 67]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_11
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `2621`. -/
private theorem prime_cert_37 : Nat.Prime 2621 := by
  apply lucasFromFactors 2621 2 [2, 2, 5, 131]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 131 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_19
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 131 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `2657`. -/
private theorem prime_cert_38 : Nat.Prime 2657 := by
  apply lucasFromFactors 2657 3 [2, 2, 2, 2, 2, 83]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 83 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_13
  · intro q hq
    have hcases : q = 2 ∨ q = 83 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `2731`. -/
private theorem prime_cert_39 : Nat.Prime 2731 := by
  apply lucasFromFactors 2731 3 [2, 3, 5, 7, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact Nat.prime_seven
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `2861`. -/
private theorem prime_cert_40 : Nat.Prime 2861 := by
  apply lucasFromFactors 2861 2 [2, 2, 5, 11, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact Nat.prime_eleven
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `4051`. -/
private theorem prime_cert_41 : Nat.Prime 4051 := by
  apply lucasFromFactors 4051 10 [2, 3, 3, 3, 3, 5, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `4423`. -/
private theorem prime_cert_42 : Nat.Prime 4423 := by
  apply lucasFromFactors 4423 3 [2, 3, 11, 67]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_11
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `5323`. -/
private theorem prime_cert_43 : Nat.Prime 5323 := by
  apply lucasFromFactors 5323 5 [2, 3, 887]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 887 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_30
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 887 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `7723`. -/
private theorem prime_cert_44 : Nat.Prime 7723 := by
  apply lucasFromFactors 7723 3 [2, 3, 3, 3, 11, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `9349`. -/
private theorem prime_cert_45 : Nat.Prime 9349 := by
  apply lucasFromFactors 9349 2 [2, 2, 3, 19, 41]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 19 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_03
    · exact prime_cert_08
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 19 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `13441`. -/
private theorem prime_cert_46 : Nat.Prime 13441 := by
  apply lucasFromFactors 13441 11 [2, 2, 2, 2, 2, 2, 2, 3, 5, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `16699`. -/
private theorem prime_cert_47 : Nat.Prime 16699 := by
  apply lucasFromFactors 16699 3 [2, 3, 11, 11, 23]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 23 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_04
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 23 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `20113`. -/
private theorem prime_cert_48 : Nat.Prime 20113 := by
  apply lucasFromFactors 20113 10 [2, 2, 2, 2, 3, 419]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 419 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_25
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 419 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `24809`. -/
private theorem prime_cert_49 : Nat.Prime 24809 := by
  apply lucasFromFactors 24809 6 [2, 2, 2, 7, 443]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_26
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `28181`. -/
private theorem prime_cert_50 : Nat.Prime 28181 := by
  apply lucasFromFactors 28181 2 [2, 2, 5, 1409]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 1409 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_33
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 1409 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `41201`. -/
private theorem prime_cert_51 : Nat.Prime 41201 := by
  apply lucasFromFactors 41201 3 [2, 2, 2, 2, 5, 5, 103]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 103 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_16
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 103 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `85831`. -/
private theorem prime_cert_52 : Nat.Prime 85831 := by
  apply lucasFromFactors 85831 3 [2, 3, 5, 2861]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 2861 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_40
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 2861 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `96557`. -/
private theorem prime_cert_53 : Nat.Prime 96557 := by
  apply lucasFromFactors 96557 2 [2, 2, 101, 239]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 101 ∨ q = 239 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_15
    · exact prime_cert_22
  · intro q hq
    have hcases : q = 2 ∨ q = 101 ∨ q = 239 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `120233`. -/
private theorem prime_cert_54 : Nat.Prime 120233 := by
  apply lucasFromFactors 120233 3 [2, 2, 2, 7, 19, 113]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 19 ∨ q = 113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_03
    · exact prime_cert_18
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 19 ∨ q = 113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `305873`. -/
private theorem prime_cert_55 : Nat.Prime 305873 := by
  apply lucasFromFactors 305873 3 [2, 2, 2, 2, 7, 2731]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 2731 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_39
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 2731 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `1206781`. -/
private theorem prime_cert_56 : Nat.Prime 1206781 := by
  apply lucasFromFactors 1206781 10 [2, 2, 3, 5, 20113]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 20113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_48
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 20113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `1627771`. -/
private theorem prime_cert_57 : Nat.Prime 1627771 := by
  apply lucasFromFactors 1627771 3 [2, 3, 5, 29, 1871]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 1871 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_05
    · exact prime_cert_35
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 1871 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `4681609`. -/
private theorem prime_cert_58 : Nat.Prime 4681609 := by
  apply lucasFromFactors 4681609 23 [2, 2, 2, 3, 97, 2011]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 97 ∨ q = 2011 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_14
    · exact prime_cert_36
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 97 ∨ q = 2011 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `7240687`. -/
private theorem prime_cert_59 : Nat.Prime 7240687 := by
  apply lucasFromFactors 7240687 3 [2, 3, 1206781]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 1206781 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_56
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 1206781 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `13331831`. -/
private theorem prime_cert_60 : Nat.Prime 13331831 := by
  apply lucasFromFactors 13331831 13 [2, 5, 971, 1373]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 971 ∨ q = 1373 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_31
    · exact prime_cert_32
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 971 ∨ q = 1373 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `44706919`. -/
private theorem prime_cert_61 : Nat.Prime 44706919 := by
  apply lucasFromFactors 44706919 6 [2, 3, 797, 9349]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 797 ∨ q = 9349 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_29
    · exact prime_cert_45
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 797 ∨ q = 9349 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `107590001`. -/
private theorem prime_cert_62 : Nat.Prime 107590001 := by
  apply lucasFromFactors 107590001 3 [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 7 ∨ q = 29 ∨ q = 53 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact Nat.prime_seven
    · exact prime_cert_05
    · exact prime_cert_09
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 7 ∨ q = 29 ∨ q = 53 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `545358713`. -/
private theorem prime_cert_63 : Nat.Prime 545358713 := by
  apply lucasFromFactors 545358713 5 [2, 2, 2, 41, 59, 28181]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 41 ∨ q = 59 ∨ q = 28181 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_08
    · exact prime_cert_10
    · exact prime_cert_50
  · intro q hq
    have hcases : q = 2 ∨ q = 41 ∨ q = 59 ∨ q = 28181 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `297159362677`. -/
private theorem prime_cert_64 : Nat.Prime 297159362677 := by
  apply lucasFromFactors 297159362677 2 [2, 2, 3, 3, 11, 461, 1627771]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 461 ∨ q = 1627771 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_27
    · exact prime_cert_57
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 461 ∨ q = 1627771 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `107361793816595537`. -/
private theorem prime_cert_65 : Nat.Prime 107361793816595537 := by
  apply lucasFromFactors 107361793816595537 3 [2, 2, 2, 2, 16699, 85831, 4681609]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 16699 ∨ q = 85831 ∨ q = 4681609 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_47
    · exact prime_cert_52
    · exact prime_cert_58
  · intro q hq
    have hcases : q = 2 ∨ q = 16699 ∨ q = 85831 ∨ q = 4681609 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `173378833005251801`. -/
private theorem prime_cert_66 : Nat.Prime 173378833005251801 := by
  apply lucasFromFactors 173378833005251801 6 [2, 2, 2, 5, 5, 2621, 24809, 13331831]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 2621 ∨ q = 24809 ∨ q = 13331831 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_37
    · exact prime_cert_49
    · exact prime_cert_60
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 2621 ∨ q = 24809 ∨ q = 13331831 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `174723607534414371449`. -/
private theorem prime_cert_67 : Nat.Prime 174723607534414371449 := by
  apply lucasFromFactors 174723607534414371449 3 [2, 2, 2, 17, 59, 4051, 120233, 44706919]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 17 ∨ q = 59 ∨ q = 4051 ∨ q = 120233 ∨ q = 44706919 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_02
    · exact prime_cert_10
    · exact prime_cert_41
    · exact prime_cert_54
    · exact prime_cert_61
  · intro q hq
    have hcases : q = 2 ∨ q = 17 ∨ q = 59 ∨ q = 4051 ∨ q = 120233 ∨ q = 44706919 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `22149492674086928081353`. -/
private theorem prime_cert_68 : Nat.Prime 22149492674086928081353 := by
  apply lucasFromFactors 22149492674086928081353 5 [2, 2, 2, 3, 5323, 173378833005251801]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5323 ∨ q = 173378833005251801 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_43
    · exact prime_cert_66
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5323 ∨ q = 173378833005251801 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `132896956044521568488119`. -/
private theorem prime_cert_69 : Nat.Prime 132896956044521568488119 := by
  apply lucasFromFactors 132896956044521568488119 6 [2, 3, 22149492674086928081353]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 22149492674086928081353 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_68
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 22149492674086928081353 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `29047611873442575647497758179`. -/
private theorem prime_cert_70 : Nat.Prime 29047611873442575647497758179 := by
  apply lucasFromFactors 29047611873442575647497758179 2 [2, 293, 305873, 545358713, 297159362677]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 293 ∨ q = 305873 ∨ q = 545358713 ∨ q = 297159362677 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_24
    · exact prime_cert_55
    · exact prime_cert_63
    · exact prime_cert_64
  · intro q hq
    have hcases : q = 2 ∨ q = 293 ∨ q = 305873 ∨ q = 545358713 ∨ q = 297159362677 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `341948486974166000522343609283189`. -/
private theorem prime_cert_71 : Nat.Prime 341948486974166000522343609283189 := by
  apply lucasFromFactors 341948486974166000522343609283189 2 [2, 2, 3, 3, 3, 109, 29047611873442575647497758179]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 109 ∨ q = 29047611873442575647497758179 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_17
    · exact prime_cert_70
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 109 ∨ q = 29047611873442575647497758179 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `255515944373312847190720520512484175977`. -/
private theorem prime_cert_72 : Nat.Prime 255515944373312847190720520512484175977 := by
  apply lucasFromFactors 255515944373312847190720520512484175977 3 [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 11 ∨ q = 1627 ∨ q = 2657 ∨ q = 4423 ∨ q = 41201 ∨ q = 96557 ∨ q = 7240687 ∨ q = 107590001 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact Nat.prime_eleven
    · exact prime_cert_34
    · exact prime_cert_38
    · exact prime_cert_42
    · exact prime_cert_51
    · exact prime_cert_53
    · exact prime_cert_59
    · exact prime_cert_62
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 11 ∨ q = 1627 ∨ q = 2657 ∨ q = 4423 ∨ q = 41201 ∨ q = 96557 ∨ q = 7240687 ∨ q = 107590001 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `205115282021455665897114700593932402728804164701536103180137503955397371`. -/
private theorem prime_cert_73 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  apply lucasFromFactors 205115282021455665897114700593932402728804164701536103180137503955397371 10 [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 31 ∨ q = 7723 ∨ q = 132896956044521568488119 ∨ q = 255515944373312847190720520512484175977 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_05
    · exact prime_cert_06
    · exact prime_cert_44
    · exact prime_cert_69
    · exact prime_cert_72
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 31 ∨ q = 7723 ∨ q = 132896956044521568488119 ∨ q = 255515944373312847190720520512484175977 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- The secp256k1 base-field modulus is prime. -/
theorem p_prime : Nat.Prime p := by
  apply lucasFromFactors p 3 [2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371]
  · unfold p
    reduce_mod_char
  · unfold p
    norm_num
  · unfold p
    norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 13441 ∨ q = 205115282021455665897114700593932402728804164701536103180137503955397371 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_seven
    · exact prime_cert_46
    · exact prime_cert_73
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 13441 ∨ q = 205115282021455665897114700593932402728804164701536103180137503955397371 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      unfold p
      reduce_mod_char
      decide

/-- The secp256k1 subgroup order is prime. -/
theorem order_prime : Nat.Prime order := by
  apply lucasFromFactors order 7 [2, 2, 2, 2, 2, 2, 3, 149, 631, 107361793816595537, 174723607534414371449, 341948486974166000522343609283189]
  · unfold order
    reduce_mod_char
  · unfold order
    norm_num
  · unfold order
    norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 149 ∨ q = 631 ∨ q = 107361793816595537 ∨ q = 174723607534414371449 ∨ q = 341948486974166000522343609283189 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_20
    · exact prime_cert_28
    · exact prime_cert_65
    · exact prime_cert_67
    · exact prime_cert_71
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 149 ∨ q = 631 ∨ q = 107361793816595537 ∨ q = 174723607534414371449 ∨ q = 341948486974166000522343609283189 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      unfold order
      reduce_mod_char
      decide

instance : Fact (Nat.Prime p) := ⟨p_prime⟩

instance : Fact (Nat.Prime order) := ⟨order_prime⟩


/-! ## Generator-order point certificate

The following generated certificate replays binary scalar multiplication of the
published generator by the published order.  Each finite step is checked by
the affine formulas from `AffineFormula`; inverses are supplied explicitly and
verified by multiplication modulo `p`. -/

theorem coordinates_eq_none_iff (P : Point) : coordinates P = none ↔ P = 0 := by
  cases P with
  | zero => constructor <;> intro _ <;> rfl
  | some h =>
      constructor
      · intro hc
        cases hc
      · intro hp
        exact False.elim (WeierstrassCurve.Affine.Point.some_ne_zero h hp)

theorem coordinates_injective : Function.Injective coordinates := by
  intro P Q h
  cases P with
  | zero =>
      have hq : coordinates Q = none := by simpa [coordinates] using h.symm
      have hQzero : Q = 0 := (coordinates_eq_none_iff Q).mp hq
      simpa using hQzero.symm
  | some hP =>
      cases Q with
      | zero =>
          have hp : coordinates (WeierstrassCurve.Affine.Point.some hP) = none := by
            simp at h
            exact h
          have hpzero : WeierstrassCurve.Affine.Point.some hP = 0 :=
            (coordinates_eq_none_iff _).mp hp
          exact False.elim (WeierstrassCurve.Affine.Point.some_ne_zero hP hpzero)
      | some hQ =>
          simp only [coordinates_some, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨hx, hy⟩
          subst hx
          subst hy
          rfl

private theorem certifiedDouble
    {x y x3 y3 : Nat}
    {hP : curve.toAffine.Nonsingular ((x : Nat) : Fp) ((y : Nat) : Fp)}
    {hR : curve.toAffine.Nonsingular ((x3 : Nat) : Fp) ((y3 : Nat) : Fp)}
    (hnot : ((y : Nat) : Fp) ≠ -((y : Nat) : Fp))
    (hx3 : doubleX ((x : Nat) : Fp) ((y : Nat) : Fp) = ((x3 : Nat) : Fp))
    (hy3 : doubleY ((x : Nat) : Fp) ((y : Nat) : Fp) = ((y3 : Nat) : Fp)) :
    affineAdd (.some hP : Point) (.some hP : Point) = .some hR := by
  calc
    affineAdd (.some hP : Point) (.some hP : Point) = doublePoint hP hnot := by
      unfold affineAdd
      simp only [↓reduceDIte, hnot]
    _ = .some hR := by
      apply coordinates_injective
      unfold doublePoint
      simp only [coordinates_some, Option.some.injEq, Prod.mk.injEq]
      exact ⟨hx3, hy3⟩

private theorem certifiedAdd
    {x1 y1 x2 y2 x3 y3 : Nat}
    {hP : curve.toAffine.Nonsingular ((x1 : Nat) : Fp) ((y1 : Nat) : Fp)}
    {hQ : curve.toAffine.Nonsingular ((x2 : Nat) : Fp) ((y2 : Nat) : Fp)}
    {hR : curve.toAffine.Nonsingular ((x3 : Nat) : Fp) ((y3 : Nat) : Fp)}
    (hxne : ((x1 : Nat) : Fp) ≠ ((x2 : Nat) : Fp))
    (hx3 : genericX ((x1 : Nat) : Fp) ((y1 : Nat) : Fp)
        ((x2 : Nat) : Fp) ((y2 : Nat) : Fp) = ((x3 : Nat) : Fp))
    (hy3 : genericY ((x1 : Nat) : Fp) ((y1 : Nat) : Fp)
        ((x2 : Nat) : Fp) ((y2 : Nat) : Fp) = ((y3 : Nat) : Fp)) :
    affineAdd (.some hP : Point) (.some hQ : Point) = .some hR := by
  calc
    affineAdd (.some hP : Point) (.some hQ : Point) = genericAdd hP hQ hxne := by
      unfold affineAdd
      simp only [hxne, ↓reduceDIte]
    _ = .some hR := by
      apply coordinates_injective
      unfold genericAdd
      simp only [coordinates_some, Option.some.injEq, Prod.mk.injEq]
      exact ⟨hx3, hy3⟩

private theorem certifiedInverseAdd
    {x1 y1 x2 y2 : Nat}
    {hP : curve.toAffine.Nonsingular ((x1 : Nat) : Fp) ((y1 : Nat) : Fp)}
    {hQ : curve.toAffine.Nonsingular ((x2 : Nat) : Fp) ((y2 : Nat) : Fp)}
    (hx : ((x1 : Nat) : Fp) = ((x2 : Nat) : Fp))
    (hy : ((y1 : Nat) : Fp) = -((y2 : Nat) : Fp)) :
    affineAdd (.some hP : Point) (.some hQ : Point) = 0 := by
  unfold affineAdd
  simp only [hx, hy, ↓reduceDIte]

private def affineNsmulBinRec (k : Nat) : Point → Point :=
  affineNsmulBinRec.go k 0
where
  go (k : Nat) : Point → Point → Point :=
    Nat.binaryRec (motive := fun _ => Point → Point → Point)
      (fun y _ => y)
      (fun bn _n fn y x => fn (if bn then affineAdd y x else y) (affineAdd x x)) k

private theorem affineNsmulBinRec_go_zero (acc base : Point) :
    affineNsmulBinRec.go 0 acc base = acc := by
  rfl

private theorem affineNsmulBinRec_go_bit_true (n : Nat) (acc base : Point) :
    affineNsmulBinRec.go (Nat.bit true n) acc base =
      affineNsmulBinRec.go n (affineAdd acc base) (affineAdd base base) := by
  unfold affineNsmulBinRec.go
  rw [Nat.binaryRec_eq true n (Or.inl rfl)]
  rfl

private theorem affineNsmulBinRec_go_bit_false (n : Nat) (acc base : Point) :
    affineNsmulBinRec.go (Nat.bit false n) acc base =
      affineNsmulBinRec.go n acc (affineAdd base base) := by
  unfold affineNsmulBinRec.go
  rw [Nat.binaryRec_eq false n (Or.inl rfl)]
  rfl

private theorem affineNsmulBinRec_go_eq (k : Nat) (y x : Point) :
    affineNsmulBinRec.go k y x = nsmulBinRec.go k y x := by
  unfold affineNsmulBinRec.go nsmulBinRec.go
  induction k using Nat.binaryRec generalizing y x with
  | zero => rfl
  | bit b n ih =>
      rw [Nat.binaryRec_eq b n (Or.inl rfl)]
      rw [Nat.binaryRec_eq b n (Or.inl rfl)]
      cases b
      · simpa [affineAdd_correct] using ih y (x + x)
      · simpa [affineAdd_correct] using ih (y + x) (x + x)

private theorem affineNsmulBinRec_eq (k : Nat) (P : Point) :
    affineNsmulBinRec k P = k • P := by
  change affineNsmulBinRec.go k 0 P = nsmulBinRec k P
  rw [affineNsmulBinRec_go_eq]
  rfl

private def base_0 : Point :=
  .some (x := ((55066263022277343669578718895168534326250603453777594175500187360389116729240 : Nat) : Fp))
    (y := ((32670510020758816978083085130507043184471273380659243275938904335757337482424 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((32670510020758816978083085130507043184471273380659243275938904335757337482424 : Nat) : Fp) ^ 2 = ((55066263022277343669578718895168534326250603453777594175500187360389116729240 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_1 : Point :=
  .some (x := ((89565891926547004231252920425935692360644145829622209833684329913297188986597 : Nat) : Fp))
    (y := ((12158399299693830322967808612713398636155367887041628176798871954788371653930 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((12158399299693830322967808612713398636155367887041628176798871954788371653930 : Nat) : Fp) ^ 2 = ((89565891926547004231252920425935692360644145829622209833684329913297188986597 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_2 : Point :=
  .some (x := ((103388573995635080359749164254216598308788835304023601477803095234286494993683 : Nat) : Fp))
    (y := ((37057141145242123013015316630864329550140216928701153669873286428255828810018 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((37057141145242123013015316630864329550140216928701153669873286428255828810018 : Nat) : Fp) ^ 2 = ((103388573995635080359749164254216598308788835304023601477803095234286494993683 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_3 : Point :=
  .some (x := ((21262057306151627953595685090280431278183829487175876377991189246716355947009 : Nat) : Fp))
    (y := ((41749993296225487051377864631615517161996906063147759678534462689479575333124 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((41749993296225487051377864631615517161996906063147759678534462689479575333124 : Nat) : Fp) ^ 2 = ((21262057306151627953595685090280431278183829487175876377991189246716355947009 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_4 : Point :=
  .some (x := ((104059883622109321374094289636044428849728529177856482232626205340719788190730 : Nat) : Fp))
    (y := ((112122903140080327253741791678230372394936108416576609264408917599318947489825 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((112122903140080327253741791678230372394936108416576609264408917599318947489825 : Nat) : Fp) ^ 2 = ((104059883622109321374094289636044428849728529177856482232626205340719788190730 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_5 : Point :=
  .some (x := ((95440839670107969455973995843666399663662641812074432045896568980475242364517 : Nat) : Fp))
    (y := ((67400892360194400039319989411395972789004161889863182881857158544061243615929 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((67400892360194400039319989411395972789004161889863182881857158544061243615929 : Nat) : Fp) ^ 2 = ((95440839670107969455973995843666399663662641812074432045896568980475242364517 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_6 : Point :=
  .some (x := ((86454928033100054822938644242727206101601557724291916072342392316125160730507 : Nat) : Fp))
    (y := ((41929975541376036990359335647717381527212342035893043668288666074313354583455 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((41929975541376036990359335647717381527212342035893043668288666074313354583455 : Nat) : Fp) ^ 2 = ((86454928033100054822938644242727206101601557724291916072342392316125160730507 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_7 : Point :=
  .some (x := ((23971227478092690611538379282579297124953800109492367109857348294863777014350 : Nat) : Fp))
    (y := ((42342609885299334444880650568116455571250837701978463648617679521175848103706 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((42342609885299334444880650568116455571250837701978463648617679521175848103706 : Nat) : Fp) ^ 2 = ((23971227478092690611538379282579297124953800109492367109857348294863777014350 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_8 : Point :=
  .some (x := ((59030624050581421406270513075794029219285200067000787157698366092408912155912 : Nat) : Fp))
    (y := ((8128656248049033031875480515138402531865803579197128279783442554673902546095 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((8128656248049033031875480515138402531865803579197128279783442554673902546095 : Nat) : Fp) ^ 2 = ((59030624050581421406270513075794029219285200067000787157698366092408912155912 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_9 : Point :=
  .some (x := ((31809325515952716603993860438135646801954922215901515683284707473623428145741 : Nat) : Fp))
    (y := ((24377531977987817432088011602449325046972761657480460991275213238540072159220 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((24377531977987817432088011602449325046972761657480460991275213238540072159220 : Nat) : Fp) ^ 2 = ((31809325515952716603993860438135646801954922215901515683284707473623428145741 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_10 : Point :=
  .some (x := ((16339661702852967382840638396154683021742565846854739320600712521008743256863 : Nat) : Fp))
    (y := ((36728284022334234592863792440353097018527397507662959793213172092233334129261 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((36728284022334234592863792440353097018527397507662959793213172092233334129261 : Nat) : Fp) ^ 2 = ((16339661702852967382840638396154683021742565846854739320600712521008743256863 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_11 : Point :=
  .some (x := ((42114313391321156005599920754056349597018482182309287550535575450912996590705 : Nat) : Fp))
    (y := ((18211792713336063942313736004207749605328499756363387606667481967702897602819 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((18211792713336063942313736004207749605328499756363387606667481967702897602819 : Nat) : Fp) ^ 2 = ((42114313391321156005599920754056349597018482182309287550535575450912996590705 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_12 : Point :=
  .some (x := ((10569428376872096169397247199835207726595431926877749141789405073030710146873 : Nat) : Fp))
    (y := ((95580118375493152898771330185112988759633284070886792649665201458589961475733 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((95580118375493152898771330185112988759633284070886792649665201458589961475733 : Nat) : Fp) ^ 2 = ((10569428376872096169397247199835207726595431926877749141789405073030710146873 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_13 : Point :=
  .some (x := ((29955133736896634235893587837609964910900820068836768599575322235881802975190 : Nat) : Fp))
    (y := ((83725361430957575604497772232028370201521594201253320640285202099397696195124 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((83725361430957575604497772232028370201521594201253320640285202099397696195124 : Nat) : Fp) ^ 2 = ((29955133736896634235893587837609964910900820068836768599575322235881802975190 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_14 : Point :=
  .some (x := ((7741290454269945723504810030002187313337519274815056282137434463684850516554 : Nat) : Fp))
    (y := ((2979905666851018206144735065445742806952013006906430309532921989383330523600 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((2979905666851018206144735065445742806952013006906430309532921989383330523600 : Nat) : Fp) ^ 2 = ((7741290454269945723504810030002187313337519274815056282137434463684850516554 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_15 : Point :=
  .some (x := ((33602655200186679430886431101373729519010186911116350037909320311808627496821 : Nat) : Fp))
    (y := ((37360103261735091089003680850413001554296156453961728314327616229790563817069 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((37360103261735091089003680850413001554296156453961728314327616229790563817069 : Nat) : Fp) ^ 2 = ((33602655200186679430886431101373729519010186911116350037909320311808627496821 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_16 : Point :=
  .some (x := ((24533671068980092868630552346995129420983823672304585196401986911541584152128 : Nat) : Fp))
    (y := ((2209357222459695347071765155987393997305194371900031813817445740077485301225 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((2209357222459695347071765155987393997305194371900031813817445740077485301225 : Nat) : Fp) ^ 2 = ((24533671068980092868630552346995129420983823672304585196401986911541584152128 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_17 : Point :=
  .some (x := ((34424533203459102608471296411716955901929203809676354171491737723302766101825 : Nat) : Fp))
    (y := ((87733804348534428731161926933835660863551297059124747814746905172819546464288 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((87733804348534428731161926933835660863551297059124747814746905172819546464288 : Nat) : Fp) ^ 2 = ((34424533203459102608471296411716955901929203809676354171491737723302766101825 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_18 : Point :=
  .some (x := ((74193831669845249654938577341216601539929459848933807922451592200153851425745 : Nat) : Fp))
    (y := ((29361396017150706741613988342393505196301946421006103373231627829781191611577 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29361396017150706741613988342393505196301946421006103373231627829781191611577 : Nat) : Fp) ^ 2 = ((74193831669845249654938577341216601539929459848933807922451592200153851425745 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_19 : Point :=
  .some (x := ((75996994270594548260051104099040009002173474732108538694613575188101535421242 : Nat) : Fp))
    (y := ((67731220512052072417843278921450425890601471538300788051881284779249943090810 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((67731220512052072417843278921450425890601471538300788051881284779249943090810 : Nat) : Fp) ^ 2 = ((75996994270594548260051104099040009002173474732108538694613575188101535421242 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_20 : Point :=
  .some (x := ((63004655751848499058589887215149057167805706207141784701705408548476267919372 : Nat) : Fp))
    (y := ((33776887358425213876727286236887696644549240079971817446727643228044518554934 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((33776887358425213876727286236887696644549240079971817446727643228044518554934 : Nat) : Fp) ^ 2 = ((63004655751848499058589887215149057167805706207141784701705408548476267919372 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_21 : Point :=
  .some (x := ((107219988410259287649822325760828753777881271537028923079899200557009639695550 : Nat) : Fp))
    (y := ((15425677638027042728233515882140468124385010133809940201784713737762399581231 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((15425677638027042728233515882140468124385010133809940201784713737762399581231 : Nat) : Fp) ^ 2 = ((107219988410259287649822325760828753777881271537028923079899200557009639695550 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_22 : Point :=
  .some (x := ((113496403293373161892995045761087341014991661230000874253822611507549586770091 : Nat) : Fp))
    (y := ((92288978233865387499357228995099386605786555025834285738713074898639193985136 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((92288978233865387499357228995099386605786555025834285738713074898639193985136 : Nat) : Fp) ^ 2 = ((113496403293373161892995045761087341014991661230000874253822611507549586770091 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_23 : Point :=
  .some (x := ((4402168996420289224849535114023409990325018394340995944430318114273800335863 : Nat) : Fp))
    (y := ((67104318001466418430256649108646734852945972191921730406768272163045294283904 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((67104318001466418430256649108646734852945972191921730406768272163045294283904 : Nat) : Fp) ^ 2 = ((4402168996420289224849535114023409990325018394340995944430318114273800335863 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_24 : Point :=
  .some (x := ((51670963786757573841189746283202124387362261809800652891978209018731111316698 : Nat) : Fp))
    (y := ((68257551575553566084241009552849606333781498777275567535225153774080710909791 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((68257551575553566084241009552849606333781498777275567535225153774080710909791 : Nat) : Fp) ^ 2 = ((51670963786757573841189746283202124387362261809800652891978209018731111316698 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_25 : Point :=
  .some (x := ((39774650486605686761949696375291962760476627649023643684500799050103063064789 : Nat) : Fp))
    (y := ((97280577493662175430906331419179376788053309764979933526226118285088405860254 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((97280577493662175430906331419179376788053309764979933526226118285088405860254 : Nat) : Fp) ^ 2 = ((39774650486605686761949696375291962760476627649023643684500799050103063064789 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_26 : Point :=
  .some (x := ((17321708023578332183628700857357458473789564616208564602894355867116410260949 : Nat) : Fp))
    (y := ((97919434988400284406895062116320315016365801759636091852848099981382771845905 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((97919434988400284406895062116320315016365801759636091852848099981382771845905 : Nat) : Fp) ^ 2 = ((17321708023578332183628700857357458473789564616208564602894355867116410260949 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_27 : Point :=
  .some (x := ((76575849854364972542951978758356689466650880857178783481542510110017069529320 : Nat) : Fp))
    (y := ((81925384519567487405199682290695043524776979911807891169446287270330277192180 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((81925384519567487405199682290695043524776979911807891169446287270330277192180 : Nat) : Fp) ^ 2 = ((76575849854364972542951978758356689466650880857178783481542510110017069529320 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_28 : Point :=
  .some (x := ((107989063369659015153804811955459434214410196483964476598208978660096898619386 : Nat) : Fp))
    (y := ((42338160021087805224648939485129818613830046750563614152037885753448952924569 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((42338160021087805224648939485129818613830046750563614152037885753448952924569 : Nat) : Fp) ^ 2 = ((107989063369659015153804811955459434214410196483964476598208978660096898619386 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_29 : Point :=
  .some (x := ((25379507781751782970997391382797328968603613636745039424586338729874508912637 : Nat) : Fp))
    (y := ((66678967052843214385960608145916057604491714224625771583834324020892145369029 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((66678967052843214385960608145916057604491714224625771583834324020892145369029 : Nat) : Fp) ^ 2 = ((25379507781751782970997391382797328968603613636745039424586338729874508912637 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_30 : Point :=
  .some (x := ((102193949730178242338502490474683128513913323030888946433219655522103301391692 : Nat) : Fp))
    (y := ((6691527371710806382780054211605006078697403702312160758173793149761505802135 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((6691527371710806382780054211605006078697403702312160758173793149761505802135 : Nat) : Fp) ^ 2 = ((102193949730178242338502490474683128513913323030888946433219655522103301391692 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_31 : Point :=
  .some (x := ((37586094085820668222219663528035831988292035114036566702275484810122124564900 : Nat) : Fp))
    (y := ((110500050436317590116317882856153568952218728972968181243435825114259637008685 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((110500050436317590116317882856153568952218728972968181243435825114259637008685 : Nat) : Fp) ^ 2 = ((37586094085820668222219663528035831988292035114036566702275484810122124564900 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_32 : Point :=
  .some (x := ((7263983490427117408129518121638485560698559702481803384958991237905117384112 : Nat) : Fp))
    (y := ((93109094002033366773627505914545361927166820241279828474630961892312310241801 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((93109094002033366773627505914545361927166820241279828474630961892312310241801 : Nat) : Fp) ^ 2 = ((7263983490427117408129518121638485560698559702481803384958991237905117384112 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_33 : Point :=
  .some (x := ((63340652510566015247975818591385417300086272434074184937732392505693958960902 : Nat) : Fp))
    (y := ((113667876764634414158091221422353531108236715357465572941896170017035409095320 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((113667876764634414158091221422353531108236715357465572941896170017035409095320 : Nat) : Fp) ^ 2 = ((63340652510566015247975818591385417300086272434074184937732392505693958960902 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_34 : Point :=
  .some (x := ((113783330688848408326400254714688308943084902760190583586245237148771972268029 : Nat) : Fp))
    (y := ((49136863138091630742201940998618633678196612987804544425991276550671171170453 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((49136863138091630742201940998618633678196612987804544425991276550671171170453 : Nat) : Fp) ^ 2 = ((113783330688848408326400254714688308943084902760190583586245237148771972268029 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_35 : Point :=
  .some (x := ((104610067874554658939189781067288826551534040873032177114963645859116975547034 : Nat) : Fp))
    (y := ((109770660671288161864329498510482442986586271328087679077837897757717839673046 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((109770660671288161864329498510482442986586271328087679077837897757717839673046 : Nat) : Fp) ^ 2 = ((104610067874554658939189781067288826551534040873032177114963645859116975547034 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_36 : Point :=
  .some (x := ((101775883922931432108027453607406809406988783938200607927691949357708936019245 : Nat) : Fp))
    (y := ((71211677518830069576439009135279320536125727843027256193157225588947573710861 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((71211677518830069576439009135279320536125727843027256193157225588947573710861 : Nat) : Fp) ^ 2 = ((101775883922931432108027453607406809406988783938200607927691949357708936019245 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_37 : Point :=
  .some (x := ((110691637496015646289262932234825854023102359733628734435283445248364686115670 : Nat) : Fp))
    (y := ((75300502224888127283828373326871043861231715295745491495384349459792808386515 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((75300502224888127283828373326871043861231715295745491495384349459792808386515 : Nat) : Fp) ^ 2 = ((110691637496015646289262932234825854023102359733628734435283445248364686115670 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_38 : Point :=
  .some (x := ((4441278141344175957087852960979663063777598386288590018731867755649013517962 : Nat) : Fp))
    (y := ((7836136238007924788592053766414363238944904687598451784829364216715569810500 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((7836136238007924788592053766414363238944904687598451784829364216715569810500 : Nat) : Fp) ^ 2 = ((4441278141344175957087852960979663063777598386288590018731867755649013517962 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_39 : Point :=
  .some (x := ((89749383265034677666862365486905244671167444330802547291623325584186528137154 : Nat) : Fp))
    (y := ((98309468026548637860626714749357698670012533693024507288465476348752328350038 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((98309468026548637860626714749357698670012533693024507288465476348752328350038 : Nat) : Fp) ^ 2 = ((89749383265034677666862365486905244671167444330802547291623325584186528137154 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_40 : Point :=
  .some (x := ((115301655840403608332148854465368444683257224081574702572138639602380667382125 : Nat) : Fp))
    (y := ((103799472776126890762485670055583971987299536955028941653349419016168013365384 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((103799472776126890762485670055583971987299536955028941653349419016168013365384 : Nat) : Fp) ^ 2 = ((115301655840403608332148854465368444683257224081574702572138639602380667382125 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_41 : Point :=
  .some (x := ((34828167905024529293425261847016829712897759939934247610415071312015953046280 : Nat) : Fp))
    (y := ((47968762878478268758489427369126262603811724231741657789486393243885145959658 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((47968762878478268758489427369126262603811724231741657789486393243885145959658 : Nat) : Fp) ^ 2 = ((34828167905024529293425261847016829712897759939934247610415071312015953046280 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_42 : Point :=
  .some (x := ((51545007865675218331521052163329117547916750428334376359731030798802230204655 : Nat) : Fp))
    (y := ((106410582405992915570439467813541861485454771813746638713688333696184247730702 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((106410582405992915570439467813541861485454771813746638713688333696184247730702 : Nat) : Fp) ^ 2 = ((51545007865675218331521052163329117547916750428334376359731030798802230204655 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_43 : Point :=
  .some (x := ((73599252554810039763407176139974374780648488828183406696254895715553023853401 : Nat) : Fp))
    (y := ((47578048250598054907858110438316220654276129654309504967125355240893257809602 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((47578048250598054907858110438316220654276129654309504967125355240893257809602 : Nat) : Fp) ^ 2 = ((73599252554810039763407176139974374780648488828183406696254895715553023853401 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_44 : Point :=
  .some (x := ((98787353431067487068174780415369765662128367506208336868623541747762523303089 : Nat) : Fp))
    (y := ((70413563958895942572205979769129125709431089683617469237670049369710274330141 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((70413563958895942572205979769129125709431089683617469237670049369710274330141 : Nat) : Fp) ^ 2 = ((98787353431067487068174780415369765662128367506208336868623541747762523303089 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_45 : Point :=
  .some (x := ((35158139218869787362323693979796990367921058080517113277431623829383205568969 : Nat) : Fp))
    (y := ((10295997985162667395889563220444841839650277790026794883844526680522437342755 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((10295997985162667395889563220444841839650277790026794883844526680522437342755 : Nat) : Fp) ^ 2 = ((35158139218869787362323693979796990367921058080517113277431623829383205568969 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_46 : Point :=
  .some (x := ((8964980402707168350657927400892132353366269496956872817449479166659938883802 : Nat) : Fp))
    (y := ((43436562493669582162283754540252355903120339577829436566794554777028968127513 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((43436562493669582162283754540252355903120339577829436566794554777028968127513 : Nat) : Fp) ^ 2 = ((8964980402707168350657927400892132353366269496956872817449479166659938883802 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_47 : Point :=
  .some (x := ((15200734767215737518231163530398231089737396965964050975192487891396519882168 : Nat) : Fp))
    (y := ((16668035065520662549877161813594040899471944430197287458384095143621564263367 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((16668035065520662549877161813594040899471944430197287458384095143621564263367 : Nat) : Fp) ^ 2 = ((15200734767215737518231163530398231089737396965964050975192487891396519882168 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_48 : Point :=
  .some (x := ((37796942232071066358676457518924870482193007026528914004372298991835746383808 : Nat) : Fp))
    (y := ((41500641220791808004786750540350768710904110215016898096683828744807363604936 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((41500641220791808004786750540350768710904110215016898096683828744807363604936 : Nat) : Fp) ^ 2 = ((37796942232071066358676457518924870482193007026528914004372298991835746383808 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_49 : Point :=
  .some (x := ((744654853145823512678710729425372655622767097643314990136170544084291976361 : Nat) : Fp))
    (y := ((21811628975969469444130274876674950438343669908561616590110157209566897229239 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((21811628975969469444130274876674950438343669908561616590110157209566897229239 : Nat) : Fp) ^ 2 = ((744654853145823512678710729425372655622767097643314990136170544084291976361 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_50 : Point :=
  .some (x := ((111242239008385952039057432864293978327910479690302189733526349492851051943515 : Nat) : Fp))
    (y := ((48678944480045457289293852267343808286651244662567230126433152661761421134978 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((48678944480045457289293852267343808286651244662567230126433152661761421134978 : Nat) : Fp) ^ 2 = ((111242239008385952039057432864293978327910479690302189733526349492851051943515 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_51 : Point :=
  .some (x := ((64822851514371701744734127217317271752112350344524279674961846392399328587059 : Nat) : Fp))
    (y := ((31943858956135239004423171297694200648464614566963609709790210548050786133055 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((31943858956135239004423171297694200648464614566963609709790210548050786133055 : Nat) : Fp) ^ 2 = ((64822851514371701744734127217317271752112350344524279674961846392399328587059 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_52 : Point :=
  .some (x := ((64447161864609791404195758691963071452721019060247337925015807247342017994823 : Nat) : Fp))
    (y := ((7561160199009862821682934691566626840504770282093073394715850644522417534762 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((7561160199009862821682934691566626840504770282093073394715850644522417534762 : Nat) : Fp) ^ 2 = ((64447161864609791404195758691963071452721019060247337925015807247342017994823 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_53 : Point :=
  .some (x := ((23384853547122068788990499588260565640987768803883409730753963558864234152785 : Nat) : Fp))
    (y := ((74875455409133275347616261968367570739354909860053424157743477951969742386200 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((74875455409133275347616261968367570739354909860053424157743477951969742386200 : Nat) : Fp) ^ 2 = ((23384853547122068788990499588260565640987768803883409730753963558864234152785 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_54 : Point :=
  .some (x := ((25014901206392249887698237444530503896296748023707107244397125743674754644790 : Nat) : Fp))
    (y := ((10433933909011809793968879060653803690577200525567091682194830769813011264330 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((10433933909011809793968879060653803690577200525567091682194830769813011264330 : Nat) : Fp) ^ 2 = ((25014901206392249887698237444530503896296748023707107244397125743674754644790 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_55 : Point :=
  .some (x := ((16058435479155118972993837131799089058715967396125428615558605751627320645142 : Nat) : Fp))
    (y := ((50458543989467853184310582844531917678045791765530172581605874408799080266778 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((50458543989467853184310582844531917678045791765530172581605874408799080266778 : Nat) : Fp) ^ 2 = ((16058435479155118972993837131799089058715967396125428615558605751627320645142 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_56 : Point :=
  .some (x := ((25497240280963516313937320941859063956353887664759333529694971679324342859874 : Nat) : Fp))
    (y := ((18198385112262447554198951719878713582193194360950043848907411919888800699475 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((18198385112262447554198951719878713582193194360950043848907411919888800699475 : Nat) : Fp) ^ 2 = ((25497240280963516313937320941859063956353887664759333529694971679324342859874 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_57 : Point :=
  .some (x := ((111703840010970554703825044762397257236786082270905035457492386104226958443132 : Nat) : Fp))
    (y := ((12575192387335088647665557233642046097109374697403005848728748607053249552642 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((12575192387335088647665557233642046097109374697403005848728748607053249552642 : Nat) : Fp) ^ 2 = ((111703840010970554703825044762397257236786082270905035457492386104226958443132 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_58 : Point :=
  .some (x := ((113599246344934629336805861786255890702306480065011524716308738005517377133750 : Nat) : Fp))
    (y := ((110309842344688524387480953361916993633315112298643725699639662741987291457779 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((110309842344688524387480953361916993633315112298643725699639662741987291457779 : Nat) : Fp) ^ 2 = ((113599246344934629336805861786255890702306480065011524716308738005517377133750 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_59 : Point :=
  .some (x := ((62223290140977849549949037397413163042719030609658769845468333603013413866526 : Nat) : Fp))
    (y := ((98850328278678552505680434968308156848819817765906617232115049710824480247537 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((98850328278678552505680434968308156848819817765906617232115049710824480247537 : Nat) : Fp) ^ 2 = ((62223290140977849549949037397413163042719030609658769845468333603013413866526 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_60 : Point :=
  .some (x := ((3155324650630266164941215407725229976924800176927891490779584824139541300135 : Nat) : Fp))
    (y := ((56314320032835626861988128097937936814282839310958875562434488369232472187232 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((56314320032835626861988128097937936814282839310958875562434488369232472187232 : Nat) : Fp) ^ 2 = ((3155324650630266164941215407725229976924800176927891490779584824139541300135 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_61 : Point :=
  .some (x := ((78940842088341059937720881764219942614374815880107123037550313585999765034797 : Nat) : Fp))
    (y := ((11720516568179571270476509769942606239875063370184749544905787775519145474236 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((11720516568179571270476509769942606239875063370184749544905787775519145474236 : Nat) : Fp) ^ 2 = ((78940842088341059937720881764219942614374815880107123037550313585999765034797 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_62 : Point :=
  .some (x := ((15507243805774944259617131345561156696188939847401319273193860618228585632400 : Nat) : Fp))
    (y := ((113088070675147226411797488422007342957654795984396137910695709288095002042967 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((113088070675147226411797488422007342957654795984396137910695709288095002042967 : Nat) : Fp) ^ 2 = ((15507243805774944259617131345561156696188939847401319273193860618228585632400 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_63 : Point :=
  .some (x := ((101817088763764058272032685058193941686495949380163784665542336507398664578275 : Nat) : Fp))
    (y := ((61440383708720907418547117747158586276459762378915736297042955400063318409160 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((61440383708720907418547117747158586276459762378915736297042955400063318409160 : Nat) : Fp) ^ 2 = ((101817088763764058272032685058193941686495949380163784665542336507398664578275 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_64 : Point :=
  .some (x := ((23129491278950567785970148376500648032717531886785241126168611397589814798013 : Nat) : Fp))
    (y := ((39307099057880941662675806615359097347682728603444928455093651353540932186784 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((39307099057880941662675806615359097347682728603444928455093651353540932186784 : Nat) : Fp) ^ 2 = ((23129491278950567785970148376500648032717531886785241126168611397589814798013 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_65 : Point :=
  .some (x := ((63843472757015161619640823952764524318291830965488059905636263767209969312866 : Nat) : Fp))
    (y := ((106712674239183055714747170770237410600716249238757184591428740534726428083980 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((106712674239183055714747170770237410600716249238757184591428740534726428083980 : Nat) : Fp) ^ 2 = ((63843472757015161619640823952764524318291830965488059905636263767209969312866 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_66 : Point :=
  .some (x := ((8241903038354912941099822707985246210294044712473769251710198461880050574899 : Nat) : Fp))
    (y := ((62697784033925076403474224442689974679135179320309080987220280194454804723717 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((62697784033925076403474224442689974679135179320309080987220280194454804723717 : Nat) : Fp) ^ 2 = ((8241903038354912941099822707985246210294044712473769251710198461880050574899 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_67 : Point :=
  .some (x := ((17692067919141883746474430216313318912323253047795385992074267436472656099942 : Nat) : Fp))
    (y := ((42168706312448760835164198288963124085049274787903511949048046806853155067687 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((42168706312448760835164198288963124085049274787903511949048046806853155067687 : Nat) : Fp) ^ 2 = ((17692067919141883746474430216313318912323253047795385992074267436472656099942 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_68 : Point :=
  .some (x := ((60339901160910692237675572757878163770580581369373573584664013679285413129091 : Nat) : Fp))
    (y := ((56214196748543440839296827556230703893730514912272645534922309181995758064550 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((56214196748543440839296827556230703893730514912272645534922309181995758064550 : Nat) : Fp) ^ 2 = ((60339901160910692237675572757878163770580581369373573584664013679285413129091 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_69 : Point :=
  .some (x := ((37677678367764998054256419260552297374816808777506812193658101085944629689381 : Nat) : Fp))
    (y := ((96542930188656188775421614396743163957109245800132742492178822512944546868854 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((96542930188656188775421614396743163957109245800132742492178822512944546868854 : Nat) : Fp) ^ 2 = ((37677678367764998054256419260552297374816808777506812193658101085944629689381 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_70 : Point :=
  .some (x := ((76492326435022593457109032906840314586595419299705002191405820035073916725430 : Nat) : Fp))
    (y := ((52712462544684042050659798408142998446211290189326915216568750458192003482817 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((52712462544684042050659798408142998446211290189326915216568750458192003482817 : Nat) : Fp) ^ 2 = ((76492326435022593457109032906840314586595419299705002191405820035073916725430 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_71 : Point :=
  .some (x := ((87459896917474640671961280404348939194085731117863029170554666522628858367860 : Nat) : Fp))
    (y := ((19748635217315891647321224482939896170227416763285583086520508401939213234176 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((19748635217315891647321224482939896170227416763285583086520508401939213234176 : Nat) : Fp) ^ 2 = ((87459896917474640671961280404348939194085731117863029170554666522628858367860 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_72 : Point :=
  .some (x := ((4199350326672760747807816527418159685216655440503240677878553304602602121738 : Nat) : Fp))
    (y := ((37834176166477149356292507688627259926034564110824553771704962901036071708041 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((37834176166477149356292507688627259926034564110824553771704962901036071708041 : Nat) : Fp) ^ 2 = ((4199350326672760747807816527418159685216655440503240677878553304602602121738 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_73 : Point :=
  .some (x := ((17451455565379830237189058882419931909327937825123020642064169531348745912330 : Nat) : Fp))
    (y := ((110851835063999899423756612638945142128964968911486626329802042725525613408346 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((110851835063999899423756612638945142128964968911486626329802042725525613408346 : Nat) : Fp) ^ 2 = ((17451455565379830237189058882419931909327937825123020642064169531348745912330 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_74 : Point :=
  .some (x := ((89639832565486215014541417774517172777425402823469120565037348938869913112470 : Nat) : Fp))
    (y := ((30572655366218421290699322537451162244586583424941183840353131006508265175422 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((30572655366218421290699322537451162244586583424941183840353131006508265175422 : Nat) : Fp) ^ 2 = ((89639832565486215014541417774517172777425402823469120565037348938869913112470 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_75 : Point :=
  .some (x := ((7442624616783078815918535545170738536276686106683368472213004009997925387451 : Nat) : Fp))
    (y := ((77751573448339894342899057498199969560748665539929390648020324044053699567908 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((77751573448339894342899057498199969560748665539929390648020324044053699567908 : Nat) : Fp) ^ 2 = ((7442624616783078815918535545170738536276686106683368472213004009997925387451 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_76 : Point :=
  .some (x := ((44497701670421232817550738477766131574027528256828192704387553796074849163496 : Nat) : Fp))
    (y := ((85115484315990908818625714664072075837750502822084508644932753849460649668119 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((85115484315990908818625714664072075837750502822084508644932753849460649668119 : Nat) : Fp) ^ 2 = ((44497701670421232817550738477766131574027528256828192704387553796074849163496 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_77 : Point :=
  .some (x := ((60540754330080069959401906198898450479294126639715413570889179042286485863469 : Nat) : Fp))
    (y := ((40065985632112285488262829097473122728635230343056068824717075042107181358448 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((40065985632112285488262829097473122728635230343056068824717075042107181358448 : Nat) : Fp) ^ 2 = ((60540754330080069959401906198898450479294126639715413570889179042286485863469 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_78 : Point :=
  .some (x := ((64303414747220612283598620667555879428236715359485947560901082787102828757209 : Nat) : Fp))
    (y := ((106228226569454347670647985876151839080805653229947291906912035484638171537232 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((106228226569454347670647985876151839080805653229947291906912035484638171537232 : Nat) : Fp) ^ 2 = ((64303414747220612283598620667555879428236715359485947560901082787102828757209 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_79 : Point :=
  .some (x := ((53648153254893980119900785370237364158138815147385101116545069153555170288062 : Nat) : Fp))
    (y := ((34361801916858031928794980991103430340262038618413794433537084872221158631519 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((34361801916858031928794980991103430340262038618413794433537084872221158631519 : Nat) : Fp) ^ 2 = ((53648153254893980119900785370237364158138815147385101116545069153555170288062 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_80 : Point :=
  .some (x := ((103585811642593135420456399622448891166663363501464111582343873522977792850477 : Nat) : Fp))
    (y := ((31409815155472435338582344935230131320197144774427706287861757740924066421722 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((31409815155472435338582344935230131320197144774427706287861757740924066421722 : Nat) : Fp) ^ 2 = ((103585811642593135420456399622448891166663363501464111582343873522977792850477 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_81 : Point :=
  .some (x := ((75027487913834453984361996105244344495268805009066851630705393620238615786735 : Nat) : Fp))
    (y := ((4325061896769276104913772732319997098916385262805927028161444887858874342220 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((4325061896769276104913772732319997098916385262805927028161444887858874342220 : Nat) : Fp) ^ 2 = ((75027487913834453984361996105244344495268805009066851630705393620238615786735 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_82 : Point :=
  .some (x := ((76702516343213003595855178542925743016592575440900459987979293581918663676498 : Nat) : Fp))
    (y := ((59169763974292048230483290348723286025776147993831754859145423822145515799140 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((59169763974292048230483290348723286025776147993831754859145423822145515799140 : Nat) : Fp) ^ 2 = ((76702516343213003595855178542925743016592575440900459987979293581918663676498 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_83 : Point :=
  .some (x := ((82065288257280364930681258037857029580600229348145328350024440340670179446551 : Nat) : Fp))
    (y := ((23027132854424541515521319202161519225460618376982276335759008484746030223405 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((23027132854424541515521319202161519225460618376982276335759008484746030223405 : Nat) : Fp) ^ 2 = ((82065288257280364930681258037857029580600229348145328350024440340670179446551 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_84 : Point :=
  .some (x := ((101493787511861733029271951475039268072513144731938223971108244357658061891365 : Nat) : Fp))
    (y := ((55437542190981407452923664626193149136100172061209688271244666364673120940509 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((55437542190981407452923664626193149136100172061209688271244666364673120940509 : Nat) : Fp) ^ 2 = ((101493787511861733029271951475039268072513144731938223971108244357658061891365 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_85 : Point :=
  .some (x := ((6636410774506556864774005162061951749450537962799954397758090215581031792446 : Nat) : Fp))
    (y := ((33193850663848721154507883351096416412681014543344176760472364118972599175560 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((33193850663848721154507883351096416412681014543344176760472364118972599175560 : Nat) : Fp) ^ 2 = ((6636410774506556864774005162061951749450537962799954397758090215581031792446 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_86 : Point :=
  .some (x := ((97007893071212898831976542306925407114333944783774668033349973529691460445404 : Nat) : Fp))
    (y := ((18507121058431491916818312533740360825972223949528183085794866203720624591878 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((18507121058431491916818312533740360825972223949528183085794866203720624591878 : Nat) : Fp) ^ 2 = ((97007893071212898831976542306925407114333944783774668033349973529691460445404 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_87 : Point :=
  .some (x := ((47579402496219589148753080604487008179301822313334601064657607711684826233267 : Nat) : Fp))
    (y := ((57448470377652821134170456021628327741101079070106580787911301709526093883982 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((57448470377652821134170456021628327741101079070106580787911301709526093883982 : Nat) : Fp) ^ 2 = ((47579402496219589148753080604487008179301822313334601064657607711684826233267 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_88 : Point :=
  .some (x := ((15033179896439470858126247808641765484544705738074160218957951164394937620308 : Nat) : Fp))
    (y := ((34117244282055289120898203738790815580918088000686828227920818069382230202610 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((34117244282055289120898203738790815580918088000686828227920818069382230202610 : Nat) : Fp) ^ 2 = ((15033179896439470858126247808641765484544705738074160218957951164394937620308 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_89 : Point :=
  .some (x := ((12831426614286788027900392815123462940913304574075286993885122038414101217196 : Nat) : Fp))
    (y := ((36179658746250976381135601610242632021826214896264269021914509495791394149615 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((36179658746250976381135601610242632021826214896264269021914509495791394149615 : Nat) : Fp) ^ 2 = ((12831426614286788027900392815123462940913304574075286993885122038414101217196 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_90 : Point :=
  .some (x := ((31731558888758314830347225402035966953019197198882726537928061332981883805116 : Nat) : Fp))
    (y := ((6359760100839187210073863293870527713027761135409961108195017073136576674018 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((6359760100839187210073863293870527713027761135409961108195017073136576674018 : Nat) : Fp) ^ 2 = ((31731558888758314830347225402035966953019197198882726537928061332981883805116 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_91 : Point :=
  .some (x := ((108516937186382041812103670511048142301189499913949040064226297021918453104669 : Nat) : Fp))
    (y := ((77218777772268311707719666397699916259759523817816920080352731398095643624469 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((77218777772268311707719666397699916259759523817816920080352731398095643624469 : Nat) : Fp) ^ 2 = ((108516937186382041812103670511048142301189499913949040064226297021918453104669 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_92 : Point :=
  .some (x := ((35499761538901346298861898883401367492089066355756477731651612619020269507900 : Nat) : Fp))
    (y := ((10609229642071556953120109475763397943884016840919846757331088165175050414822 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((10609229642071556953120109475763397943884016840919846757331088165175050414822 : Nat) : Fp) ^ 2 = ((35499761538901346298861898883401367492089066355756477731651612619020269507900 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_93 : Point :=
  .some (x := ((62221449722415965098534394864216300756619410467360193813993841802984909839181 : Nat) : Fp))
    (y := ((30612701817593165310829908596077980446317954217062442246601062375597549071147 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((30612701817593165310829908596077980446317954217062442246601062375597549071147 : Nat) : Fp) ^ 2 = ((62221449722415965098534394864216300756619410467360193813993841802984909839181 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_94 : Point :=
  .some (x := ((47023343771514073333682842422673144869316327792644186859934319437403081634095 : Nat) : Fp))
    (y := ((83317154179385276448599698389111199063686628672572418790396772309007183470821 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((83317154179385276448599698389111199063686628672572418790396772309007183470821 : Nat) : Fp) ^ 2 = ((47023343771514073333682842422673144869316327792644186859934319437403081634095 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_95 : Point :=
  .some (x := ((22840966669343746868657542410372307235035375411707745900291535045354561578850 : Nat) : Fp))
    (y := ((80886292560052078022819942209443457651640717456431378184925170018374473757441 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((80886292560052078022819942209443457651640717456431378184925170018374473757441 : Nat) : Fp) ^ 2 = ((22840966669343746868657542410372307235035375411707745900291535045354561578850 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_96 : Point :=
  .some (x := ((115183067000797961901920784023024616254245272923307973061240480176353201301430 : Nat) : Fp))
    (y := ((49763971281659542105744668679966078286699279184665337082856648066049033156975 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((49763971281659542105744668679966078286699279184665337082856648066049033156975 : Nat) : Fp) ^ 2 = ((115183067000797961901920784023024616254245272923307973061240480176353201301430 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_97 : Point :=
  .some (x := ((107460092490405557856637269383143137018363307684850226624646466770567328913124 : Nat) : Fp))
    (y := ((27927879468288414295198600435976090224174968562527111521940172877594627850158 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((27927879468288414295198600435976090224174968562527111521940172877594627850158 : Nat) : Fp) ^ 2 = ((107460092490405557856637269383143137018363307684850226624646466770567328913124 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_98 : Point :=
  .some (x := ((18928961140921885700908658116849834750075223885003133432284077605308119970073 : Nat) : Fp))
    (y := ((57811541833390055306833565592598106401230808311112346834369084436570498753337 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((57811541833390055306833565592598106401230808311112346834369084436570498753337 : Nat) : Fp) ^ 2 = ((18928961140921885700908658116849834750075223885003133432284077605308119970073 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_99 : Point :=
  .some (x := ((8331289978464196047324092750470018314791143098216854808915615772554507199633 : Nat) : Fp))
    (y := ((87592962133464766467334907348498449098375430086853996682723463167279731306372 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((87592962133464766467334907348498449098375430086853996682723463167279731306372 : Nat) : Fp) ^ 2 = ((8331289978464196047324092750470018314791143098216854808915615772554507199633 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_100 : Point :=
  .some (x := ((53779740109432100521872576345148245383728952983207835874526110853417815367225 : Nat) : Fp))
    (y := ((90939394492963130914544575569526310734855569061258844327812366475243930364929 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((90939394492963130914544575569526310734855569061258844327812366475243930364929 : Nat) : Fp) ^ 2 = ((53779740109432100521872576345148245383728952983207835874526110853417815367225 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_101 : Point :=
  .some (x := ((50903437175324684576123794325687091093316794895342376267022156508043454547877 : Nat) : Fp))
    (y := ((70349280139070181932538936546431771279420426752065163651109781251026950404544 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((70349280139070181932538936546431771279420426752065163651109781251026950404544 : Nat) : Fp) ^ 2 = ((50903437175324684576123794325687091093316794895342376267022156508043454547877 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_102 : Point :=
  .some (x := ((11673581412764099021153615077620366366802304893369795243117390666352665359806 : Nat) : Fp))
    (y := ((18493885180880533479983549127533520654731835271435443031664047750964210440946 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((18493885180880533479983549127533520654731835271435443031664047750964210440946 : Nat) : Fp) ^ 2 = ((11673581412764099021153615077620366366802304893369795243117390666352665359806 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_103 : Point :=
  .some (x := ((79346041630131869075645430486783108716991485536433518103538843150249487037416 : Nat) : Fp))
    (y := ((3399478885375643092936720555036030158803236931787480448997057703838011734762 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((3399478885375643092936720555036030158803236931787480448997057703838011734762 : Nat) : Fp) ^ 2 = ((79346041630131869075645430486783108716991485536433518103538843150249487037416 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_104 : Point :=
  .some (x := ((90110562832831649967185144230038867070402237425213645393423897349775852026001 : Nat) : Fp))
    (y := ((62079424087973467789382713581435573708404480254567931314506333392316481045699 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((62079424087973467789382713581435573708404480254567931314506333392316481045699 : Nat) : Fp) ^ 2 = ((90110562832831649967185144230038867070402237425213645393423897349775852026001 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_105 : Point :=
  .some (x := ((38659527363743848181468463025813757193528718820669569569114028561419930348315 : Nat) : Fp))
    (y := ((104083246136889829683331969264423162114671872108616362771383171554424986219793 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((104083246136889829683331969264423162114671872108616362771383171554424986219793 : Nat) : Fp) ^ 2 = ((38659527363743848181468463025813757193528718820669569569114028561419930348315 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_106 : Point :=
  .some (x := ((32543944108095182552403308115282823595699487874750970784134326899018753076265 : Nat) : Fp))
    (y := ((32924494876951284146279766638563025708747643322813908934636585593423158017785 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((32924494876951284146279766638563025708747643322813908934636585593423158017785 : Nat) : Fp) ^ 2 = ((32543944108095182552403308115282823595699487874750970784134326899018753076265 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_107 : Point :=
  .some (x := ((87183516938829948739214915672694597601526144237528747913079459935123543116507 : Nat) : Fp))
    (y := ((5210361221244717547856165246556020619071402127820810229408988718584663707749 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((5210361221244717547856165246556020619071402127820810229408988718584663707749 : Nat) : Fp) ^ 2 = ((87183516938829948739214915672694597601526144237528747913079459935123543116507 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_108 : Point :=
  .some (x := ((97963514608391620515365258119340011983767027607182736209046173629563994030411 : Nat) : Fp))
    (y := ((115226106161721418677257600232626422670483402750299325766423254986581008554271 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((115226106161721418677257600232626422670483402750299325766423254986581008554271 : Nat) : Fp) ^ 2 = ((97963514608391620515365258119340011983767027607182736209046173629563994030411 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_109 : Point :=
  .some (x := ((114469486435796862354824725635274301733105436679732187907727741160909533840420 : Nat) : Fp))
    (y := ((15176610360357502916376731715182826626094867832295623397483794147117662068209 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((15176610360357502916376731715182826626094867832295623397483794147117662068209 : Nat) : Fp) ^ 2 = ((114469486435796862354824725635274301733105436679732187907727741160909533840420 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_110 : Point :=
  .some (x := ((98432034282390382237828948384540370085442598032656811937139102930236777548604 : Nat) : Fp))
    (y := ((24813777388505064074621970457041023547619648696034102349374362496379715467175 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((24813777388505064074621970457041023547619648696034102349374362496379715467175 : Nat) : Fp) ^ 2 = ((98432034282390382237828948384540370085442598032656811937139102930236777548604 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_111 : Point :=
  .some (x := ((1805616805351721617653443610838676066411318390548678811172302707980664066418 : Nat) : Fp))
    (y := ((29197166736887483563928586983131420527850770453920557715930559189098823391124 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29197166736887483563928586983131420527850770453920557715930559189098823391124 : Nat) : Fp) ^ 2 = ((1805616805351721617653443610838676066411318390548678811172302707980664066418 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_112 : Point :=
  .some (x := ((83611758343266467712438158213251624839283837284463888705796077990149381123587 : Nat) : Fp))
    (y := ((18101124850041158815009009485735144088925930424123803647507665853537289369319 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((18101124850041158815009009485735144088925930424123803647507665853537289369319 : Nat) : Fp) ^ 2 = ((83611758343266467712438158213251624839283837284463888705796077990149381123587 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_113 : Point :=
  .some (x := ((49398952861877205296964985511595482837454065472867773380651392793273881817706 : Nat) : Fp))
    (y := ((103456599417569656329743525842643406894367321159609200220648758243892831845501 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((103456599417569656329743525842643406894367321159609200220648758243892831845501 : Nat) : Fp) ^ 2 = ((49398952861877205296964985511595482837454065472867773380651392793273881817706 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_114 : Point :=
  .some (x := ((26557021881017484338287109395067993477080269267457693436680348679906749635481 : Nat) : Fp))
    (y := ((84487769519853421430030359463214449378435630494204186353059369760950916380835 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((84487769519853421430030359463214449378435630494204186353059369760950916380835 : Nat) : Fp) ^ 2 = ((26557021881017484338287109395067993477080269267457693436680348679906749635481 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_115 : Point :=
  .some (x := ((54910438115352124820925906331600651980234249876402837107104827961903280048346 : Nat) : Fp))
    (y := ((35080546347367598434982768185387546912732524650521251475529423425038042189569 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((35080546347367598434982768185387546912732524650521251475529423425038042189569 : Nat) : Fp) ^ 2 = ((54910438115352124820925906331600651980234249876402837107104827961903280048346 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_116 : Point :=
  .some (x := ((104964699132307836705335251996858916554346905150414321329455806487577227222877 : Nat) : Fp))
    (y := ((108021264621442630025722058757308611603027665565497116827018930375054827580536 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((108021264621442630025722058757308611603027665565497116827018930375054827580536 : Nat) : Fp) ^ 2 = ((104964699132307836705335251996858916554346905150414321329455806487577227222877 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_117 : Point :=
  .some (x := ((30779593535010329084651325212930254896397289835007988481712809855381584203096 : Nat) : Fp))
    (y := ((75438522668351783504686245637900335802808862903871170538716693983846568968011 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((75438522668351783504686245637900335802808862903871170538716693983846568968011 : Nat) : Fp) ^ 2 = ((30779593535010329084651325212930254896397289835007988481712809855381584203096 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_118 : Point :=
  .some (x := ((111531859894160106348996194269099060679947894846103401064923066647433585462032 : Nat) : Fp))
    (y := ((29241751855199681568367284518448893439960716762286924487213503019678103002705 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29241751855199681568367284518448893439960716762286924487213503019678103002705 : Nat) : Fp) ^ 2 = ((111531859894160106348996194269099060679947894846103401064923066647433585462032 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_119 : Point :=
  .some (x := ((63066765102144977597923579437181551876011710207298597143023780209765509321725 : Nat) : Fp))
    (y := ((106007349317296939888635500379499007381281650903559653902304432927687101375981 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((106007349317296939888635500379499007381281650903559653902304432927687101375981 : Nat) : Fp) ^ 2 = ((63066765102144977597923579437181551876011710207298597143023780209765509321725 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_120 : Point :=
  .some (x := ((73729489189146206306669255701359614973467519172738994441001234600131693731952 : Nat) : Fp))
    (y := ((52215583774525796109567946288556659634043653399932078971590626905269875474081 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((52215583774525796109567946288556659634043653399932078971590626905269875474081 : Nat) : Fp) ^ 2 = ((73729489189146206306669255701359614973467519172738994441001234600131693731952 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_121 : Point :=
  .some (x := ((18039326416892417753003755158326429558922487640705110383763721719977461130670 : Nat) : Fp))
    (y := ((22183031661069407114947469617732171225545226302519288081136966780058091537843 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((22183031661069407114947469617732171225545226302519288081136966780058091537843 : Nat) : Fp) ^ 2 = ((18039326416892417753003755158326429558922487640705110383763721719977461130670 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_122 : Point :=
  .some (x := ((90043658892995399465363207869075768002289250211409595011736991935239142954926 : Nat) : Fp))
    (y := ((33195971463859634916825320647431346032578912048614106257629795755556424999572 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((33195971463859634916825320647431346032578912048614106257629795755556424999572 : Nat) : Fp) ^ 2 = ((90043658892995399465363207869075768002289250211409595011736991935239142954926 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_123 : Point :=
  .some (x := ((5420721428656512733924502511426114039091019723753927823327107920655123143427 : Nat) : Fp))
    (y := ((11458489637841101089267453881300170307046154505862838558859267626137645974850 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((11458489637841101089267453881300170307046154505862838558859267626137645974850 : Nat) : Fp) ^ 2 = ((5420721428656512733924502511426114039091019723753927823327107920655123143427 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_124 : Point :=
  .some (x := ((65439637510807713056358030282940995565074807966223863057633547322884310978260 : Nat) : Fp))
    (y := ((6474571117676685817754405485757825849845707811112126411536249919905291235664 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((6474571117676685817754405485757825849845707811112126411536249919905291235664 : Nat) : Fp) ^ 2 = ((65439637510807713056358030282940995565074807966223863057633547322884310978260 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_125 : Point :=
  .some (x := ((57070623766206825319979971604352341937693971268571462200885005684041460744529 : Nat) : Fp))
    (y := ((65294641003401362594966851216569681914884202591426370350835007421691752226503 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((65294641003401362594966851216569681914884202591426370350835007421691752226503 : Nat) : Fp) ^ 2 = ((57070623766206825319979971604352341937693971268571462200885005684041460744529 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_126 : Point :=
  .some (x := ((72947739749743623666767893079604022957810777496958067665094811548956867552663 : Nat) : Fp))
    (y := ((74931287229039237066253562221237323976647082407514979153759017931296701314826 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((74931287229039237066253562221237323976647082407514979153759017931296701314826 : Nat) : Fp) ^ 2 = ((72947739749743623666767893079604022957810777496958067665094811548956867552663 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_127 : Point :=
  .some (x := ((95120790446093252839327344452467895851663435942220974758177611352160193500228 : Nat) : Fp))
    (y := ((40252511218087247830580930812776238463499994792031801540758272438053921180247 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((40252511218087247830580930812776238463499994792031801540758272438053921180247 : Nat) : Fp) ^ 2 = ((95120790446093252839327344452467895851663435942220974758177611352160193500228 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_128 : Point :=
  .some (x := ((64865771952738249789114440545196421582918768733599534045195125031385885360346 : Nat) : Fp))
    (y := ((46211216742671250426576585530459394900178019437443360579906162037052661563266 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((46211216742671250426576585530459394900178019437443360579906162037052661563266 : Nat) : Fp) ^ 2 = ((64865771952738249789114440545196421582918768733599534045195125031385885360346 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_129 : Point :=
  .some (x := ((34958276914040952500699582748843894357474821914666173518868387777824232206454 : Nat) : Fp))
    (y := ((92814217969284136468346182500006122495187572087944979217112043851363214063646 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((92814217969284136468346182500006122495187572087944979217112043851363214063646 : Nat) : Fp) ^ 2 = ((34958276914040952500699582748843894357474821914666173518868387777824232206454 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_130 : Point :=
  .some (x := ((53097865109432700015174734468294135156387483155245154627764610227234210717734 : Nat) : Fp))
    (y := ((87675404738916139099090938273911264414778058285600924992648328889621933853939 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((87675404738916139099090938273911264414778058285600924992648328889621933853939 : Nat) : Fp) ^ 2 = ((53097865109432700015174734468294135156387483155245154627764610227234210717734 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_131 : Point :=
  .some (x := ((14944996539173920287535718879437473208319387726469358424706553507748318061176 : Nat) : Fp))
    (y := ((46613147883270029947538528514141525607759085017677379708440701301821571539505 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((46613147883270029947538528514141525607759085017677379708440701301821571539505 : Nat) : Fp) ^ 2 = ((14944996539173920287535718879437473208319387726469358424706553507748318061176 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_132 : Point :=
  .some (x := ((103558405691517931349553446884579863115096122592891559643307293876412976668177 : Nat) : Fp))
    (y := ((13744988175479693349153508932944119281940564264745175840075269177938566411196 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((13744988175479693349153508932944119281940564264745175840075269177938566411196 : Nat) : Fp) ^ 2 = ((103558405691517931349553446884579863115096122592891559643307293876412976668177 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_133 : Point :=
  .some (x := ((34009678302028016429416675792156881929217167215919330167617059558107204398895 : Nat) : Fp))
    (y := ((52818492011674921634940119787779214367302340414675558363211486292657494734263 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((52818492011674921634940119787779214367302340414675558363211486292657494734263 : Nat) : Fp) ^ 2 = ((34009678302028016429416675792156881929217167215919330167617059558107204398895 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_134 : Point :=
  .some (x := ((92137904221004991822640747341747548945462418389173665085162488592935043663263 : Nat) : Fp))
    (y := ((33517309963374711058233805017888397313880557032455674904311603088567752722188 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((33517309963374711058233805017888397313880557032455674904311603088567752722188 : Nat) : Fp) ^ 2 = ((92137904221004991822640747341747548945462418389173665085162488592935043663263 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_135 : Point :=
  .some (x := ((110576394165891695959547398864574113324861677782985712232382940604063624860352 : Nat) : Fp))
    (y := ((57461221252293229523075183660643751795445411566005575478984600070226388935166 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((57461221252293229523075183660643751795445411566005575478984600070226388935166 : Nat) : Fp) ^ 2 = ((110576394165891695959547398864574113324861677782985712232382940604063624860352 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_136 : Point :=
  .some (x := ((63325528419660284613648700910995098077763772416467869706013046991065094742686 : Nat) : Fp))
    (y := ((108393323332799615882600625899672562866564791265938552990560624893577369108811 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((108393323332799615882600625899672562866564791265938552990560624893577369108811 : Nat) : Fp) ^ 2 = ((63325528419660284613648700910995098077763772416467869706013046991065094742686 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_137 : Point :=
  .some (x := ((16650325658330045346563110008023955204728736149712219077558782426015089744479 : Nat) : Fp))
    (y := ((106745057410625224717707804586771450297805286348157954948730939917388737042539 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((106745057410625224717707804586771450297805286348157954948730939917388737042539 : Nat) : Fp) ^ 2 = ((16650325658330045346563110008023955204728736149712219077558782426015089744479 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_138 : Point :=
  .some (x := ((131611795964869315746733228552844550837488089277020511476213613441587846562 : Nat) : Fp))
    (y := ((83923066471392572458821227876885635434639856986135936389815903323954601786918 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((83923066471392572458821227876885635434639856986135936389815903323954601786918 : Nat) : Fp) ^ 2 = ((131611795964869315746733228552844550837488089277020511476213613441587846562 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_139 : Point :=
  .some (x := ((107872043834894622552741642145000578443189656222946491690889504134408605289317 : Nat) : Fp))
    (y := ((107099881035735432711210408988501874747725935128038800415340434399284629514586 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((107099881035735432711210408988501874747725935128038800415340434399284629514586 : Nat) : Fp) ^ 2 = ((107872043834894622552741642145000578443189656222946491690889504134408605289317 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_140 : Point :=
  .some (x := ((104771248853243272236194848180534099944827442851439463989997715693033419914817 : Nat) : Fp))
    (y := ((19204842090783572478934763263896016084146536297748178843263225598863834152273 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((19204842090783572478934763263896016084146536297748178843263225598863834152273 : Nat) : Fp) ^ 2 = ((104771248853243272236194848180534099944827442851439463989997715693033419914817 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_141 : Point :=
  .some (x := ((111175281461482630465516451385666215051004681245013976528598462758289754744929 : Nat) : Fp))
    (y := ((11718140657345423934070547093851147149502657148997117054604879635944084480924 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((11718140657345423934070547093851147149502657148997117054604879635944084480924 : Nat) : Fp) ^ 2 = ((111175281461482630465516451385666215051004681245013976528598462758289754744929 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_142 : Point :=
  .some (x := ((105488831999329979845280202950265439784555002249815723414248217238410787198545 : Nat) : Fp))
    (y := ((60737856123767596328148824409984345799986282506783260172759469126809007188004 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((60737856123767596328148824409984345799986282506783260172759469126809007188004 : Nat) : Fp) ^ 2 = ((105488831999329979845280202950265439784555002249815723414248217238410787198545 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_143 : Point :=
  .some (x := ((17310420785061577297752661644696441307039468088644562990992232456213652941707 : Nat) : Fp))
    (y := ((55135767764556490992818664763424664824858578437374820236794056603342661870707 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((55135767764556490992818664763424664824858578437374820236794056603342661870707 : Nat) : Fp) ^ 2 = ((17310420785061577297752661644696441307039468088644562990992232456213652941707 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_144 : Point :=
  .some (x := ((82443941766934163206572457262087615792206098199618204196957878539943664124143 : Nat) : Fp))
    (y := ((2933900802655320228371872386727285565009607891164205160519475145640485435973 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((2933900802655320228371872386727285565009607891164205160519475145640485435973 : Nat) : Fp) ^ 2 = ((82443941766934163206572457262087615792206098199618204196957878539943664124143 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_145 : Point :=
  .some (x := ((103962888990006132945402596005118657935911401245401713878311715854693536019743 : Nat) : Fp))
    (y := ((35170703879107070397528715355676250246151611539838021540277202550315100054233 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((35170703879107070397528715355676250246151611539838021540277202550315100054233 : Nat) : Fp) ^ 2 = ((103962888990006132945402596005118657935911401245401713878311715854693536019743 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_146 : Point :=
  .some (x := ((76798050358113205419697175833140553167147138571698176181621558826323550756452 : Nat) : Fp))
    (y := ((110695089775790420212275781036515251705109498767909652055725128324950720721559 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((110695089775790420212275781036515251705109498767909652055725128324950720721559 : Nat) : Fp) ^ 2 = ((76798050358113205419697175833140553167147138571698176181621558826323550756452 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_147 : Point :=
  .some (x := ((47484798214816784752283428012568388928491303787309098798019624575261039535228 : Nat) : Fp))
    (y := ((92757387985797433337504154397545024770971021650910819219563990946722655340125 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((92757387985797433337504154397545024770971021650910819219563990946722655340125 : Nat) : Fp) ^ 2 = ((47484798214816784752283428012568388928491303787309098798019624575261039535228 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_148 : Point :=
  .some (x := ((97039663311497459657247911541193759080562874005661443810591707745986428879848 : Nat) : Fp))
    (y := ((99303278877429417088246557868681959316984965013771041163804468621043567898912 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((99303278877429417088246557868681959316984965013771041163804468621043567898912 : Nat) : Fp) ^ 2 = ((97039663311497459657247911541193759080562874005661443810591707745986428879848 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_149 : Point :=
  .some (x := ((109195128225849040977606835881519875573565462568688209681805403608282150647549 : Nat) : Fp))
    (y := ((19112323507498003064396425936166321573933767740378942347221947598633080738522 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((19112323507498003064396425936166321573933767740378942347221947598633080738522 : Nat) : Fp) ^ 2 = ((109195128225849040977606835881519875573565462568688209681805403608282150647549 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_150 : Point :=
  .some (x := ((29549999707259271673252605691545279799740052232833339972136839518663945868516 : Nat) : Fp))
    (y := ((16136664718778354741239915467490083114312845627443806165166400322025562172700 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((16136664718778354741239915467490083114312845627443806165166400322025562172700 : Nat) : Fp) ^ 2 = ((29549999707259271673252605691545279799740052232833339972136839518663945868516 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_151 : Point :=
  .some (x := ((82879960253585350000979087803723632982965447634585893737399105385978335789638 : Nat) : Fp))
    (y := ((69839675855252625382864852692238872585628385971310815662725729943087609430139 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((69839675855252625382864852692238872585628385971310815662725729943087609430139 : Nat) : Fp) ^ 2 = ((82879960253585350000979087803723632982965447634585893737399105385978335789638 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_152 : Point :=
  .some (x := ((22748028221779319076176510624118970842784515483405130895360428655102883872093 : Nat) : Fp))
    (y := ((45475484805375289014292969224159029645777915241785857295305535555664117202052 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((45475484805375289014292969224159029645777915241785857295305535555664117202052 : Nat) : Fp) ^ 2 = ((22748028221779319076176510624118970842784515483405130895360428655102883872093 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_153 : Point :=
  .some (x := ((22971131504152232323989187247411808869683627396897027961368542431926019004233 : Nat) : Fp))
    (y := ((97609736426556728831591583803631233034684715940413408963258107819767740020195 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((97609736426556728831591583803631233034684715940413408963258107819767740020195 : Nat) : Fp) ^ 2 = ((22971131504152232323989187247411808869683627396897027961368542431926019004233 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_154 : Point :=
  .some (x := ((106366286125714711143514653622793217383752466534676761043495549248010028815844 : Nat) : Fp))
    (y := ((63443518936078980928975271049594475518271079655621131486236396265316979810558 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((63443518936078980928975271049594475518271079655621131486236396265316979810558 : Nat) : Fp) ^ 2 = ((106366286125714711143514653622793217383752466534676761043495549248010028815844 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_155 : Point :=
  .some (x := ((75243349452409400390670867080265400955826636238534964912250945418780832972765 : Nat) : Fp))
    (y := ((54981855232630153751619068839379710690392191850677614602646052403990831204099 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((54981855232630153751619068839379710690392191850677614602646052403990831204099 : Nat) : Fp) ^ 2 = ((75243349452409400390670867080265400955826636238534964912250945418780832972765 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_156 : Point :=
  .some (x := ((35269368267879876076917370410294906058734293247594447113822550857168296692886 : Nat) : Fp))
    (y := ((95273891293316720854000721987756315180413338976852308839788251922692115805 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((95273891293316720854000721987756315180413338976852308839788251922692115805 : Nat) : Fp) ^ 2 = ((35269368267879876076917370410294906058734293247594447113822550857168296692886 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_157 : Point :=
  .some (x := ((107287887465783333787672797357624470089624197428007725918345876586585458515460 : Nat) : Fp))
    (y := ((8424212039425668253022291013437891429871302723219086751247826238756909595104 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((8424212039425668253022291013437891429871302723219086751247826238756909595104 : Nat) : Fp) ^ 2 = ((107287887465783333787672797357624470089624197428007725918345876586585458515460 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_158 : Point :=
  .some (x := ((104996070104664638505320040442013632557530551413809799698237157067229055154261 : Nat) : Fp))
    (y := ((78673807004489092854216395411129353437829079224915559696534676000382399098335 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((78673807004489092854216395411129353437829079224915559696534676000382399098335 : Nat) : Fp) ^ 2 = ((104996070104664638505320040442013632557530551413809799698237157067229055154261 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_159 : Point :=
  .some (x := ((28519628026037066657027912209611592939997525521524547924497404284374169515054 : Nat) : Fp))
    (y := ((113911143471074069342269815156022191118395698271153725836799489558703307009470 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((113911143471074069342269815156022191118395698271153725836799489558703307009470 : Nat) : Fp) ^ 2 = ((28519628026037066657027912209611592939997525521524547924497404284374169515054 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_160 : Point :=
  .some (x := ((70661691742434068036519986667419907196041281127668848645928138120846244813005 : Nat) : Fp))
    (y := ((100286785047006832236729389681182172543048508833941702006321829459516874054045 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((100286785047006832236729389681182172543048508833941702006321829459516874054045 : Nat) : Fp) ^ 2 = ((70661691742434068036519986667419907196041281127668848645928138120846244813005 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_161 : Point :=
  .some (x := ((20912437725801942983686217293131152237262404596163037810613525995454376577516 : Nat) : Fp))
    (y := ((56487811975550303384642959780870327480512649236944577417586609378984145534 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((56487811975550303384642959780870327480512649236944577417586609378984145534 : Nat) : Fp) ^ 2 = ((20912437725801942983686217293131152237262404596163037810613525995454376577516 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_162 : Point :=
  .some (x := ((105337008461688988395496963115550441795554320308823072776506794583685171281126 : Nat) : Fp))
    (y := ((32017945344679105301355390714034191900569536621409624903946887176817068091004 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((32017945344679105301355390714034191900569536621409624903946887176817068091004 : Nat) : Fp) ^ 2 = ((105337008461688988395496963115550441795554320308823072776506794583685171281126 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_163 : Point :=
  .some (x := ((75685728382744045810490612211978229115853638039525209649070995925887462388674 : Nat) : Fp))
    (y := ((85529213318684499199278987295719119779748279834721244243621489005051282713327 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((85529213318684499199278987295719119779748279834721244243621489005051282713327 : Nat) : Fp) ^ 2 = ((75685728382744045810490612211978229115853638039525209649070995925887462388674 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_164 : Point :=
  .some (x := ((43575908198494793243005774075373759548810068549539444933972772880645886663141 : Nat) : Fp))
    (y := ((69703777934707822825561719800850612270463729018593401066444767531444843422376 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((69703777934707822825561719800850612270463729018593401066444767531444843422376 : Nat) : Fp) ^ 2 = ((43575908198494793243005774075373759548810068549539444933972772880645886663141 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_165 : Point :=
  .some (x := ((46793159748319014521754592728195492543648682627431155803053172123841138087004 : Nat) : Fp))
    (y := ((30896349737549724559469649176734599846674275470447944521491009517811476115886 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((30896349737549724559469649176734599846674275470447944521491009517811476115886 : Nat) : Fp) ^ 2 = ((46793159748319014521754592728195492543648682627431155803053172123841138087004 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_166 : Point :=
  .some (x := ((101757012457202265442783729516325848567041695344201435111479322003948473610273 : Nat) : Fp))
    (y := ((5581666239041823897511191387175605974957398643319691692931775273945574355546 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((5581666239041823897511191387175605974957398643319691692931775273945574355546 : Nat) : Fp) ^ 2 = ((101757012457202265442783729516325848567041695344201435111479322003948473610273 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_167 : Point :=
  .some (x := ((30209700677164570836251569796863977697827501003939778269324249569134489792003 : Nat) : Fp))
    (y := ((47413224699192139329891654683339940809213741191817662756932842522986369283987 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((47413224699192139329891654683339940809213741191817662756932842522986369283987 : Nat) : Fp) ^ 2 = ((30209700677164570836251569796863977697827501003939778269324249569134489792003 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_168 : Point :=
  .some (x := ((74841650891382527078449938271109455202772530131693735678356618476847598486118 : Nat) : Fp))
    (y := ((29242638042721994709047470454581660554102402946865770918554005639977770323656 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29242638042721994709047470454581660554102402946865770918554005639977770323656 : Nat) : Fp) ^ 2 = ((74841650891382527078449938271109455202772530131693735678356618476847598486118 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_169 : Point :=
  .some (x := ((71631157476704051659259801706240663560508572801269375166786124610215506626710 : Nat) : Fp))
    (y := ((50626912648402731289281390580926582439784259522574187076012504768241480157237 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((50626912648402731289281390580926582439784259522574187076012504768241480157237 : Nat) : Fp) ^ 2 = ((71631157476704051659259801706240663560508572801269375166786124610215506626710 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_170 : Point :=
  .some (x := ((75928542468193195488721590741574481272714198891253064800438184108329627778720 : Nat) : Fp))
    (y := ((75192750551909937947468929249355987104463312649195251159923289612823008422826 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((75192750551909937947468929249355987104463312649195251159923289612823008422826 : Nat) : Fp) ^ 2 = ((75928542468193195488721590741574481272714198891253064800438184108329627778720 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_171 : Point :=
  .some (x := ((87929611941466450580474503142124427241088012317746799540322218015595119056635 : Nat) : Fp))
    (y := ((104894792315886610373915701617963847607765162153160773537780133243754931320852 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((104894792315886610373915701617963847607765162153160773537780133243754931320852 : Nat) : Fp) ^ 2 = ((87929611941466450580474503142124427241088012317746799540322218015595119056635 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_172 : Point :=
  .some (x := ((54038406999518685708957755903010924118312453838615747233838912018122735660401 : Nat) : Fp))
    (y := ((23694175599991408963414726019522496431384061981312306500396236825552398271404 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((23694175599991408963414726019522496431384061981312306500396236825552398271404 : Nat) : Fp) ^ 2 = ((54038406999518685708957755903010924118312453838615747233838912018122735660401 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_173 : Point :=
  .some (x := ((104811972735495353830322167991327219943131946744088941348424456729187245615225 : Nat) : Fp))
    (y := ((8467783976897375037636665426419232997456360183332998866888776438963891641752 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((8467783976897375037636665426419232997456360183332998866888776438963891641752 : Nat) : Fp) ^ 2 = ((104811972735495353830322167991327219943131946744088941348424456729187245615225 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_174 : Point :=
  .some (x := ((3215551885474507458266292022538992596230437910109015106438584379300426977039 : Nat) : Fp))
    (y := ((37306322622624672463065915763956225690223522454760918147434180740861300687668 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((37306322622624672463065915763956225690223522454760918147434180740861300687668 : Nat) : Fp) ^ 2 = ((3215551885474507458266292022538992596230437910109015106438584379300426977039 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_175 : Point :=
  .some (x := ((947390502650680957920869582008711724723808429374401610775941200653824958689 : Nat) : Fp))
    (y := ((86236473645369998874832829444512637388615157303166534859982939866800801290421 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((86236473645369998874832829444512637388615157303166534859982939866800801290421 : Nat) : Fp) ^ 2 = ((947390502650680957920869582008711724723808429374401610775941200653824958689 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_176 : Point :=
  .some (x := ((4142520438525914541011842624208056062406705649998025173845082041682105009068 : Nat) : Fp))
    (y := ((87900869236804138087371702825961176259461360124819616238035200569139627100447 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((87900869236804138087371702825961176259461360124819616238035200569139627100447 : Nat) : Fp) ^ 2 = ((4142520438525914541011842624208056062406705649998025173845082041682105009068 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_177 : Point :=
  .some (x := ((35976083938318534650029463496695503152893117754555618189020557340809841204638 : Nat) : Fp))
    (y := ((91581555597957928166775283241751618539413557986610388037330404183144654090313 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((91581555597957928166775283241751618539413557986610388037330404183144654090313 : Nat) : Fp) ^ 2 = ((35976083938318534650029463496695503152893117754555618189020557340809841204638 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_178 : Point :=
  .some (x := ((92099574356616060718641758322300714450252979003106256663913657963750974558615 : Nat) : Fp))
    (y := ((44679714547892089078501304545394627678115758391255360766903436677955303545885 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((44679714547892089078501304545394627678115758391255360766903436677955303545885 : Nat) : Fp) ^ 2 = ((92099574356616060718641758322300714450252979003106256663913657963750974558615 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_179 : Point :=
  .some (x := ((102652556215175073222018368450968179239643399116479030486157396231787228507330 : Nat) : Fp))
    (y := ((14437232828413691012043572600308410207374052858180415647749396463091843383375 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((14437232828413691012043572600308410207374052858180415647749396463091843383375 : Nat) : Fp) ^ 2 = ((102652556215175073222018368450968179239643399116479030486157396231787228507330 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_180 : Point :=
  .some (x := ((60526872670786283833918632266282189958727983389364017821054603492994282170193 : Nat) : Fp))
    (y := ((14027692582691445211169305233477544073839133566657605745596417381878123854178 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((14027692582691445211169305233477544073839133566657605745596417381878123854178 : Nat) : Fp) ^ 2 = ((60526872670786283833918632266282189958727983389364017821054603492994282170193 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_181 : Point :=
  .some (x := ((48611368844139479430646292898246827799543615133757497943303942111011000011486 : Nat) : Fp))
    (y := ((94184599433492315644214590509977869566386224898957355163260253699332858500095 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((94184599433492315644214590509977869566386224898957355163260253699332858500095 : Nat) : Fp) ^ 2 = ((48611368844139479430646292898246827799543615133757497943303942111011000011486 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_182 : Point :=
  .some (x := ((29436743060920481988952312356424937775284815172144744489261980482023293444299 : Nat) : Fp))
    (y := ((90938483595262914582675074472013558936350058640531727255070751800362248713128 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((90938483595262914582675074472013558936350058640531727255070751800362248713128 : Nat) : Fp) ^ 2 = ((29436743060920481988952312356424937775284815172144744489261980482023293444299 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_183 : Point :=
  .some (x := ((94976567038575040138507300949054306311784168683241399150467020165872178418684 : Nat) : Fp))
    (y := ((65079320657075459505472718093134166223214459592164919156492801936293394346061 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((65079320657075459505472718093134166223214459592164919156492801936293394346061 : Nat) : Fp) ^ 2 = ((94976567038575040138507300949054306311784168683241399150467020165872178418684 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_184 : Point :=
  .some (x := ((115415846104970316816674669646231381722554829723945808246505339409944432478334 : Nat) : Fp))
    (y := ((33126753624353590316677983729603901933376151587979623867133648552767197976839 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((33126753624353590316677983729603901933376151587979623867133648552767197976839 : Nat) : Fp) ^ 2 = ((115415846104970316816674669646231381722554829723945808246505339409944432478334 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_185 : Point :=
  .some (x := ((18776033471282089014310671094577787458033563645391456854929614351132929947887 : Nat) : Fp))
    (y := ((75132272094628034345708172112257475055149432967843434987053037295066962960968 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((75132272094628034345708172112257475055149432967843434987053037295066962960968 : Nat) : Fp) ^ 2 = ((18776033471282089014310671094577787458033563645391456854929614351132929947887 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_186 : Point :=
  .some (x := ((11832388558031419782808688022015883762691763226078981998965787321613871498267 : Nat) : Fp))
    (y := ((38657913077255361434444622743436849344919651203626641239625924177481274928933 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((38657913077255361434444622743436849344919651203626641239625924177481274928933 : Nat) : Fp) ^ 2 = ((11832388558031419782808688022015883762691763226078981998965787321613871498267 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_187 : Point :=
  .some (x := ((5674256344222473770316337151722717121901524681814366176584467328211802271911 : Nat) : Fp))
    (y := ((6241280037293053435562565229917129205739093461742926377996529691184676112606 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((6241280037293053435562565229917129205739093461742926377996529691184676112606 : Nat) : Fp) ^ 2 = ((5674256344222473770316337151722717121901524681814366176584467328211802271911 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_188 : Point :=
  .some (x := ((59026356685222097294628395983368866596266777678130656463811370893799945855553 : Nat) : Fp))
    (y := ((89585527340406565500019872698075135548357340032819778309253570440118818477036 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((89585527340406565500019872698075135548357340032819778309253570440118818477036 : Nat) : Fp) ^ 2 = ((59026356685222097294628395983368866596266777678130656463811370893799945855553 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_189 : Point :=
  .some (x := ((82997769624973021721207329827925752179285999209160244580518381248798973329757 : Nat) : Fp))
    (y := ((34120506380485136088917855908736915544289626703143468135554854919091047095237 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((34120506380485136088917855908736915544289626703143468135554854919091047095237 : Nat) : Fp) ^ 2 = ((82997769624973021721207329827925752179285999209160244580518381248798973329757 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_190 : Point :=
  .some (x := ((32833730202948453445551585602227016221189718115335492475756041315423310145004 : Nat) : Fp))
    (y := ((53428498708335298930383652178427276342268514807561120763391253036328211515369 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((53428498708335298930383652178427276342268514807561120763391253036328211515369 : Nat) : Fp) ^ 2 = ((32833730202948453445551585602227016221189718115335492475756041315423310145004 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_191 : Point :=
  .some (x := ((105475728434031409379183406694662903881450546214247029555786593600199689335290 : Nat) : Fp))
    (y := ((113583883859274030372082034862029605514506016193810719839027086029553530647303 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((113583883859274030372082034862029605514506016193810719839027086029553530647303 : Nat) : Fp) ^ 2 = ((105475728434031409379183406694662903881450546214247029555786593600199689335290 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_192 : Point :=
  .some (x := ((106135013536326263233204638779771538367307463662639765758785315935371743257267 : Nat) : Fp))
    (y := ((86028625094535483850261571256264386723357163272666519397289099603747119225149 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((86028625094535483850261571256264386723357163272666519397289099603747119225149 : Nat) : Fp) ^ 2 = ((106135013536326263233204638779771538367307463662639765758785315935371743257267 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_193 : Point :=
  .some (x := ((26622173145108500381473837459513401868318671376325266944487505521378511663272 : Nat) : Fp))
    (y := ((25015334278771650323507319424566501275290669267697587988960111333611631525338 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((25015334278771650323507319424566501275290669267697587988960111333611631525338 : Nat) : Fp) ^ 2 = ((26622173145108500381473837459513401868318671376325266944487505521378511663272 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_194 : Point :=
  .some (x := ((8421370599800668602652103103676786751239058426611888163586601660098353727225 : Nat) : Fp))
    (y := ((29567823868173186762768009528067406508648153893486721194867955006028793890909 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29567823868173186762768009528067406508648153893486721194867955006028793890909 : Nat) : Fp) ^ 2 = ((8421370599800668602652103103676786751239058426611888163586601660098353727225 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_195 : Point :=
  .some (x := ((43457843735276724612075728233726406612249501219998543099634755887188281768154 : Nat) : Fp))
    (y := ((63192765102271790090487849294643355539231117908172846139915612801187217034173 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((63192765102271790090487849294643355539231117908172846139915612801187217034173 : Nat) : Fp) ^ 2 = ((43457843735276724612075728233726406612249501219998543099634755887188281768154 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_196 : Point :=
  .some (x := ((103417404801342136514940355813672218236352240817568397971691640510748940358223 : Nat) : Fp))
    (y := ((35110031909328754691401904954608234218729030798549406331812068095064570237972 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((35110031909328754691401904954608234218729030798549406331812068095064570237972 : Nat) : Fp) ^ 2 = ((103417404801342136514940355813672218236352240817568397971691640510748940358223 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_197 : Point :=
  .some (x := ((114612401220431600857626100267884543594407662822495910668441731424729600844475 : Nat) : Fp))
    (y := ((104607607047518035749515575138521003921603783202160061984102438399564594284817 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((104607607047518035749515575138521003921603783202160061984102438399564594284817 : Nat) : Fp) ^ 2 = ((114612401220431600857626100267884543594407662822495910668441731424729600844475 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_198 : Point :=
  .some (x := ((13990119276603863648855793891913240987255865021321113597676024132284912134507 : Nat) : Fp))
    (y := ((45762644100243963560173177200312509818364497605040202142354576105708649526139 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((45762644100243963560173177200312509818364497605040202142354576105708649526139 : Nat) : Fp) ^ 2 = ((13990119276603863648855793891913240987255865021321113597676024132284912134507 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_199 : Point :=
  .some (x := ((92297683643826826163064140665368589970769892635084083631213834209281061470421 : Nat) : Fp))
    (y := ((112881168890164609406380094011411584051648553985034449899770310954622772391910 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((112881168890164609406380094011411584051648553985034449899770310954622772391910 : Nat) : Fp) ^ 2 = ((92297683643826826163064140665368589970769892635084083631213834209281061470421 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_200 : Point :=
  .some (x := ((13922864845768229163833387034770518418928910654248512738626529054912919158553 : Nat) : Fp))
    (y := ((79126321700797654134629819022700262425734361986906066326971931873703874776829 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((79126321700797654134629819022700262425734361986906066326971931873703874776829 : Nat) : Fp) ^ 2 = ((13922864845768229163833387034770518418928910654248512738626529054912919158553 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_201 : Point :=
  .some (x := ((41570227333295029806389479208245314517359112018029925112212608294602008426980 : Nat) : Fp))
    (y := ((23045309029356249714220314716068128691355103924384360360907873576255068618171 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((23045309029356249714220314716068128691355103924384360360907873576255068618171 : Nat) : Fp) ^ 2 = ((41570227333295029806389479208245314517359112018029925112212608294602008426980 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_202 : Point :=
  .some (x := ((40228630408040464220910435747595136926324159053542900046172368281189438159800 : Nat) : Fp))
    (y := ((57003788001796941708539841608272678584351968322832676412429854825222401371502 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((57003788001796941708539841608272678584351968322832676412429854825222401371502 : Nat) : Fp) ^ 2 = ((40228630408040464220910435747595136926324159053542900046172368281189438159800 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_203 : Point :=
  .some (x := ((80048584874349841980004729440562797202284935506199377684670339908062345334316 : Nat) : Fp))
    (y := ((33429049751972530035656964727545283238705649483087953982909059058238089924020 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((33429049751972530035656964727545283238705649483087953982909059058238089924020 : Nat) : Fp) ^ 2 = ((80048584874349841980004729440562797202284935506199377684670339908062345334316 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_204 : Point :=
  .some (x := ((9234367843203278475460402406049705063687486936070061072085337642077459464894 : Nat) : Fp))
    (y := ((81007956585093945832919421410562969694439825683280800865606243366544248926160 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((81007956585093945832919421410562969694439825683280800865606243366544248926160 : Nat) : Fp) ^ 2 = ((9234367843203278475460402406049705063687486936070061072085337642077459464894 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_205 : Point :=
  .some (x := ((39490693885239044366982942241753219569930195973938085206409539076747633253548 : Nat) : Fp))
    (y := ((4398739609727183326946131652218256147146051104900180052629746226509188319237 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((4398739609727183326946131652218256147146051104900180052629746226509188319237 : Nat) : Fp) ^ 2 = ((39490693885239044366982942241753219569930195973938085206409539076747633253548 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_206 : Point :=
  .some (x := ((95822289762910972444474447423403522943496613059597976864337566726465943856851 : Nat) : Fp))
    (y := ((64164296153307859244227616480023302862568188165333043899999315127086687727186 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((64164296153307859244227616480023302862568188165333043899999315127086687727186 : Nat) : Fp) ^ 2 = ((95822289762910972444474447423403522943496613059597976864337566726465943856851 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_207 : Point :=
  .some (x := ((80360436639024982802108928438318908385607328476345612824787216050095821450571 : Nat) : Fp))
    (y := ((57369573270620142518340730615920379521637759094789396191309454253793769270353 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((57369573270620142518340730615920379521637759094789396191309454253793769270353 : Nat) : Fp) ^ 2 = ((80360436639024982802108928438318908385607328476345612824787216050095821450571 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_208 : Point :=
  .some (x := ((113220891681512744492539364929916345410061947313878915456447722256969001660153 : Nat) : Fp))
    (y := ((48632069096637554924274413793295750001160491151445521927536133070043743201297 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((48632069096637554924274413793295750001160491151445521927536133070043743201297 : Nat) : Fp) ^ 2 = ((113220891681512744492539364929916345410061947313878915456447722256969001660153 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_209 : Point :=
  .some (x := ((45044543832417204813964322358265561912289006474729602217500750943638473625672 : Nat) : Fp))
    (y := ((26879011462743840335691591457228606967066124790316477921535328699756712074744 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((26879011462743840335691591457228606967066124790316477921535328699756712074744 : Nat) : Fp) ^ 2 = ((45044543832417204813964322358265561912289006474729602217500750943638473625672 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_210 : Point :=
  .some (x := ((40815729452528180238295637155137130875534812174241845066103240363483841899109 : Nat) : Fp))
    (y := ((62963488700699789032569184806979115722324448122457023739501893021766746537757 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((62963488700699789032569184806979115722324448122457023739501893021766746537757 : Nat) : Fp) ^ 2 = ((40815729452528180238295637155137130875534812174241845066103240363483841899109 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_211 : Point :=
  .some (x := ((42019196137391938823787938398084615301261359872699590349124401997914530858192 : Nat) : Fp))
    (y := ((34767682558797648670566810324631233163266973542786319846918260332343694917893 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((34767682558797648670566810324631233163266973542786319846918260332343694917893 : Nat) : Fp) ^ 2 = ((42019196137391938823787938398084615301261359872699590349124401997914530858192 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_212 : Point :=
  .some (x := ((98656114654415212951351030182220503262040501999861380370740706389056647757506 : Nat) : Fp))
    (y := ((58503766529248989798675151322237530184126490579454294759021188248409021626097 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((58503766529248989798675151322237530184126490579454294759021188248409021626097 : Nat) : Fp) ^ 2 = ((98656114654415212951351030182220503262040501999861380370740706389056647757506 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_213 : Point :=
  .some (x := ((70779672864013442204047147619761736872402708735011963696772144922503503135593 : Nat) : Fp))
    (y := ((66095546131926016776182664572158682372222134031052577075352350981138964190485 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((66095546131926016776182664572158682372222134031052577075352350981138964190485 : Nat) : Fp) ^ 2 = ((70779672864013442204047147619761736872402708735011963696772144922503503135593 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_214 : Point :=
  .some (x := ((7147807088254754984115277020319280513928719273510749291220264632533393132003 : Nat) : Fp))
    (y := ((48870560607183744840505722498698757682142671336868405907998491847376392333741 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((48870560607183744840505722498698757682142671336868405907998491847376392333741 : Nat) : Fp) ^ 2 = ((7147807088254754984115277020319280513928719273510749291220264632533393132003 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_215 : Point :=
  .some (x := ((51318518135047612923054807776796525309348753908885584948123548636564953982193 : Nat) : Fp))
    (y := ((30623581788749822100382745859868645699047673268215141926580384967860112471253 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((30623581788749822100382745859868645699047673268215141926580384967860112471253 : Nat) : Fp) ^ 2 = ((51318518135047612923054807776796525309348753908885584948123548636564953982193 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_216 : Point :=
  .some (x := ((76388770101766026847299654420802367216385774412973782315160485495908694642195 : Nat) : Fp))
    (y := ((57710893937692665357647691724236515472507145065106377254221657836468024167436 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((57710893937692665357647691724236515472507145065106377254221657836468024167436 : Nat) : Fp) ^ 2 = ((76388770101766026847299654420802367216385774412973782315160485495908694642195 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_217 : Point :=
  .some (x := ((91718707606862637550154068541437645781425587687664226689694763206157559813025 : Nat) : Fp))
    (y := ((112096003213917921965697623480695740549761355267313232789540725477513634374998 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((112096003213917921965697623480695740549761355267313232789540725477513634374998 : Nat) : Fp) ^ 2 = ((91718707606862637550154068541437645781425587687664226689694763206157559813025 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_218 : Point :=
  .some (x := ((104427496169569391842377213290478515885839261332812951511591855258537350660157 : Nat) : Fp))
    (y := ((61132381960602712033174130914468477784017762207402074270409666098181344508219 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((61132381960602712033174130914468477784017762207402074270409666098181344508219 : Nat) : Fp) ^ 2 = ((104427496169569391842377213290478515885839261332812951511591855258537350660157 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_219 : Point :=
  .some (x := ((27276644428692416698688499014810854312801165379030850386665499374796427550985 : Nat) : Fp))
    (y := ((30749753566896120889917442069556393166141012006459550615871962942905620475626 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((30749753566896120889917442069556393166141012006459550615871962942905620475626 : Nat) : Fp) ^ 2 = ((27276644428692416698688499014810854312801165379030850386665499374796427550985 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_220 : Point :=
  .some (x := ((10534520053980272543867405036685817400667875723664235737120499452559222196604 : Nat) : Fp))
    (y := ((92628477256112478580738935680261058160861780653699013741020467863885755120243 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((92628477256112478580738935680261058160861780653699013741020467863885755120243 : Nat) : Fp) ^ 2 = ((10534520053980272543867405036685817400667875723664235737120499452559222196604 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_221 : Point :=
  .some (x := ((14881952017843508107868018207655541299293805975448542164953269149202864001651 : Nat) : Fp))
    (y := ((95744524462485084732056560754575516048250645981636693364989777482955901810067 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((95744524462485084732056560754575516048250645981636693364989777482955901810067 : Nat) : Fp) ^ 2 = ((14881952017843508107868018207655541299293805975448542164953269149202864001651 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_222 : Point :=
  .some (x := ((64250787150254837153343438979016395164129717520259441534727718215719657633396 : Nat) : Fp))
    (y := ((2226821049909366001426284673098873826917960544595316002560147822639123525016 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((2226821049909366001426284673098873826917960544595316002560147822639123525016 : Nat) : Fp) ^ 2 = ((64250787150254837153343438979016395164129717520259441534727718215719657633396 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_223 : Point :=
  .some (x := ((112052232026769664929658561660710941635228959956787050473536200851071191032897 : Nat) : Fp))
    (y := ((66850838866234897399334488953202946314182773756688684015551691304105443157422 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((66850838866234897399334488953202946314182773756688684015551691304105443157422 : Nat) : Fp) ^ 2 = ((112052232026769664929658561660710941635228959956787050473536200851071191032897 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_224 : Point :=
  .some (x := ((67655380319953589260148826173219524241109847135242745518793369102772071675834 : Nat) : Fp))
    (y := ((21029601506232444319368385136955684033497833311867654114423309422350207087357 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((21029601506232444319368385136955684033497833311867654114423309422350207087357 : Nat) : Fp) ^ 2 = ((67655380319953589260148826173219524241109847135242745518793369102772071675834 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_225 : Point :=
  .some (x := ((92240156060407253479030676529662381214111644319002643127826873158938047083835 : Nat) : Fp))
    (y := ((111327482796856645338109375925255091131664696057056686983936700507225403719493 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((111327482796856645338109375925255091131664696057056686983936700507225403719493 : Nat) : Fp) ^ 2 = ((92240156060407253479030676529662381214111644319002643127826873158938047083835 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_226 : Point :=
  .some (x := ((78627750631242170634484650157951616270326041285698762428910452596338546905565 : Nat) : Fp))
    (y := ((105735616450588913958761248879135978906628726313788624529292917321934778581901 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((105735616450588913958761248879135978906628726313788624529292917321934778581901 : Nat) : Fp) ^ 2 = ((78627750631242170634484650157951616270326041285698762428910452596338546905565 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_227 : Point :=
  .some (x := ((37970007016072384636196615568949856628931570059897898485017028997234414061945 : Nat) : Fp))
    (y := ((85633666146296869475846120618182213756296576205663668204532591586342323566242 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((85633666146296869475846120618182213756296576205663668204532591586342323566242 : Nat) : Fp) ^ 2 = ((37970007016072384636196615568949856628931570059897898485017028997234414061945 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_228 : Point :=
  .some (x := ((95279397291673716158331856496563878128970306290864555825308960160147858174289 : Nat) : Fp))
    (y := ((105017020600749110255205601310325343926653803681868124843703017010103026488325 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((105017020600749110255205601310325343926653803681868124843703017010103026488325 : Nat) : Fp) ^ 2 = ((95279397291673716158331856496563878128970306290864555825308960160147858174289 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_229 : Point :=
  .some (x := ((84556908620397086490574354609607180077068693777212695160113645418094198446687 : Nat) : Fp))
    (y := ((100718452597198377694892433543251040205084258311006913553384445818907946819791 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((100718452597198377694892433543251040205084258311006913553384445818907946819791 : Nat) : Fp) ^ 2 = ((84556908620397086490574354609607180077068693777212695160113645418094198446687 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_230 : Point :=
  .some (x := ((112030421148703629201942613873270492163488999678896447559274774208446269765955 : Nat) : Fp))
    (y := ((35384723941339661147011733585239808738288755024824978650787507425153094271729 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((35384723941339661147011733585239808738288755024824978650787507425153094271729 : Nat) : Fp) ^ 2 = ((112030421148703629201942613873270492163488999678896447559274774208446269765955 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_231 : Point :=
  .some (x := ((101186060051338727518238790300531351495613041202762303390359395316390096421977 : Nat) : Fp))
    (y := ((70018069425595998018260816426652965226827561219175179343976674369210843266462 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((70018069425595998018260816426652965226827561219175179343976674369210843266462 : Nat) : Fp) ^ 2 = ((101186060051338727518238790300531351495613041202762303390359395316390096421977 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_232 : Point :=
  .some (x := ((45387637969275774150653095889876699672169323470095019346305801601969322188915 : Nat) : Fp))
    (y := ((98434237446496148394183890050136756428510322717221929962654009239641273623945 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((98434237446496148394183890050136756428510322717221929962654009239641273623945 : Nat) : Fp) ^ 2 = ((45387637969275774150653095889876699672169323470095019346305801601969322188915 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_233 : Point :=
  .some (x := ((83407264292599769979907512419974269146592549057292719108468866098684905146381 : Nat) : Fp))
    (y := ((11344377696059311412860255181221495902312688613306488893294163454119121825704 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((11344377696059311412860255181221495902312688613306488893294163454119121825704 : Nat) : Fp) ^ 2 = ((83407264292599769979907512419974269146592549057292719108468866098684905146381 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_234 : Point :=
  .some (x := ((106823080507094536302171587221364767641207071699356594725100487456618775186796 : Nat) : Fp))
    (y := ((92690132246900151323277569114758090527006018018792578401159597199495559705760 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((92690132246900151323277569114758090527006018018792578401159597199495559705760 : Nat) : Fp) ^ 2 = ((106823080507094536302171587221364767641207071699356594725100487456618775186796 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_235 : Point :=
  .some (x := ((51458812640674469987191057145664724195213971571581134911909867396919133773071 : Nat) : Fp))
    (y := ((8629245570289361512928824496793066884814249866400051283675066385256088984418 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((8629245570289361512928824496793066884814249866400051283675066385256088984418 : Nat) : Fp) ^ 2 = ((51458812640674469987191057145664724195213971571581134911909867396919133773071 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_236 : Point :=
  .some (x := ((59934529777540515900169509345926368831906655562972450327405481276732036473944 : Nat) : Fp))
    (y := ((25750881830896011524081627616138971820801200943932001974011760182257795007870 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((25750881830896011524081627616138971820801200943932001974011760182257795007870 : Nat) : Fp) ^ 2 = ((59934529777540515900169509345926368831906655562972450327405481276732036473944 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_237 : Point :=
  .some (x := ((67920502080269633306026372339646975598405744544879176039587252097767227126036 : Nat) : Fp))
    (y := ((86511203683128773200503204915391168752553058701578039004115361443541322212241 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((86511203683128773200503204915391168752553058701578039004115361443541322212241 : Nat) : Fp) ^ 2 = ((67920502080269633306026372339646975598405744544879176039587252097767227126036 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_238 : Point :=
  .some (x := ((82877690455795689589323624744144337630277711329294127826630078132465967983811 : Nat) : Fp))
    (y := ((39922059842557940073913288636103872861952687103330770522978967679436902620067 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((39922059842557940073913288636103872861952687103330770522978967679436902620067 : Nat) : Fp) ^ 2 = ((82877690455795689589323624744144337630277711329294127826630078132465967983811 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_239 : Point :=
  .some (x := ((107647080929067738343525460704633213843414790178366076706967300283813568943072 : Nat) : Fp))
    (y := ((107835997232065897977399831129863752621211712639335526979670771458251622188461 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((107835997232065897977399831129863752621211712639335526979670771458251622188461 : Nat) : Fp) ^ 2 = ((107647080929067738343525460704633213843414790178366076706967300283813568943072 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_240 : Point :=
  .some (x := ((8718136510001795340016406650816398436241492966773881626425334457414292825707 : Nat) : Fp))
    (y := ((47828698862917730813607230394980222348159325738755616817276492989172802309159 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((47828698862917730813607230394980222348159325738755616817276492989172802309159 : Nat) : Fp) ^ 2 = ((8718136510001795340016406650816398436241492966773881626425334457414292825707 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_241 : Point :=
  .some (x := ((106401248484515799960476859862399114279959120497224302323517862298350223656110 : Nat) : Fp))
    (y := ((90554055872943285359562789441845937705225388396376669909302342738611517756544 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((90554055872943285359562789441845937705225388396376669909302342738611517756544 : Nat) : Fp) ^ 2 = ((106401248484515799960476859862399114279959120497224302323517862298350223656110 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_242 : Point :=
  .some (x := ((85914087585702408016005337307470673574025858586827994345031653897824524412368 : Nat) : Fp))
    (y := ((29212277550782883303312106838911213847133545583225907622635973696278860332923 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29212277550782883303312106838911213847133545583225907622635973696278860332923 : Nat) : Fp) ^ 2 = ((85914087585702408016005337307470673574025858586827994345031653897824524412368 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_243 : Point :=
  .some (x := ((47276261486337148374827016504378500997420604221918318826137905934201132672881 : Nat) : Fp))
    (y := ((54113652565211585717578927649047183887090734340027236246806164434159486622390 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((54113652565211585717578927649047183887090734340027236246806164434159486622390 : Nat) : Fp) ^ 2 = ((47276261486337148374827016504378500997420604221918318826137905934201132672881 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_244 : Point :=
  .some (x := ((85166652415091435001797631336388904339331836647982294920464378555175360787302 : Nat) : Fp))
    (y := ((5983439944161437184729068253379966091033304045142912300433002697874386924481 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((5983439944161437184729068253379966091033304045142912300433002697874386924481 : Nat) : Fp) ^ 2 = ((85166652415091435001797631336388904339331836647982294920464378555175360787302 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_245 : Point :=
  .some (x := ((98723003287129746819861849635856388307092482938644489660108201582085516618521 : Nat) : Fp))
    (y := ((103397407405374187698982141346926700394890519747915912573020442958629189307492 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((103397407405374187698982141346926700394890519747915912573020442958629189307492 : Nat) : Fp) ^ 2 = ((98723003287129746819861849635856388307092482938644489660108201582085516618521 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_246 : Point :=
  .some (x := ((1410924839106319455438998906475131322254088508411264224845861103682022500650 : Nat) : Fp))
    (y := ((78473624517617731927860216277549078632861074607574001991821266037345967105658 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((78473624517617731927860216277549078632861074607574001991821266037345967105658 : Nat) : Fp) ^ 2 = ((1410924839106319455438998906475131322254088508411264224845861103682022500650 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_247 : Point :=
  .some (x := ((76680320804797823168246424599385182501909051371397652720933062691171176057014 : Nat) : Fp))
    (y := ((94762424439059506170177300542547484894285259654945103834474381188217886845725 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((94762424439059506170177300542547484894285259654945103834474381188217886845725 : Nat) : Fp) ^ 2 = ((76680320804797823168246424599385182501909051371397652720933062691171176057014 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_248 : Point :=
  .some (x := ((63395642421589016740518975608504846303065672135176650115036476193363423546538 : Nat) : Fp))
    (y := ((29236048674093813394523910922582374630829081423043497254162533033164154049666 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29236048674093813394523910922582374630829081423043497254162533033164154049666 : Nat) : Fp) ^ 2 = ((63395642421589016740518975608504846303065672135176650115036476193363423546538 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_249 : Point :=
  .some (x := ((77392770812506936202877798844009338869624245327085260572871517211271361583330 : Nat) : Fp))
    (y := ((9026183085953335931861042123363330152002153911485343327487109499224702177627 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((9026183085953335931861042123363330152002153911485343327487109499224702177627 : Nat) : Fp) ^ 2 = ((77392770812506936202877798844009338869624245327085260572871517211271361583330 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_250 : Point :=
  .some (x := ((16914017336104237881775315886787930831164045006039241266138286261112962921466 : Nat) : Fp))
    (y := ((62804288124927804794141542013461961167839995408257184926209413592463329006125 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((62804288124927804794141542013461961167839995408257184926209413592463329006125 : Nat) : Fp) ^ 2 = ((16914017336104237881775315886787930831164045006039241266138286261112962921466 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_251 : Point :=
  .some (x := ((115448225011842706572960659933294318341945799523635471708109888288281266225256 : Nat) : Fp))
    (y := ((8682685012247630765815268889801361118442695513083738308010936359908165836919 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((8682685012247630765815268889801361118442695513083738308010936359908165836919 : Nat) : Fp) ^ 2 = ((115448225011842706572960659933294318341945799523635471708109888288281266225256 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_252 : Point :=
  .some (x := ((4032983015753143990395647783770666587927265353624430905763286836981504199392 : Nat) : Fp))
    (y := ((44353125519324157186344456159742269880631179110473143840214086765587351124293 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((44353125519324157186344456159742269880631179110473143840214086765587351124293 : Nat) : Fp) ^ 2 = ((4032983015753143990395647783770666587927265353624430905763286836981504199392 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_253 : Point :=
  .some (x := ((87917229428110789366561422587307072970088695150214603900351294636804298290738 : Nat) : Fp))
    (y := ((37579621872809717799779570009674914438024800886176540314162770583770981830863 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((37579621872809717799779570009674914438024800886176540314162770583770981830863 : Nat) : Fp) ^ 2 = ((87917229428110789366561422587307072970088695150214603900351294636804298290738 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_254 : Point :=
  .some (x := ((19277281477197177963613685635111727513957886411799201238917757645493897712993 : Nat) : Fp))
    (y := ((847959926674921704613916930352312808004252888284294958523157455244708242291 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((847959926674921704613916930352312808004252888284294958523157455244708242291 : Nat) : Fp) ^ 2 = ((19277281477197177963613685635111727513957886411799201238917757645493897712993 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def base_255 : Point :=
  .some (x := ((80609861913912564376813326121470687649554127203741395941834419933864230904708 : Nat) : Fp))
    (y := ((114172617133077519546499241751011876596863476376685168252563264143225481955342 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((114172617133077519546499241751011876596863476376685168252563264143225481955342 : Nat) : Fp) ^ 2 = ((80609861913912564376813326121470687649554127203741395941834419933864230904708 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)

private def acc_7 : Point :=
  .some (x := ((11045059572793568563399009827450521654436229950346969273826455203229685425899 : Nat) : Fp))
    (y := ((26950030226550877209429637342197821712469081306958210747276495411981785794699 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((26950030226550877209429637342197821712469081306958210747276495411981785794699 : Nat) : Fp) ^ 2 = ((11045059572793568563399009827450521654436229950346969273826455203229685425899 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_9 : Point :=
  .some (x := ((62993874516558554105998507783025790934389611786421029894195191716181730180203 : Nat) : Fp))
    (y := ((103084015873580191872113386278634009007605873809987838839171888914212736480525 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((103084015873580191872113386278634009007605873809987838839171888914212736480525 : Nat) : Fp) ^ 2 = ((62993874516558554105998507783025790934389611786421029894195191716181730180203 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_15 : Point :=
  .some (x := ((94913787221764930918395305492653186337662262006421321283318132192378151570664 : Nat) : Fp))
    (y := ((38121777075044651756879505076685935625833052072522374266672280044016621196774 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((38121777075044651756879505076685935625833052072522374266672280044016621196774 : Nat) : Fp) ^ 2 = ((94913787221764930918395305492653186337662262006421321283318132192378151570664 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_18 : Point :=
  .some (x := ((29143731705339141020573143536865033240207337756459069554333709854927801226474 : Nat) : Fp))
    (y := ((111697187642339357432029595148178850493560050683050466215971168162100425174313 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((111697187642339357432029595148178850493560050683050466215971168162100425174313 : Nat) : Fp) ^ 2 = ((29143731705339141020573143536865033240207337756459069554333709854927801226474 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_19 : Point :=
  .some (x := ((90849555490501463584933875627311483322534276480368275854037302915980746150944 : Nat) : Fp))
    (y := ((29046469570949835964838041207714827657784607995221101405901654271395799837763 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29046469570949835964838041207714827657784607995221101405901654271395799837763 : Nat) : Fp) ^ 2 = ((90849555490501463584933875627311483322534276480368275854037302915980746150944 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_21 : Point :=
  .some (x := ((89477026208564161510117767278811649609638282443724716428920033606201704315067 : Nat) : Fp))
    (y := ((88853493507276595671235274390746320249613099765923277334937217813846588180570 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((88853493507276595671235274390746320249613099765923277334937217813846588180570 : Nat) : Fp) ^ 2 = ((89477026208564161510117767278811649609638282443724716428920033606201704315067 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_22 : Point :=
  .some (x := ((105117500916977773616594155617683380201243349076787575587894204199931887461275 : Nat) : Fp))
    (y := ((104345613394280605290885993209698592187710647825197983914950071252490822507998 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((104345613394280605290885993209698592187710647825197983914950071252490822507998 : Nat) : Fp) ^ 2 = ((105117500916977773616594155617683380201243349076787575587894204199931887461275 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_29 : Point :=
  .some (x := ((33783762117358464705901306764751882743375394820654715821356128391667619714744 : Nat) : Fp))
    (y := ((32404131728136409619522464330118803716746429756002833513611357845302147708073 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((32404131728136409619522464330118803716746429756002833513611357845302147708073 : Nat) : Fp) ^ 2 = ((33783762117358464705901306764751882743375394820654715821356128391667619714744 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_31 : Point :=
  .some (x := ((65690204794470308527683968204692797115282228827141914913431062282090561707752 : Nat) : Fp))
    (y := ((75448620086351013552061125930670315246457098204871965775672739415283009585325 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((75448620086351013552061125930670315246457098204871965775672739415283009585325 : Nat) : Fp) ^ 2 = ((65690204794470308527683968204692797115282228827141914913431062282090561707752 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_32 : Point :=
  .some (x := ((41618715794919262343288247885775468705279947972537888270396336879835196892309 : Nat) : Fp))
    (y := ((94880314162588594310192561282903645520579166239361797117295241397497651873235 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((94880314162588594310192561282903645520579166239361797117295241397497651873235 : Nat) : Fp) ^ 2 = ((41618715794919262343288247885775468705279947972537888270396336879835196892309 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_35 : Point :=
  .some (x := ((26987509267674617032564560708794887116074759337281694404645619351738152609835 : Nat) : Fp))
    (y := ((75919703103009890628426411441223875383582131523107608400144934424085198612963 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((75919703103009890628426411441223875383582131523107608400144934424085198612963 : Nat) : Fp) ^ 2 = ((26987509267674617032564560708794887116074759337281694404645619351738152609835 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_36 : Point :=
  .some (x := ((90670167833274761944578800724498188827088614564367350696785506786556880665943 : Nat) : Fp))
    (y := ((92990610626764881785930818553425290442648685967372451588092631477369184864589 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((92990610626764881785930818553425290442648685967372451588092631477369184864589 : Nat) : Fp) ^ 2 = ((90670167833274761944578800724498188827088614564367350696785506786556880665943 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_40 : Point :=
  .some (x := ((81516270644508254972885744636153652471500891511912876378582865082758736795477 : Nat) : Fp))
    (y := ((51497795809475827504543371761538304658868233203581897281135587160038189000212 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((51497795809475827504543371761538304658868233203581897281135587160038189000212 : Nat) : Fp) ^ 2 = ((81516270644508254972885744636153652471500891511912876378582865082758736795477 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_42 : Point :=
  .some (x := ((60071965084468911187377148037867676523542376580279561249395160962599431041583 : Nat) : Fp))
    (y := ((15021233916647288615784431109881913332014746487622185207833962415666153199931 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((15021233916647288615784431109881913332014746487622185207833962415666153199931 : Nat) : Fp) ^ 2 = ((60071965084468911187377148037867676523542376580279561249395160962599431041583 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_43 : Point :=
  .some (x := ((70461669509128515110401879623799383994591745881104094861864290047217329804875 : Nat) : Fp))
    (y := ((99332552862914231749676062877933518980284997959302517586808703067604814057410 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((99332552862914231749676062877933518980284997959302517586808703067604814057410 : Nat) : Fp) ^ 2 = ((70461669509128515110401879623799383994591745881104094861864290047217329804875 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_44 : Point :=
  .some (x := ((81655338892537041067055604246338288373085611726097761412397446724784214369483 : Nat) : Fp))
    (y := ((93266534087033745023988495465402405148099926109400993024740279485995506407024 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((93266534087033745023988495465402405148099926109400993024740279485995506407024 : Nat) : Fp) ^ 2 = ((81655338892537041067055604246338288373085611726097761412397446724784214369483 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_45 : Point :=
  .some (x := ((68259249210418618144302303847781214325835610307148491130815063758657141614627 : Nat) : Fp))
    (y := ((102041891974531286183934237528263240247246056290551400958728294224355785772557 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((102041891974531286183934237528263240247246056290551400958728294224355785772557 : Nat) : Fp) ^ 2 = ((68259249210418618144302303847781214325835610307148491130815063758657141614627 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_47 : Point :=
  .some (x := ((27762703325796909550034319905135946240294058406315182939056603236183625351842 : Nat) : Fp))
    (y := ((113667738956118784507605894520552320882824051857489728508054634122524566371753 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((113667738956118784507605894520552320882824051857489728508054634122524566371753 : Nat) : Fp) ^ 2 = ((27762703325796909550034319905135946240294058406315182939056603236183625351842 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_50 : Point :=
  .some (x := ((99194189383376580806912732530734056588783061829478900752337249255154902255827 : Nat) : Fp))
    (y := ((64410542444570483028642601756679525395304606757644810636651682692111442763257 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((64410542444570483028642601756679525395304606757644810636651682692111442763257 : Nat) : Fp) ^ 2 = ((99194189383376580806912732530734056588783061829478900752337249255154902255827 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_53 : Point :=
  .some (x := ((69187203649075496263558380068530805903295971191518681710653387161368690281111 : Nat) : Fp))
    (y := ((48135635028035215701050676285431063073492846547677592419510785277659689312666 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((48135635028035215701050676285431063073492846547677592419510785277659689312666 : Nat) : Fp) ^ 2 = ((69187203649075496263558380068530805903295971191518681710653387161368690281111 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_55 : Point :=
  .some (x := ((15223848390017212906680881981813393413677039340503028595624541674101902531963 : Nat) : Fp))
    (y := ((44570955422994050652917840013847722326766360134107318890754453693128309568571 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((44570955422994050652917840013847722326766360134107318890754453693128309568571 : Nat) : Fp) ^ 2 = ((15223848390017212906680881981813393413677039340503028595624541674101902531963 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_56 : Point :=
  .some (x := ((57185860723879935035866354173246676411942596839444195638204647215815346768112 : Nat) : Fp))
    (y := ((60630120880092665311664887862527641786255659590941702157532952227297429492176 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((60630120880092665311664887862527641786255659590941702157532952227297429492176 : Nat) : Fp) ^ 2 = ((57185860723879935035866354173246676411942596839444195638204647215815346768112 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_57 : Point :=
  .some (x := ((23118118866888655613556245973026645805119182871186618924392625013176520610465 : Nat) : Fp))
    (y := ((112895022531704548229105724991974270871908201019764926972499615184558433677379 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((112895022531704548229105724991974270871908201019764926972499615184558433677379 : Nat) : Fp) ^ 2 = ((23118118866888655613556245973026645805119182871186618924392625013176520610465 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_58 : Point :=
  .some (x := ((109268062965302509751249725782841497693627030916462198496686435014212514468944 : Nat) : Fp))
    (y := ((40453008757637546467101231051844287890930702141121285841762042464934598901656 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((40453008757637546467101231051844287890930702141121285841762042464934598901656 : Nat) : Fp) ^ 2 = ((109268062965302509751249725782841497693627030916462198496686435014212514468944 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_59 : Point :=
  .some (x := ((8009867505253292627563618294460798837052598759293890721633944836155070435023 : Nat) : Fp))
    (y := ((8372182007924405609622237583407674428319300964422536250658257680576144314550 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((8372182007924405609622237583407674428319300964422536250658257680576144314550 : Nat) : Fp) ^ 2 = ((8009867505253292627563618294460798837052598759293890721633944836155070435023 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_60 : Point :=
  .some (x := ((37038459036163776514058476381271657069201060930499270675974535267129853015692 : Nat) : Fp))
    (y := ((21077090730298895164245456409466535377554118971536318822444928562424897505234 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((21077090730298895164245456409466535377554118971536318822444928562424897505234 : Nat) : Fp) ^ 2 = ((37038459036163776514058476381271657069201060930499270675974535267129853015692 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_61 : Point :=
  .some (x := ((75749617177574834102149252734770805170663915898998128466674389318315036187752 : Nat) : Fp))
    (y := ((65260251076370058199083669522406252185050335530299045257879839385447656973127 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((65260251076370058199083669522406252185050335530299045257879839385447656973127 : Nat) : Fp) ^ 2 = ((75749617177574834102149252734770805170663915898998128466674389318315036187752 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_62 : Point :=
  .some (x := ((26961910731381032139552785280349446080688665026897053639184453099671199281653 : Nat) : Fp))
    (y := ((19225901277119210270526234788013057702748968868411355964598338166574146506549 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((19225901277119210270526234788013057702748968868411355964598338166574146506549 : Nat) : Fp) ^ 2 = ((26961910731381032139552785280349446080688665026897053639184453099671199281653 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_64 : Point :=
  .some (x := ((60136517557012337886219143441347989931997721743090658581626858228326433472322 : Nat) : Fp))
    (y := ((36561241511934786181747000543741354953016942877030566678373432424712287474694 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((36561241511934786181747000543741354953016942877030566678373432424712287474694 : Nat) : Fp) ^ 2 = ((60136517557012337886219143441347989931997721743090658581626858228326433472322 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_65 : Point :=
  .some (x := ((86189600100549013261218396657850864219874730265296776543117159178463788186174 : Nat) : Fp))
    (y := ((90959855302219868837933088822377621275611973567245607971627311097343894919839 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((90959855302219868837933088822377621275611973567245607971627311097343894919839 : Nat) : Fp) ^ 2 = ((86189600100549013261218396657850864219874730265296776543117159178463788186174 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_66 : Point :=
  .some (x := ((49985759286094074597680466732886939186456207479529083039553970260762539159489 : Nat) : Fp))
    (y := ((110838148757080555347711120133988103797443398676724707733367451071894438037253 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((110838148757080555347711120133988103797443398676724707733367451071894438037253 : Nat) : Fp) ^ 2 = ((49985759286094074597680466732886939186456207479529083039553970260762539159489 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_68 : Point :=
  .some (x := ((6695453148659735962002278213602542997318133052565924704593474838173153106710 : Nat) : Fp))
    (y := ((46485298069974473504580690177384313698277301393718293347306004902936287833429 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((46485298069974473504580690177384313698277301393718293347306004902936287833429 : Nat) : Fp) ^ 2 = ((6695453148659735962002278213602542997318133052565924704593474838173153106710 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_69 : Point :=
  .some (x := ((104426448526774961863592430878135482344898700069802556168947359175483153349152 : Nat) : Fp))
    (y := ((70451996996368836093976516871864366361017094170088744097262044823768267276698 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((70451996996368836093976516871864366361017094170088744097262044823768267276698 : Nat) : Fp) ^ 2 = ((104426448526774961863592430878135482344898700069802556168947359175483153349152 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_70 : Point :=
  .some (x := ((25706115431223231104349502338425676760948233609524549927682567987735767988359 : Nat) : Fp))
    (y := ((86030344383075434546407535965820914874011898795760114264794801526033406629855 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((86030344383075434546407535965820914874011898795760114264794801526033406629855 : Nat) : Fp) ^ 2 = ((25706115431223231104349502338425676760948233609524549927682567987735767988359 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_78 : Point :=
  .some (x := ((73125825156308139294675747886866421016441910230119720499669894621285502251079 : Nat) : Fp))
    (y := ((19888432106953872326075255198634055088926467183450751775018780927964758097378 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((19888432106953872326075255198634055088926467183450751775018780927964758097378 : Nat) : Fp) ^ 2 = ((73125825156308139294675747886866421016441910230119720499669894621285502251079 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_80 : Point :=
  .some (x := ((3799410324969024133081081695082414846245373966520493209198350038600691536914 : Nat) : Fp))
    (y := ((64590755570687246173876293161993570922670019950127150336867014279037138113218 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((64590755570687246173876293161993570922670019950127150336867014279037138113218 : Nat) : Fp) ^ 2 = ((3799410324969024133081081695082414846245373966520493209198350038600691536914 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_84 : Point :=
  .some (x := ((36481107058847661184720422216126033568491719697437610972538970425171464994134 : Nat) : Fp))
    (y := ((59375892896459583478283107209861739188594974709872699287649203685554258936156 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((59375892896459583478283107209861739188594974709872699287649203685554258936156 : Nat) : Fp) ^ 2 = ((36481107058847661184720422216126033568491719697437610972538970425171464994134 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_87 : Point :=
  .some (x := ((39167433951545998662469544307046456080123148394186949127521342155774454045112 : Nat) : Fp))
    (y := ((30298408788746136852882903631010855906662855042173128674647864287464037353913 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((30298408788746136852882903631010855906662855042173128674647864287464037353913 : Nat) : Fp) ^ 2 = ((39167433951545998662469544307046456080123148394186949127521342155774454045112 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_89 : Point :=
  .some (x := ((47721097417240342851575869518307123551954077459667301577181113199159910028448 : Nat) : Fp))
    (y := ((52658075691142254803030327010985865064719216595411720435801443495674009399093 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((52658075691142254803030327010985865064719216595411720435801443495674009399093 : Nat) : Fp) ^ 2 = ((47721097417240342851575869518307123551954077459667301577181113199159910028448 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_90 : Point :=
  .some (x := ((5974904400430543259455560848409761135828404883755769475812545840798994420626 : Nat) : Fp))
    (y := ((102402017295650327470724168950542695526850430255659426106274860509810802780367 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((102402017295650327470724168950542695526850430255659426106274860509810802780367 : Nat) : Fp) ^ 2 = ((5974904400430543259455560848409761135828404883755769475812545840798994420626 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_91 : Point :=
  .some (x := ((5509577011086727080997845992373093152769990707708497256037145900212757718763 : Nat) : Fp))
    (y := ((33437607306713300453742465290808031932224959267266785803236743457017283421378 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((33437607306713300453742465290808031932224959267266785803236743457017283421378 : Nat) : Fp) ^ 2 = ((5509577011086727080997845992373093152769990707708497256037145900212757718763 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_92 : Point :=
  .some (x := ((81498813144553065193277101791088765223666465594788231317695429763494990800161 : Nat) : Fp))
    (y := ((102578830382552685677753812882205076681221589676210636107665700206153835720334 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((102578830382552685677753812882205076681221589676210636107665700206153835720334 : Nat) : Fp) ^ 2 = ((81498813144553065193277101791088765223666465594788231317695429763494990800161 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_94 : Point :=
  .some (x := ((82882321221271994761165685376483487612453422273385368815479594044555354887913 : Nat) : Fp))
    (y := ((35894132640904045101881577472630543914061150570585350050149732598924420865433 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((35894132640904045101881577472630543914061150570585350050149732598924420865433 : Nat) : Fp) ^ 2 = ((82882321221271994761165685376483487612453422273385368815479594044555354887913 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_96 : Point :=
  .some (x := ((85822199919418065873158677931932224637840315064394798344509210798366262760486 : Nat) : Fp))
    (y := ((47043993167359473997990137877132683987732339713702799210771155580442464319499 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((47043993167359473997990137877132683987732339713702799210771155580442464319499 : Nat) : Fp) ^ 2 = ((85822199919418065873158677931932224637840315064394798344509210798366262760486 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_98 : Point :=
  .some (x := ((36018791698582241120782688987973347775778125434698149796719209811558341468509 : Nat) : Fp))
    (y := ((96602876010518921436011014945987442948354913803632054205250383396029141753974 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((96602876010518921436011014945987442948354913803632054205250383396029141753974 : Nat) : Fp) ^ 2 = ((36018791698582241120782688987973347775778125434698149796719209811558341468509 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_99 : Point :=
  .some (x := ((41111154781556033377440121874077527421315943697062380855736502909096841867206 : Nat) : Fp))
    (y := ((19896192142047753665974087407183447002805652795370305833366361894451278502736 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((19896192142047753665974087407183447002805652795370305833366361894451278502736 : Nat) : Fp) ^ 2 = ((41111154781556033377440121874077527421315943697062380855736502909096841867206 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_102 : Point :=
  .some (x := ((70107473280607648069001123872136195111137548018812398968844687706317006207302 : Nat) : Fp))
    (y := ((61064251065141043117034600730541076400344949438238427304395638523020478236934 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((61064251065141043117034600730541076400344949438238427304395638523020478236934 : Nat) : Fp) ^ 2 = ((70107473280607648069001123872136195111137548018812398968844687706317006207302 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_103 : Point :=
  .some (x := ((102080125537512830561429134257341642762801162083249309315826629272439682303930 : Nat) : Fp))
    (y := ((107247405574961466334473303157787794781972237839054603619594180612693970753467 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((107247405574961466334473303157787794781972237839054603619594180612693970753467 : Nat) : Fp) ^ 2 = ((102080125537512830561429134257341642762801162083249309315826629272439682303930 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_104 : Point :=
  .some (x := ((94368376047009421717855463218318015560972492266809599892431797191812862745821 : Nat) : Fp))
    (y := ((67580342042135832441154392154495076586749938607000332644247005057394429881399 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((67580342042135832441154392154495076586749938607000332644247005057394429881399 : Nat) : Fp) ^ 2 = ((94368376047009421717855463218318015560972492266809599892431797191812862745821 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_107 : Point :=
  .some (x := ((10321650696684694424956901291088654816318080924060828571726835953248311385544 : Nat) : Fp))
    (y := ((72708667601984235170927616181641316600362066063903614191606698601692852015347 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((72708667601984235170927616181641316600362066063903614191606698601692852015347 : Nat) : Fp) ^ 2 = ((10321650696684694424956901291088654816318080924060828571726835953248311385544 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_108 : Point :=
  .some (x := ((110885102143344023004297714671567539084344995277262228798154482989829145471921 : Nat) : Fp))
    (y := ((48792966665433983021832836713700470855228821505406247609557161866405336250215 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((48792966665433983021832836713700470855228821505406247609557161866405336250215 : Nat) : Fp) ^ 2 = ((110885102143344023004297714671567539084344995277262228798154482989829145471921 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_109 : Point :=
  .some (x := ((688280669162989546390772776013627019489387407390641084214463900619024372191 : Nat) : Fp))
    (y := ((31019324467414918607770553953778668153444018624350943437811339340649051573402 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((31019324467414918607770553953778668153444018624350943437811339340649051573402 : Nat) : Fp) ^ 2 = ((688280669162989546390772776013627019489387407390641084214463900619024372191 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_111 : Point :=
  .some (x := ((55569353933861153981007938645731919034676101358716740918948668607947783287783 : Nat) : Fp))
    (y := ((102772542859727198188668425842571602963864943512156450408760577499799524206224 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((102772542859727198188668425842571602963864943512156450408760577499799524206224 : Nat) : Fp) ^ 2 = ((55569353933861153981007938645731919034676101358716740918948668607947783287783 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_112 : Point :=
  .some (x := ((69583153015791561848491236522420332279446720326520150735477129200128611100578 : Nat) : Fp))
    (y := ((54442876088266950041552228116867279466264916861574397804557819670187343850859 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((54442876088266950041552228116867279466264916861574397804557819670187343850859 : Nat) : Fp) ^ 2 = ((69583153015791561848491236522420332279446720326520150735477129200128611100578 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_114 : Point :=
  .some (x := ((19633159299856099907314563658736240791444294953890097332202432654822417141512 : Nat) : Fp))
    (y := ((67740373626039556911284018287362258285447810095435817077894444978733560769037 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((67740373626039556911284018287362258285447810095435817077894444978733560769037 : Nat) : Fp) ^ 2 = ((19633159299856099907314563658736240791444294953890097332202432654822417141512 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_115 : Point :=
  .some (x := ((16646694601055444161462789274198939361644158325658382956372688880992905138311 : Nat) : Fp))
    (y := ((43713514400941308126797661227140820790297978254636241027532509696601361643237 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((43713514400941308126797661227140820790297978254636241027532509696601361643237 : Nat) : Fp) ^ 2 = ((16646694601055444161462789274198939361644158325658382956372688880992905138311 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_116 : Point :=
  .some (x := ((57101222887932246968439371290112973346171902219944257147746332672280620593970 : Nat) : Fp))
    (y := ((22011996830761967843679676119411463408358998855302182680085434858533095036583 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((22011996830761967843679676119411463408358998855302182680085434858533095036583 : Nat) : Fp) ^ 2 = ((57101222887932246968439371290112973346171902219944257147746332672280620593970 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_118 : Point :=
  .some (x := ((95944886742557707932362876789624879591893495467445214359084245806917774340757 : Nat) : Fp))
    (y := ((110751044278523775594571320869660721200928379381841027764964231195772728276770 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((110751044278523775594571320869660721200928379381841027764964231195772728276770 : Nat) : Fp) ^ 2 = ((95944886742557707932362876789624879591893495467445214359084245806917774340757 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_120 : Point :=
  .some (x := ((54167007267059197045221945990254946807947280925068536125576886778329475540076 : Nat) : Fp))
    (y := ((72055959636406295061054909626683074948993352707213006551507980813796168229048 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((72055959636406295061054909626683074948993352707213006551507980813796168229048 : Nat) : Fp) ^ 2 = ((54167007267059197045221945990254946807947280925068536125576886778329475540076 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_122 : Point :=
  .some (x := ((98860079765909358796142953988580893109144029840399878081833223424758478366643 : Nat) : Fp))
    (y := ((42863448657478433777088560299070653878760991519406980060740899145649261852062 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((42863448657478433777088560299070653878760991519406980060740899145649261852062 : Nat) : Fp) ^ 2 = ((98860079765909358796142953988580893109144029840399878081833223424758478366643 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_124 : Point :=
  .some (x := ((42048476443960000607055303567932611428047936177544484184308593834997252715145 : Nat) : Fp))
    (y := ((73466656252853239349742406038788760723553339994741973797631739173712191992133 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((73466656252853239349742406038788760723553339994741973797631739173712191992133 : Nat) : Fp) ^ 2 = ((42048476443960000607055303567932611428047936177544484184308593834997252715145 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_125 : Point :=
  .some (x := ((40808566356087706713890706648386103099378437079371712127830451490467855389508 : Nat) : Fp))
    (y := ((105414085726370355741499668926251975606631447663687793963451501913713607085511 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((105414085726370355741499668926251975606631447663687793963451501913713607085511 : Nat) : Fp) ^ 2 = ((40808566356087706713890706648386103099378437079371712127830451490467855389508 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_126 : Point :=
  .some (x := ((56288351935501938235309378627037995070659666184532694594320684497895417783803 : Nat) : Fp))
    (y := ((87057618380663887317286822613056874715224314213166279024992080230242765618114 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((87057618380663887317286822613056874715224314213166279024992080230242765618114 : Nat) : Fp) ^ 2 = ((56288351935501938235309378627037995070659666184532694594320684497895417783803 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_128 : Point :=
  .some (x := ((32256737403791914686372586254330362595305275169830061794707745295581356675058 : Nat) : Fp))
    (y := ((81527510300654142997208084696556813307392657339414968740384212117171109925658 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((81527510300654142997208084696556813307392657339414968740384212117171109925658 : Nat) : Fp) ^ 2 = ((32256737403791914686372586254330362595305275169830061794707745295581356675058 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_130 : Point :=
  .some (x := ((91741821106593624285097037099343471848474224858941232879131869967755051054218 : Nat) : Fp))
    (y := ((71021452885563151057532052504329181705099633460022030837729546140481449972497 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((71021452885563151057532052504329181705099633460022030837729546140481449972497 : Nat) : Fp) ^ 2 = ((91741821106593624285097037099343471848474224858941232879131869967755051054218 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_131 : Point :=
  .some (x := ((876047637419442076877020655258504368469881489828225470144032574576745391356 : Nat) : Fp))
    (y := ((54113812953787505085983237446334027288636341582549712045131730722239023266017 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((54113812953787505085983237446334027288636341582549712045131730722239023266017 : Nat) : Fp) ^ 2 = ((876047637419442076877020655258504368469881489828225470144032574576745391356 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_132 : Point :=
  .some (x := ((41292388911594828841688755398275203008656246181806000113850535655350608353168 : Nat) : Fp))
    (y := ((68146070699127177379784201658310604544291547352561072875698030897747232922273 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((68146070699127177379784201658310604544291547352561072875698030897747232922273 : Nat) : Fp) ^ 2 = ((41292388911594828841688755398275203008656246181806000113850535655350608353168 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_133 : Point :=
  .some (x := ((56815726206465773808453127650822173850241926431943623033908133580612678261480 : Nat) : Fp))
    (y := ((86962078245404183196586729986131155699056121032963089479802907931919241014479 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((86962078245404183196586729986131155699056121032963089479802907931919241014479 : Nat) : Fp) ^ 2 = ((56815726206465773808453127650822173850241926431943623033908133580612678261480 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_134 : Point :=
  .some (x := ((23220893035889910636946805781344549261675078085456573395822142317137928410713 : Nat) : Fp))
    (y := ((57621796455599442197045009877404664212419187530914025935630953433489442579002 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((57621796455599442197045009877404664212419187530914025935630953433489442579002 : Nat) : Fp) ^ 2 = ((23220893035889910636946805781344549261675078085456573395822142317137928410713 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_135 : Point :=
  .some (x := ((14986505511071864390751319822613268135838572187452595128300726684100967021470 : Nat) : Fp))
    (y := ((62020730481804803719561524049800312807387460099630443501595035287525063798994 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((62020730481804803719561524049800312807387460099630443501595035287525063798994 : Nat) : Fp) ^ 2 = ((14986505511071864390751319822613268135838572187452595128300726684100967021470 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_136 : Point :=
  .some (x := ((83640465507401686462263533627622564812678268326224187181898793301565321681751 : Nat) : Fp))
    (y := ((109134439146168824131351559614623953197395257566233961730867948095783758407139 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((109134439146168824131351559614623953197395257566233961730867948095783758407139 : Nat) : Fp) ^ 2 = ((83640465507401686462263533627622564812678268326224187181898793301565321681751 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_137 : Point :=
  .some (x := ((86130755921611212044147249845724329580220518801808515059278645831102457009272 : Nat) : Fp))
    (y := ((30084020417228989210253053606261698950888669025890702731303978496996225598027 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((30084020417228989210253053606261698950888669025890702731303978496996225598027 : Nat) : Fp) ^ 2 = ((86130755921611212044147249845724329580220518801808515059278645831102457009272 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_138 : Point :=
  .some (x := ((75330202358275438652442019080086978139032819196890473859747676497570155441290 : Nat) : Fp))
    (y := ((88105028260814169772177227500247055218212880147827308418428527652086205925273 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((88105028260814169772177227500247055218212880147827308418428527652086205925273 : Nat) : Fp) ^ 2 = ((75330202358275438652442019080086978139032819196890473859747676497570155441290 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_139 : Point :=
  .some (x := ((71777962321459349406000724597903971388434741523230555797285671830852712859798 : Nat) : Fp))
    (y := ((36201072399255268942103655379331395118704297289411113095502336649664884513361 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((36201072399255268942103655379331395118704297289411113095502336649664884513361 : Nat) : Fp) ^ 2 = ((71777962321459349406000724597903971388434741523230555797285671830852712859798 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_140 : Point :=
  .some (x := ((41533720893661563846206482311205371897195853024687889444099883272216698110652 : Nat) : Fp))
    (y := ((53323290439282793614577378782659314963414058752113829549490197095768979707060 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((53323290439282793614577378782659314963414058752113829549490197095768979707060 : Nat) : Fp) ^ 2 = ((41533720893661563846206482311205371897195853024687889444099883272216698110652 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_141 : Point :=
  .some (x := ((50473025432973961967967320146606874116870403908968619853667703910850312319789 : Nat) : Fp))
    (y := ((105310061754630067182434722915899192641790266983653207826682573597297380908488 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((105310061754630067182434722915899192641790266983653207826682573597297380908488 : Nat) : Fp) ^ 2 = ((50473025432973961967967320146606874116870403908968619853667703910850312319789 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_142 : Point :=
  .some (x := ((87823185991211788184309284762850137952436592112622220988032007483043824662964 : Nat) : Fp))
    (y := ((6688803962140634735988835929090864288812946058955406852694546634055926980527 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((6688803962140634735988835929090864288812946058955406852694546634055926980527 : Nat) : Fp) ^ 2 = ((87823185991211788184309284762850137952436592112622220988032007483043824662964 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_143 : Point :=
  .some (x := ((90163261311683285674689513851666750706603686918501102041262299506509314620988 : Nat) : Fp))
    (y := ((74509803696176320985942317025510241902577779179603758824099703837492750765214 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((74509803696176320985942317025510241902577779179603758824099703837492750765214 : Nat) : Fp) ^ 2 = ((90163261311683285674689513851666750706603686918501102041262299506509314620988 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_144 : Point :=
  .some (x := ((22551397232250930154134754775306783641591530410463695625277699798220437219399 : Nat) : Fp))
    (y := ((22300401800434807498397191466715504535300228199893767604777531771471628865102 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((22300401800434807498397191466715504535300228199893767604777531771471628865102 : Nat) : Fp) ^ 2 = ((22551397232250930154134754775306783641591530410463695625277699798220437219399 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_145 : Point :=
  .some (x := ((100298860435074318269866579939242844366430460264739520744523048625540766996065 : Nat) : Fp))
    (y := ((88513182605632356692522405523131199235045673808811896300895425364158937594489 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((88513182605632356692522405523131199235045673808811896300895425364158937594489 : Nat) : Fp) ^ 2 = ((100298860435074318269866579939242844366430460264739520744523048625540766996065 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_146 : Point :=
  .some (x := ((17848721041874530924046462006098247088013963003544838587581308688097280151280 : Nat) : Fp))
    (y := ((34159256826805232052241494313207328573695354171728960295235024566835808034037 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((34159256826805232052241494313207328573695354171728960295235024566835808034037 : Nat) : Fp) ^ 2 = ((17848721041874530924046462006098247088013963003544838587581308688097280151280 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_147 : Point :=
  .some (x := ((45623407705562943711880395222077400353581483244328863799912097202000040865402 : Nat) : Fp))
    (y := ((107316396356635083049318973698309037298632105785368871779441596235125246650583 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((107316396356635083049318973698309037298632105785368871779441596235125246650583 : Nat) : Fp) ^ 2 = ((45623407705562943711880395222077400353581483244328863799912097202000040865402 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_148 : Point :=
  .some (x := ((65611104680918539788679488399408385865507511853104175426681765416774357510107 : Nat) : Fp))
    (y := ((43876206029510945360886303119405145979281675325303827235302129310450908555943 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((43876206029510945360886303119405145979281675325303827235302129310450908555943 : Nat) : Fp) ^ 2 = ((65611104680918539788679488399408385865507511853104175426681765416774357510107 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_149 : Point :=
  .some (x := ((9175530125303015082993852518922959453678574958986082937661837288658019653921 : Nat) : Fp))
    (y := ((81149895401758819099870646032106501065177933443158078516098528446088178744237 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((81149895401758819099870646032106501065177933443158078516098528446088178744237 : Nat) : Fp) ^ 2 = ((9175530125303015082993852518922959453678574958986082937661837288658019653921 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_150 : Point :=
  .some (x := ((99405957026185278736888962341521709440058377180351135776332231411165316932338 : Nat) : Fp))
    (y := ((41073203091423046432494013929436699193927712795365893183454114478036003095264 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((41073203091423046432494013929436699193927712795365893183454114478036003095264 : Nat) : Fp) ^ 2 = ((99405957026185278736888962341521709440058377180351135776332231411165316932338 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_151 : Point :=
  .some (x := ((385323763397091340965387960723257533269278287453460106838431826015871103476 : Nat) : Fp))
    (y := ((39741205680205240979965348861247182832451598649957587788282291616589443536287 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((39741205680205240979965348861247182832451598649957587788282291616589443536287 : Nat) : Fp) ^ 2 = ((385323763397091340965387960723257533269278287453460106838431826015871103476 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_152 : Point :=
  .some (x := ((37913721730568578793482317157181727653930256717449208778212425598522088421245 : Nat) : Fp))
    (y := ((65825222424684364308079047446795845460767465746268132972648661792861124226520 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((65825222424684364308079047446795845460767465746268132972648661792861124226520 : Nat) : Fp) ^ 2 = ((37913721730568578793482317157181727653930256717449208778212425598522088421245 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_153 : Point :=
  .some (x := ((101033778425503574014684099111759490344154621228683854436296107272222670739677 : Nat) : Fp))
    (y := ((42796250005518910873947435274088804650613359832499456467147440966228327442201 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((42796250005518910873947435274088804650613359832499456467147440966228327442201 : Nat) : Fp) ^ 2 = ((101033778425503574014684099111759490344154621228683854436296107272222670739677 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_154 : Point :=
  .some (x := ((62694638710103142966512874778432251245752677992976717721765521316164604626861 : Nat) : Fp))
    (y := ((24095758639911844996771481976405251778358567578312806925735546674890671086736 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((24095758639911844996771481976405251778358567578312806925735546674890671086736 : Nat) : Fp) ^ 2 = ((62694638710103142966512874778432251245752677992976717721765521316164604626861 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_155 : Point :=
  .some (x := ((81413426396105580183786943568605611210297419672204161304267129474314778869714 : Nat) : Fp))
    (y := ((51643406721498035591926987814921009332997171699847023416613139272914924014822 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((51643406721498035591926987814921009332997171699847023416613139272914924014822 : Nat) : Fp) ^ 2 = ((81413426396105580183786943568605611210297419672204161304267129474314778869714 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_156 : Point :=
  .some (x := ((21064159776649894241607833220796825188513353040509085695513938191477550484029 : Nat) : Fp))
    (y := ((15846066697264671155349699086334552093749382433758902315880203622950896270571 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((15846066697264671155349699086334552093749382433758902315880203622950896270571 : Nat) : Fp) ^ 2 = ((21064159776649894241607833220796825188513353040509085695513938191477550484029 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_157 : Point :=
  .some (x := ((8067130280375955498155270582300992518528567789421409511369299258617075631199 : Nat) : Fp))
    (y := ((28402050314672328579154242697337517867912453266071606258953688577151710859568 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((28402050314672328579154242697337517867912453266071606258953688577151710859568 : Nat) : Fp) ^ 2 = ((8067130280375955498155270582300992518528567789421409511369299258617075631199 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_158 : Point :=
  .some (x := ((45761152285074963888706750847007678101194029126391568292164862834287743236260 : Nat) : Fp))
    (y := ((9666512234623561881627866384222152217805821208798249635499112356546692877079 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((9666512234623561881627866384222152217805821208798249635499112356546692877079 : Nat) : Fp) ^ 2 = ((45761152285074963888706750847007678101194029126391568292164862834287743236260 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_159 : Point :=
  .some (x := ((18560929348648493496902303852929981826943633598245840785444694875193215692174 : Nat) : Fp))
    (y := ((112769562991526566581429180106091770796339008911662367862242582485643366576384 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((112769562991526566581429180106091770796339008911662367862242582485643366576384 : Nat) : Fp) ^ 2 = ((18560929348648493496902303852929981826943633598245840785444694875193215692174 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_160 : Point :=
  .some (x := ((82573376505735398797749460473420703975557479532007200170569724442995876740115 : Nat) : Fp))
    (y := ((39299027964379713774792743053537718647474776468391445360563566742887773271967 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((39299027964379713774792743053537718647474776468391445360563566742887773271967 : Nat) : Fp) ^ 2 = ((82573376505735398797749460473420703975557479532007200170569724442995876740115 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_161 : Point :=
  .some (x := ((50613684197574533383325475395772840295275209808597143405520121315576830549186 : Nat) : Fp))
    (y := ((51805907568463563985607985934819899230192571470607329638432349900267088729081 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((51805907568463563985607985934819899230192571470607329638432349900267088729081 : Nat) : Fp) ^ 2 = ((50613684197574533383325475395772840295275209808597143405520121315576830549186 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_162 : Point :=
  .some (x := ((62248462504263467714584230639972138759161200691249656819712187384075316604332 : Nat) : Fp))
    (y := ((7965997658390101079332281606136996653182077908250494180895408009046119779296 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((7965997658390101079332281606136996653182077908250494180895408009046119779296 : Nat) : Fp) ^ 2 = ((62248462504263467714584230639972138759161200691249656819712187384075316604332 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_163 : Point :=
  .some (x := ((94304331522273496808116349343247115097055453840393084609261207752741124358128 : Nat) : Fp))
    (y := ((31753488936967043696809363174701549528556726880817095842685633602961996585636 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((31753488936967043696809363174701549528556726880817095842685633602961996585636 : Nat) : Fp) ^ 2 = ((94304331522273496808116349343247115097055453840393084609261207752741124358128 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_164 : Point :=
  .some (x := ((114749105857829616057603277433445827949030992454201980219292508691539427079064 : Nat) : Fp))
    (y := ((4476763698178109215061468145393122881130255579336894294178167191581612073296 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((4476763698178109215061468145393122881130255579336894294178167191581612073296 : Nat) : Fp) ^ 2 = ((114749105857829616057603277433445827949030992454201980219292508691539427079064 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_165 : Point :=
  .some (x := ((73156421406644187235081997026000499221545159563463308076613754647691436301708 : Nat) : Fp))
    (y := ((72731185322230603800534659625273863081746753514036875805286803777153280448494 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((72731185322230603800534659625273863081746753514036875805286803777153280448494 : Nat) : Fp) ^ 2 = ((73156421406644187235081997026000499221545159563463308076613754647691436301708 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_166 : Point :=
  .some (x := ((62734468877395534755757165923205128268653264925969806142579124920023589270036 : Nat) : Fp))
    (y := ((59407832839423674474108084154443451585523788883120070401167552875467080655349 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((59407832839423674474108084154443451585523788883120070401167552875467080655349 : Nat) : Fp) ^ 2 = ((62734468877395534755757165923205128268653264925969806142579124920023589270036 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_167 : Point :=
  .some (x := ((112172446824784397943995176919888054471487948449592980499391769875633346581368 : Nat) : Fp))
    (y := ((55859448214441627279579698475192060498900609882065822563585336025129430054846 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((55859448214441627279579698475192060498900609882065822563585336025129430054846 : Nat) : Fp) ^ 2 = ((112172446824784397943995176919888054471487948449592980499391769875633346581368 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_168 : Point :=
  .some (x := ((93912565785139307016161950679622968781046914571229830494986975930576605778711 : Nat) : Fp))
    (y := ((29964694777065420508021296115347598096702416321325475110750515324977580655062 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29964694777065420508021296115347598096702416321325475110750515324977580655062 : Nat) : Fp) ^ 2 = ((93912565785139307016161950679622968781046914571229830494986975930576605778711 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_169 : Point :=
  .some (x := ((35226059335101933311749405272571863457568325597634905831690332789817180515430 : Nat) : Fp))
    (y := ((33384763739153480822164745313988675215284906542338000026214103211366784021762 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((33384763739153480822164745313988675215284906542338000026214103211366784021762 : Nat) : Fp) ^ 2 = ((35226059335101933311749405272571863457568325597634905831690332789817180515430 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_170 : Point :=
  .some (x := ((113149396721675226183785687199223313575294111180927885353779286447025943321527 : Nat) : Fp))
    (y := ((59894430033256809996284190027797713341759201348462922346211113257141828004855 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((59894430033256809996284190027797713341759201348462922346211113257141828004855 : Nat) : Fp) ^ 2 = ((113149396721675226183785687199223313575294111180927885353779286447025943321527 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_171 : Point :=
  .some (x := ((2070204883874586979755513349640918964830615684643216416182655782655758594541 : Nat) : Fp))
    (y := ((85913346119219550608918492453541442982755921573256835284083073987406074747760 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((85913346119219550608918492453541442982755921573256835284083073987406074747760 : Nat) : Fp) ^ 2 = ((2070204883874586979755513349640918964830615684643216416182655782655758594541 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_172 : Point :=
  .some (x := ((29873748141905807058024221897945895150426782627928752455872311607406879110292 : Nat) : Fp))
    (y := ((60314029818254727737267413732752055509495781222255259696456950426078141934717 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((60314029818254727737267413732752055509495781222255259696456950426078141934717 : Nat) : Fp) ^ 2 = ((29873748141905807058024221897945895150426782627928752455872311607406879110292 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_173 : Point :=
  .some (x := ((52711587612775625797697341722512137836488587027913421465260586332499447009502 : Nat) : Fp))
    (y := ((13693183853723932982658988534614564085336030000449643408659872070924800253870 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((13693183853723932982658988534614564085336030000449643408659872070924800253870 : Nat) : Fp) ^ 2 = ((52711587612775625797697341722512137836488587027913421465260586332499447009502 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_174 : Point :=
  .some (x := ((114929085248450553725830617566960843911747044598908522223285933841276842744276 : Nat) : Fp))
    (y := ((87830507935707959954958782318601029278248223436796437882574575498737203188114 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((87830507935707959954958782318601029278248223436796437882574575498737203188114 : Nat) : Fp) ^ 2 = ((114929085248450553725830617566960843911747044598908522223285933841276842744276 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_175 : Point :=
  .some (x := ((42506850229344260533699254673607416329486700005533824580814509045108411872876 : Nat) : Fp))
    (y := ((51402263881715333216875830854680085658510428392897165749394538891132414388550 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((51402263881715333216875830854680085658510428392897165749394538891132414388550 : Nat) : Fp) ^ 2 = ((42506850229344260533699254673607416329486700005533824580814509045108411872876 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_176 : Point :=
  .some (x := ((22688283644905229582878684955816599114744435964831567715612498102492263638185 : Nat) : Fp))
    (y := ((25432323947914688525796610309512452751151618294517290768406018952511473076002 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((25432323947914688525796610309512452751151618294517290768406018952511473076002 : Nat) : Fp) ^ 2 = ((22688283644905229582878684955816599114744435964831567715612498102492263638185 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_177 : Point :=
  .some (x := ((56313531445760181520291524148546735166936497593520315965293404361066917373463 : Nat) : Fp))
    (y := ((7023894789066727864946544612688650223068469975986256496831813544917972514157 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((7023894789066727864946544612688650223068469975986256496831813544917972514157 : Nat) : Fp) ^ 2 = ((56313531445760181520291524148546735166936497593520315965293404361066917373463 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_178 : Point :=
  .some (x := ((61395379527807154589910593530388813956074296196146759454533147536489311870064 : Nat) : Fp))
    (y := ((60982411027170441390433730145619550479056017399567039311076256568038987248209 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((60982411027170441390433730145619550479056017399567039311076256568038987248209 : Nat) : Fp) ^ 2 = ((61395379527807154589910593530388813956074296196146759454533147536489311870064 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_179 : Point :=
  .some (x := ((60602008552774070692677442494729302278814488972178655463377434598891056704362 : Nat) : Fp))
    (y := ((69652999832373287830413259163074242998390147242088075325550673119691028760126 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((69652999832373287830413259163074242998390147242088075325550673119691028760126 : Nat) : Fp) ^ 2 = ((60602008552774070692677442494729302278814488972178655463377434598891056704362 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_180 : Point :=
  .some (x := ((63486259634284010518869700171992398503661545992267646023489026482566456550680 : Nat) : Fp))
    (y := ((68068739873562892420495356343759067810318960198244271889240148296759038135300 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((68068739873562892420495356343759067810318960198244271889240148296759038135300 : Nat) : Fp) ^ 2 = ((63486259634284010518869700171992398503661545992267646023489026482566456550680 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_181 : Point :=
  .some (x := ((54101560700677057488529534741850644660042807169323832715061677300725817542945 : Nat) : Fp))
    (y := ((106168333532991453879971453163277109879803401700822822299742876147761440309986 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((106168333532991453879971453163277109879803401700822822299742876147761440309986 : Nat) : Fp) ^ 2 = ((54101560700677057488529534741850644660042807169323832715061677300725817542945 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_182 : Point :=
  .some (x := ((58803828977889904056958201134416749289453418644284312180892862150470978232871 : Nat) : Fp))
    (y := ((68452637737348940430426184124178236692535050505332233028361893573654271099616 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((68452637737348940430426184124178236692535050505332233028361893573654271099616 : Nat) : Fp) ^ 2 = ((58803828977889904056958201134416749289453418644284312180892862150470978232871 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_183 : Point :=
  .some (x := ((66518931987740708092984178574691790016917337737952891688123449635061325216156 : Nat) : Fp))
    (y := ((63754585599876267609156917378169350991360481042700069865689657451230775548364 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((63754585599876267609156917378169350991360481042700069865689657451230775548364 : Nat) : Fp) ^ 2 = ((66518931987740708092984178574691790016917337737952891688123449635061325216156 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_184 : Point :=
  .some (x := ((114989896324114142582880091593198513170996485363105493920687794509420983332961 : Nat) : Fp))
    (y := ((7481367548924958910439849234132001479707060958931045511835875367415060017631 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((7481367548924958910439849234132001479707060958931045511835875367415060017631 : Nat) : Fp) ^ 2 = ((114989896324114142582880091593198513170996485363105493920687794509420983332961 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_185 : Point :=
  .some (x := ((103027176964090739901348021419433442083819779335333888871571742362270166514167 : Nat) : Fp))
    (y := ((54181323159617956693674588492020250288031145001273986907292449155885602796649 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((54181323159617956693674588492020250288031145001273986907292449155885602796649 : Nat) : Fp) ^ 2 = ((103027176964090739901348021419433442083819779335333888871571742362270166514167 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_186 : Point :=
  .some (x := ((4204695906946780589313791879208530286494667006376374838986876141639449894612 : Nat) : Fp))
    (y := ((104209475553988776387256580368715944301255144328160595977204614846757114076509 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((104209475553988776387256580368715944301255144328160595977204614846757114076509 : Nat) : Fp) ^ 2 = ((4204695906946780589313791879208530286494667006376374838986876141639449894612 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_187 : Point :=
  .some (x := ((54242991660078524246918591746260064059264467522232695105655327418938766831688 : Nat) : Fp))
    (y := ((4193113019248963161905915003596032009497563786460297449393726659570364859079 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((4193113019248963161905915003596032009497563786460297449393726659570364859079 : Nat) : Fp) ^ 2 = ((54242991660078524246918591746260064059264467522232695105655327418938766831688 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_188 : Point :=
  .some (x := ((47641762048130959225463157744936741734004477513581969797239495873127107041545 : Nat) : Fp))
    (y := ((76207105472136298014269720338542649558764238652312501597524413778998387938985 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((76207105472136298014269720338542649558764238652312501597524413778998387938985 : Nat) : Fp) ^ 2 = ((47641762048130959225463157744936741734004477513581969797239495873127107041545 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_189 : Point :=
  .some (x := ((69472768068364136774272514248217981945764793800798781763504648168259253466708 : Nat) : Fp))
    (y := ((84066309016639162622272974958451153753611922903235405923145116548454900762224 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((84066309016639162622272974958451153753611922903235405923145116548454900762224 : Nat) : Fp) ^ 2 = ((69472768068364136774272514248217981945764793800798781763504648168259253466708 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_190 : Point :=
  .some (x := ((7479663366765373719254913328326893330953174271598814660940401003642652305012 : Nat) : Fp))
    (y := ((76397558670108916513522558135257170527595729312327759784355169197723725322970 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((76397558670108916513522558135257170527595729312327759784355169197723725322970 : Nat) : Fp) ^ 2 = ((7479663366765373719254913328326893330953174271598814660940401003642652305012 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_191 : Point :=
  .some (x := ((93214559303503295622146213850162265162499163294906951100460861720335563037717 : Nat) : Fp))
    (y := ((103051017875081872528402971112466631275333185906029800312422230478788782875349 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((103051017875081872528402971112466631275333185906029800312422230478788782875349 : Nat) : Fp) ^ 2 = ((93214559303503295622146213850162265162499163294906951100460861720335563037717 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_192 : Point :=
  .some (x := ((19436059746748227418925458231805909355641770432714992717682190711891460146984 : Nat) : Fp))
    (y := ((25123249739837458872363581055900892661847146841399057288865559747995855903950 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((25123249739837458872363581055900892661847146841399057288865559747995855903950 : Nat) : Fp) ^ 2 = ((19436059746748227418925458231805909355641770432714992717682190711891460146984 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_193 : Point :=
  .some (x := ((113244355352594671284226941655179016027454160970747784394405576931970465735633 : Nat) : Fp))
    (y := ((96695630708123308266617042421227815773548125428873656885849064873582072419487 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((96695630708123308266617042421227815773548125428873656885849064873582072419487 : Nat) : Fp) ^ 2 = ((113244355352594671284226941655179016027454160970747784394405576931970465735633 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_194 : Point :=
  .some (x := ((103323434291070884810043926593444845888906981086108116030348704516931883710008 : Nat) : Fp))
    (y := ((60614954341398185246747036263666980376835306511800380097735627237901586744236 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((60614954341398185246747036263666980376835306511800380097735627237901586744236 : Nat) : Fp) ^ 2 = ((103323434291070884810043926593444845888906981086108116030348704516931883710008 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_195 : Point :=
  .some (x := ((80822841823700864217117565279855889926619437465175519975430218626939254678860 : Nat) : Fp))
    (y := ((101545319536084464273213754428643567843044807454585186438203512310492502660561 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((101545319536084464273213754428643567843044807454585186438203512310492502660561 : Nat) : Fp) ^ 2 = ((80822841823700864217117565279855889926619437465175519975430218626939254678860 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_196 : Point :=
  .some (x := ((51096724926566392371895137521611104302365830865332930293042238411804011589445 : Nat) : Fp))
    (y := ((40824548172978966131607959632971172363468140787933718344760888091268432727169 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((40824548172978966131607959632971172363468140787933718344760888091268432727169 : Nat) : Fp) ^ 2 = ((51096724926566392371895137521611104302365830865332930293042238411804011589445 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_197 : Point :=
  .some (x := ((90681586653169617779724882027536820663872472108929860672486884584989353164892 : Nat) : Fp))
    (y := ((36198769797273642795280020762145615993106519554492961120353098076646595428190 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((36198769797273642795280020762145615993106519554492961120353098076646595428190 : Nat) : Fp) ^ 2 = ((90681586653169617779724882027536820663872472108929860672486884584989353164892 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_198 : Point :=
  .some (x := ((41097730418687468851840028126570808766847487756664368122837651685823309251855 : Nat) : Fp))
    (y := ((79366651424484606923205901822845691838604394119985222589765970603926825676036 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((79366651424484606923205901822845691838604394119985222589765970603926825676036 : Nat) : Fp) ^ 2 = ((41097730418687468851840028126570808766847487756664368122837651685823309251855 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_199 : Point :=
  .some (x := ((100704980427187950776566009868772393822532287775712850841327750834699511142076 : Nat) : Fp))
    (y := ((58279719471599953411736560524316424649647803014212054128376061886270798582759 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((58279719471599953411736560524316424649647803014212054128376061886270798582759 : Nat) : Fp) ^ 2 = ((100704980427187950776566009868772393822532287775712850841327750834699511142076 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_200 : Point :=
  .some (x := ((41963437398022779394570776873507781528187696448205583322868397102405779089972 : Nat) : Fp))
    (y := ((57362915043750247267111067825215655467129105761756114712540643209886435294434 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((57362915043750247267111067825215655467129105761756114712540643209886435294434 : Nat) : Fp) ^ 2 = ((41963437398022779394570776873507781528187696448205583322868397102405779089972 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_201 : Point :=
  .some (x := ((64419789759124835279729547014899220968818131819816898784308065307874796862988 : Nat) : Fp))
    (y := ((85510922709722318341833382684795019085551042873821458130390800114407923905170 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((85510922709722318341833382684795019085551042873821458130390800114407923905170 : Nat) : Fp) ^ 2 = ((64419789759124835279729547014899220968818131819816898784308065307874796862988 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_202 : Point :=
  .some (x := ((62762142072396476060995371274969129115807131197458019781481479852775245520736 : Nat) : Fp))
    (y := ((39189045373874238657965130442923520884226579305924330722158128762609599265819 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((39189045373874238657965130442923520884226579305924330722158128762609599265819 : Nat) : Fp) ^ 2 = ((62762142072396476060995371274969129115807131197458019781481479852775245520736 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_203 : Point :=
  .some (x := ((81615542260013623080339118753093837651874029535279762844239949691510089428628 : Nat) : Fp))
    (y := ((15542823241052834997162844864929216308776318395726222376084422754657441440224 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((15542823241052834997162844864929216308776318395726222376084422754657441440224 : Nat) : Fp) ^ 2 = ((81615542260013623080339118753093837651874029535279762844239949691510089428628 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_204 : Point :=
  .some (x := ((48726931970016250047517938777773102332101668546633360222010741296033996096059 : Nat) : Fp))
    (y := ((37151443891203614589508296499676557261245300420893273150963960323855351730398 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((37151443891203614589508296499676557261245300420893273150963960323855351730398 : Nat) : Fp) ^ 2 = ((48726931970016250047517938777773102332101668546633360222010741296033996096059 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_205 : Point :=
  .some (x := ((54035609470183790619350063949481307628740160218997884888697305595486899105681 : Nat) : Fp))
    (y := ((91525222724606641924413740905419896621164065448962045575146661981601529096398 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((91525222724606641924413740905419896621164065448962045575146661981601529096398 : Nat) : Fp) ^ 2 = ((54035609470183790619350063949481307628740160218997884888697305595486899105681 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_206 : Point :=
  .some (x := ((71920580694916078600878092949303681142291501514878757409581660259274225713408 : Nat) : Fp))
    (y := ((85141204748235599617662991498115204753351720057112938184957140690209621477869 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((85141204748235599617662991498115204753351720057112938184957140690209621477869 : Nat) : Fp) ^ 2 = ((71920580694916078600878092949303681142291501514878757409581660259274225713408 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_207 : Point :=
  .some (x := ((110649361901339181582290433203418318532663230954106722444955944360769864936149 : Nat) : Fp))
    (y := ((95492280861049391672980770681885009033963018742644227169516433092767152305541 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((95492280861049391672980770681885009033963018742644227169516433092767152305541 : Nat) : Fp) ^ 2 = ((110649361901339181582290433203418318532663230954106722444955944360769864936149 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_208 : Point :=
  .some (x := ((109961148091824176007590053632285201349622686517333656494286472429021334697930 : Nat) : Fp))
    (y := ((94501178915109615761365616122845036057831010861487347292135005418156124398201 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((94501178915109615761365616122845036057831010861487347292135005418156124398201 : Nat) : Fp) ^ 2 = ((109961148091824176007590053632285201349622686517333656494286472429021334697930 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_209 : Point :=
  .some (x := ((46951501587352933349155760188503284574509445044054321376621673100514231210604 : Nat) : Fp))
    (y := ((73874290702339017551103780401677166407923928000021350360787570683944037349563 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((73874290702339017551103780401677166407923928000021350360787570683944037349563 : Nat) : Fp) ^ 2 = ((46951501587352933349155760188503284574509445044054321376621673100514231210604 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_210 : Point :=
  .some (x := ((97720067671541014565491635141056425321913971719848552697820062655710295564581 : Nat) : Fp))
    (y := ((91583069352580589986532598645254828584747897817455570768471020681515419255875 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((91583069352580589986532598645254828584747897817455570768471020681515419255875 : Nat) : Fp) ^ 2 = ((97720067671541014565491635141056425321913971719848552697820062655710295564581 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_211 : Point :=
  .some (x := ((58456002847219606930033165567268340163347895955202507410521224552567431240037 : Nat) : Fp))
    (y := ((102974837974855080610402408124307772827745839286803963952229890761307565020517 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((102974837974855080610402408124307772827745839286803963952229890761307565020517 : Nat) : Fp) ^ 2 = ((58456002847219606930033165567268340163347895955202507410521224552567431240037 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_212 : Point :=
  .some (x := ((93710686539520880202642124984978698613172097623838661478597627527919706519903 : Nat) : Fp))
    (y := ((66906886892884708749140497590475052727151600251841470407614075014787938567321 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((66906886892884708749140497590475052727151600251841470407614075014787938567321 : Nat) : Fp) ^ 2 = ((93710686539520880202642124984978698613172097623838661478597627527919706519903 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_213 : Point :=
  .some (x := ((13729583756584371036628625429921855110250353243232558895041351865827625664590 : Nat) : Fp))
    (y := ((39869739216990426028486357669345227846369444094542437724806371097677663773169 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((39869739216990426028486357669345227846369444094542437724806371097677663773169 : Nat) : Fp) ^ 2 = ((13729583756584371036628625429921855110250353243232558895041351865827625664590 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_214 : Point :=
  .some (x := ((10446955228596413538270086605964137190912466144578740813346210569455704801609 : Nat) : Fp))
    (y := ((1407403829713203913743195399088790650696456245059557065394226261280222108840 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((1407403829713203913743195399088790650696456245059557065394226261280222108840 : Nat) : Fp) ^ 2 = ((10446955228596413538270086605964137190912466144578740813346210569455704801609 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_215 : Point :=
  .some (x := ((41708199630613563533857844054749904790579703403714948734142644304174964773257 : Nat) : Fp))
    (y := ((50759700133657942080854254763037287091221517622959618665319570203141980890096 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((50759700133657942080854254763037287091221517622959618665319570203141980890096 : Nat) : Fp) ^ 2 = ((41708199630613563533857844054749904790579703403714948734142644304174964773257 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_216 : Point :=
  .some (x := ((95367128378517088778906915528758206507061675325718874859459424551456925441454 : Nat) : Fp))
    (y := ((106003138703447446131835973364374586593091113783845312467465483197305129343889 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((106003138703447446131835973364374586593091113783845312467465483197305129343889 : Nat) : Fp) ^ 2 = ((95367128378517088778906915528758206507061675325718874859459424551456925441454 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_217 : Point :=
  .some (x := ((104772712857957687009810078163398532492793836342123717975543767946170854974007 : Nat) : Fp))
    (y := ((33407490115134982232800441480915789342132192284309993103393807431126433473381 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((33407490115134982232800441480915789342132192284309993103393807431126433473381 : Nat) : Fp) ^ 2 = ((104772712857957687009810078163398532492793836342123717975543767946170854974007 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_218 : Point :=
  .some (x := ((10161864771496804080798517767423742549677304171259080353233424123274977274833 : Nat) : Fp))
    (y := ((44507238317834590896412790561396090023766241139715176814139899683790365433775 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((44507238317834590896412790561396090023766241139715176814139899683790365433775 : Nat) : Fp) ^ 2 = ((10161864771496804080798517767423742549677304171259080353233424123274977274833 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_219 : Point :=
  .some (x := ((74331454221247671029245522801737699388867226471994116703508684088775243649882 : Nat) : Fp))
    (y := ((43723714222616435094057467466094517144641234542831142427410611420480550977314 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((43723714222616435094057467466094517144641234542831142427410611420480550977314 : Nat) : Fp) ^ 2 = ((74331454221247671029245522801737699388867226471994116703508684088775243649882 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_220 : Point :=
  .some (x := ((100359178303740786438883038125571840410727210042578402665267813525668086889985 : Nat) : Fp))
    (y := ((24112768755817544284611785890008363126648003755894211635980155476369465654516 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((24112768755817544284611785890008363126648003755894211635980155476369465654516 : Nat) : Fp) ^ 2 = ((100359178303740786438883038125571840410727210042578402665267813525668086889985 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_221 : Point :=
  .some (x := ((101715476756552087767187807538033124532838833535719454646948903410609456669352 : Nat) : Fp))
    (y := ((97574807453842336263165617038094841567894229721985878685970974675946140750600 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((97574807453842336263165617038094841567894229721985878685970974675946140750600 : Nat) : Fp) ^ 2 = ((101715476756552087767187807538033124532838833535719454646948903410609456669352 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_222 : Point :=
  .some (x := ((26201990199447264150340244601088843223044207513721979159517717223349558797573 : Nat) : Fp))
    (y := ((62929508287993277639004659409221556516575433796605423441812829407015555217178 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((62929508287993277639004659409221556516575433796605423441812829407015555217178 : Nat) : Fp) ^ 2 = ((26201990199447264150340244601088843223044207513721979159517717223349558797573 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_223 : Point :=
  .some (x := ((14921441360743431835062401086497095963484503041023341661521987401860874976443 : Nat) : Fp))
    (y := ((78850265360787620829238252009399605140645486851388334653366951691458547663000 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((78850265360787620829238252009399605140645486851388334653366951691458547663000 : Nat) : Fp) ^ 2 = ((14921441360743431835062401086497095963484503041023341661521987401860874976443 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_224 : Point :=
  .some (x := ((78286964671916748464002077903524610882307428783999554209283543510913862216099 : Nat) : Fp))
    (y := ((69208207262524231989781998869308227471702474397686588373130614081572599272393 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((69208207262524231989781998869308227471702474397686588373130614081572599272393 : Nat) : Fp) ^ 2 = ((78286964671916748464002077903524610882307428783999554209283543510913862216099 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_225 : Point :=
  .some (x := ((32105100545289841423885087965333143227423632123747622691327036134947413387996 : Nat) : Fp))
    (y := ((107176501216347319872941766300897194349458849660572881794244933385499532575842 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((107176501216347319872941766300897194349458849660572881794244933385499532575842 : Nat) : Fp) ^ 2 = ((32105100545289841423885087965333143227423632123747622691327036134947413387996 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_226 : Point :=
  .some (x := ((53684246945455233892169494117752543755515973407332488164311693838822716083874 : Nat) : Fp))
    (y := ((104228328354891129794577475529432762877260837553513567146351935828039658278779 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((104228328354891129794577475529432762877260837553513567146351935828039658278779 : Nat) : Fp) ^ 2 = ((53684246945455233892169494117752543755515973407332488164311693838822716083874 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_227 : Point :=
  .some (x := ((51408690339641306259502862117523444905541421107318686013500544629508968693518 : Nat) : Fp))
    (y := ((38962542652774759152447502158801181378596740070486063181510616016690053121357 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((38962542652774759152447502158801181378596740070486063181510616016690053121357 : Nat) : Fp) ^ 2 = ((51408690339641306259502862117523444905541421107318686013500544629508968693518 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_228 : Point :=
  .some (x := ((52786968606586592704978338159563606167635515874663699931786977412781890025330 : Nat) : Fp))
    (y := ((58697020490641830694991289667448246507708277770194013988374765413618928696102 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((58697020490641830694991289667448246507708277770194013988374765413618928696102 : Nat) : Fp) ^ 2 = ((52786968606586592704978338159563606167635515874663699931786977412781890025330 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_229 : Point :=
  .some (x := ((86156646838761427890073982424487469968465991327301981509193839358381582224146 : Nat) : Fp))
    (y := ((48244124533489911091464029142676735357156585326334056395334755085302048760140 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((48244124533489911091464029142676735357156585326334056395334755085302048760140 : Nat) : Fp) ^ 2 = ((86156646838761427890073982424487469968465991327301981509193839358381582224146 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_230 : Point :=
  .some (x := ((97860223995786388436718584398015194619729937254824459850925401805715135240037 : Nat) : Fp))
    (y := ((9450363544228185891002858073527001779083311253255079730475207282364117871804 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((9450363544228185891002858073527001779083311253255079730475207282364117871804 : Nat) : Fp) ^ 2 = ((97860223995786388436718584398015194619729937254824459850925401805715135240037 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_231 : Point :=
  .some (x := ((97543033203699496180030109729025514517779016973665982852482659210135496439562 : Nat) : Fp))
    (y := ((96485919188640319661734814117407264415512485743206780005275327817967484589025 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((96485919188640319661734814117407264415512485743206780005275327817967484589025 : Nat) : Fp) ^ 2 = ((97543033203699496180030109729025514517779016973665982852482659210135496439562 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_232 : Point :=
  .some (x := ((102830533340956686198994875465671816784497224723621699776483958495310423492487 : Nat) : Fp))
    (y := ((30409364465911376382062081903253235354581412893702179936620223597366139023447 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((30409364465911376382062081903253235354581412893702179936620223597366139023447 : Nat) : Fp) ^ 2 = ((102830533340956686198994875465671816784497224723621699776483958495310423492487 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_233 : Point :=
  .some (x := ((30296781290666500851168272802295872378717872596910351160793153249076866250067 : Nat) : Fp))
    (y := ((55916929317641937071084404866045275140201483451351707426073383549397819490988 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((55916929317641937071084404866045275140201483451351707426073383549397819490988 : Nat) : Fp) ^ 2 = ((30296781290666500851168272802295872378717872596910351160793153249076866250067 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_234 : Point :=
  .some (x := ((112315026525901017482762550793305442477113960914535610904227469025227247239111 : Nat) : Fp))
    (y := ((49871746725307346317681367110993781904741915431745890154213666738710559760208 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((49871746725307346317681367110993781904741915431745890154213666738710559760208 : Nat) : Fp) ^ 2 = ((112315026525901017482762550793305442477113960914535610904227469025227247239111 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_235 : Point :=
  .some (x := ((46569867216501492463829635190455011087054375636727173037363205698031811292777 : Nat) : Fp))
    (y := ((99554292090938309716246192958684556782056231624071931546120340801585990975109 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((99554292090938309716246192958684556782056231624071931546120340801585990975109 : Nat) : Fp) ^ 2 = ((46569867216501492463829635190455011087054375636727173037363205698031811292777 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_236 : Point :=
  .some (x := ((30460618184285782433506524833173452821317744234050953035479650134294695229687 : Nat) : Fp))
    (y := ((1029480740930620994498373859936262084317436194780107773001520906588264935059 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((1029480740930620994498373859936262084317436194780107773001520906588264935059 : Nat) : Fp) ^ 2 = ((30460618184285782433506524833173452821317744234050953035479650134294695229687 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_237 : Point :=
  .some (x := ((71270092845352995479434385129475437865313439324845947026235006874099517319235 : Nat) : Fp))
    (y := ((16501345542646850933158666325129275564880408279633706132371349688183435035119 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((16501345542646850933158666325129275564880408279633706132371349688183435035119 : Nat) : Fp) ^ 2 = ((71270092845352995479434385129475437865313439324845947026235006874099517319235 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_238 : Point :=
  .some (x := ((16618556853955496303621456858521371789817942603952389038933742455201500272862 : Nat) : Fp))
    (y := ((105623413539446534475123892922000765066384377862553587703656459409095412557051 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((105623413539446534475123892922000765066384377862553587703656459409095412557051 : Nat) : Fp) ^ 2 = ((16618556853955496303621456858521371789817942603952389038933742455201500272862 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_239 : Point :=
  .some (x := ((74742492579009244357905242041687175457775327266132249497268901437517232845332 : Nat) : Fp))
    (y := ((114699055254734085331164357669320705839111992500985393140160222788774166861494 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((114699055254734085331164357669320705839111992500985393140160222788774166861494 : Nat) : Fp) ^ 2 = ((74742492579009244357905242041687175457775327266132249497268901437517232845332 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_240 : Point :=
  .some (x := ((1081612414056764282020452592787223287568754890085769046997177576205063339491 : Nat) : Fp))
    (y := ((44747613108632260717822144637987652971391392858915576291280779809256471377238 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((44747613108632260717822144637987652971391392858915576291280779809256471377238 : Nat) : Fp) ^ 2 = ((1081612414056764282020452592787223287568754890085769046997177576205063339491 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_241 : Point :=
  .some (x := ((49811277349567224411985508482634174791584736505241552453091834927605838997743 : Nat) : Fp))
    (y := ((88053982202123090461505576929120316231093483547555797784533027534394422022869 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((88053982202123090461505576929120316231093483547555797784533027534394422022869 : Nat) : Fp) ^ 2 = ((49811277349567224411985508482634174791584736505241552453091834927605838997743 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_242 : Point :=
  .some (x := ((77706397775829796206513053180104330003887931466756047681323827121198156235594 : Nat) : Fp))
    (y := ((60088041830652310201575685525116711717955821314283880815939940330960602595366 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((60088041830652310201575685525116711717955821314283880815939940330960602595366 : Nat) : Fp) ^ 2 = ((77706397775829796206513053180104330003887931466756047681323827121198156235594 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_243 : Point :=
  .some (x := ((23785567577982762677578830488290362080656906729902214709880944246705510538322 : Nat) : Fp))
    (y := ((29195547448378149604690967779902473397916800306677216156987726536034103090328 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((29195547448378149604690967779902473397916800306677216156987726536034103090328 : Nat) : Fp) ^ 2 = ((23785567577982762677578830488290362080656906729902214709880944246705510538322 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_244 : Point :=
  .some (x := ((14090046075950136180562018246382077790895898809530716464155275291397585164913 : Nat) : Fp))
    (y := ((87833992341023535479845708371432066550999723108376977466264044242266341733141 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((87833992341023535479845708371432066550999723108376977466264044242266341733141 : Nat) : Fp) ^ 2 = ((14090046075950136180562018246382077790895898809530716464155275291397585164913 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_245 : Point :=
  .some (x := ((37828421047972008774017066608768410609187446689017066363359154428044810742785 : Nat) : Fp))
    (y := ((113226292101255053265912448708291971531186503653436133578142918006414973486957 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((113226292101255053265912448708291971531186503653436133578142918006414973486957 : Nat) : Fp) ^ 2 = ((37828421047972008774017066608768410609187446689017066363359154428044810742785 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_246 : Point :=
  .some (x := ((20842789763102640913372864025301593491814512580224379177912388102803212159731 : Nat) : Fp))
    (y := ((107410244362911412413053286079934390031031550454718341727117045597825912151135 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((107410244362911412413053286079934390031031550454718341727117045597825912151135 : Nat) : Fp) ^ 2 = ((20842789763102640913372864025301593491814512580224379177912388102803212159731 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_247 : Point :=
  .some (x := ((110539463342885515017316615115704012034156315028293057517191961487462828970401 : Nat) : Fp))
    (y := ((115445443873164393444233708083243158013211351768761441982691257404063982064328 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((115445443873164393444233708083243158013211351768761441982691257404063982064328 : Nat) : Fp) ^ 2 = ((110539463342885515017316615115704012034156315028293057517191961487462828970401 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_248 : Point :=
  .some (x := ((60514053294911466398737601314427703479018544726564927088684814673373104577301 : Nat) : Fp))
    (y := ((22551341913608398905414162624851807282361939577344960293160427740218883912555 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((22551341913608398905414162624851807282361939577344960293160427740218883912555 : Nat) : Fp) ^ 2 = ((60514053294911466398737601314427703479018544726564927088684814673373104577301 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_249 : Point :=
  .some (x := ((32052271579092252526176234927591189443293762247044804283344858953002472806271 : Nat) : Fp))
    (y := ((98302918787849364714396393177487078334103885001289606499004072092703617200351 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((98302918787849364714396393177487078334103885001289606499004072092703617200351 : Nat) : Fp) ^ 2 = ((32052271579092252526176234927591189443293762247044804283344858953002472806271 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_250 : Point :=
  .some (x := ((103456305090242564895712946172826220978932802667151275263999199465000893101440 : Nat) : Fp))
    (y := ((48463618096607934694683864929401532211182636135002885938396848762261901925143 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((48463618096607934694683864929401532211182636135002885938396848762261901925143 : Nat) : Fp) ^ 2 = ((103456305090242564895712946172826220978932802667151275263999199465000893101440 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_251 : Point :=
  .some (x := ((46530563348586613959865991838199016313984999584228385081042307393336696728902 : Nat) : Fp))
    (y := ((91874707878155191194124261263280250469425140692523701542530477097747056195324 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((91874707878155191194124261263280250469425140692523701542530477097747056195324 : Nat) : Fp) ^ 2 = ((46530563348586613959865991838199016313984999584228385081042307393336696728902 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_252 : Point :=
  .some (x := ((27037594016997265388276663112501048648670817957697121730841628104825126763212 : Nat) : Fp))
    (y := ((51478215930460196269611559500912157526194914189145635983032375182192219324041 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((51478215930460196269611559500912157526194914189145635983032375182192219324041 : Nat) : Fp) ^ 2 = ((27037594016997265388276663112501048648670817957697121730841628104825126763212 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_253 : Point :=
  .some (x := ((77692363628108059885443663784710924525445718788147207068968950173471674635534 : Nat) : Fp))
    (y := ((37020575757196479510264675333438911221659819676852640814616424037620478864221 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((37020575757196479510264675333438911221659819676852640814616424037620478864221 : Nat) : Fp) ^ 2 = ((77692363628108059885443663784710924525445718788147207068968950173471674635534 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_254 : Point :=
  .some (x := ((51523398464344358728983437505968609663784806853362284802296319167775841330559 : Nat) : Fp))
    (y := ((61130711260811300073628625088702243303261080157180463958970891742667571336877 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((61130711260811300073628625088702243303261080157180463958970891742667571336877 : Nat) : Fp) ^ 2 = ((51523398464344358728983437505968609663784806853362284802296319167775841330559 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)
private def acc_255 : Point :=
  .some (x := ((80609861913912564376813326121470687649554127203741395941834419933864230904708 : Nat) : Fp))
    (y := ((1619472104238675877071743257676031256406508288955395786894319864683352716321 : Nat) : Fp)) (by
      apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero curve_discriminant_ne_zero).mp
      rw [curve.toAffine.equation_iff]
      change (((1619472104238675877071743257676031256406508288955395786894319864683352716321 : Nat) : Fp) ^ 2 = ((80609861913912564376813326121470687649554127203741395941834419933864230904708 : Nat) : Fp) ^ 3 + 7)
      unfold Fp p
      reduce_mod_char)

private theorem base_0_eq_G : base_0 = G := by
  apply coordinates_injective
  unfold base_0 G
  simp only [coordinates_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · unfold generatorX
    rfl
  · unfold generatorY
    rfl

private theorem base_double_0 : affineAdd base_0 base_0 = base_1 := by
  unfold base_0 base_1
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((32670510020758816978083085130507043184471273380659243275938904335757337482424 : Nat) : Fp))⁻¹ = ((83174505189910067536517124096019359197644205712500122884473429251812128958118 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((32670510020758816978083085130507043184471273380659243275938904335757337482424 : Nat) : Fp))⁻¹ = ((83174505189910067536517124096019359197644205712500122884473429251812128958118 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_1 : affineAdd base_1 base_1 = base_2 := by
  unfold base_1 base_2
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((12158399299693830322967808612713398636155367887041628176798871954788371653930 : Nat) : Fp))⁻¹ = ((93736451599995461267424215486556527005103980679329099329644578865571485201981 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((12158399299693830322967808612713398636155367887041628176798871954788371653930 : Nat) : Fp))⁻¹ = ((93736451599995461267424215486556527005103980679329099329644578865571485201981 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_2 : affineAdd base_2 base_2 = base_3 := by
  unfold base_2 base_3
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((37057141145242123013015316630864329550140216928701153669873286428255828810018 : Nat) : Fp))⁻¹ = ((28251856789096162999762519039887113235530305026901261163221850518573700905610 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((37057141145242123013015316630864329550140216928701153669873286428255828810018 : Nat) : Fp))⁻¹ = ((28251856789096162999762519039887113235530305026901261163221850518573700905610 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_3 : affineAdd base_3 base_3 = base_4 := by
  unfold base_3 base_4
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((41749993296225487051377864631615517161996906063147759678534462689479575333124 : Nat) : Fp))⁻¹ = ((44908759060410746426936320578584839352891245825107015656635909502382714814724 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((41749993296225487051377864631615517161996906063147759678534462689479575333124 : Nat) : Fp))⁻¹ = ((44908759060410746426936320578584839352891245825107015656635909502382714814724 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_4 : affineAdd base_4 base_4 = base_5 := by
  unfold base_4 base_5
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((112122903140080327253741791678230372394936108416576609264408917599318947489825 : Nat) : Fp))⁻¹ = ((17825568012884182675766143213511682455505826626476410795439574664363245530263 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((112122903140080327253741791678230372394936108416576609264408917599318947489825 : Nat) : Fp))⁻¹ = ((17825568012884182675766143213511682455505826626476410795439574664363245530263 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_5 : affineAdd base_5 base_5 = base_6 := by
  unfold base_5 base_6
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((67400892360194400039319989411395972789004161889863182881857158544061243615929 : Nat) : Fp))⁻¹ = ((12786479899922343417991798164630903075627618206908979180411597188899718055589 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((67400892360194400039319989411395972789004161889863182881857158544061243615929 : Nat) : Fp))⁻¹ = ((12786479899922343417991798164630903075627618206908979180411597188899718055589 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_6 : affineAdd base_6 base_6 = base_7 := by
  unfold base_6 base_7
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((41929975541376036990359335647717381527212342035893043668288666074313354583455 : Nat) : Fp))⁻¹ = ((47518630023279931174649623558106216072802955186670440489970803158820291670810 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((41929975541376036990359335647717381527212342035893043668288666074313354583455 : Nat) : Fp))⁻¹ = ((47518630023279931174649623558106216072802955186670440489970803158820291670810 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_7 : affineAdd base_7 base_7 = base_8 := by
  unfold base_7 base_8
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((42342609885299334444880650568116455571250837701978463648617679521175848103706 : Nat) : Fp))⁻¹ = ((62802202702015010968693581972871454208292311925657926586234704568904361743893 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((42342609885299334444880650568116455571250837701978463648617679521175848103706 : Nat) : Fp))⁻¹ = ((62802202702015010968693581972871454208292311925657926586234704568904361743893 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_8 : affineAdd base_8 base_8 = base_9 := by
  unfold base_8 base_9
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((8128656248049033031875480515138402531865803579197128279783442554673902546095 : Nat) : Fp))⁻¹ = ((97742869888744051470506515753491785124041069887454146098619031396008042322210 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((8128656248049033031875480515138402531865803579197128279783442554673902546095 : Nat) : Fp))⁻¹ = ((97742869888744051470506515753491785124041069887454146098619031396008042322210 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_9 : affineAdd base_9 base_9 = base_10 := by
  unfold base_9 base_10
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((24377531977987817432088011602449325046972761657480460991275213238540072159220 : Nat) : Fp))⁻¹ = ((64585384618317792074319987919222363446108240452753815467460457027419595448158 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((24377531977987817432088011602449325046972761657480460991275213238540072159220 : Nat) : Fp))⁻¹ = ((64585384618317792074319987919222363446108240452753815467460457027419595448158 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_10 : affineAdd base_10 base_10 = base_11 := by
  unfold base_10 base_11
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((36728284022334234592863792440353097018527397507662959793213172092233334129261 : Nat) : Fp))⁻¹ = ((56022179547941566534377416509424820648214956315064888672070939903186810774544 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((36728284022334234592863792440353097018527397507662959793213172092233334129261 : Nat) : Fp))⁻¹ = ((56022179547941566534377416509424820648214956315064888672070939903186810774544 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_11 : affineAdd base_11 base_11 = base_12 := by
  unfold base_11 base_12
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((18211792713336063942313736004207749605328499756363387606667481967702897602819 : Nat) : Fp))⁻¹ = ((46553536980509727857078602906520989348303270700069690459441258747317462902876 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((18211792713336063942313736004207749605328499756363387606667481967702897602819 : Nat) : Fp))⁻¹ = ((46553536980509727857078602906520989348303270700069690459441258747317462902876 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_12 : affineAdd base_12 base_12 = base_13 := by
  unfold base_12 base_13
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((95580118375493152898771330185112988759633284070886792649665201458589961475733 : Nat) : Fp))⁻¹ = ((18279908501689292066471383549871719855949160301741493496988315658604306502970 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((95580118375493152898771330185112988759633284070886792649665201458589961475733 : Nat) : Fp))⁻¹ = ((18279908501689292066471383549871719855949160301741493496988315658604306502970 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_13 : affineAdd base_13 base_13 = base_14 := by
  unfold base_13 base_14
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((83725361430957575604497772232028370201521594201253320640285202099397696195124 : Nat) : Fp))⁻¹ = ((72967957932113978987694380445693166684125916090156996153384354982254363985475 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((83725361430957575604497772232028370201521594201253320640285202099397696195124 : Nat) : Fp))⁻¹ = ((72967957932113978987694380445693166684125916090156996153384354982254363985475 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_14 : affineAdd base_14 base_14 = base_15 := by
  unfold base_14 base_15
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((2979905666851018206144735065445742806952013006906430309532921989383330523600 : Nat) : Fp))⁻¹ = ((25902289881486705264223263271227332454394336239178008851484151450394125071363 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((2979905666851018206144735065445742806952013006906430309532921989383330523600 : Nat) : Fp))⁻¹ = ((25902289881486705264223263271227332454394336239178008851484151450394125071363 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_15 : affineAdd base_15 base_15 = base_16 := by
  unfold base_15 base_16
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((37360103261735091089003680850413001554296156453961728314327616229790563817069 : Nat) : Fp))⁻¹ = ((75281299823753875216163072107839590067968036013224327079542800503841318614886 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((37360103261735091089003680850413001554296156453961728314327616229790563817069 : Nat) : Fp))⁻¹ = ((75281299823753875216163072107839590067968036013224327079542800503841318614886 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_16 : affineAdd base_16 base_16 = base_17 := by
  unfold base_16 base_17
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((2209357222459695347071765155987393997305194371900031813817445740077485301225 : Nat) : Fp))⁻¹ = ((4118250909444105318441676035029117028440948709898090225769434902598988524714 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((2209357222459695347071765155987393997305194371900031813817445740077485301225 : Nat) : Fp))⁻¹ = ((4118250909444105318441676035029117028440948709898090225769434902598988524714 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_17 : affineAdd base_17 base_17 = base_18 := by
  unfold base_17 base_18
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((87733804348534428731161926933835660863551297059124747814746905172819546464288 : Nat) : Fp))⁻¹ = ((42022910952391263196849949673394918371324021021898886938523379323314643185786 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((87733804348534428731161926933835660863551297059124747814746905172819546464288 : Nat) : Fp))⁻¹ = ((42022910952391263196849949673394918371324021021898886938523379323314643185786 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_18 : affineAdd base_18 base_18 = base_19 := by
  unfold base_18 base_19
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((29361396017150706741613988342393505196301946421006103373231627829781191611577 : Nat) : Fp))⁻¹ = ((16956031182445019091373640357132530317909828147132232789209555313715878030304 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((29361396017150706741613988342393505196301946421006103373231627829781191611577 : Nat) : Fp))⁻¹ = ((16956031182445019091373640357132530317909828147132232789209555313715878030304 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_19 : affineAdd base_19 base_19 = base_20 := by
  unfold base_19 base_20
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((67731220512052072417843278921450425890601471538300788051881284779249943090810 : Nat) : Fp))⁻¹ = ((87312567426712433170551076883874352635770166878968122955840755943575885669425 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((67731220512052072417843278921450425890601471538300788051881284779249943090810 : Nat) : Fp))⁻¹ = ((87312567426712433170551076883874352635770166878968122955840755943575885669425 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_20 : affineAdd base_20 base_20 = base_21 := by
  unfold base_20 base_21
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((33776887358425213876727286236887696644549240079971817446727643228044518554934 : Nat) : Fp))⁻¹ = ((12254622361099297639233420267669420578178604072766320566201301339962721592248 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((33776887358425213876727286236887696644549240079971817446727643228044518554934 : Nat) : Fp))⁻¹ = ((12254622361099297639233420267669420578178604072766320566201301339962721592248 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_21 : affineAdd base_21 base_21 = base_22 := by
  unfold base_21 base_22
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((15425677638027042728233515882140468124385010133809940201784713737762399581231 : Nat) : Fp))⁻¹ = ((58257239923510584953758405370404666723777987098606105760479546410821645863688 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((15425677638027042728233515882140468124385010133809940201784713737762399581231 : Nat) : Fp))⁻¹ = ((58257239923510584953758405370404666723777987098606105760479546410821645863688 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_22 : affineAdd base_22 base_22 = base_23 := by
  unfold base_22 base_23
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((92288978233865387499357228995099386605786555025834285738713074898639193985136 : Nat) : Fp))⁻¹ = ((10710690423931168603895477207529704380685446483158818042376118567851954057485 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((92288978233865387499357228995099386605786555025834285738713074898639193985136 : Nat) : Fp))⁻¹ = ((10710690423931168603895477207529704380685446483158818042376118567851954057485 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_23 : affineAdd base_23 base_23 = base_24 := by
  unfold base_23 base_24
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((67104318001466418430256649108646734852945972191921730406768272163045294283904 : Nat) : Fp))⁻¹ = ((104397989377267004616657002282090203797803686410463744833312214590198207844545 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((67104318001466418430256649108646734852945972191921730406768272163045294283904 : Nat) : Fp))⁻¹ = ((104397989377267004616657002282090203797803686410463744833312214590198207844545 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_24 : affineAdd base_24 base_24 = base_25 := by
  unfold base_24 base_25
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((68257551575553566084241009552849606333781498777275567535225153774080710909791 : Nat) : Fp))⁻¹ = ((43905548963985291592484730936270627374971570785564084979154367155472971370760 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((68257551575553566084241009552849606333781498777275567535225153774080710909791 : Nat) : Fp))⁻¹ = ((43905548963985291592484730936270627374971570785564084979154367155472971370760 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_25 : affineAdd base_25 base_25 = base_26 := by
  unfold base_25 base_26
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((97280577493662175430906331419179376788053309764979933526226118285088405860254 : Nat) : Fp))⁻¹ = ((69703730232751414728293933134378622030739546143830554629840973371086916121634 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((97280577493662175430906331419179376788053309764979933526226118285088405860254 : Nat) : Fp))⁻¹ = ((69703730232751414728293933134378622030739546143830554629840973371086916121634 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_26 : affineAdd base_26 base_26 = base_27 := by
  unfold base_26 base_27
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((97919434988400284406895062116320315016365801759636091852848099981382771845905 : Nat) : Fp))⁻¹ = ((61171389882507769645284420023202565268172553701883049635173119830937090881749 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((97919434988400284406895062116320315016365801759636091852848099981382771845905 : Nat) : Fp))⁻¹ = ((61171389882507769645284420023202565268172553701883049635173119830937090881749 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_27 : affineAdd base_27 base_27 = base_28 := by
  unfold base_27 base_28
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((81925384519567487405199682290695043524776979911807891169446287270330277192180 : Nat) : Fp))⁻¹ = ((73355281677668588440805730300634434737190112549399880554982435129389176481954 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((81925384519567487405199682290695043524776979911807891169446287270330277192180 : Nat) : Fp))⁻¹ = ((73355281677668588440805730300634434737190112549399880554982435129389176481954 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_28 : affineAdd base_28 base_28 = base_29 := by
  unfold base_28 base_29
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((42338160021087805224648939485129818613830046750563614152037885753448952924569 : Nat) : Fp))⁻¹ = ((73041893344117691793970607057476265792224061609695069126323735369450741758210 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((42338160021087805224648939485129818613830046750563614152037885753448952924569 : Nat) : Fp))⁻¹ = ((73041893344117691793970607057476265792224061609695069126323735369450741758210 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_29 : affineAdd base_29 base_29 = base_30 := by
  unfold base_29 base_30
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((66678967052843214385960608145916057604491714224625771583834324020892145369029 : Nat) : Fp))⁻¹ = ((43429121432697938872122738899526846437328455480822237790875786873971884719552 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((66678967052843214385960608145916057604491714224625771583834324020892145369029 : Nat) : Fp))⁻¹ = ((43429121432697938872122738899526846437328455480822237790875786873971884719552 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_30 : affineAdd base_30 base_30 = base_31 := by
  unfold base_30 base_31
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((6691527371710806382780054211605006078697403702312160758173793149761505802135 : Nat) : Fp))⁻¹ = ((25417390439715819199880701723483568891645258381796628705859720905291076936125 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((6691527371710806382780054211605006078697403702312160758173793149761505802135 : Nat) : Fp))⁻¹ = ((25417390439715819199880701723483568891645258381796628705859720905291076936125 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_31 : affineAdd base_31 base_31 = base_32 := by
  unfold base_31 base_32
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((110500050436317590116317882856153568952218728972968181243435825114259637008685 : Nat) : Fp))⁻¹ = ((83299305915020143158566183691451347721470799473981475301062832448203039790664 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((110500050436317590116317882856153568952218728972968181243435825114259637008685 : Nat) : Fp))⁻¹ = ((83299305915020143158566183691451347721470799473981475301062832448203039790664 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_32 : affineAdd base_32 base_32 = base_33 := by
  unfold base_32 base_33
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((93109094002033366773627505914545361927166820241279828474630961892312310241801 : Nat) : Fp))⁻¹ = ((110517426487345072959329366950807278912709564145285855983972504390773699176139 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((93109094002033366773627505914545361927166820241279828474630961892312310241801 : Nat) : Fp))⁻¹ = ((110517426487345072959329366950807278912709564145285855983972504390773699176139 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_33 : affineAdd base_33 base_33 = base_34 := by
  unfold base_33 base_34
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((113667876764634414158091221422353531108236715357465572941896170017035409095320 : Nat) : Fp))⁻¹ = ((2159591353425063971450126159626352882370854966095976796776215680304302793230 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((113667876764634414158091221422353531108236715357465572941896170017035409095320 : Nat) : Fp))⁻¹ = ((2159591353425063971450126159626352882370854966095976796776215680304302793230 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_34 : affineAdd base_34 base_34 = base_35 := by
  unfold base_34 base_35
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((49136863138091630742201940998618633678196612987804544425991276550671171170453 : Nat) : Fp))⁻¹ = ((61523858279763306855012824991500076176142604614439090155848604607999444501490 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((49136863138091630742201940998618633678196612987804544425991276550671171170453 : Nat) : Fp))⁻¹ = ((61523858279763306855012824991500076176142604614439090155848604607999444501490 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_35 : affineAdd base_35 base_35 = base_36 := by
  unfold base_35 base_36
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((109770660671288161864329498510482442986586271328087679077837897757717839673046 : Nat) : Fp))⁻¹ = ((2595725192483359487009017005045068442615980956913527569237052640115875922644 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((109770660671288161864329498510482442986586271328087679077837897757717839673046 : Nat) : Fp))⁻¹ = ((2595725192483359487009017005045068442615980956913527569237052640115875922644 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_36 : affineAdd base_36 base_36 = base_37 := by
  unfold base_36 base_37
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((71211677518830069576439009135279320536125727843027256193157225588947573710861 : Nat) : Fp))⁻¹ = ((78641913645068410169490544470232763378737252324706246064429569664032253400477 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((71211677518830069576439009135279320536125727843027256193157225588947573710861 : Nat) : Fp))⁻¹ = ((78641913645068410169490544470232763378737252324706246064429569664032253400477 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_37 : affineAdd base_37 base_37 = base_38 := by
  unfold base_37 base_38
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((75300502224888127283828373326871043861231715295745491495384349459792808386515 : Nat) : Fp))⁻¹ = ((96960169042183477145071232736458932945417687079522317485293467434893096486220 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((75300502224888127283828373326871043861231715295745491495384349459792808386515 : Nat) : Fp))⁻¹ = ((96960169042183477145071232736458932945417687079522317485293467434893096486220 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_38 : affineAdd base_38 base_38 = base_39 := by
  unfold base_38 base_39
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((7836136238007924788592053766414363238944904687598451784829364216715569810500 : Nat) : Fp))⁻¹ = ((23236730568703452525562368661903192287495194433219711417126408424972661550823 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((7836136238007924788592053766414363238944904687598451784829364216715569810500 : Nat) : Fp))⁻¹ = ((23236730568703452525562368661903192287495194433219711417126408424972661550823 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_39 : affineAdd base_39 base_39 = base_40 := by
  unfold base_39 base_40
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((98309468026548637860626714749357698670012533693024507288465476348752328350038 : Nat) : Fp))⁻¹ = ((3073228470080430236833430768507898298312850418265512497430704979341233545411 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((98309468026548637860626714749357698670012533693024507288465476348752328350038 : Nat) : Fp))⁻¹ = ((3073228470080430236833430768507898298312850418265512497430704979341233545411 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_40 : affineAdd base_40 base_40 = base_41 := by
  unfold base_40 base_41
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((103799472776126890762485670055583971987299536955028941653349419016168013365384 : Nat) : Fp))⁻¹ = ((19181914220922474975292944621350570631419744500263950587669881916515359401658 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((103799472776126890762485670055583971987299536955028941653349419016168013365384 : Nat) : Fp))⁻¹ = ((19181914220922474975292944621350570631419744500263950587669881916515359401658 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_41 : affineAdd base_41 base_41 = base_42 := by
  unfold base_41 base_42
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((47968762878478268758489427369126262603811724231741657789486393243885145959658 : Nat) : Fp))⁻¹ = ((74573499834090610612948220703835110661067920773005084806261005846555891971318 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((47968762878478268758489427369126262603811724231741657789486393243885145959658 : Nat) : Fp))⁻¹ = ((74573499834090610612948220703835110661067920773005084806261005846555891971318 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_42 : affineAdd base_42 base_42 = base_43 := by
  unfold base_42 base_43
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((106410582405992915570439467813541861485454771813746638713688333696184247730702 : Nat) : Fp))⁻¹ = ((12260321776502108480795346603239858803737325715521310613558272366014527227154 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((106410582405992915570439467813541861485454771813746638713688333696184247730702 : Nat) : Fp))⁻¹ = ((12260321776502108480795346603239858803737325715521310613558272366014527227154 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_43 : affineAdd base_43 base_43 = base_44 := by
  unfold base_43 base_44
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((47578048250598054907858110438316220654276129654309504967125355240893257809602 : Nat) : Fp))⁻¹ = ((6834970982450752195482306942253909959285517408890410534721085511867852310546 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((47578048250598054907858110438316220654276129654309504967125355240893257809602 : Nat) : Fp))⁻¹ = ((6834970982450752195482306942253909959285517408890410534721085511867852310546 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_44 : affineAdd base_44 base_44 = base_45 := by
  unfold base_44 base_45
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((70413563958895942572205979769129125709431089683617469237670049369710274330141 : Nat) : Fp))⁻¹ = ((32074632401321710081626197620111380690814373989611900482683573366125123907767 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((70413563958895942572205979769129125709431089683617469237670049369710274330141 : Nat) : Fp))⁻¹ = ((32074632401321710081626197620111380690814373989611900482683573366125123907767 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_45 : affineAdd base_45 base_45 = base_46 := by
  unfold base_45 base_46
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((10295997985162667395889563220444841839650277790026794883844526680522437342755 : Nat) : Fp))⁻¹ = ((114521138811827909552685747045696867716569044269769480623288087259212497918429 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((10295997985162667395889563220444841839650277790026794883844526680522437342755 : Nat) : Fp))⁻¹ = ((114521138811827909552685747045696867716569044269769480623288087259212497918429 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_46 : affineAdd base_46 base_46 = base_47 := by
  unfold base_46 base_47
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((43436562493669582162283754540252355903120339577829436566794554777028968127513 : Nat) : Fp))⁻¹ = ((47416287419808820719710444148454771503605331847986265303753645650852311968665 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((43436562493669582162283754540252355903120339577829436566794554777028968127513 : Nat) : Fp))⁻¹ = ((47416287419808820719710444148454771503605331847986265303753645650852311968665 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_47 : affineAdd base_47 base_47 = base_48 := by
  unfold base_47 base_48
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((16668035065520662549877161813594040899471944430197287458384095143621564263367 : Nat) : Fp))⁻¹ = ((86847524557229522558579282724103751237138172204033298882341913312962911475396 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((16668035065520662549877161813594040899471944430197287458384095143621564263367 : Nat) : Fp))⁻¹ = ((86847524557229522558579282724103751237138172204033298882341913312962911475396 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_48 : affineAdd base_48 base_48 = base_49 := by
  unfold base_48 base_49
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((41500641220791808004786750540350768710904110215016898096683828744807363604936 : Nat) : Fp))⁻¹ = ((14292971808381209843272683079275134864477538414875931035075103919748102565625 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((41500641220791808004786750540350768710904110215016898096683828744807363604936 : Nat) : Fp))⁻¹ = ((14292971808381209843272683079275134864477538414875931035075103919748102565625 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_49 : affineAdd base_49 base_49 = base_50 := by
  unfold base_49 base_50
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((21811628975969469444130274876674950438343669908561616590110157209566897229239 : Nat) : Fp))⁻¹ = ((51671757878592371733625996938103603561875822231610715720380986791890225502915 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((21811628975969469444130274876674950438343669908561616590110157209566897229239 : Nat) : Fp))⁻¹ = ((51671757878592371733625996938103603561875822231610715720380986791890225502915 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_50 : affineAdd base_50 base_50 = base_51 := by
  unfold base_50 base_51
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((48678944480045457289293852267343808286651244662567230126433152661761421134978 : Nat) : Fp))⁻¹ = ((63838753071622326662636225512921809052136552596157651720282015528883952277228 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((48678944480045457289293852267343808286651244662567230126433152661761421134978 : Nat) : Fp))⁻¹ = ((63838753071622326662636225512921809052136552596157651720282015528883952277228 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_51 : affineAdd base_51 base_51 = base_52 := by
  unfold base_51 base_52
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((31943858956135239004423171297694200648464614566963609709790210548050786133055 : Nat) : Fp))⁻¹ = ((65565365282350309482431085086465274515693011864434197574599341060543246161989 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((31943858956135239004423171297694200648464614566963609709790210548050786133055 : Nat) : Fp))⁻¹ = ((65565365282350309482431085086465274515693011864434197574599341060543246161989 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_52 : affineAdd base_52 base_52 = base_53 := by
  unfold base_52 base_53
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((7561160199009862821682934691566626840504770282093073394715850644522417534762 : Nat) : Fp))⁻¹ = ((74430128732288101369212394632915457324242372966447196304591389653286560376864 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((7561160199009862821682934691566626840504770282093073394715850644522417534762 : Nat) : Fp))⁻¹ = ((74430128732288101369212394632915457324242372966447196304591389653286560376864 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_53 : affineAdd base_53 base_53 = base_54 := by
  unfold base_53 base_54
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((74875455409133275347616261968367570739354909860053424157743477951969742386200 : Nat) : Fp))⁻¹ = ((24335107847723275944320600402532690124489211111511282058542445663245088706180 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((74875455409133275347616261968367570739354909860053424157743477951969742386200 : Nat) : Fp))⁻¹ = ((24335107847723275944320600402532690124489211111511282058542445663245088706180 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_54 : affineAdd base_54 base_54 = base_55 := by
  unfold base_54 base_55
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((10433933909011809793968879060653803690577200525567091682194830769813011264330 : Nat) : Fp))⁻¹ = ((9442630279326356146769611599493452492443212379632786237904888820568032866138 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((10433933909011809793968879060653803690577200525567091682194830769813011264330 : Nat) : Fp))⁻¹ = ((9442630279326356146769611599493452492443212379632786237904888820568032866138 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_55 : affineAdd base_55 base_55 = base_56 := by
  unfold base_55 base_56
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((50458543989467853184310582844531917678045791765530172581605874408799080266778 : Nat) : Fp))⁻¹ = ((109126313190962133675622457262006669935814651015232126307570646222258896570502 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((50458543989467853184310582844531917678045791765530172581605874408799080266778 : Nat) : Fp))⁻¹ = ((109126313190962133675622457262006669935814651015232126307570646222258896570502 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_56 : affineAdd base_56 base_56 = base_57 := by
  unfold base_56 base_57
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((18198385112262447554198951719878713582193194360950043848907411919888800699475 : Nat) : Fp))⁻¹ = ((90836753867375469229442351633618817876216041762475391584924760682172756140730 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((18198385112262447554198951719878713582193194360950043848907411919888800699475 : Nat) : Fp))⁻¹ = ((90836753867375469229442351633618817876216041762475391584924760682172756140730 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_57 : affineAdd base_57 base_57 = base_58 := by
  unfold base_57 base_58
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((12575192387335088647665557233642046097109374697403005848728748607053249552642 : Nat) : Fp))⁻¹ = ((80620560116683287806687775389359374741060516464963580025500203085996474972422 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((12575192387335088647665557233642046097109374697403005848728748607053249552642 : Nat) : Fp))⁻¹ = ((80620560116683287806687775389359374741060516464963580025500203085996474972422 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_58 : affineAdd base_58 base_58 = base_59 := by
  unfold base_58 base_59
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((110309842344688524387480953361916993633315112298643725699639662741987291457779 : Nat) : Fp))⁻¹ = ((10632783341377469158564208899787773401911307362728571115738705179131840983318 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((110309842344688524387480953361916993633315112298643725699639662741987291457779 : Nat) : Fp))⁻¹ = ((10632783341377469158564208899787773401911307362728571115738705179131840983318 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_59 : affineAdd base_59 base_59 = base_60 := by
  unfold base_59 base_60
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((98850328278678552505680434968308156848819817765906617232115049710824480247537 : Nat) : Fp))⁻¹ = ((90208998511357430236337265098979800703895018142489840386481987289273803352994 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((98850328278678552505680434968308156848819817765906617232115049710824480247537 : Nat) : Fp))⁻¹ = ((90208998511357430236337265098979800703895018142489840386481987289273803352994 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_60 : affineAdd base_60 base_60 = base_61 := by
  unfold base_60 base_61
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((56314320032835626861988128097937936814282839310958875562434488369232472187232 : Nat) : Fp))⁻¹ = ((107516586000591496205377439523050091893433054681172392326665943978026117146915 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((56314320032835626861988128097937936814282839310958875562434488369232472187232 : Nat) : Fp))⁻¹ = ((107516586000591496205377439523050091893433054681172392326665943978026117146915 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_61 : affineAdd base_61 base_61 = base_62 := by
  unfold base_61 base_62
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((11720516568179571270476509769942606239875063370184749544905787775519145474236 : Nat) : Fp))⁻¹ = ((105656090841607129356561540090181137324229703769484410075957045219840127971459 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((11720516568179571270476509769942606239875063370184749544905787775519145474236 : Nat) : Fp))⁻¹ = ((105656090841607129356561540090181137324229703769484410075957045219840127971459 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_62 : affineAdd base_62 base_62 = base_63 := by
  unfold base_62 base_63
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((113088070675147226411797488422007342957654795984396137910695709288095002042967 : Nat) : Fp))⁻¹ = ((91145409967385660760431821748342605080106907240688377665650467028260265433301 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((113088070675147226411797488422007342957654795984396137910695709288095002042967 : Nat) : Fp))⁻¹ = ((91145409967385660760431821748342605080106907240688377665650467028260265433301 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_63 : affineAdd base_63 base_63 = base_64 := by
  unfold base_63 base_64
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((61440383708720907418547117747158586276459762378915736297042955400063318409160 : Nat) : Fp))⁻¹ = ((6684766579291501919531345988428271283749277944974710722711731404933340729572 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((61440383708720907418547117747158586276459762378915736297042955400063318409160 : Nat) : Fp))⁻¹ = ((6684766579291501919531345988428271283749277944974710722711731404933340729572 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_64 : affineAdd base_64 base_64 = base_65 := by
  unfold base_64 base_65
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((39307099057880941662675806615359097347682728603444928455093651353540932186784 : Nat) : Fp))⁻¹ = ((72565937560411586278144942110622939907435419338699071538754293420451858787222 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((39307099057880941662675806615359097347682728603444928455093651353540932186784 : Nat) : Fp))⁻¹ = ((72565937560411586278144942110622939907435419338699071538754293420451858787222 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_65 : affineAdd base_65 base_65 = base_66 := by
  unfold base_65 base_66
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((106712674239183055714747170770237410600716249238757184591428740534726428083980 : Nat) : Fp))⁻¹ = ((29649323624749799141756045878473681987876264272874116621882989500711197316170 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((106712674239183055714747170770237410600716249238757184591428740534726428083980 : Nat) : Fp))⁻¹ = ((29649323624749799141756045878473681987876264272874116621882989500711197316170 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_66 : affineAdd base_66 base_66 = base_67 := by
  unfold base_66 base_67
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((62697784033925076403474224442689974679135179320309080987220280194454804723717 : Nat) : Fp))⁻¹ = ((38770960299848144179787015075784337937396745241442450977761671054901674181013 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((62697784033925076403474224442689974679135179320309080987220280194454804723717 : Nat) : Fp))⁻¹ = ((38770960299848144179787015075784337937396745241442450977761671054901674181013 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_67 : affineAdd base_67 base_67 = base_68 := by
  unfold base_67 base_68
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((42168706312448760835164198288963124085049274787903511949048046806853155067687 : Nat) : Fp))⁻¹ = ((103414269535246809082782116824664963015586171962762620665429691919538954678199 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((42168706312448760835164198288963124085049274787903511949048046806853155067687 : Nat) : Fp))⁻¹ = ((103414269535246809082782116824664963015586171962762620665429691919538954678199 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_68 : affineAdd base_68 base_68 = base_69 := by
  unfold base_68 base_69
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((56214196748543440839296827556230703893730514912272645534922309181995758064550 : Nat) : Fp))⁻¹ = ((80803609355590347763268130817734028664131108784988638942280975716330971002837 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((56214196748543440839296827556230703893730514912272645534922309181995758064550 : Nat) : Fp))⁻¹ = ((80803609355590347763268130817734028664131108784988638942280975716330971002837 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_69 : affineAdd base_69 base_69 = base_70 := by
  unfold base_69 base_70
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((96542930188656188775421614396743163957109245800132742492178822512944546868854 : Nat) : Fp))⁻¹ = ((12284654286731931685886773591027627927048609565674316637923950040250782284959 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((96542930188656188775421614396743163957109245800132742492178822512944546868854 : Nat) : Fp))⁻¹ = ((12284654286731931685886773591027627927048609565674316637923950040250782284959 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_70 : affineAdd base_70 base_70 = base_71 := by
  unfold base_70 base_71
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((52712462544684042050659798408142998446211290189326915216568750458192003482817 : Nat) : Fp))⁻¹ = ((50312712865385256976860191223485414307925595845625045102076699230974150627664 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((52712462544684042050659798408142998446211290189326915216568750458192003482817 : Nat) : Fp))⁻¹ = ((50312712865385256976860191223485414307925595845625045102076699230974150627664 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_71 : affineAdd base_71 base_71 = base_72 := by
  unfold base_71 base_72
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((19748635217315891647321224482939896170227416763285583086520508401939213234176 : Nat) : Fp))⁻¹ = ((90424656058714300436829333961013658899666862202576316346282489017635645161115 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((19748635217315891647321224482939896170227416763285583086520508401939213234176 : Nat) : Fp))⁻¹ = ((90424656058714300436829333961013658899666862202576316346282489017635645161115 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_72 : affineAdd base_72 base_72 = base_73 := by
  unfold base_72 base_73
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((37834176166477149356292507688627259926034564110824553771704962901036071708041 : Nat) : Fp))⁻¹ = ((110760724313061912205263332674806977153850210988866226783204024328952813297889 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((37834176166477149356292507688627259926034564110824553771704962901036071708041 : Nat) : Fp))⁻¹ = ((110760724313061912205263332674806977153850210988866226783204024328952813297889 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_73 : affineAdd base_73 base_73 = base_74 := by
  unfold base_73 base_74
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((110851835063999899423756612638945142128964968911486626329802042725525613408346 : Nat) : Fp))⁻¹ = ((70591011094199581301961906701507646511405654972092096864213622036746016167570 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((110851835063999899423756612638945142128964968911486626329802042725525613408346 : Nat) : Fp))⁻¹ = ((70591011094199581301961906701507646511405654972092096864213622036746016167570 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_74 : affineAdd base_74 base_74 = base_75 := by
  unfold base_74 base_75
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((30572655366218421290699322537451162244586583424941183840353131006508265175422 : Nat) : Fp))⁻¹ = ((12657639649331111550860932576388350948050150395244019767768149200313742570561 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((30572655366218421290699322537451162244586583424941183840353131006508265175422 : Nat) : Fp))⁻¹ = ((12657639649331111550860932576388350948050150395244019767768149200313742570561 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_75 : affineAdd base_75 base_75 = base_76 := by
  unfold base_75 base_76
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((77751573448339894342899057498199969560748665539929390648020324044053699567908 : Nat) : Fp))⁻¹ = ((91134237738523056165135191063710277891440438574863350932511092811702496505168 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((77751573448339894342899057498199969560748665539929390648020324044053699567908 : Nat) : Fp))⁻¹ = ((91134237738523056165135191063710277891440438574863350932511092811702496505168 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_76 : affineAdd base_76 base_76 = base_77 := by
  unfold base_76 base_77
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((85115484315990908818625714664072075837750502822084508644932753849460649668119 : Nat) : Fp))⁻¹ = ((31885309985337588351391731029522654472407690554454615901563409587253212993043 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((85115484315990908818625714664072075837750502822084508644932753849460649668119 : Nat) : Fp))⁻¹ = ((31885309985337588351391731029522654472407690554454615901563409587253212993043 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_77 : affineAdd base_77 base_77 = base_78 := by
  unfold base_77 base_78
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((40065985632112285488262829097473122728635230343056068824717075042107181358448 : Nat) : Fp))⁻¹ = ((37929894006605773555066595987413265637084799339376102761981147964518198692863 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((40065985632112285488262829097473122728635230343056068824717075042107181358448 : Nat) : Fp))⁻¹ = ((37929894006605773555066595987413265637084799339376102761981147964518198692863 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_78 : affineAdd base_78 base_78 = base_79 := by
  unfold base_78 base_79
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((106228226569454347670647985876151839080805653229947291906912035484638171537232 : Nat) : Fp))⁻¹ = ((113550177652601947115672154348603738235193171738805270679125180927860266308527 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((106228226569454347670647985876151839080805653229947291906912035484638171537232 : Nat) : Fp))⁻¹ = ((113550177652601947115672154348603738235193171738805270679125180927860266308527 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_79 : affineAdd base_79 base_79 = base_80 := by
  unfold base_79 base_80
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((34361801916858031928794980991103430340262038618413794433537084872221158631519 : Nat) : Fp))⁻¹ = ((26426161892929359772349997340017873199082250795468309409673538501231747130082 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((34361801916858031928794980991103430340262038618413794433537084872221158631519 : Nat) : Fp))⁻¹ = ((26426161892929359772349997340017873199082250795468309409673538501231747130082 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_80 : affineAdd base_80 base_80 = base_81 := by
  unfold base_80 base_81
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((31409815155472435338582344935230131320197144774427706287861757740924066421722 : Nat) : Fp))⁻¹ = ((16650433690548269754352775892013701894418266540680710903118227839602489342474 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((31409815155472435338582344935230131320197144774427706287861757740924066421722 : Nat) : Fp))⁻¹ = ((16650433690548269754352775892013701894418266540680710903118227839602489342474 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_81 : affineAdd base_81 base_81 = base_82 := by
  unfold base_81 base_82
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((4325061896769276104913772732319997098916385262805927028161444887858874342220 : Nat) : Fp))⁻¹ = ((97935884232111770798127857874616930232163929045925634346097202263205373092596 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((4325061896769276104913772732319997098916385262805927028161444887858874342220 : Nat) : Fp))⁻¹ = ((97935884232111770798127857874616930232163929045925634346097202263205373092596 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_82 : affineAdd base_82 base_82 = base_83 := by
  unfold base_82 base_83
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((59169763974292048230483290348723286025776147993831754859145423822145515799140 : Nat) : Fp))⁻¹ = ((66270473285970161642294097898558707766416613733594240607009421269953743934732 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((59169763974292048230483290348723286025776147993831754859145423822145515799140 : Nat) : Fp))⁻¹ = ((66270473285970161642294097898558707766416613733594240607009421269953743934732 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_83 : affineAdd base_83 base_83 = base_84 := by
  unfold base_83 base_84
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((23027132854424541515521319202161519225460618376982276335759008484746030223405 : Nat) : Fp))⁻¹ = ((42754994800955249135784887318242078507962522008067683572130944757750202022010 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((23027132854424541515521319202161519225460618376982276335759008484746030223405 : Nat) : Fp))⁻¹ = ((42754994800955249135784887318242078507962522008067683572130944757750202022010 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_84 : affineAdd base_84 base_84 = base_85 := by
  unfold base_84 base_85
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((55437542190981407452923664626193149136100172061209688271244666364673120940509 : Nat) : Fp))⁻¹ = ((15901318517183596931799984803216628008529929163489017842435080696422179071494 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((55437542190981407452923664626193149136100172061209688271244666364673120940509 : Nat) : Fp))⁻¹ = ((15901318517183596931799984803216628008529929163489017842435080696422179071494 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_85 : affineAdd base_85 base_85 = base_86 := by
  unfold base_85 base_86
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((33193850663848721154507883351096416412681014543344176760472364118972599175560 : Nat) : Fp))⁻¹ = ((77817661071334103373009329410738973727106829188641526900365383520613177419920 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((33193850663848721154507883351096416412681014543344176760472364118972599175560 : Nat) : Fp))⁻¹ = ((77817661071334103373009329410738973727106829188641526900365383520613177419920 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_86 : affineAdd base_86 base_86 = base_87 := by
  unfold base_86 base_87
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((18507121058431491916818312533740360825972223949528183085794866203720624591878 : Nat) : Fp))⁻¹ = ((37391820538358660466700611737651654126758241012003252982425612720863793409015 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((18507121058431491916818312533740360825972223949528183085794866203720624591878 : Nat) : Fp))⁻¹ = ((37391820538358660466700611737651654126758241012003252982425612720863793409015 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_87 : affineAdd base_87 base_87 = base_88 := by
  unfold base_87 base_88
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((57448470377652821134170456021628327741101079070106580787911301709526093883982 : Nat) : Fp))⁻¹ = ((28659962906369973581703631764562413930747719333354382441858682115041243767742 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((57448470377652821134170456021628327741101079070106580787911301709526093883982 : Nat) : Fp))⁻¹ = ((28659962906369973581703631764562413930747719333354382441858682115041243767742 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_88 : affineAdd base_88 base_88 = base_89 := by
  unfold base_88 base_89
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((34117244282055289120898203738790815580918088000686828227920818069382230202610 : Nat) : Fp))⁻¹ = ((111696899933601246728452174116007407814308456025667830051630800064547955781508 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((34117244282055289120898203738790815580918088000686828227920818069382230202610 : Nat) : Fp))⁻¹ = ((111696899933601246728452174116007407814308456025667830051630800064547955781508 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_89 : affineAdd base_89 base_89 = base_90 := by
  unfold base_89 base_90
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((36179658746250976381135601610242632021826214896264269021914509495791394149615 : Nat) : Fp))⁻¹ = ((48904868557548223206329220233664448400697404135414412915151154709129062890326 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((36179658746250976381135601610242632021826214896264269021914509495791394149615 : Nat) : Fp))⁻¹ = ((48904868557548223206329220233664448400697404135414412915151154709129062890326 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_90 : affineAdd base_90 base_90 = base_91 := by
  unfold base_90 base_91
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((6359760100839187210073863293870527713027761135409961108195017073136576674018 : Nat) : Fp))⁻¹ = ((71525176566794638245036005993668858413248039178049368275672736751086976638066 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((6359760100839187210073863293870527713027761135409961108195017073136576674018 : Nat) : Fp))⁻¹ = ((71525176566794638245036005993668858413248039178049368275672736751086976638066 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_91 : affineAdd base_91 base_91 = base_92 := by
  unfold base_91 base_92
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((77218777772268311707719666397699916259759523817816920080352731398095643624469 : Nat) : Fp))⁻¹ = ((57126796608899904657833784384661655195738012539642886435447422692489066155935 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((77218777772268311707719666397699916259759523817816920080352731398095643624469 : Nat) : Fp))⁻¹ = ((57126796608899904657833784384661655195738012539642886435447422692489066155935 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_92 : affineAdd base_92 base_92 = base_93 := by
  unfold base_92 base_93
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((10609229642071556953120109475763397943884016840919846757331088165175050414822 : Nat) : Fp))⁻¹ = ((91749241804753055609019463716202175052873219191759774187787859011802359508088 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((10609229642071556953120109475763397943884016840919846757331088165175050414822 : Nat) : Fp))⁻¹ = ((91749241804753055609019463716202175052873219191759774187787859011802359508088 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_93 : affineAdd base_93 base_93 = base_94 := by
  unfold base_93 base_94
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((30612701817593165310829908596077980446317954217062442246601062375597549071147 : Nat) : Fp))⁻¹ = ((83934606244455918206660902029180225598437326019140040184347642562079867045569 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((30612701817593165310829908596077980446317954217062442246601062375597549071147 : Nat) : Fp))⁻¹ = ((83934606244455918206660902029180225598437326019140040184347642562079867045569 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_94 : affineAdd base_94 base_94 = base_95 := by
  unfold base_94 base_95
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((83317154179385276448599698389111199063686628672572418790396772309007183470821 : Nat) : Fp))⁻¹ = ((38489606593270990756961710412972636594498180657431574093213878775370348293257 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((83317154179385276448599698389111199063686628672572418790396772309007183470821 : Nat) : Fp))⁻¹ = ((38489606593270990756961710412972636594498180657431574093213878775370348293257 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_95 : affineAdd base_95 base_95 = base_96 := by
  unfold base_95 base_96
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((80886292560052078022819942209443457651640717456431378184925170018374473757441 : Nat) : Fp))⁻¹ = ((87022748238913688867578852756896253167203795685820514907171482210966863910123 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((80886292560052078022819942209443457651640717456431378184925170018374473757441 : Nat) : Fp))⁻¹ = ((87022748238913688867578852756896253167203795685820514907171482210966863910123 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_96 : affineAdd base_96 base_96 = base_97 := by
  unfold base_96 base_97
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((49763971281659542105744668679966078286699279184665337082856648066049033156975 : Nat) : Fp))⁻¹ = ((53397333918399712538976549681440857307829631764998269319871412827098573763773 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((49763971281659542105744668679966078286699279184665337082856648066049033156975 : Nat) : Fp))⁻¹ = ((53397333918399712538976549681440857307829631764998269319871412827098573763773 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_97 : affineAdd base_97 base_97 = base_98 := by
  unfold base_97 base_98
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((27927879468288414295198600435976090224174968562527111521940172877594627850158 : Nat) : Fp))⁻¹ = ((103452393820390493467570899463276013263485227387725395507202263298431629553972 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((27927879468288414295198600435976090224174968562527111521940172877594627850158 : Nat) : Fp))⁻¹ = ((103452393820390493467570899463276013263485227387725395507202263298431629553972 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_98 : affineAdd base_98 base_98 = base_99 := by
  unfold base_98 base_99
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((57811541833390055306833565592598106401230808311112346834369084436570498753337 : Nat) : Fp))⁻¹ = ((99129241769717217257938762702184132693736854935932857056839522515115194474016 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((57811541833390055306833565592598106401230808311112346834369084436570498753337 : Nat) : Fp))⁻¹ = ((99129241769717217257938762702184132693736854935932857056839522515115194474016 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_99 : affineAdd base_99 base_99 = base_100 := by
  unfold base_99 base_100
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((87592962133464766467334907348498449098375430086853996682723463167279731306372 : Nat) : Fp))⁻¹ = ((57158194155139764605786271739428792855613059603528698700647058207248391029280 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((87592962133464766467334907348498449098375430086853996682723463167279731306372 : Nat) : Fp))⁻¹ = ((57158194155139764605786271739428792855613059603528698700647058207248391029280 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_100 : affineAdd base_100 base_100 = base_101 := by
  unfold base_100 base_101
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((90939394492963130914544575569526310734855569061258844327812366475243930364929 : Nat) : Fp))⁻¹ = ((8775045788693489662334433579251645767006616838252080153249085287083561771320 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((90939394492963130914544575569526310734855569061258844327812366475243930364929 : Nat) : Fp))⁻¹ = ((8775045788693489662334433579251645767006616838252080153249085287083561771320 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_101 : affineAdd base_101 base_101 = base_102 := by
  unfold base_101 base_102
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((70349280139070181932538936546431771279420426752065163651109781251026950404544 : Nat) : Fp))⁻¹ = ((62231720846315800863262315627981968558536272964987618321811863823966100538150 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((70349280139070181932538936546431771279420426752065163651109781251026950404544 : Nat) : Fp))⁻¹ = ((62231720846315800863262315627981968558536272964987618321811863823966100538150 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_102 : affineAdd base_102 base_102 = base_103 := by
  unfold base_102 base_103
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((18493885180880533479983549127533520654731835271435443031664047750964210440946 : Nat) : Fp))⁻¹ = ((16280702300127334455250540590884632284722671312937613212856593442267194187787 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((18493885180880533479983549127533520654731835271435443031664047750964210440946 : Nat) : Fp))⁻¹ = ((16280702300127334455250540590884632284722671312937613212856593442267194187787 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_103 : affineAdd base_103 base_103 = base_104 := by
  unfold base_103 base_104
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((3399478885375643092936720555036030158803236931787480448997057703838011734762 : Nat) : Fp))⁻¹ = ((19854382153619828709887284467843992416440107266068648054610761943413198609358 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((3399478885375643092936720555036030158803236931787480448997057703838011734762 : Nat) : Fp))⁻¹ = ((19854382153619828709887284467843992416440107266068648054610761943413198609358 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_104 : affineAdd base_104 base_104 = base_105 := by
  unfold base_104 base_105
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((62079424087973467789382713581435573708404480254567931314506333392316481045699 : Nat) : Fp))⁻¹ = ((53434238516092890774549965945385635268640299945063397813869311132930798787326 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((62079424087973467789382713581435573708404480254567931314506333392316481045699 : Nat) : Fp))⁻¹ = ((53434238516092890774549965945385635268640299945063397813869311132930798787326 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_105 : affineAdd base_105 base_105 = base_106 := by
  unfold base_105 base_106
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((104083246136889829683331969264423162114671872108616362771383171554424986219793 : Nat) : Fp))⁻¹ = ((76081385323224142425370141548114690373020511082766012646387714789729099481485 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((104083246136889829683331969264423162114671872108616362771383171554424986219793 : Nat) : Fp))⁻¹ = ((76081385323224142425370141548114690373020511082766012646387714789729099481485 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_106 : affineAdd base_106 base_106 = base_107 := by
  unfold base_106 base_107
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((32924494876951284146279766638563025708747643322813908934636585593423158017785 : Nat) : Fp))⁻¹ = ((12660328383668567949357803018449260784641514062655416237203819194961267635094 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((32924494876951284146279766638563025708747643322813908934636585593423158017785 : Nat) : Fp))⁻¹ = ((12660328383668567949357803018449260784641514062655416237203819194961267635094 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_107 : affineAdd base_107 base_107 = base_108 := by
  unfold base_107 base_108
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((5210361221244717547856165246556020619071402127820810229408988718584663707749 : Nat) : Fp))⁻¹ = ((24855182191007332907186014446108259465858828128513639846836811748395566569906 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((5210361221244717547856165246556020619071402127820810229408988718584663707749 : Nat) : Fp))⁻¹ = ((24855182191007332907186014446108259465858828128513639846836811748395566569906 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_108 : affineAdd base_108 base_108 = base_109 := by
  unfold base_108 base_109
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((115226106161721418677257600232626422670483402750299325766423254986581008554271 : Nat) : Fp))⁻¹ = ((53876040240761927502356483452915022400648124516463607182766152010213654865991 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((115226106161721418677257600232626422670483402750299325766423254986581008554271 : Nat) : Fp))⁻¹ = ((53876040240761927502356483452915022400648124516463607182766152010213654865991 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_109 : affineAdd base_109 base_109 = base_110 := by
  unfold base_109 base_110
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((15176610360357502916376731715182826626094867832295623397483794147117662068209 : Nat) : Fp))⁻¹ = ((35255965090034737547962211356273236041217698813987341008174632904326325680490 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((15176610360357502916376731715182826626094867832295623397483794147117662068209 : Nat) : Fp))⁻¹ = ((35255965090034737547962211356273236041217698813987341008174632904326325680490 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_110 : affineAdd base_110 base_110 = base_111 := by
  unfold base_110 base_111
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((24813777388505064074621970457041023547619648696034102349374362496379715467175 : Nat) : Fp))⁻¹ = ((67433181658134480107323533054426641541516977011518440416355480768371923960477 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((24813777388505064074621970457041023547619648696034102349374362496379715467175 : Nat) : Fp))⁻¹ = ((67433181658134480107323533054426641541516977011518440416355480768371923960477 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_111 : affineAdd base_111 base_111 = base_112 := by
  unfold base_111 base_112
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((29197166736887483563928586983131420527850770453920557715930559189098823391124 : Nat) : Fp))⁻¹ = ((52628995433557552761471996081999028967817784211757603148039707231929102825300 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((29197166736887483563928586983131420527850770453920557715930559189098823391124 : Nat) : Fp))⁻¹ = ((52628995433557552761471996081999028967817784211757603148039707231929102825300 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_112 : affineAdd base_112 base_112 = base_113 := by
  unfold base_112 base_113
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((18101124850041158815009009485735144088925930424123803647507665853537289369319 : Nat) : Fp))⁻¹ = ((26169101932432248498763785405477960291993680118251153113234298043757820686491 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((18101124850041158815009009485735144088925930424123803647507665853537289369319 : Nat) : Fp))⁻¹ = ((26169101932432248498763785405477960291993680118251153113234298043757820686491 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_113 : affineAdd base_113 base_113 = base_114 := by
  unfold base_113 base_114
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((103456599417569656329743525842643406894367321159609200220648758243892831845501 : Nat) : Fp))⁻¹ = ((65073390432971498835788735267013495655074023699783109482260142092872379506172 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((103456599417569656329743525842643406894367321159609200220648758243892831845501 : Nat) : Fp))⁻¹ = ((65073390432971498835788735267013495655074023699783109482260142092872379506172 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_114 : affineAdd base_114 base_114 = base_115 := by
  unfold base_114 base_115
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((84487769519853421430030359463214449378435630494204186353059369760950916380835 : Nat) : Fp))⁻¹ = ((71533581448252230470419535409174837586992342724715195599504441942587392887734 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((84487769519853421430030359463214449378435630494204186353059369760950916380835 : Nat) : Fp))⁻¹ = ((71533581448252230470419535409174837586992342724715195599504441942587392887734 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_115 : affineAdd base_115 base_115 = base_116 := by
  unfold base_115 base_116
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((35080546347367598434982768185387546912732524650521251475529423425038042189569 : Nat) : Fp))⁻¹ = ((107205519452293484380957454972014315548772977561492065945827103674279823462067 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((35080546347367598434982768185387546912732524650521251475529423425038042189569 : Nat) : Fp))⁻¹ = ((107205519452293484380957454972014315548772977561492065945827103674279823462067 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_116 : affineAdd base_116 base_116 = base_117 := by
  unfold base_116 base_117
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((108021264621442630025722058757308611603027665565497116827018930375054827580536 : Nat) : Fp))⁻¹ = ((46141791300012967013372339762908569420336999141677374507997362586655105786919 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((108021264621442630025722058757308611603027665565497116827018930375054827580536 : Nat) : Fp))⁻¹ = ((46141791300012967013372339762908569420336999141677374507997362586655105786919 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_117 : affineAdd base_117 base_117 = base_118 := by
  unfold base_117 base_118
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((75438522668351783504686245637900335802808862903871170538716693983846568968011 : Nat) : Fp))⁻¹ = ((45369716159865384049412780986729320517540521541543264238893001335571307271448 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((75438522668351783504686245637900335802808862903871170538716693983846568968011 : Nat) : Fp))⁻¹ = ((45369716159865384049412780986729320517540521541543264238893001335571307271448 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_118 : affineAdd base_118 base_118 = base_119 := by
  unfold base_118 base_119
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((29241751855199681568367284518448893439960716762286924487213503019678103002705 : Nat) : Fp))⁻¹ = ((61122162253213386931926037090406653553702346918627831514702726323208397534575 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((29241751855199681568367284518448893439960716762286924487213503019678103002705 : Nat) : Fp))⁻¹ = ((61122162253213386931926037090406653553702346918627831514702726323208397534575 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_119 : affineAdd base_119 base_119 = base_120 := by
  unfold base_119 base_120
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((106007349317296939888635500379499007381281650903559653902304432927687101375981 : Nat) : Fp))⁻¹ = ((67700923689077989832031242971377792445767393760075123552657073690778763679567 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((106007349317296939888635500379499007381281650903559653902304432927687101375981 : Nat) : Fp))⁻¹ = ((67700923689077989832031242971377792445767393760075123552657073690778763679567 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_120 : affineAdd base_120 base_120 = base_121 := by
  unfold base_120 base_121
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((52215583774525796109567946288556659634043653399932078971590626905269875474081 : Nat) : Fp))⁻¹ = ((96380816540426150839055885644631749418327216786533098371775546825440740149282 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((52215583774525796109567946288556659634043653399932078971590626905269875474081 : Nat) : Fp))⁻¹ = ((96380816540426150839055885644631749418327216786533098371775546825440740149282 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_121 : affineAdd base_121 base_121 = base_122 := by
  unfold base_121 base_122
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((22183031661069407114947469617732171225545226302519288081136966780058091537843 : Nat) : Fp))⁻¹ = ((107728471541494102845311003198055450681698417477747823502896472241831487442254 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((22183031661069407114947469617732171225545226302519288081136966780058091537843 : Nat) : Fp))⁻¹ = ((107728471541494102845311003198055450681698417477747823502896472241831487442254 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_122 : affineAdd base_122 base_122 = base_123 := by
  unfold base_122 base_123
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((33195971463859634916825320647431346032578912048614106257629795755556424999572 : Nat) : Fp))⁻¹ = ((39779815809878241690303277855062758431540942356656330805746453765638575030327 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((33195971463859634916825320647431346032578912048614106257629795755556424999572 : Nat) : Fp))⁻¹ = ((39779815809878241690303277855062758431540942356656330805746453765638575030327 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_123 : affineAdd base_123 base_123 = base_124 := by
  unfold base_123 base_124
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((11458489637841101089267453881300170307046154505862838558859267626137645974850 : Nat) : Fp))⁻¹ = ((8347531059383747235123288222141117943636336545099628114066970834822767651801 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((11458489637841101089267453881300170307046154505862838558859267626137645974850 : Nat) : Fp))⁻¹ = ((8347531059383747235123288222141117943636336545099628114066970834822767651801 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_124 : affineAdd base_124 base_124 = base_125 := by
  unfold base_124 base_125
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((6474571117676685817754405485757825849845707811112126411536249919905291235664 : Nat) : Fp))⁻¹ = ((1501478383692426852441570332914858290211702692457641832263238247986685686868 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((6474571117676685817754405485757825849845707811112126411536249919905291235664 : Nat) : Fp))⁻¹ = ((1501478383692426852441570332914858290211702692457641832263238247986685686868 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_125 : affineAdd base_125 base_125 = base_126 := by
  unfold base_125 base_126
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((65294641003401362594966851216569681914884202591426370350835007421691752226503 : Nat) : Fp))⁻¹ = ((64800232155687266566513313202346384067174415019059719487148839156561851895865 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((65294641003401362594966851216569681914884202591426370350835007421691752226503 : Nat) : Fp))⁻¹ = ((64800232155687266566513313202346384067174415019059719487148839156561851895865 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_126 : affineAdd base_126 base_126 = base_127 := by
  unfold base_126 base_127
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((74931287229039237066253562221237323976647082407514979153759017931296701314826 : Nat) : Fp))⁻¹ = ((44193909745205392493310540874863803894055661424824686226295673845872373765481 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((74931287229039237066253562221237323976647082407514979153759017931296701314826 : Nat) : Fp))⁻¹ = ((44193909745205392493310540874863803894055661424824686226295673845872373765481 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_127 : affineAdd base_127 base_127 = base_128 := by
  unfold base_127 base_128
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((40252511218087247830580930812776238463499994792031801540758272438053921180247 : Nat) : Fp))⁻¹ = ((43067036975690112588005065852232531417875779385756880169590435378832629560766 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((40252511218087247830580930812776238463499994792031801540758272438053921180247 : Nat) : Fp))⁻¹ = ((43067036975690112588005065852232531417875779385756880169590435378832629560766 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_128 : affineAdd base_128 base_128 = base_129 := by
  unfold base_128 base_129
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((46211216742671250426576585530459394900178019437443360579906162037052661563266 : Nat) : Fp))⁻¹ = ((88675795099902803966670219792965272448751336084793157573210232065396013444497 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((46211216742671250426576585530459394900178019437443360579906162037052661563266 : Nat) : Fp))⁻¹ = ((88675795099902803966670219792965272448751336084793157573210232065396013444497 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_129 : affineAdd base_129 base_129 = base_130 := by
  unfold base_129 base_130
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((92814217969284136468346182500006122495187572087944979217112043851363214063646 : Nat) : Fp))⁻¹ = ((37477128567372209803710470557004474850132392451661021400338195666977803428861 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((92814217969284136468346182500006122495187572087944979217112043851363214063646 : Nat) : Fp))⁻¹ = ((37477128567372209803710470557004474850132392451661021400338195666977803428861 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_130 : affineAdd base_130 base_130 = base_131 := by
  unfold base_130 base_131
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((87675404738916139099090938273911264414778058285600924992648328889621933853939 : Nat) : Fp))⁻¹ = ((47177408909056912191016969891395795607674346560362038848050888030357645247849 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((87675404738916139099090938273911264414778058285600924992648328889621933853939 : Nat) : Fp))⁻¹ = ((47177408909056912191016969891395795607674346560362038848050888030357645247849 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_131 : affineAdd base_131 base_131 = base_132 := by
  unfold base_131 base_132
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((46613147883270029947538528514141525607759085017677379708440701301821571539505 : Nat) : Fp))⁻¹ = ((111007777565745198015423655915359471223779648364122935631441231811311000359137 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((46613147883270029947538528514141525607759085017677379708440701301821571539505 : Nat) : Fp))⁻¹ = ((111007777565745198015423655915359471223779648364122935631441231811311000359137 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_132 : affineAdd base_132 base_132 = base_133 := by
  unfold base_132 base_133
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((13744988175479693349153508932944119281940564264745175840075269177938566411196 : Nat) : Fp))⁻¹ = ((74082198615072439996282521659147609003944231490698419223657929223423074229650 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((13744988175479693349153508932944119281940564264745175840075269177938566411196 : Nat) : Fp))⁻¹ = ((74082198615072439996282521659147609003944231490698419223657929223423074229650 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_133 : affineAdd base_133 base_133 = base_134 := by
  unfold base_133 base_134
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((52818492011674921634940119787779214367302340414675558363211486292657494734263 : Nat) : Fp))⁻¹ = ((41477844186977630377960092136593500973621171350396095314125694343266764665774 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((52818492011674921634940119787779214367302340414675558363211486292657494734263 : Nat) : Fp))⁻¹ = ((41477844186977630377960092136593500973621171350396095314125694343266764665774 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_134 : affineAdd base_134 base_134 = base_135 := by
  unfold base_134 base_135
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((33517309963374711058233805017888397313880557032455674904311603088567752722188 : Nat) : Fp))⁻¹ = ((29026560257006811268930710719701727412968902421817452688171240382650553999354 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((33517309963374711058233805017888397313880557032455674904311603088567752722188 : Nat) : Fp))⁻¹ = ((29026560257006811268930710719701727412968902421817452688171240382650553999354 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_135 : affineAdd base_135 base_135 = base_136 := by
  unfold base_135 base_136
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((57461221252293229523075183660643751795445411566005575478984600070226388935166 : Nat) : Fp))⁻¹ = ((74688279179114431350131045005881871174299886566748071200171283828577990688466 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((57461221252293229523075183660643751795445411566005575478984600070226388935166 : Nat) : Fp))⁻¹ = ((74688279179114431350131045005881871174299886566748071200171283828577990688466 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_136 : affineAdd base_136 base_136 = base_137 := by
  unfold base_136 base_137
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((108393323332799615882600625899672562866564791265938552990560624893577369108811 : Nat) : Fp))⁻¹ = ((21994996243093739698288898726464105273585010912297899873158095858833603215380 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((108393323332799615882600625899672562866564791265938552990560624893577369108811 : Nat) : Fp))⁻¹ = ((21994996243093739698288898726464105273585010912297899873158095858833603215380 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_137 : affineAdd base_137 base_137 = base_138 := by
  unfold base_137 base_138
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((106745057410625224717707804586771450297805286348157954948730939917388737042539 : Nat) : Fp))⁻¹ = ((53339260907829478031439983526479722436735598324310568893848439784233515918341 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((106745057410625224717707804586771450297805286348157954948730939917388737042539 : Nat) : Fp))⁻¹ = ((53339260907829478031439983526479722436735598324310568893848439784233515918341 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_138 : affineAdd base_138 base_138 = base_139 := by
  unfold base_138 base_139
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((83923066471392572458821227876885635434639856986135936389815903323954601786918 : Nat) : Fp))⁻¹ = ((87891553017889705515934817624293402184508234240702250846103155349584504284808 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((83923066471392572458821227876885635434639856986135936389815903323954601786918 : Nat) : Fp))⁻¹ = ((87891553017889705515934817624293402184508234240702250846103155349584504284808 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_139 : affineAdd base_139 base_139 = base_140 := by
  unfold base_139 base_140
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((107099881035735432711210408988501874747725935128038800415340434399284629514586 : Nat) : Fp))⁻¹ = ((100053005035945955081197776932291858734007497167239388672301406426497015659103 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((107099881035735432711210408988501874747725935128038800415340434399284629514586 : Nat) : Fp))⁻¹ = ((100053005035945955081197776932291858734007497167239388672301406426497015659103 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_140 : affineAdd base_140 base_140 = base_141 := by
  unfold base_140 base_141
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((19204842090783572478934763263896016084146536297748178843263225598863834152273 : Nat) : Fp))⁻¹ = ((105640480285999709787292607771434493298215861196660241144617601626294774353157 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((19204842090783572478934763263896016084146536297748178843263225598863834152273 : Nat) : Fp))⁻¹ = ((105640480285999709787292607771434493298215861196660241144617601626294774353157 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_141 : affineAdd base_141 base_141 = base_142 := by
  unfold base_141 base_142
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((11718140657345423934070547093851147149502657148997117054604879635944084480924 : Nat) : Fp))⁻¹ = ((36190989738151150607634083781076420310442577390066387084463397607258926386742 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((11718140657345423934070547093851147149502657148997117054604879635944084480924 : Nat) : Fp))⁻¹ = ((36190989738151150607634083781076420310442577390066387084463397607258926386742 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_142 : affineAdd base_142 base_142 = base_143 := by
  unfold base_142 base_143
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((60737856123767596328148824409984345799986282506783260172759469126809007188004 : Nat) : Fp))⁻¹ = ((58123620113154935985858940518783240575581308468831909905254243928842460140893 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((60737856123767596328148824409984345799986282506783260172759469126809007188004 : Nat) : Fp))⁻¹ = ((58123620113154935985858940518783240575581308468831909905254243928842460140893 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_143 : affineAdd base_143 base_143 = base_144 := by
  unfold base_143 base_144
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((55135767764556490992818664763424664824858578437374820236794056603342661870707 : Nat) : Fp))⁻¹ = ((13833470373946633435215029600329373805333691599657102299625214468976594030506 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((55135767764556490992818664763424664824858578437374820236794056603342661870707 : Nat) : Fp))⁻¹ = ((13833470373946633435215029600329373805333691599657102299625214468976594030506 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_144 : affineAdd base_144 base_144 = base_145 := by
  unfold base_144 base_145
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((2933900802655320228371872386727285565009607891164205160519475145640485435973 : Nat) : Fp))⁻¹ = ((81503242130832945672322181590183304854482816867403910601147204103968405714389 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((2933900802655320228371872386727285565009607891164205160519475145640485435973 : Nat) : Fp))⁻¹ = ((81503242130832945672322181590183304854482816867403910601147204103968405714389 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_145 : affineAdd base_145 base_145 = base_146 := by
  unfold base_145 base_146
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((35170703879107070397528715355676250246151611539838021540277202550315100054233 : Nat) : Fp))⁻¹ = ((7038538453607005260331044556857054311814001656708564814503780786273634854588 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((35170703879107070397528715355676250246151611539838021540277202550315100054233 : Nat) : Fp))⁻¹ = ((7038538453607005260331044556857054311814001656708564814503780786273634854588 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_146 : affineAdd base_146 base_146 = base_147 := by
  unfold base_146 base_147
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((110695089775790420212275781036515251705109498767909652055725128324950720721559 : Nat) : Fp))⁻¹ = ((55808592197561637339919065836267815975132468673294724556647377875524655472515 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((110695089775790420212275781036515251705109498767909652055725128324950720721559 : Nat) : Fp))⁻¹ = ((55808592197561637339919065836267815975132468673294724556647377875524655472515 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_147 : affineAdd base_147 base_147 = base_148 := by
  unfold base_147 base_148
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((92757387985797433337504154397545024770971021650910819219563990946722655340125 : Nat) : Fp))⁻¹ = ((64762462373691261356486766932107534711033706873330973294497811884834285372631 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((92757387985797433337504154397545024770971021650910819219563990946722655340125 : Nat) : Fp))⁻¹ = ((64762462373691261356486766932107534711033706873330973294497811884834285372631 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_148 : affineAdd base_148 base_148 = base_149 := by
  unfold base_148 base_149
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((99303278877429417088246557868681959316984965013771041163804468621043567898912 : Nat) : Fp))⁻¹ = ((19280093670653264396558844051104127475461286846604128416468895637433042583886 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((99303278877429417088246557868681959316984965013771041163804468621043567898912 : Nat) : Fp))⁻¹ = ((19280093670653264396558844051104127475461286846604128416468895637433042583886 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_149 : affineAdd base_149 base_149 = base_150 := by
  unfold base_149 base_150
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((19112323507498003064396425936166321573933767740378942347221947598633080738522 : Nat) : Fp))⁻¹ = ((24860214045097230171863566808971845209400322430551685406426733637828904633306 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((19112323507498003064396425936166321573933767740378942347221947598633080738522 : Nat) : Fp))⁻¹ = ((24860214045097230171863566808971845209400322430551685406426733637828904633306 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_150 : affineAdd base_150 base_150 = base_151 := by
  unfold base_150 base_151
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((16136664718778354741239915467490083114312845627443806165166400322025562172700 : Nat) : Fp))⁻¹ = ((83065413694612314025444457209884443827495564340564700924649885389791880179928 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((16136664718778354741239915467490083114312845627443806165166400322025562172700 : Nat) : Fp))⁻¹ = ((83065413694612314025444457209884443827495564340564700924649885389791880179928 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_151 : affineAdd base_151 base_151 = base_152 := by
  unfold base_151 base_152
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((69839675855252625382864852692238872585628385971310815662725729943087609430139 : Nat) : Fp))⁻¹ = ((10008302461766507375752932773833754965680891380952375443557990621821383755491 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((69839675855252625382864852692238872585628385971310815662725729943087609430139 : Nat) : Fp))⁻¹ = ((10008302461766507375752932773833754965680891380952375443557990621821383755491 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_152 : affineAdd base_152 base_152 = base_153 := by
  unfold base_152 base_153
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((45475484805375289014292969224159029645777915241785857295305535555664117202052 : Nat) : Fp))⁻¹ = ((16923040770062434958547688634389886958025182711916771194010127319164226140387 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((45475484805375289014292969224159029645777915241785857295305535555664117202052 : Nat) : Fp))⁻¹ = ((16923040770062434958547688634389886958025182711916771194010127319164226140387 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_153 : affineAdd base_153 base_153 = base_154 := by
  unfold base_153 base_154
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((97609736426556728831591583803631233034684715940413408963258107819767740020195 : Nat) : Fp))⁻¹ = ((105951849840165099202661065395443481601814014049860825959586582825692298359681 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((97609736426556728831591583803631233034684715940413408963258107819767740020195 : Nat) : Fp))⁻¹ = ((105951849840165099202661065395443481601814014049860825959586582825692298359681 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_154 : affineAdd base_154 base_154 = base_155 := by
  unfold base_154 base_155
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((63443518936078980928975271049594475518271079655621131486236396265316979810558 : Nat) : Fp))⁻¹ = ((70490598759339497713950438339757372028283309507790751522528747079349754152492 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((63443518936078980928975271049594475518271079655621131486236396265316979810558 : Nat) : Fp))⁻¹ = ((70490598759339497713950438339757372028283309507790751522528747079349754152492 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_155 : affineAdd base_155 base_155 = base_156 := by
  unfold base_155 base_156
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((54981855232630153751619068839379710690392191850677614602646052403990831204099 : Nat) : Fp))⁻¹ = ((14046792899463053326312648058886387485270774003275799769245671858301942329788 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((54981855232630153751619068839379710690392191850677614602646052403990831204099 : Nat) : Fp))⁻¹ = ((14046792899463053326312648058886387485270774003275799769245671858301942329788 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_156 : affineAdd base_156 base_156 = base_157 := by
  unfold base_156 base_157
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((95273891293316720854000721987756315180413338976852308839788251922692115805 : Nat) : Fp))⁻¹ = ((13427491503903251873026281634072277809205990873286978248390143363085062919330 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((95273891293316720854000721987756315180413338976852308839788251922692115805 : Nat) : Fp))⁻¹ = ((13427491503903251873026281634072277809205990873286978248390143363085062919330 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_157 : affineAdd base_157 base_157 = base_158 := by
  unfold base_157 base_158
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((8424212039425668253022291013437891429871302723219086751247826238756909595104 : Nat) : Fp))⁻¹ = ((97732696424925312767327262744066143172266971887692015972241829999371417182642 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((8424212039425668253022291013437891429871302723219086751247826238756909595104 : Nat) : Fp))⁻¹ = ((97732696424925312767327262744066143172266971887692015972241829999371417182642 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_158 : affineAdd base_158 base_158 = base_159 := by
  unfold base_158 base_159
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((78673807004489092854216395411129353437829079224915559696534676000382399098335 : Nat) : Fp))⁻¹ = ((71433535870472601869195784556630344982240328419561520578093829460861825560282 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((78673807004489092854216395411129353437829079224915559696534676000382399098335 : Nat) : Fp))⁻¹ = ((71433535870472601869195784556630344982240328419561520578093829460861825560282 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_159 : affineAdd base_159 base_159 = base_160 := by
  unfold base_159 base_160
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((113911143471074069342269815156022191118395698271153725836799489558703307009470 : Nat) : Fp))⁻¹ = ((1635012395540347103678352208949415792512305712689227181394861803560708856940 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((113911143471074069342269815156022191118395698271153725836799489558703307009470 : Nat) : Fp))⁻¹ = ((1635012395540347103678352208949415792512305712689227181394861803560708856940 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_160 : affineAdd base_160 base_160 = base_161 := by
  unfold base_160 base_161
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((100286785047006832236729389681182172543048508833941702006321829459516874054045 : Nat) : Fp))⁻¹ = ((110003340058946078995870196531013796614728765748384203670656694698327492898307 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((100286785047006832236729389681182172543048508833941702006321829459516874054045 : Nat) : Fp))⁻¹ = ((110003340058946078995870196531013796614728765748384203670656694698327492898307 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_161 : affineAdd base_161 base_161 = base_162 := by
  unfold base_161 base_162
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((56487811975550303384642959780870327480512649236944577417586609378984145534 : Nat) : Fp))⁻¹ = ((114219707261951163543299712813790858164682810870265561738279674806284750676204 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((56487811975550303384642959780870327480512649236944577417586609378984145534 : Nat) : Fp))⁻¹ = ((114219707261951163543299712813790858164682810870265561738279674806284750676204 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_162 : affineAdd base_162 base_162 = base_163 := by
  unfold base_162 base_163
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((32017945344679105301355390714034191900569536621409624903946887176817068091004 : Nat) : Fp))⁻¹ = ((20642584052864188570734673630889047337025076819210595649005360194961196765373 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((32017945344679105301355390714034191900569536621409624903946887176817068091004 : Nat) : Fp))⁻¹ = ((20642584052864188570734673630889047337025076819210595649005360194961196765373 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_163 : affineAdd base_163 base_163 = base_164 := by
  unfold base_163 base_164
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((85529213318684499199278987295719119779748279834721244243621489005051282713327 : Nat) : Fp))⁻¹ = ((38703249659610621259791597410731853000555788129057154052001776847935145131539 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((85529213318684499199278987295719119779748279834721244243621489005051282713327 : Nat) : Fp))⁻¹ = ((38703249659610621259791597410731853000555788129057154052001776847935145131539 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_164 : affineAdd base_164 base_164 = base_165 := by
  unfold base_164 base_165
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((69703777934707822825561719800850612270463729018593401066444767531444843422376 : Nat) : Fp))⁻¹ = ((68885193368820360809242528750632017176021425139211256057375313559644855133666 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((69703777934707822825561719800850612270463729018593401066444767531444843422376 : Nat) : Fp))⁻¹ = ((68885193368820360809242528750632017176021425139211256057375313559644855133666 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_165 : affineAdd base_165 base_165 = base_166 := by
  unfold base_165 base_166
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((30896349737549724559469649176734599846674275470447944521491009517811476115886 : Nat) : Fp))⁻¹ = ((79709575707503606796880177826299540269409735639429363379820796891008224780735 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((30896349737549724559469649176734599846674275470447944521491009517811476115886 : Nat) : Fp))⁻¹ = ((79709575707503606796880177826299540269409735639429363379820796891008224780735 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_166 : affineAdd base_166 base_166 = base_167 := by
  unfold base_166 base_167
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((5581666239041823897511191387175605974957398643319691692931775273945574355546 : Nat) : Fp))⁻¹ = ((65778143908292045697715875160147080438082710268647618290765691311066967845111 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((5581666239041823897511191387175605974957398643319691692931775273945574355546 : Nat) : Fp))⁻¹ = ((65778143908292045697715875160147080438082710268647618290765691311066967845111 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_167 : affineAdd base_167 base_167 = base_168 := by
  unfold base_167 base_168
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((47413224699192139329891654683339940809213741191817662756932842522986369283987 : Nat) : Fp))⁻¹ = ((75090114300321618752163049206956652515355789079372795449921656468566858653901 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((47413224699192139329891654683339940809213741191817662756932842522986369283987 : Nat) : Fp))⁻¹ = ((75090114300321618752163049206956652515355789079372795449921656468566858653901 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_168 : affineAdd base_168 base_168 = base_169 := by
  unfold base_168 base_169
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((29242638042721994709047470454581660554102402946865770918554005639977770323656 : Nat) : Fp))⁻¹ = ((41583586414754263102132597338745076002239940886314968158938365331139947673554 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((29242638042721994709047470454581660554102402946865770918554005639977770323656 : Nat) : Fp))⁻¹ = ((41583586414754263102132597338745076002239940886314968158938365331139947673554 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_169 : affineAdd base_169 base_169 = base_170 := by
  unfold base_169 base_170
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((50626912648402731289281390580926582439784259522574187076012504768241480157237 : Nat) : Fp))⁻¹ = ((115215201577173899463119776584063303067135107912613042089406188036455096341259 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((50626912648402731289281390580926582439784259522574187076012504768241480157237 : Nat) : Fp))⁻¹ = ((115215201577173899463119776584063303067135107912613042089406188036455096341259 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_170 : affineAdd base_170 base_170 = base_171 := by
  unfold base_170 base_171
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((75192750551909937947468929249355987104463312649195251159923289612823008422826 : Nat) : Fp))⁻¹ = ((35041372184749017742837400384667696143847516778229665721307914765175769928723 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((75192750551909937947468929249355987104463312649195251159923289612823008422826 : Nat) : Fp))⁻¹ = ((35041372184749017742837400384667696143847516778229665721307914765175769928723 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_171 : affineAdd base_171 base_171 = base_172 := by
  unfold base_171 base_172
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((104894792315886610373915701617963847607765162153160773537780133243754931320852 : Nat) : Fp))⁻¹ = ((75062182689814696822124221685833782622930878705098395111021231492649025723092 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((104894792315886610373915701617963847607765162153160773537780133243754931320852 : Nat) : Fp))⁻¹ = ((75062182689814696822124221685833782622930878705098395111021231492649025723092 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_172 : affineAdd base_172 base_172 = base_173 := by
  unfold base_172 base_173
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((23694175599991408963414726019522496431384061981312306500396236825552398271404 : Nat) : Fp))⁻¹ = ((52257982522154613108960830840332542284203307062898368763285932742375828056803 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((23694175599991408963414726019522496431384061981312306500396236825552398271404 : Nat) : Fp))⁻¹ = ((52257982522154613108960830840332542284203307062898368763285932742375828056803 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_173 : affineAdd base_173 base_173 = base_174 := by
  unfold base_173 base_174
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((8467783976897375037636665426419232997456360183332998866888776438963891641752 : Nat) : Fp))⁻¹ = ((95272052448193584370960743179485203003847234151377384312406470671818765220407 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((8467783976897375037636665426419232997456360183332998866888776438963891641752 : Nat) : Fp))⁻¹ = ((95272052448193584370960743179485203003847234151377384312406470671818765220407 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_174 : affineAdd base_174 base_174 = base_175 := by
  unfold base_174 base_175
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((37306322622624672463065915763956225690223522454760918147434180740861300687668 : Nat) : Fp))⁻¹ = ((81618469734962567860826105148763026713200614631269855037594709912979888807874 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((37306322622624672463065915763956225690223522454760918147434180740861300687668 : Nat) : Fp))⁻¹ = ((81618469734962567860826105148763026713200614631269855037594709912979888807874 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_175 : affineAdd base_175 base_175 = base_176 := by
  unfold base_175 base_176
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((86236473645369998874832829444512637388615157303166534859982939866800801290421 : Nat) : Fp))⁻¹ = ((1587966541489049063276405469591686269293436040861698230554883725696101617408 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((86236473645369998874832829444512637388615157303166534859982939866800801290421 : Nat) : Fp))⁻¹ = ((1587966541489049063276405469591686269293436040861698230554883725696101617408 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_176 : affineAdd base_176 base_176 = base_177 := by
  unfold base_176 base_177
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((87900869236804138087371702825961176259461360124819616238035200569139627100447 : Nat) : Fp))⁻¹ = ((12469336074533754097152500080166372306833041668578821014122368365104425578274 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((87900869236804138087371702825961176259461360124819616238035200569139627100447 : Nat) : Fp))⁻¹ = ((12469336074533754097152500080166372306833041668578821014122368365104425578274 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_177 : affineAdd base_177 base_177 = base_178 := by
  unfold base_177 base_178
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((91581555597957928166775283241751618539413557986610388037330404183144654090313 : Nat) : Fp))⁻¹ = ((1677755034758129612532549491389725914601632695976112948442725546506719182399 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((91581555597957928166775283241751618539413557986610388037330404183144654090313 : Nat) : Fp))⁻¹ = ((1677755034758129612532549491389725914601632695976112948442725546506719182399 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_178 : affineAdd base_178 base_178 = base_179 := by
  unfold base_178 base_179
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((44679714547892089078501304545394627678115758391255360766903436677955303545885 : Nat) : Fp))⁻¹ = ((78785875820205081174199191819243927547353363792804161715755415095197047893638 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((44679714547892089078501304545394627678115758391255360766903436677955303545885 : Nat) : Fp))⁻¹ = ((78785875820205081174199191819243927547353363792804161715755415095197047893638 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_179 : affineAdd base_179 base_179 = base_180 := by
  unfold base_179 base_180
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((14437232828413691012043572600308410207374052858180415647749396463091843383375 : Nat) : Fp))⁻¹ = ((9694679771945889992648470092711317909127060988495670952498058489016785400410 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((14437232828413691012043572600308410207374052858180415647749396463091843383375 : Nat) : Fp))⁻¹ = ((9694679771945889992648470092711317909127060988495670952498058489016785400410 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_180 : affineAdd base_180 base_180 = base_181 := by
  unfold base_180 base_181
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((14027692582691445211169305233477544073839133566657605745596417381878123854178 : Nat) : Fp))⁻¹ = ((75176343092637829362284973646024913309523335319442533834727782215319755003169 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((14027692582691445211169305233477544073839133566657605745596417381878123854178 : Nat) : Fp))⁻¹ = ((75176343092637829362284973646024913309523335319442533834727782215319755003169 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_181 : affineAdd base_181 base_181 = base_182 := by
  unfold base_181 base_182
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((94184599433492315644214590509977869566386224898957355163260253699332858500095 : Nat) : Fp))⁻¹ = ((108130655227481114378227053175884626416700052103840556039395038998397805688970 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((94184599433492315644214590509977869566386224898957355163260253699332858500095 : Nat) : Fp))⁻¹ = ((108130655227481114378227053175884626416700052103840556039395038998397805688970 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_182 : affineAdd base_182 base_182 = base_183 := by
  unfold base_182 base_183
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((90938483595262914582675074472013558936350058640531727255070751800362248713128 : Nat) : Fp))⁻¹ = ((97236351956105420531538028739188606185094806043747310382741321467627690124626 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((90938483595262914582675074472013558936350058640531727255070751800362248713128 : Nat) : Fp))⁻¹ = ((97236351956105420531538028739188606185094806043747310382741321467627690124626 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_183 : affineAdd base_183 base_183 = base_184 := by
  unfold base_183 base_184
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((65079320657075459505472718093134166223214459592164919156492801936293394346061 : Nat) : Fp))⁻¹ = ((40195289652996728963180228686765862330548786986940850182083576659395473930033 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((65079320657075459505472718093134166223214459592164919156492801936293394346061 : Nat) : Fp))⁻¹ = ((40195289652996728963180228686765862330548786986940850182083576659395473930033 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_184 : affineAdd base_184 base_184 = base_185 := by
  unfold base_184 base_185
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((33126753624353590316677983729603901933376151587979623867133648552767197976839 : Nat) : Fp))⁻¹ = ((2706068585121040967925515455522222972418114499661555945748000634360674688377 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((33126753624353590316677983729603901933376151587979623867133648552767197976839 : Nat) : Fp))⁻¹ = ((2706068585121040967925515455522222972418114499661555945748000634360674688377 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_185 : affineAdd base_185 base_185 = base_186 := by
  unfold base_185 base_186
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((75132272094628034345708172112257475055149432967843434987053037295066962960968 : Nat) : Fp))⁻¹ = ((1004586753915559032987303902613110590160590688650635733661140930765675114165 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((75132272094628034345708172112257475055149432967843434987053037295066962960968 : Nat) : Fp))⁻¹ = ((1004586753915559032987303902613110590160590688650635733661140930765675114165 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_186 : affineAdd base_186 base_186 = base_187 := by
  unfold base_186 base_187
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((38657913077255361434444622743436849344919651203626641239625924177481274928933 : Nat) : Fp))⁻¹ = ((20789725674110554128921435000459965732798750992709849974925339687018610260561 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((38657913077255361434444622743436849344919651203626641239625924177481274928933 : Nat) : Fp))⁻¹ = ((20789725674110554128921435000459965732798750992709849974925339687018610260561 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_187 : affineAdd base_187 base_187 = base_188 := by
  unfold base_187 base_188
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((6241280037293053435562565229917129205739093461742926377996529691184676112606 : Nat) : Fp))⁻¹ = ((42282791511393687737673107880650013966221942146606212412247739451412945060884 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((6241280037293053435562565229917129205739093461742926377996529691184676112606 : Nat) : Fp))⁻¹ = ((42282791511393687737673107880650013966221942146606212412247739451412945060884 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_188 : affineAdd base_188 base_188 = base_189 := by
  unfold base_188 base_189
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((89585527340406565500019872698075135548357340032819778309253570440118818477036 : Nat) : Fp))⁻¹ = ((106421429454758322208547383202251491469115797447975764157428451386766304344596 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((89585527340406565500019872698075135548357340032819778309253570440118818477036 : Nat) : Fp))⁻¹ = ((106421429454758322208547383202251491469115797447975764157428451386766304344596 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_189 : affineAdd base_189 base_189 = base_190 := by
  unfold base_189 base_190
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((34120506380485136088917855908736915544289626703143468135554854919091047095237 : Nat) : Fp))⁻¹ = ((54851905234501207980249209545961595771216501410842604274363260048262137098309 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((34120506380485136088917855908736915544289626703143468135554854919091047095237 : Nat) : Fp))⁻¹ = ((54851905234501207980249209545961595771216501410842604274363260048262137098309 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_190 : affineAdd base_190 base_190 = base_191 := by
  unfold base_190 base_191
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((53428498708335298930383652178427276342268514807561120763391253036328211515369 : Nat) : Fp))⁻¹ = ((47628691153924720375748244484499517123881414249793794472734481670793018059891 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((53428498708335298930383652178427276342268514807561120763391253036328211515369 : Nat) : Fp))⁻¹ = ((47628691153924720375748244484499517123881414249793794472734481670793018059891 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_191 : affineAdd base_191 base_191 = base_192 := by
  unfold base_191 base_192
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((113583883859274030372082034862029605514506016193810719839027086029553530647303 : Nat) : Fp))⁻¹ = ((96045600208918762911097352925302156153525200376033426022014350128678213804918 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((113583883859274030372082034862029605514506016193810719839027086029553530647303 : Nat) : Fp))⁻¹ = ((96045600208918762911097352925302156153525200376033426022014350128678213804918 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_192 : affineAdd base_192 base_192 = base_193 := by
  unfold base_192 base_193
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((86028625094535483850261571256264386723357163272666519397289099603747119225149 : Nat) : Fp))⁻¹ = ((50023953707655492099729105282061706553501126726538515773023516239304309277009 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((86028625094535483850261571256264386723357163272666519397289099603747119225149 : Nat) : Fp))⁻¹ = ((50023953707655492099729105282061706553501126726538515773023516239304309277009 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_193 : affineAdd base_193 base_193 = base_194 := by
  unfold base_193 base_194
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((25015334278771650323507319424566501275290669267697587988960111333611631525338 : Nat) : Fp))⁻¹ = ((12779813712820916508782116532681216250858946511889850337315600051491834518764 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((25015334278771650323507319424566501275290669267697587988960111333611631525338 : Nat) : Fp))⁻¹ = ((12779813712820916508782116532681216250858946511889850337315600051491834518764 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_194 : affineAdd base_194 base_194 = base_195 := by
  unfold base_194 base_195
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((29567823868173186762768009528067406508648153893486721194867955006028793890909 : Nat) : Fp))⁻¹ = ((92238191626091806228815020880980384192825551816872371677713469193878357086709 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((29567823868173186762768009528067406508648153893486721194867955006028793890909 : Nat) : Fp))⁻¹ = ((92238191626091806228815020880980384192825551816872371677713469193878357086709 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_195 : affineAdd base_195 base_195 = base_196 := by
  unfold base_195 base_196
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((63192765102271790090487849294643355539231117908172846139915612801187217034173 : Nat) : Fp))⁻¹ = ((54300434630110123398509104008531707867843294026547837634468777812899002669529 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((63192765102271790090487849294643355539231117908172846139915612801187217034173 : Nat) : Fp))⁻¹ = ((54300434630110123398509104008531707867843294026547837634468777812899002669529 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_196 : affineAdd base_196 base_196 = base_197 := by
  unfold base_196 base_197
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((35110031909328754691401904954608234218729030798549406331812068095064570237972 : Nat) : Fp))⁻¹ = ((79302411148885929301880285417112874647650781637742208243068922428273388337708 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((35110031909328754691401904954608234218729030798549406331812068095064570237972 : Nat) : Fp))⁻¹ = ((79302411148885929301880285417112874647650781637742208243068922428273388337708 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_197 : affineAdd base_197 base_197 = base_198 := by
  unfold base_197 base_198
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((104607607047518035749515575138521003921603783202160061984102438399564594284817 : Nat) : Fp))⁻¹ = ((17359152114004423880501402481659574103477696458489177033317111530279469626287 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((104607607047518035749515575138521003921603783202160061984102438399564594284817 : Nat) : Fp))⁻¹ = ((17359152114004423880501402481659574103477696458489177033317111530279469626287 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_198 : affineAdd base_198 base_198 = base_199 := by
  unfold base_198 base_199
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((45762644100243963560173177200312509818364497605040202142354576105708649526139 : Nat) : Fp))⁻¹ = ((48128354531827650582999693806619736121308746870011552219793278551687692067202 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((45762644100243963560173177200312509818364497605040202142354576105708649526139 : Nat) : Fp))⁻¹ = ((48128354531827650582999693806619736121308746870011552219793278551687692067202 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_199 : affineAdd base_199 base_199 = base_200 := by
  unfold base_199 base_200
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((112881168890164609406380094011411584051648553985034449899770310954622772391910 : Nat) : Fp))⁻¹ = ((105292886276693390279639762126970536117830289668012354672949813892720748424077 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((112881168890164609406380094011411584051648553985034449899770310954622772391910 : Nat) : Fp))⁻¹ = ((105292886276693390279639762126970536117830289668012354672949813892720748424077 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_200 : affineAdd base_200 base_200 = base_201 := by
  unfold base_200 base_201
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((79126321700797654134629819022700262425734361986906066326971931873703874776829 : Nat) : Fp))⁻¹ = ((64314347984186572726596434131124377641099055577093482828023032215280064101423 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((79126321700797654134629819022700262425734361986906066326971931873703874776829 : Nat) : Fp))⁻¹ = ((64314347984186572726596434131124377641099055577093482828023032215280064101423 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_201 : affineAdd base_201 base_201 = base_202 := by
  unfold base_201 base_202
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((23045309029356249714220314716068128691355103924384360360907873576255068618171 : Nat) : Fp))⁻¹ = ((90568705077621304596933453508222330657437550020462649347340755673110445645766 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((23045309029356249714220314716068128691355103924384360360907873576255068618171 : Nat) : Fp))⁻¹ = ((90568705077621304596933453508222330657437550020462649347340755673110445645766 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_202 : affineAdd base_202 base_202 = base_203 := by
  unfold base_202 base_203
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((57003788001796941708539841608272678584351968322832676412429854825222401371502 : Nat) : Fp))⁻¹ = ((80595795965566305986833724325149845499019422894875124208922511479140202276497 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((57003788001796941708539841608272678584351968322832676412429854825222401371502 : Nat) : Fp))⁻¹ = ((80595795965566305986833724325149845499019422894875124208922511479140202276497 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_203 : affineAdd base_203 base_203 = base_204 := by
  unfold base_203 base_204
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((33429049751972530035656964727545283238705649483087953982909059058238089924020 : Nat) : Fp))⁻¹ = ((21420496436538037052304475600023532301906366807659420463028347584706706195707 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((33429049751972530035656964727545283238705649483087953982909059058238089924020 : Nat) : Fp))⁻¹ = ((21420496436538037052304475600023532301906366807659420463028347584706706195707 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_204 : affineAdd base_204 base_204 = base_205 := by
  unfold base_204 base_205
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((81007956585093945832919421410562969694439825683280800865606243366544248926160 : Nat) : Fp))⁻¹ = ((72162182975627335674902932071069549892900127949299530348506398130782693067867 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((81007956585093945832919421410562969694439825683280800865606243366544248926160 : Nat) : Fp))⁻¹ = ((72162182975627335674902932071069549892900127949299530348506398130782693067867 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_205 : affineAdd base_205 base_205 = base_206 := by
  unfold base_205 base_206
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((4398739609727183326946131652218256147146051104900180052629746226509188319237 : Nat) : Fp))⁻¹ = ((429779647444567384062064644081379571090498860440581030034325274589688805196 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((4398739609727183326946131652218256147146051104900180052629746226509188319237 : Nat) : Fp))⁻¹ = ((429779647444567384062064644081379571090498860440581030034325274589688805196 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_206 : affineAdd base_206 base_206 = base_207 := by
  unfold base_206 base_207
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((64164296153307859244227616480023302862568188165333043899999315127086687727186 : Nat) : Fp))⁻¹ = ((24060821064960685134039386611513123542379477482964512286313050807279658888140 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((64164296153307859244227616480023302862568188165333043899999315127086687727186 : Nat) : Fp))⁻¹ = ((24060821064960685134039386611513123542379477482964512286313050807279658888140 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_207 : affineAdd base_207 base_207 = base_208 := by
  unfold base_207 base_208
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((57369573270620142518340730615920379521637759094789396191309454253793769270353 : Nat) : Fp))⁻¹ = ((9867340405502527351649324483827076471291479143169237300901864118108067775581 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((57369573270620142518340730615920379521637759094789396191309454253793769270353 : Nat) : Fp))⁻¹ = ((9867340405502527351649324483827076471291479143169237300901864118108067775581 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_208 : affineAdd base_208 base_208 = base_209 := by
  unfold base_208 base_209
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((48632069096637554924274413793295750001160491151445521927536133070043743201297 : Nat) : Fp))⁻¹ = ((89758675054278667318603787723867271565172024158837468540737681605519931249348 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((48632069096637554924274413793295750001160491151445521927536133070043743201297 : Nat) : Fp))⁻¹ = ((89758675054278667318603787723867271565172024158837468540737681605519931249348 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_209 : affineAdd base_209 base_209 = base_210 := by
  unfold base_209 base_210
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((26879011462743840335691591457228606967066124790316477921535328699756712074744 : Nat) : Fp))⁻¹ = ((88085696962865014976770788649853193214500801308094586176080419992029581590289 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((26879011462743840335691591457228606967066124790316477921535328699756712074744 : Nat) : Fp))⁻¹ = ((88085696962865014976770788649853193214500801308094586176080419992029581590289 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_210 : affineAdd base_210 base_210 = base_211 := by
  unfold base_210 base_211
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((62963488700699789032569184806979115722324448122457023739501893021766746537757 : Nat) : Fp))⁻¹ = ((61842356840822369473698875132710257940453660541592262196425431349211761854865 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((62963488700699789032569184806979115722324448122457023739501893021766746537757 : Nat) : Fp))⁻¹ = ((61842356840822369473698875132710257940453660541592262196425431349211761854865 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_211 : affineAdd base_211 base_211 = base_212 := by
  unfold base_211 base_212
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((34767682558797648670566810324631233163266973542786319846918260332343694917893 : Nat) : Fp))⁻¹ = ((13197047115499952165125882201249752460016072224235047175258245060066355623531 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((34767682558797648670566810324631233163266973542786319846918260332343694917893 : Nat) : Fp))⁻¹ = ((13197047115499952165125882201249752460016072224235047175258245060066355623531 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_212 : affineAdd base_212 base_212 = base_213 := by
  unfold base_212 base_213
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((58503766529248989798675151322237530184126490579454294759021188248409021626097 : Nat) : Fp))⁻¹ = ((35217143214391737501924855837783686136986736510561807192632491456722613535796 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((58503766529248989798675151322237530184126490579454294759021188248409021626097 : Nat) : Fp))⁻¹ = ((35217143214391737501924855837783686136986736510561807192632491456722613535796 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_213 : affineAdd base_213 base_213 = base_214 := by
  unfold base_213 base_214
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((66095546131926016776182664572158682372222134031052577075352350981138964190485 : Nat) : Fp))⁻¹ = ((20763254027363838626433853419916101202236270205420309910677772200190149409254 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((66095546131926016776182664572158682372222134031052577075352350981138964190485 : Nat) : Fp))⁻¹ = ((20763254027363838626433853419916101202236270205420309910677772200190149409254 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_214 : affineAdd base_214 base_214 = base_215 := by
  unfold base_214 base_215
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((48870560607183744840505722498698757682142671336868405907998491847376392333741 : Nat) : Fp))⁻¹ = ((37020345877998656468162971089630720725518528881713493930634042853197437080744 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((48870560607183744840505722498698757682142671336868405907998491847376392333741 : Nat) : Fp))⁻¹ = ((37020345877998656468162971089630720725518528881713493930634042853197437080744 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_215 : affineAdd base_215 base_215 = base_216 := by
  unfold base_215 base_216
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((30623581788749822100382745859868645699047673268215141926580384967860112471253 : Nat) : Fp))⁻¹ = ((22897708860600781917745354010799041284850747086824500538866284795669645388206 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((30623581788749822100382745859868645699047673268215141926580384967860112471253 : Nat) : Fp))⁻¹ = ((22897708860600781917745354010799041284850747086824500538866284795669645388206 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_216 : affineAdd base_216 base_216 = base_217 := by
  unfold base_216 base_217
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((57710893937692665357647691724236515472507145065106377254221657836468024167436 : Nat) : Fp))⁻¹ = ((15315030689456244907310714513381359921861553616100067383155465335087520945069 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((57710893937692665357647691724236515472507145065106377254221657836468024167436 : Nat) : Fp))⁻¹ = ((15315030689456244907310714513381359921861553616100067383155465335087520945069 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_217 : affineAdd base_217 base_217 = base_218 := by
  unfold base_217 base_218
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((112096003213917921965697623480695740549761355267313232789540725477513634374998 : Nat) : Fp))⁻¹ = ((25324539181646741951635417566289667597234128711102122137928527440406754015947 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((112096003213917921965697623480695740549761355267313232789540725477513634374998 : Nat) : Fp))⁻¹ = ((25324539181646741951635417566289667597234128711102122137928527440406754015947 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_218 : affineAdd base_218 base_218 = base_219 := by
  unfold base_218 base_219
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((61132381960602712033174130914468477784017762207402074270409666098181344508219 : Nat) : Fp))⁻¹ = ((73058607525036219435065275950475112464189848920554982127149188436659688392659 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((61132381960602712033174130914468477784017762207402074270409666098181344508219 : Nat) : Fp))⁻¹ = ((73058607525036219435065275950475112464189848920554982127149188436659688392659 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_219 : affineAdd base_219 base_219 = base_220 := by
  unfold base_219 base_220
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((30749753566896120889917442069556393166141012006459550615871962942905620475626 : Nat) : Fp))⁻¹ = ((71101482518260335512735319553202961582974944276743354475217404262720777462456 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((30749753566896120889917442069556393166141012006459550615871962942905620475626 : Nat) : Fp))⁻¹ = ((71101482518260335512735319553202961582974944276743354475217404262720777462456 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_220 : affineAdd base_220 base_220 = base_221 := by
  unfold base_220 base_221
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((92628477256112478580738935680261058160861780653699013741020467863885755120243 : Nat) : Fp))⁻¹ = ((29199109170796309555452383886263112929957888748645270531771907869729423392094 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((92628477256112478580738935680261058160861780653699013741020467863885755120243 : Nat) : Fp))⁻¹ = ((29199109170796309555452383886263112929957888748645270531771907869729423392094 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_221 : affineAdd base_221 base_221 = base_222 := by
  unfold base_221 base_222
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((95744524462485084732056560754575516048250645981636693364989777482955901810067 : Nat) : Fp))⁻¹ = ((33343234492066841824859473492676109428077871058080834545383028501628382743299 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((95744524462485084732056560754575516048250645981636693364989777482955901810067 : Nat) : Fp))⁻¹ = ((33343234492066841824859473492676109428077871058080834545383028501628382743299 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_222 : affineAdd base_222 base_222 = base_223 := by
  unfold base_222 base_223
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((2226821049909366001426284673098873826917960544595316002560147822639123525016 : Nat) : Fp))⁻¹ = ((3920752382795727500126677695549155820209282546492906184146483298309288710975 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((2226821049909366001426284673098873826917960544595316002560147822639123525016 : Nat) : Fp))⁻¹ = ((3920752382795727500126677695549155820209282546492906184146483298309288710975 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_223 : affineAdd base_223 base_223 = base_224 := by
  unfold base_223 base_224
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((66850838866234897399334488953202946314182773756688684015551691304105443157422 : Nat) : Fp))⁻¹ = ((110085451703085979787828577103053337489349223039707675626096568501644860933693 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((66850838866234897399334488953202946314182773756688684015551691304105443157422 : Nat) : Fp))⁻¹ = ((110085451703085979787828577103053337489349223039707675626096568501644860933693 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_224 : affineAdd base_224 base_224 = base_225 := by
  unfold base_224 base_225
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((21029601506232444319368385136955684033497833311867654114423309422350207087357 : Nat) : Fp))⁻¹ = ((95660310754726542828155801086913325872083242445896765066460945278310535358873 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((21029601506232444319368385136955684033497833311867654114423309422350207087357 : Nat) : Fp))⁻¹ = ((95660310754726542828155801086913325872083242445896765066460945278310535358873 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_225 : affineAdd base_225 base_225 = base_226 := by
  unfold base_225 base_226
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((111327482796856645338109375925255091131664696057056686983936700507225403719493 : Nat) : Fp))⁻¹ = ((15295522670490849617968572596822156072351063200659875305733243945869641886468 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((111327482796856645338109375925255091131664696057056686983936700507225403719493 : Nat) : Fp))⁻¹ = ((15295522670490849617968572596822156072351063200659875305733243945869641886468 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_226 : affineAdd base_226 base_226 = base_227 := by
  unfold base_226 base_227
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((105735616450588913958761248879135978906628726313788624529292917321934778581901 : Nat) : Fp))⁻¹ = ((65916835964192653530019520427011165490656218703088293546713166657222739971372 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((105735616450588913958761248879135978906628726313788624529292917321934778581901 : Nat) : Fp))⁻¹ = ((65916835964192653530019520427011165490656218703088293546713166657222739971372 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_227 : affineAdd base_227 base_227 = base_228 := by
  unfold base_227 base_228
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((85633666146296869475846120618182213756296576205663668204532591586342323566242 : Nat) : Fp))⁻¹ = ((109712620584824030024260172407594963317319282104459392491789669903081443558105 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((85633666146296869475846120618182213756296576205663668204532591586342323566242 : Nat) : Fp))⁻¹ = ((109712620584824030024260172407594963317319282104459392491789669903081443558105 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_228 : affineAdd base_228 base_228 = base_229 := by
  unfold base_228 base_229
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((105017020600749110255205601310325343926653803681868124843703017010103026488325 : Nat) : Fp))⁻¹ = ((87414760962781721110327768760664535219937127884531821230471762147808943240742 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((105017020600749110255205601310325343926653803681868124843703017010103026488325 : Nat) : Fp))⁻¹ = ((87414760962781721110327768760664535219937127884531821230471762147808943240742 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_229 : affineAdd base_229 base_229 = base_230 := by
  unfold base_229 base_230
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((100718452597198377694892433543251040205084258311006913553384445818907946819791 : Nat) : Fp))⁻¹ = ((77603793989947230522008567640355065585518306228541485067030980856568549180000 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((100718452597198377694892433543251040205084258311006913553384445818907946819791 : Nat) : Fp))⁻¹ = ((77603793989947230522008567640355065585518306228541485067030980856568549180000 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_230 : affineAdd base_230 base_230 = base_231 := by
  unfold base_230 base_231
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((35384723941339661147011733585239808738288755024824978650787507425153094271729 : Nat) : Fp))⁻¹ = ((43878548303423512898269857891446981862929031111510755319966876933820964556972 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((35384723941339661147011733585239808738288755024824978650787507425153094271729 : Nat) : Fp))⁻¹ = ((43878548303423512898269857891446981862929031111510755319966876933820964556972 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_231 : affineAdd base_231 base_231 = base_232 := by
  unfold base_231 base_232
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((70018069425595998018260816426652965226827561219175179343976674369210843266462 : Nat) : Fp))⁻¹ = ((62509707549538594773783214331117894201167782880639127315123874165761648868903 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((70018069425595998018260816426652965226827561219175179343976674369210843266462 : Nat) : Fp))⁻¹ = ((62509707549538594773783214331117894201167782880639127315123874165761648868903 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_232 : affineAdd base_232 base_232 = base_233 := by
  unfold base_232 base_233
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((98434237446496148394183890050136756428510322717221929962654009239641273623945 : Nat) : Fp))⁻¹ = ((56650322688511203933589477190393400726727143868163917746397194220571836919125 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((98434237446496148394183890050136756428510322717221929962654009239641273623945 : Nat) : Fp))⁻¹ = ((56650322688511203933589477190393400726727143868163917746397194220571836919125 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_233 : affineAdd base_233 base_233 = base_234 := by
  unfold base_233 base_234
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((11344377696059311412860255181221495902312688613306488893294163454119121825704 : Nat) : Fp))⁻¹ = ((87536249941413345457524704883606555594017768553001390906557338242171830815217 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((11344377696059311412860255181221495902312688613306488893294163454119121825704 : Nat) : Fp))⁻¹ = ((87536249941413345457524704883606555594017768553001390906557338242171830815217 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_234 : affineAdd base_234 base_234 = base_235 := by
  unfold base_234 base_235
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((92690132246900151323277569114758090527006018018792578401159597199495559705760 : Nat) : Fp))⁻¹ = ((37530086091034413617389994448879494066594547253067400139380082338295029488384 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((92690132246900151323277569114758090527006018018792578401159597199495559705760 : Nat) : Fp))⁻¹ = ((37530086091034413617389994448879494066594547253067400139380082338295029488384 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_235 : affineAdd base_235 base_235 = base_236 := by
  unfold base_235 base_236
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((8629245570289361512928824496793066884814249866400051283675066385256088984418 : Nat) : Fp))⁻¹ = ((23940216300593840667349065764893258764968693591953710859549489996583134861334 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((8629245570289361512928824496793066884814249866400051283675066385256088984418 : Nat) : Fp))⁻¹ = ((23940216300593840667349065764893258764968693591953710859549489996583134861334 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_236 : affineAdd base_236 base_236 = base_237 := by
  unfold base_236 base_237
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((25750881830896011524081627616138971820801200943932001974011760182257795007870 : Nat) : Fp))⁻¹ = ((99431743198666031590319797017321219173668416986612890293305591844969167650327 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((25750881830896011524081627616138971820801200943932001974011760182257795007870 : Nat) : Fp))⁻¹ = ((99431743198666031590319797017321219173668416986612890293305591844969167650327 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_237 : affineAdd base_237 base_237 = base_238 := by
  unfold base_237 base_238
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((86511203683128773200503204915391168752553058701578039004115361443541322212241 : Nat) : Fp))⁻¹ = ((19509582393260654339931151192599689176631203940239728747039986650673491156180 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((86511203683128773200503204915391168752553058701578039004115361443541322212241 : Nat) : Fp))⁻¹ = ((19509582393260654339931151192599689176631203940239728747039986650673491156180 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_238 : affineAdd base_238 base_238 = base_239 := by
  unfold base_238 base_239
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((39922059842557940073913288636103872861952687103330770522978967679436902620067 : Nat) : Fp))⁻¹ = ((93313616875310554137546057087769750030496559986894987635263048713239212241591 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((39922059842557940073913288636103872861952687103330770522978967679436902620067 : Nat) : Fp))⁻¹ = ((93313616875310554137546057087769750030496559986894987635263048713239212241591 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_239 : affineAdd base_239 base_239 = base_240 := by
  unfold base_239 base_240
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((107835997232065897977399831129863752621211712639335526979670771458251622188461 : Nat) : Fp))⁻¹ = ((73806492655781681624994440136836574701827105730928381762026400997062553734432 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((107835997232065897977399831129863752621211712639335526979670771458251622188461 : Nat) : Fp))⁻¹ = ((73806492655781681624994440136836574701827105730928381762026400997062553734432 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_240 : affineAdd base_240 base_240 = base_241 := by
  unfold base_240 base_241
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((47828698862917730813607230394980222348159325738755616817276492989172802309159 : Nat) : Fp))⁻¹ = ((83814684551851427440268016491950434326972990461507085460677925420075031829786 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((47828698862917730813607230394980222348159325738755616817276492989172802309159 : Nat) : Fp))⁻¹ = ((83814684551851427440268016491950434326972990461507085460677925420075031829786 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_241 : affineAdd base_241 base_241 = base_242 := by
  unfold base_241 base_242
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((90554055872943285359562789441845937705225388396376669909302342738611517756544 : Nat) : Fp))⁻¹ = ((89530279390245254102559121820209448742212149390729214699022913343455987874487 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((90554055872943285359562789441845937705225388396376669909302342738611517756544 : Nat) : Fp))⁻¹ = ((89530279390245254102559121820209448742212149390729214699022913343455987874487 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_242 : affineAdd base_242 base_242 = base_243 := by
  unfold base_242 base_243
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((29212277550782883303312106838911213847133545583225907622635973696278860332923 : Nat) : Fp))⁻¹ = ((59016674288353854667220046825615506159949276262991256846941067250514104612445 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((29212277550782883303312106838911213847133545583225907622635973696278860332923 : Nat) : Fp))⁻¹ = ((59016674288353854667220046825615506159949276262991256846941067250514104612445 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_243 : affineAdd base_243 base_243 = base_244 := by
  unfold base_243 base_244
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((54113652565211585717578927649047183887090734340027236246806164434159486622390 : Nat) : Fp))⁻¹ = ((3645219108425620790482262900099716569384023660448994395837087050295119162258 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((54113652565211585717578927649047183887090734340027236246806164434159486622390 : Nat) : Fp))⁻¹ = ((3645219108425620790482262900099716569384023660448994395837087050295119162258 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_244 : affineAdd base_244 base_244 = base_245 := by
  unfold base_244 base_245
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((5983439944161437184729068253379966091033304045142912300433002697874386924481 : Nat) : Fp))⁻¹ = ((71964758569799523034151209161735405938839572031562005191191104030769313990222 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((5983439944161437184729068253379966091033304045142912300433002697874386924481 : Nat) : Fp))⁻¹ = ((71964758569799523034151209161735405938839572031562005191191104030769313990222 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_245 : affineAdd base_245 base_245 = base_246 := by
  unfold base_245 base_246
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((103397407405374187698982141346926700394890519747915912573020442958629189307492 : Nat) : Fp))⁻¹ = ((11004575305538630798129770100246039416885582145327351883885829329971046856372 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((103397407405374187698982141346926700394890519747915912573020442958629189307492 : Nat) : Fp))⁻¹ = ((11004575305538630798129770100246039416885582145327351883885829329971046856372 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_246 : affineAdd base_246 base_246 = base_247 := by
  unfold base_246 base_247
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((78473624517617731927860216277549078632861074607574001991821266037345967105658 : Nat) : Fp))⁻¹ = ((64079725791863165325153471238121948499879774585319889413577292993785934552341 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((78473624517617731927860216277549078632861074607574001991821266037345967105658 : Nat) : Fp))⁻¹ = ((64079725791863165325153471238121948499879774585319889413577292993785934552341 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_247 : affineAdd base_247 base_247 = base_248 := by
  unfold base_247 base_248
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((94762424439059506170177300542547484894285259654945103834474381188217886845725 : Nat) : Fp))⁻¹ = ((46101429785710918641101564362549770785719737306556270568664408485327605673670 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((94762424439059506170177300542547484894285259654945103834474381188217886845725 : Nat) : Fp))⁻¹ = ((46101429785710918641101564362549770785719737306556270568664408485327605673670 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_248 : affineAdd base_248 base_248 = base_249 := by
  unfold base_248 base_249
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((29236048674093813394523910922582374630829081423043497254162533033164154049666 : Nat) : Fp))⁻¹ = ((78472434726273648619143972980153001843749698293464232331127572474584077440152 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((29236048674093813394523910922582374630829081423043497254162533033164154049666 : Nat) : Fp))⁻¹ = ((78472434726273648619143972980153001843749698293464232331127572474584077440152 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_249 : affineAdd base_249 base_249 = base_250 := by
  unfold base_249 base_250
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((9026183085953335931861042123363330152002153911485343327487109499224702177627 : Nat) : Fp))⁻¹ = ((85676735693508926390609917799574293775891918538394746953620653602163239837438 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((9026183085953335931861042123363330152002153911485343327487109499224702177627 : Nat) : Fp))⁻¹ = ((85676735693508926390609917799574293775891918538394746953620653602163239837438 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_250 : affineAdd base_250 base_250 = base_251 := by
  unfold base_250 base_251
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((62804288124927804794141542013461961167839995408257184926209413592463329006125 : Nat) : Fp))⁻¹ = ((22939226736543009726883554824109661496746741991407892455772577496671726896073 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((62804288124927804794141542013461961167839995408257184926209413592463329006125 : Nat) : Fp))⁻¹ = ((22939226736543009726883554824109661496746741991407892455772577496671726896073 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_251 : affineAdd base_251 base_251 = base_252 := by
  unfold base_251 base_252
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((8682685012247630765815268889801361118442695513083738308010936359908165836919 : Nat) : Fp))⁻¹ = ((31772524753733775343861184113252295565118441777266919325795488068648067073886 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((8682685012247630765815268889801361118442695513083738308010936359908165836919 : Nat) : Fp))⁻¹ = ((31772524753733775343861184113252295565118441777266919325795488068648067073886 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_252 : affineAdd base_252 base_252 = base_253 := by
  unfold base_252 base_253
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((44353125519324157186344456159742269880631179110473143840214086765587351124293 : Nat) : Fp))⁻¹ = ((31049344584016126447108833081186712631113892179528788132757933952942826450614 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((44353125519324157186344456159742269880631179110473143840214086765587351124293 : Nat) : Fp))⁻¹ = ((31049344584016126447108833081186712631113892179528788132757933952942826450614 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_253 : affineAdd base_253 base_253 = base_254 := by
  unfold base_253 base_254
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((37579621872809717799779570009674914438024800886176540314162770583770981830863 : Nat) : Fp))⁻¹ = ((42804151747217338164534656890511759141811092865293164195550640699239569089052 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((37579621872809717799779570009674914438024800886176540314162770583770981830863 : Nat) : Fp))⁻¹ = ((42804151747217338164534656890511759141811092865293164195550640699239569089052 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem base_double_254 : affineAdd base_254 base_254 = base_255 := by
  unfold base_254 base_255
  apply certifiedDouble
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (doubleDenominator ((847959926674921704613916930352312808004252888284294958523157455244708242291 : Nat) : Fp))⁻¹ = ((45216786234585038967808945125173349819177190112060894743018281719174137832456 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (doubleDenominator ((847959926674921704613916930352312808004252888284294958523157455244708242291 : Nat) : Fp))⁻¹ = ((45216786234585038967808945125173349819177190112060894743018281719174137832456 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold doubleDenominator
      unfold Fp p
      reduce_mod_char
    unfold doubleY doubleX doubleSlope
    rw [hinv]
    unfold doubleNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_6 : affineAdd base_0 base_6 = acc_7 := by
  unfold base_0 base_6 acc_7
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((55066263022277343669578718895168534326250603453777594175500187360389116729240 : Nat) : Fp) - ((86454928033100054822938644242727206101601557724291916072342392316125160730507 : Nat) : Fp))⁻¹ = ((1930988469515460839322060645146086315706001551828613756927013626513655678517 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((55066263022277343669578718895168534326250603453777594175500187360389116729240 : Nat) : Fp) - ((86454928033100054822938644242727206101601557724291916072342392316125160730507 : Nat) : Fp))⁻¹ = ((1930988469515460839322060645146086315706001551828613756927013626513655678517 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_8 : affineAdd acc_7 base_8 = acc_9 := by
  unfold acc_7 base_8 acc_9
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((11045059572793568563399009827450521654436229950346969273826455203229685425899 : Nat) : Fp) - ((59030624050581421406270513075794029219285200067000787157698366092408912155912 : Nat) : Fp))⁻¹ = ((21344218184668533468027930433293609051180797011531247759616428563794765184746 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((11045059572793568563399009827450521654436229950346969273826455203229685425899 : Nat) : Fp) - ((59030624050581421406270513075794029219285200067000787157698366092408912155912 : Nat) : Fp))⁻¹ = ((21344218184668533468027930433293609051180797011531247759616428563794765184746 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_14 : affineAdd acc_9 base_14 = acc_15 := by
  unfold acc_9 base_14 acc_15
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((62993874516558554105998507783025790934389611786421029894195191716181730180203 : Nat) : Fp) - ((7741290454269945723504810030002187313337519274815056282137434463684850516554 : Nat) : Fp))⁻¹ = ((100413014800999242701763191927904109471609182354130146465125263464302301534051 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((62993874516558554105998507783025790934389611786421029894195191716181730180203 : Nat) : Fp) - ((7741290454269945723504810030002187313337519274815056282137434463684850516554 : Nat) : Fp))⁻¹ = ((100413014800999242701763191927904109471609182354130146465125263464302301534051 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_17 : affineAdd acc_15 base_17 = acc_18 := by
  unfold acc_15 base_17 acc_18
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((94913787221764930918395305492653186337662262006421321283318132192378151570664 : Nat) : Fp) - ((34424533203459102608471296411716955901929203809676354171491737723302766101825 : Nat) : Fp))⁻¹ = ((20341161659597960222559045186109191923134338801181264254049191402807743104466 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((94913787221764930918395305492653186337662262006421321283318132192378151570664 : Nat) : Fp) - ((34424533203459102608471296411716955901929203809676354171491737723302766101825 : Nat) : Fp))⁻¹ = ((20341161659597960222559045186109191923134338801181264254049191402807743104466 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_18 : affineAdd acc_18 base_18 = acc_19 := by
  unfold acc_18 base_18 acc_19
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((29143731705339141020573143536865033240207337756459069554333709854927801226474 : Nat) : Fp) - ((74193831669845249654938577341216601539929459848933807922451592200153851425745 : Nat) : Fp))⁻¹ = ((114158475880569382326874722290000865873614871562595479305613189579096530804465 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((29143731705339141020573143536865033240207337756459069554333709854927801226474 : Nat) : Fp) - ((74193831669845249654938577341216601539929459848933807922451592200153851425745 : Nat) : Fp))⁻¹ = ((114158475880569382326874722290000865873614871562595479305613189579096530804465 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_20 : affineAdd acc_19 base_20 = acc_21 := by
  unfold acc_19 base_20 acc_21
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((90849555490501463584933875627311483322534276480368275854037302915980746150944 : Nat) : Fp) - ((63004655751848499058589887215149057167805706207141784701705408548476267919372 : Nat) : Fp))⁻¹ = ((4883507527092235002729825498447519644190618571281151741441317656462391682527 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((90849555490501463584933875627311483322534276480368275854037302915980746150944 : Nat) : Fp) - ((63004655751848499058589887215149057167805706207141784701705408548476267919372 : Nat) : Fp))⁻¹ = ((4883507527092235002729825498447519644190618571281151741441317656462391682527 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_21 : affineAdd acc_21 base_21 = acc_22 := by
  unfold acc_21 base_21 acc_22
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((89477026208564161510117767278811649609638282443724716428920033606201704315067 : Nat) : Fp) - ((107219988410259287649822325760828753777881271537028923079899200557009639695550 : Nat) : Fp))⁻¹ = ((108754424047909899968236774591340359695953789030897017033969450399729546574764 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((89477026208564161510117767278811649609638282443724716428920033606201704315067 : Nat) : Fp) - ((107219988410259287649822325760828753777881271537028923079899200557009639695550 : Nat) : Fp))⁻¹ = ((108754424047909899968236774591340359695953789030897017033969450399729546574764 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_28 : affineAdd acc_22 base_28 = acc_29 := by
  unfold acc_22 base_28 acc_29
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((105117500916977773616594155617683380201243349076787575587894204199931887461275 : Nat) : Fp) - ((107989063369659015153804811955459434214410196483964476598208978660096898619386 : Nat) : Fp))⁻¹ = ((43927177129787812478791872719694008707682603222956735320581220150489006397882 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((105117500916977773616594155617683380201243349076787575587894204199931887461275 : Nat) : Fp) - ((107989063369659015153804811955459434214410196483964476598208978660096898619386 : Nat) : Fp))⁻¹ = ((43927177129787812478791872719694008707682603222956735320581220150489006397882 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_30 : affineAdd acc_29 base_30 = acc_31 := by
  unfold acc_29 base_30 acc_31
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((33783762117358464705901306764751882743375394820654715821356128391667619714744 : Nat) : Fp) - ((102193949730178242338502490474683128513913323030888946433219655522103301391692 : Nat) : Fp))⁻¹ = ((42654536354480984468689748914357180799579686255901544230297805164379862558088 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((33783762117358464705901306764751882743375394820654715821356128391667619714744 : Nat) : Fp) - ((102193949730178242338502490474683128513913323030888946433219655522103301391692 : Nat) : Fp))⁻¹ = ((42654536354480984468689748914357180799579686255901544230297805164379862558088 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_31 : affineAdd acc_31 base_31 = acc_32 := by
  unfold acc_31 base_31 acc_32
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((65690204794470308527683968204692797115282228827141914913431062282090561707752 : Nat) : Fp) - ((37586094085820668222219663528035831988292035114036566702275484810122124564900 : Nat) : Fp))⁻¹ = ((38434319372476657519875377006384645476584371681907188804357665279600632233342 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((65690204794470308527683968204692797115282228827141914913431062282090561707752 : Nat) : Fp) - ((37586094085820668222219663528035831988292035114036566702275484810122124564900 : Nat) : Fp))⁻¹ = ((38434319372476657519875377006384645476584371681907188804357665279600632233342 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_34 : affineAdd acc_32 base_34 = acc_35 := by
  unfold acc_32 base_34 acc_35
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((41618715794919262343288247885775468705279947972537888270396336879835196892309 : Nat) : Fp) - ((113783330688848408326400254714688308943084902760190583586245237148771972268029 : Nat) : Fp))⁻¹ = ((82083598858397817528243387428875941105903388233789449254337291047253243513142 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((41618715794919262343288247885775468705279947972537888270396336879835196892309 : Nat) : Fp) - ((113783330688848408326400254714688308943084902760190583586245237148771972268029 : Nat) : Fp))⁻¹ = ((82083598858397817528243387428875941105903388233789449254337291047253243513142 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_35 : affineAdd acc_35 base_35 = acc_36 := by
  unfold acc_35 base_35 acc_36
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((26987509267674617032564560708794887116074759337281694404645619351738152609835 : Nat) : Fp) - ((104610067874554658939189781067288826551534040873032177114963645859116975547034 : Nat) : Fp))⁻¹ = ((80270583801227663251941627965047814712225057017814906473474264507093229617757 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((26987509267674617032564560708794887116074759337281694404645619351738152609835 : Nat) : Fp) - ((104610067874554658939189781067288826551534040873032177114963645859116975547034 : Nat) : Fp))⁻¹ = ((80270583801227663251941627965047814712225057017814906473474264507093229617757 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_39 : affineAdd acc_36 base_39 = acc_40 := by
  unfold acc_36 base_39 acc_40
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((90670167833274761944578800724498188827088614564367350696785506786556880665943 : Nat) : Fp) - ((89749383265034677666862365486905244671167444330802547291623325584186528137154 : Nat) : Fp))⁻¹ = ((1146410463995180586911937943633880196679936671241870326359801139401371428263 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((90670167833274761944578800724498188827088614564367350696785506786556880665943 : Nat) : Fp) - ((89749383265034677666862365486905244671167444330802547291623325584186528137154 : Nat) : Fp))⁻¹ = ((1146410463995180586911937943633880196679936671241870326359801139401371428263 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_41 : affineAdd acc_40 base_41 = acc_42 := by
  unfold acc_40 base_41 acc_42
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((81516270644508254972885744636153652471500891511912876378582865082758736795477 : Nat) : Fp) - ((34828167905024529293425261847016829712897759939934247610415071312015953046280 : Nat) : Fp))⁻¹ = ((87625433872763612013112480238578583168447239454530236852810555060264054301597 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((81516270644508254972885744636153652471500891511912876378582865082758736795477 : Nat) : Fp) - ((34828167905024529293425261847016829712897759939934247610415071312015953046280 : Nat) : Fp))⁻¹ = ((87625433872763612013112480238578583168447239454530236852810555060264054301597 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_42 : affineAdd acc_42 base_42 = acc_43 := by
  unfold acc_42 base_42 acc_43
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((60071965084468911187377148037867676523542376580279561249395160962599431041583 : Nat) : Fp) - ((51545007865675218331521052163329117547916750428334376359731030798802230204655 : Nat) : Fp))⁻¹ = ((51525220005466255466164053154910174026251802069035918567403449502425721426245 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((60071965084468911187377148037867676523542376580279561249395160962599431041583 : Nat) : Fp) - ((51545007865675218331521052163329117547916750428334376359731030798802230204655 : Nat) : Fp))⁻¹ = ((51525220005466255466164053154910174026251802069035918567403449502425721426245 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_43 : affineAdd acc_43 base_43 = acc_44 := by
  unfold acc_43 base_43 acc_44
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((70461669509128515110401879623799383994591745881104094861864290047217329804875 : Nat) : Fp) - ((73599252554810039763407176139974374780648488828183406696254895715553023853401 : Nat) : Fp))⁻¹ = ((68105422254383314021294939804680830200104091822129214401143080888760644224427 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((70461669509128515110401879623799383994591745881104094861864290047217329804875 : Nat) : Fp) - ((73599252554810039763407176139974374780648488828183406696254895715553023853401 : Nat) : Fp))⁻¹ = ((68105422254383314021294939804680830200104091822129214401143080888760644224427 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_44 : affineAdd acc_44 base_44 = acc_45 := by
  unfold acc_44 base_44 acc_45
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((81655338892537041067055604246338288373085611726097761412397446724784214369483 : Nat) : Fp) - ((98787353431067487068174780415369765662128367506208336868623541747762523303089 : Nat) : Fp))⁻¹ = ((79339644481360206760356119907529808218060763396175640941284255096251603425565 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((81655338892537041067055604246338288373085611726097761412397446724784214369483 : Nat) : Fp) - ((98787353431067487068174780415369765662128367506208336868623541747762523303089 : Nat) : Fp))⁻¹ = ((79339644481360206760356119907529808218060763396175640941284255096251603425565 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_46 : affineAdd acc_45 base_46 = acc_47 := by
  unfold acc_45 base_46 acc_47
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((68259249210418618144302303847781214325835610307148491130815063758657141614627 : Nat) : Fp) - ((8964980402707168350657927400892132353366269496956872817449479166659938883802 : Nat) : Fp))⁻¹ = ((83713636359869971297597270976592936463776396634086662181848665141980953073340 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((68259249210418618144302303847781214325835610307148491130815063758657141614627 : Nat) : Fp) - ((8964980402707168350657927400892132353366269496956872817449479166659938883802 : Nat) : Fp))⁻¹ = ((83713636359869971297597270976592936463776396634086662181848665141980953073340 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_49 : affineAdd acc_47 base_49 = acc_50 := by
  unfold acc_47 base_49 acc_50
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((27762703325796909550034319905135946240294058406315182939056603236183625351842 : Nat) : Fp) - ((744654853145823512678710729425372655622767097643314990136170544084291976361 : Nat) : Fp))⁻¹ = ((5845642927399530596784060208870151997744641907870088000284928498791304996019 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((27762703325796909550034319905135946240294058406315182939056603236183625351842 : Nat) : Fp) - ((744654853145823512678710729425372655622767097643314990136170544084291976361 : Nat) : Fp))⁻¹ = ((5845642927399530596784060208870151997744641907870088000284928498791304996019 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_52 : affineAdd acc_50 base_52 = acc_53 := by
  unfold acc_50 base_52 acc_53
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((99194189383376580806912732530734056588783061829478900752337249255154902255827 : Nat) : Fp) - ((64447161864609791404195758691963071452721019060247337925015807247342017994823 : Nat) : Fp))⁻¹ = ((76845677374267301478915585317588100964703294987296412875459091756390043166615 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((99194189383376580806912732530734056588783061829478900752337249255154902255827 : Nat) : Fp) - ((64447161864609791404195758691963071452721019060247337925015807247342017994823 : Nat) : Fp))⁻¹ = ((76845677374267301478915585317588100964703294987296412875459091756390043166615 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_54 : affineAdd acc_53 base_54 = acc_55 := by
  unfold acc_53 base_54 acc_55
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((69187203649075496263558380068530805903295971191518681710653387161368690281111 : Nat) : Fp) - ((25014901206392249887698237444530503896296748023707107244397125743674754644790 : Nat) : Fp))⁻¹ = ((60990451336193680224841856574862200822079920610972962725543804291448722172547 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((69187203649075496263558380068530805903295971191518681710653387161368690281111 : Nat) : Fp) - ((25014901206392249887698237444530503896296748023707107244397125743674754644790 : Nat) : Fp))⁻¹ = ((60990451336193680224841856574862200822079920610972962725543804291448722172547 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_55 : affineAdd acc_55 base_55 = acc_56 := by
  unfold acc_55 base_55 acc_56
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((15223848390017212906680881981813393413677039340503028595624541674101902531963 : Nat) : Fp) - ((16058435479155118972993837131799089058715967396125428615558605751627320645142 : Nat) : Fp))⁻¹ = ((59800049743265477337890632751994636544700023198243427791841189942860479645018 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((15223848390017212906680881981813393413677039340503028595624541674101902531963 : Nat) : Fp) - ((16058435479155118972993837131799089058715967396125428615558605751627320645142 : Nat) : Fp))⁻¹ = ((59800049743265477337890632751994636544700023198243427791841189942860479645018 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_56 : affineAdd acc_56 base_56 = acc_57 := by
  unfold acc_56 base_56 acc_57
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((57185860723879935035866354173246676411942596839444195638204647215815346768112 : Nat) : Fp) - ((25497240280963516313937320941859063956353887664759333529694971679324342859874 : Nat) : Fp))⁻¹ = ((50678641145405078971038621491297955006940422485160643418923758175296832600638 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((57185860723879935035866354173246676411942596839444195638204647215815346768112 : Nat) : Fp) - ((25497240280963516313937320941859063956353887664759333529694971679324342859874 : Nat) : Fp))⁻¹ = ((50678641145405078971038621491297955006940422485160643418923758175296832600638 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_57 : affineAdd acc_57 base_57 = acc_58 := by
  unfold acc_57 base_57 acc_58
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((23118118866888655613556245973026645805119182871186618924392625013176520610465 : Nat) : Fp) - ((111703840010970554703825044762397257236786082270905035457492386104226958443132 : Nat) : Fp))⁻¹ = ((50760990460863010985247372930804026679378768459190603541454285268106624044255 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((23118118866888655613556245973026645805119182871186618924392625013176520610465 : Nat) : Fp) - ((111703840010970554703825044762397257236786082270905035457492386104226958443132 : Nat) : Fp))⁻¹ = ((50760990460863010985247372930804026679378768459190603541454285268106624044255 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_58 : affineAdd acc_58 base_58 = acc_59 := by
  unfold acc_58 base_58 acc_59
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((109268062965302509751249725782841497693627030916462198496686435014212514468944 : Nat) : Fp) - ((113599246344934629336805861786255890702306480065011524716308738005517377133750 : Nat) : Fp))⁻¹ = ((115543505426594657728867265506837592241601873251997863746411356883220651255280 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((109268062965302509751249725782841497693627030916462198496686435014212514468944 : Nat) : Fp) - ((113599246344934629336805861786255890702306480065011524716308738005517377133750 : Nat) : Fp))⁻¹ = ((115543505426594657728867265506837592241601873251997863746411356883220651255280 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_59 : affineAdd acc_59 base_59 = acc_60 := by
  unfold acc_59 base_59 acc_60
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((8009867505253292627563618294460798837052598759293890721633944836155070435023 : Nat) : Fp) - ((62223290140977849549949037397413163042719030609658769845468333603013413866526 : Nat) : Fp))⁻¹ = ((45183649583693719937203489170893696381791835661719025130803861022609502632026 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((8009867505253292627563618294460798837052598759293890721633944836155070435023 : Nat) : Fp) - ((62223290140977849549949037397413163042719030609658769845468333603013413866526 : Nat) : Fp))⁻¹ = ((45183649583693719937203489170893696381791835661719025130803861022609502632026 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_60 : affineAdd acc_60 base_60 = acc_61 := by
  unfold acc_60 base_60 acc_61
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((37038459036163776514058476381271657069201060930499270675974535267129853015692 : Nat) : Fp) - ((3155324650630266164941215407725229976924800176927891490779584824139541300135 : Nat) : Fp))⁻¹ = ((12998076761972577113599006535507390087820890190308161425335580019401211970941 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((37038459036163776514058476381271657069201060930499270675974535267129853015692 : Nat) : Fp) - ((3155324650630266164941215407725229976924800176927891490779584824139541300135 : Nat) : Fp))⁻¹ = ((12998076761972577113599006535507390087820890190308161425335580019401211970941 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_61 : affineAdd acc_61 base_61 = acc_62 := by
  unfold acc_61 base_61 acc_62
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((75749617177574834102149252734770805170663915898998128466674389318315036187752 : Nat) : Fp) - ((78940842088341059937720881764219942614374815880107123037550313585999765034797 : Nat) : Fp))⁻¹ = ((62321048793574904113632624087255792518027317534661786191861180922067476660022 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((75749617177574834102149252734770805170663915898998128466674389318315036187752 : Nat) : Fp) - ((78940842088341059937720881764219942614374815880107123037550313585999765034797 : Nat) : Fp))⁻¹ = ((62321048793574904113632624087255792518027317534661786191861180922067476660022 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_63 : affineAdd acc_62 base_63 = acc_64 := by
  unfold acc_62 base_63 acc_64
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((26961910731381032139552785280349446080688665026897053639184453099671199281653 : Nat) : Fp) - ((101817088763764058272032685058193941686495949380163784665542336507398664578275 : Nat) : Fp))⁻¹ = ((110740664161249724283100533002897718028852949667465808994771659566050621157064 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((26961910731381032139552785280349446080688665026897053639184453099671199281653 : Nat) : Fp) - ((101817088763764058272032685058193941686495949380163784665542336507398664578275 : Nat) : Fp))⁻¹ = ((110740664161249724283100533002897718028852949667465808994771659566050621157064 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_64 : affineAdd acc_64 base_64 = acc_65 := by
  unfold acc_64 base_64 acc_65
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((60136517557012337886219143441347989931997721743090658581626858228326433472322 : Nat) : Fp) - ((23129491278950567785970148376500648032717531886785241126168611397589814798013 : Nat) : Fp))⁻¹ = ((89741101360973302664287821123502804285170438440848377816218461296561014003917 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((60136517557012337886219143441347989931997721743090658581626858228326433472322 : Nat) : Fp) - ((23129491278950567785970148376500648032717531886785241126168611397589814798013 : Nat) : Fp))⁻¹ = ((89741101360973302664287821123502804285170438440848377816218461296561014003917 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_65 : affineAdd acc_65 base_65 = acc_66 := by
  unfold acc_65 base_65 acc_66
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((86189600100549013261218396657850864219874730265296776543117159178463788186174 : Nat) : Fp) - ((63843472757015161619640823952764524318291830965488059905636263767209969312866 : Nat) : Fp))⁻¹ = ((80817171207175344398686218543124284659063820400843849050760446049334030574544 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((86189600100549013261218396657850864219874730265296776543117159178463788186174 : Nat) : Fp) - ((63843472757015161619640823952764524318291830965488059905636263767209969312866 : Nat) : Fp))⁻¹ = ((80817171207175344398686218543124284659063820400843849050760446049334030574544 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_67 : affineAdd acc_66 base_67 = acc_68 := by
  unfold acc_66 base_67 acc_68
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((49985759286094074597680466732886939186456207479529083039553970260762539159489 : Nat) : Fp) - ((17692067919141883746474430216313318912323253047795385992074267436472656099942 : Nat) : Fp))⁻¹ = ((93971479717681915312538524913638738277977503384092905006535847778543389348063 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((49985759286094074597680466732886939186456207479529083039553970260762539159489 : Nat) : Fp) - ((17692067919141883746474430216313318912323253047795385992074267436472656099942 : Nat) : Fp))⁻¹ = ((93971479717681915312538524913638738277977503384092905006535847778543389348063 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_68 : affineAdd acc_68 base_68 = acc_69 := by
  unfold acc_68 base_68 acc_69
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((6695453148659735962002278213602542997318133052565924704593474838173153106710 : Nat) : Fp) - ((60339901160910692237675572757878163770580581369373573584664013679285413129091 : Nat) : Fp))⁻¹ = ((104865671351519982898266943824586558131207849600572470765510793374647921971836 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((6695453148659735962002278213602542997318133052565924704593474838173153106710 : Nat) : Fp) - ((60339901160910692237675572757878163770580581369373573584664013679285413129091 : Nat) : Fp))⁻¹ = ((104865671351519982898266943824586558131207849600572470765510793374647921971836 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_69 : affineAdd acc_69 base_69 = acc_70 := by
  unfold acc_69 base_69 acc_70
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((104426448526774961863592430878135482344898700069802556168947359175483153349152 : Nat) : Fp) - ((37677678367764998054256419260552297374816808777506812193658101085944629689381 : Nat) : Fp))⁻¹ = ((12490086194486054400122087533910132771751414039044925958703769141614803983469 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((104426448526774961863592430878135482344898700069802556168947359175483153349152 : Nat) : Fp) - ((37677678367764998054256419260552297374816808777506812193658101085944629689381 : Nat) : Fp))⁻¹ = ((12490086194486054400122087533910132771751414039044925958703769141614803983469 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_77 : affineAdd acc_70 base_77 = acc_78 := by
  unfold acc_70 base_77 acc_78
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((25706115431223231104349502338425676760948233609524549927682567987735767988359 : Nat) : Fp) - ((60540754330080069959401906198898450479294126639715413570889179042286485863469 : Nat) : Fp))⁻¹ = ((12854628435545948303098303502359923072091794462512016394762004446154336937596 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((25706115431223231104349502338425676760948233609524549927682567987735767988359 : Nat) : Fp) - ((60540754330080069959401906198898450479294126639715413570889179042286485863469 : Nat) : Fp))⁻¹ = ((12854628435545948303098303502359923072091794462512016394762004446154336937596 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_79 : affineAdd acc_78 base_79 = acc_80 := by
  unfold acc_78 base_79 acc_80
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((73125825156308139294675747886866421016441910230119720499669894621285502251079 : Nat) : Fp) - ((53648153254893980119900785370237364158138815147385101116545069153555170288062 : Nat) : Fp))⁻¹ = ((20124729862487999779982374451750361114885234040066677358608649498620848696758 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((73125825156308139294675747886866421016441910230119720499669894621285502251079 : Nat) : Fp) - ((53648153254893980119900785370237364158138815147385101116545069153555170288062 : Nat) : Fp))⁻¹ = ((20124729862487999779982374451750361114885234040066677358608649498620848696758 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_83 : affineAdd acc_80 base_83 = acc_84 := by
  unfold acc_80 base_83 acc_84
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((3799410324969024133081081695082414846245373966520493209198350038600691536914 : Nat) : Fp) - ((82065288257280364930681258037857029580600229348145328350024440340670179446551 : Nat) : Fp))⁻¹ = ((27515322381640727854017668267039364276065713084728794480192173259934675549710 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((3799410324969024133081081695082414846245373966520493209198350038600691536914 : Nat) : Fp) - ((82065288257280364930681258037857029580600229348145328350024440340670179446551 : Nat) : Fp))⁻¹ = ((27515322381640727854017668267039364276065713084728794480192173259934675549710 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_86 : affineAdd acc_84 base_86 = acc_87 := by
  unfold acc_84 base_86 acc_87
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((36481107058847661184720422216126033568491719697437610972538970425171464994134 : Nat) : Fp) - ((97007893071212898831976542306925407114333944783774668033349973529691460445404 : Nat) : Fp))⁻¹ = ((26865710500820976920453883039052097798194227153564133413091272385884935420138 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((36481107058847661184720422216126033568491719697437610972538970425171464994134 : Nat) : Fp) - ((97007893071212898831976542306925407114333944783774668033349973529691460445404 : Nat) : Fp))⁻¹ = ((26865710500820976920453883039052097798194227153564133413091272385884935420138 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_88 : affineAdd acc_87 base_88 = acc_89 := by
  unfold acc_87 base_88 acc_89
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((39167433951545998662469544307046456080123148394186949127521342155774454045112 : Nat) : Fp) - ((15033179896439470858126247808641765484544705738074160218957951164394937620308 : Nat) : Fp))⁻¹ = ((76382603301724691343818658755189244458953870332585951346340886234830016615065 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((39167433951545998662469544307046456080123148394186949127521342155774454045112 : Nat) : Fp) - ((15033179896439470858126247808641765484544705738074160218957951164394937620308 : Nat) : Fp))⁻¹ = ((76382603301724691343818658755189244458953870332585951346340886234830016615065 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_89 : affineAdd acc_89 base_89 = acc_90 := by
  unfold acc_89 base_89 acc_90
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((47721097417240342851575869518307123551954077459667301577181113199159910028448 : Nat) : Fp) - ((12831426614286788027900392815123462940913304574075286993885122038414101217196 : Nat) : Fp))⁻¹ = ((102010182127182272858067469400430067102026946137330256661080955062682666829873 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((47721097417240342851575869518307123551954077459667301577181113199159910028448 : Nat) : Fp) - ((12831426614286788027900392815123462940913304574075286993885122038414101217196 : Nat) : Fp))⁻¹ = ((102010182127182272858067469400430067102026946137330256661080955062682666829873 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_90 : affineAdd acc_90 base_90 = acc_91 := by
  unfold acc_90 base_90 acc_91
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((5974904400430543259455560848409761135828404883755769475812545840798994420626 : Nat) : Fp) - ((31731558888758314830347225402035966953019197198882726537928061332981883805116 : Nat) : Fp))⁻¹ = ((80662734868768719174212645106082697017946681043567652328184467726486246861649 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((5974904400430543259455560848409761135828404883755769475812545840798994420626 : Nat) : Fp) - ((31731558888758314830347225402035966953019197198882726537928061332981883805116 : Nat) : Fp))⁻¹ = ((80662734868768719174212645106082697017946681043567652328184467726486246861649 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_91 : affineAdd acc_91 base_91 = acc_92 := by
  unfold acc_91 base_91 acc_92
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((5509577011086727080997845992373093152769990707708497256037145900212757718763 : Nat) : Fp) - ((108516937186382041812103670511048142301189499913949040064226297021918453104669 : Nat) : Fp))⁻¹ = ((24988679958449970455061038142193361053171349900560373097497631003335557545593 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((5509577011086727080997845992373093152769990707708497256037145900212757718763 : Nat) : Fp) - ((108516937186382041812103670511048142301189499913949040064226297021918453104669 : Nat) : Fp))⁻¹ = ((24988679958449970455061038142193361053171349900560373097497631003335557545593 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_93 : affineAdd acc_92 base_93 = acc_94 := by
  unfold acc_92 base_93 acc_94
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((81498813144553065193277101791088765223666465594788231317695429763494990800161 : Nat) : Fp) - ((62221449722415965098534394864216300756619410467360193813993841802984909839181 : Nat) : Fp))⁻¹ = ((50478500041157617854150140506676414559348080118115394054830205951449731276754 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((81498813144553065193277101791088765223666465594788231317695429763494990800161 : Nat) : Fp) - ((62221449722415965098534394864216300756619410467360193813993841802984909839181 : Nat) : Fp))⁻¹ = ((50478500041157617854150140506676414559348080118115394054830205951449731276754 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_95 : affineAdd acc_94 base_95 = acc_96 := by
  unfold acc_94 base_95 acc_96
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((82882321221271994761165685376483487612453422273385368815479594044555354887913 : Nat) : Fp) - ((22840966669343746868657542410372307235035375411707745900291535045354561578850 : Nat) : Fp))⁻¹ = ((41385825550780008856899695514881545825514430616873982861224335452954964969371 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((82882321221271994761165685376483487612453422273385368815479594044555354887913 : Nat) : Fp) - ((22840966669343746868657542410372307235035375411707745900291535045354561578850 : Nat) : Fp))⁻¹ = ((41385825550780008856899695514881545825514430616873982861224335452954964969371 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_97 : affineAdd acc_96 base_97 = acc_98 := by
  unfold acc_96 base_97 acc_98
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((85822199919418065873158677931932224637840315064394798344509210798366262760486 : Nat) : Fp) - ((107460092490405557856637269383143137018363307684850226624646466770567328913124 : Nat) : Fp))⁻¹ = ((18789624131922633946575360905626801614221577319461095308760256788797988691977 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((85822199919418065873158677931932224637840315064394798344509210798366262760486 : Nat) : Fp) - ((107460092490405557856637269383143137018363307684850226624646466770567328913124 : Nat) : Fp))⁻¹ = ((18789624131922633946575360905626801614221577319461095308760256788797988691977 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_98 : affineAdd acc_98 base_98 = acc_99 := by
  unfold acc_98 base_98 acc_99
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((36018791698582241120782688987973347775778125434698149796719209811558341468509 : Nat) : Fp) - ((18928961140921885700908658116849834750075223885003133432284077605308119970073 : Nat) : Fp))⁻¹ = ((46861087035783479678282094198712918139093630861212907020746530507736684528625 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((36018791698582241120782688987973347775778125434698149796719209811558341468509 : Nat) : Fp) - ((18928961140921885700908658116849834750075223885003133432284077605308119970073 : Nat) : Fp))⁻¹ = ((46861087035783479678282094198712918139093630861212907020746530507736684528625 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_101 : affineAdd acc_99 base_101 = acc_102 := by
  unfold acc_99 base_101 acc_102
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((41111154781556033377440121874077527421315943697062380855736502909096841867206 : Nat) : Fp) - ((50903437175324684576123794325687091093316794895342376267022156508043454547877 : Nat) : Fp))⁻¹ = ((10809491305640826924647657866984560341894786870138883128053771447349563943183 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((41111154781556033377440121874077527421315943697062380855736502909096841867206 : Nat) : Fp) - ((50903437175324684576123794325687091093316794895342376267022156508043454547877 : Nat) : Fp))⁻¹ = ((10809491305640826924647657866984560341894786870138883128053771447349563943183 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_102 : affineAdd acc_102 base_102 = acc_103 := by
  unfold acc_102 base_102 acc_103
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((70107473280607648069001123872136195111137548018812398968844687706317006207302 : Nat) : Fp) - ((11673581412764099021153615077620366366802304893369795243117390666352665359806 : Nat) : Fp))⁻¹ = ((26911438632634936143128620202612839460866868704503780223745665965234908977685 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((70107473280607648069001123872136195111137548018812398968844687706317006207302 : Nat) : Fp) - ((11673581412764099021153615077620366366802304893369795243117390666352665359806 : Nat) : Fp))⁻¹ = ((26911438632634936143128620202612839460866868704503780223745665965234908977685 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_103 : affineAdd acc_103 base_103 = acc_104 := by
  unfold acc_103 base_103 acc_104
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((102080125537512830561429134257341642762801162083249309315826629272439682303930 : Nat) : Fp) - ((79346041630131869075645430486783108716991485536433518103538843150249487037416 : Nat) : Fp))⁻¹ = ((35294205917974536764595211366172550165754501217945085411380982009050859258248 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((102080125537512830561429134257341642762801162083249309315826629272439682303930 : Nat) : Fp) - ((79346041630131869075645430486783108716991485536433518103538843150249487037416 : Nat) : Fp))⁻¹ = ((35294205917974536764595211366172550165754501217945085411380982009050859258248 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_106 : affineAdd acc_104 base_106 = acc_107 := by
  unfold acc_104 base_106 acc_107
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((94368376047009421717855463218318015560972492266809599892431797191812862745821 : Nat) : Fp) - ((32543944108095182552403308115282823595699487874750970784134326899018753076265 : Nat) : Fp))⁻¹ = ((36182946596272775432305262027888082652916527831779451703281988014509940239227 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((94368376047009421717855463218318015560972492266809599892431797191812862745821 : Nat) : Fp) - ((32543944108095182552403308115282823595699487874750970784134326899018753076265 : Nat) : Fp))⁻¹ = ((36182946596272775432305262027888082652916527831779451703281988014509940239227 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_107 : affineAdd acc_107 base_107 = acc_108 := by
  unfold acc_107 base_107 acc_108
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((10321650696684694424956901291088654816318080924060828571726835953248311385544 : Nat) : Fp) - ((87183516938829948739214915672694597601526144237528747913079459935123543116507 : Nat) : Fp))⁻¹ = ((32291366151815950382361699754352874919577445157813521434871044625812502647176 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((10321650696684694424956901291088654816318080924060828571726835953248311385544 : Nat) : Fp) - ((87183516938829948739214915672694597601526144237528747913079459935123543116507 : Nat) : Fp))⁻¹ = ((32291366151815950382361699754352874919577445157813521434871044625812502647176 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_108 : affineAdd acc_108 base_108 = acc_109 := by
  unfold acc_108 base_108 acc_109
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((110885102143344023004297714671567539084344995277262228798154482989829145471921 : Nat) : Fp) - ((97963514608391620515365258119340011983767027607182736209046173629563994030411 : Nat) : Fp))⁻¹ = ((97208284922469212344524976764041527190079849260225032308593319662460641720075 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((110885102143344023004297714671567539084344995277262228798154482989829145471921 : Nat) : Fp) - ((97963514608391620515365258119340011983767027607182736209046173629563994030411 : Nat) : Fp))⁻¹ = ((97208284922469212344524976764041527190079849260225032308593319662460641720075 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_110 : affineAdd acc_109 base_110 = acc_111 := by
  unfold acc_109 base_110 acc_111
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((688280669162989546390772776013627019489387407390641084214463900619024372191 : Nat) : Fp) - ((98432034282390382237828948384540370085442598032656811937139102930236777548604 : Nat) : Fp))⁻¹ = ((58743611965649776759572491244559883203431972844555545113889110797123067600964 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((688280669162989546390772776013627019489387407390641084214463900619024372191 : Nat) : Fp) - ((98432034282390382237828948384540370085442598032656811937139102930236777548604 : Nat) : Fp))⁻¹ = ((58743611965649776759572491244559883203431972844555545113889110797123067600964 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_111 : affineAdd acc_111 base_111 = acc_112 := by
  unfold acc_111 base_111 acc_112
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((55569353933861153981007938645731919034676101358716740918948668607947783287783 : Nat) : Fp) - ((1805616805351721617653443610838676066411318390548678811172302707980664066418 : Nat) : Fp))⁻¹ = ((5031004174592452970888968237584397628150448347121014469787918920089664197562 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((55569353933861153981007938645731919034676101358716740918948668607947783287783 : Nat) : Fp) - ((1805616805351721617653443610838676066411318390548678811172302707980664066418 : Nat) : Fp))⁻¹ = ((5031004174592452970888968237584397628150448347121014469787918920089664197562 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_113 : affineAdd acc_112 base_113 = acc_114 := by
  unfold acc_112 base_113 acc_114
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((69583153015791561848491236522420332279446720326520150735477129200128611100578 : Nat) : Fp) - ((49398952861877205296964985511595482837454065472867773380651392793273881817706 : Nat) : Fp))⁻¹ = ((7820059416102850781589073527265568571339786639281146316270078038730135410784 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((69583153015791561848491236522420332279446720326520150735477129200128611100578 : Nat) : Fp) - ((49398952861877205296964985511595482837454065472867773380651392793273881817706 : Nat) : Fp))⁻¹ = ((7820059416102850781589073527265568571339786639281146316270078038730135410784 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_114 : affineAdd acc_114 base_114 = acc_115 := by
  unfold acc_114 base_114 acc_115
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((19633159299856099907314563658736240791444294953890097332202432654822417141512 : Nat) : Fp) - ((26557021881017484338287109395067993477080269267457693436680348679906749635481 : Nat) : Fp))⁻¹ = ((31052856654140420949485895451599507865419283324093321517338485880276008780770 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((19633159299856099907314563658736240791444294953890097332202432654822417141512 : Nat) : Fp) - ((26557021881017484338287109395067993477080269267457693436680348679906749635481 : Nat) : Fp))⁻¹ = ((31052856654140420949485895451599507865419283324093321517338485880276008780770 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_115 : affineAdd acc_115 base_115 = acc_116 := by
  unfold acc_115 base_115 acc_116
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((16646694601055444161462789274198939361644158325658382956372688880992905138311 : Nat) : Fp) - ((54910438115352124820925906331600651980234249876402837107104827961903280048346 : Nat) : Fp))⁻¹ = ((111650969347480202357152655687367662230060585900253144212399729799531326350638 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((16646694601055444161462789274198939361644158325658382956372688880992905138311 : Nat) : Fp) - ((54910438115352124820925906331600651980234249876402837107104827961903280048346 : Nat) : Fp))⁻¹ = ((111650969347480202357152655687367662230060585900253144212399729799531326350638 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_117 : affineAdd acc_116 base_117 = acc_118 := by
  unfold acc_116 base_117 acc_118
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((57101222887932246968439371290112973346171902219944257147746332672280620593970 : Nat) : Fp) - ((30779593535010329084651325212930254896397289835007988481712809855381584203096 : Nat) : Fp))⁻¹ = ((18455294159489714921967889340907031067289636525212108948252788007280835060569 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((57101222887932246968439371290112973346171902219944257147746332672280620593970 : Nat) : Fp) - ((30779593535010329084651325212930254896397289835007988481712809855381584203096 : Nat) : Fp))⁻¹ = ((18455294159489714921967889340907031067289636525212108948252788007280835060569 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_119 : affineAdd acc_118 base_119 = acc_120 := by
  unfold acc_118 base_119 acc_120
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((95944886742557707932362876789624879591893495467445214359084245806917774340757 : Nat) : Fp) - ((63066765102144977597923579437181551876011710207298597143023780209765509321725 : Nat) : Fp))⁻¹ = ((95264003637961566958521931327596192648728913479458777809882139380163978248051 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((95944886742557707932362876789624879591893495467445214359084245806917774340757 : Nat) : Fp) - ((63066765102144977597923579437181551876011710207298597143023780209765509321725 : Nat) : Fp))⁻¹ = ((95264003637961566958521931327596192648728913479458777809882139380163978248051 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_121 : affineAdd acc_120 base_121 = acc_122 := by
  unfold acc_120 base_121 acc_122
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((54167007267059197045221945990254946807947280925068536125576886778329475540076 : Nat) : Fp) - ((18039326416892417753003755158326429558922487640705110383763721719977461130670 : Nat) : Fp))⁻¹ = ((36407819245147999229330613390079744631099835136713783540267167150302928040870 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((54167007267059197045221945990254946807947280925068536125576886778329475540076 : Nat) : Fp) - ((18039326416892417753003755158326429558922487640705110383763721719977461130670 : Nat) : Fp))⁻¹ = ((36407819245147999229330613390079744631099835136713783540267167150302928040870 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_123 : affineAdd acc_122 base_123 = acc_124 := by
  unfold acc_122 base_123 acc_124
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((98860079765909358796142953988580893109144029840399878081833223424758478366643 : Nat) : Fp) - ((5420721428656512733924502511426114039091019723753927823327107920655123143427 : Nat) : Fp))⁻¹ = ((44894565516532880559923573825792995988298081964103158028592579566839731914968 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((98860079765909358796142953988580893109144029840399878081833223424758478366643 : Nat) : Fp) - ((5420721428656512733924502511426114039091019723753927823327107920655123143427 : Nat) : Fp))⁻¹ = ((44894565516532880559923573825792995988298081964103158028592579566839731914968 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_124 : affineAdd acc_124 base_124 = acc_125 := by
  unfold acc_124 base_124 acc_125
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((42048476443960000607055303567932611428047936177544484184308593834997252715145 : Nat) : Fp) - ((65439637510807713056358030282940995565074807966223863057633547322884310978260 : Nat) : Fp))⁻¹ = ((37221958754778801269277392838943884327241830873420501172881586250862178945954 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((42048476443960000607055303567932611428047936177544484184308593834997252715145 : Nat) : Fp) - ((65439637510807713056358030282940995565074807966223863057633547322884310978260 : Nat) : Fp))⁻¹ = ((37221958754778801269277392838943884327241830873420501172881586250862178945954 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_125 : affineAdd acc_125 base_125 = acc_126 := by
  unfold acc_125 base_125 acc_126
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((40808566356087706713890706648386103099378437079371712127830451490467855389508 : Nat) : Fp) - ((57070623766206825319979971604352341937693971268571462200885005684041460744529 : Nat) : Fp))⁻¹ = ((103849513492010114182721512455855798306065923794553821224498053287034547678361 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((40808566356087706713890706648386103099378437079371712127830451490467855389508 : Nat) : Fp) - ((57070623766206825319979971604352341937693971268571462200885005684041460744529 : Nat) : Fp))⁻¹ = ((103849513492010114182721512455855798306065923794553821224498053287034547678361 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_127 : affineAdd acc_126 base_127 = acc_128 := by
  unfold acc_126 base_127 acc_128
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((56288351935501938235309378627037995070659666184532694594320684497895417783803 : Nat) : Fp) - ((95120790446093252839327344452467895851663435942220974758177611352160193500228 : Nat) : Fp))⁻¹ = ((91321931996368887615180429365847323612072695986467460274580862716552424462866 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((56288351935501938235309378627037995070659666184532694594320684497895417783803 : Nat) : Fp) - ((95120790446093252839327344452467895851663435942220974758177611352160193500228 : Nat) : Fp))⁻¹ = ((91321931996368887615180429365847323612072695986467460274580862716552424462866 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_129 : affineAdd acc_128 base_129 = acc_130 := by
  unfold acc_128 base_129 acc_130
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((32256737403791914686372586254330362595305275169830061794707745295581356675058 : Nat) : Fp) - ((34958276914040952500699582748843894357474821914666173518868387777824232206454 : Nat) : Fp))⁻¹ = ((22174976627191705436941463787026560430868155639736252497457096687599814631731 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((32256737403791914686372586254330362595305275169830061794707745295581356675058 : Nat) : Fp) - ((34958276914040952500699582748843894357474821914666173518868387777824232206454 : Nat) : Fp))⁻¹ = ((22174976627191705436941463787026560430868155639736252497457096687599814631731 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_130 : affineAdd acc_130 base_130 = acc_131 := by
  unfold acc_130 base_130 acc_131
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((91741821106593624285097037099343471848474224858941232879131869967755051054218 : Nat) : Fp) - ((53097865109432700015174734468294135156387483155245154627764610227234210717734 : Nat) : Fp))⁻¹ = ((70552587258020462336197566167544663154448197619694194357075208113889365673580 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((91741821106593624285097037099343471848474224858941232879131869967755051054218 : Nat) : Fp) - ((53097865109432700015174734468294135156387483155245154627764610227234210717734 : Nat) : Fp))⁻¹ = ((70552587258020462336197566167544663154448197619694194357075208113889365673580 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_131 : affineAdd acc_131 base_131 = acc_132 := by
  unfold acc_131 base_131 acc_132
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((876047637419442076877020655258504368469881489828225470144032574576745391356 : Nat) : Fp) - ((14944996539173920287535718879437473208319387726469358424706553507748318061176 : Nat) : Fp))⁻¹ = ((38249197247416048401982632393264922525856615907849679770563224307003319973484 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((876047637419442076877020655258504368469881489828225470144032574576745391356 : Nat) : Fp) - ((14944996539173920287535718879437473208319387726469358424706553507748318061176 : Nat) : Fp))⁻¹ = ((38249197247416048401982632393264922525856615907849679770563224307003319973484 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_132 : affineAdd acc_132 base_132 = acc_133 := by
  unfold acc_132 base_132 acc_133
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((41292388911594828841688755398275203008656246181806000113850535655350608353168 : Nat) : Fp) - ((103558405691517931349553446884579863115096122592891559643307293876412976668177 : Nat) : Fp))⁻¹ = ((33755704342162605333544987632419796416072210093354660122195719401816054167396 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((41292388911594828841688755398275203008656246181806000113850535655350608353168 : Nat) : Fp) - ((103558405691517931349553446884579863115096122592891559643307293876412976668177 : Nat) : Fp))⁻¹ = ((33755704342162605333544987632419796416072210093354660122195719401816054167396 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_133 : affineAdd acc_133 base_133 = acc_134 := by
  unfold acc_133 base_133 acc_134
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((56815726206465773808453127650822173850241926431943623033908133580612678261480 : Nat) : Fp) - ((34009678302028016429416675792156881929217167215919330167617059558107204398895 : Nat) : Fp))⁻¹ = ((57539714046259694169894961621992209544850981189022169165711265845524151503779 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((56815726206465773808453127650822173850241926431943623033908133580612678261480 : Nat) : Fp) - ((34009678302028016429416675792156881929217167215919330167617059558107204398895 : Nat) : Fp))⁻¹ = ((57539714046259694169894961621992209544850981189022169165711265845524151503779 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_134 : affineAdd acc_134 base_134 = acc_135 := by
  unfold acc_134 base_134 acc_135
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((23220893035889910636946805781344549261675078085456573395822142317137928410713 : Nat) : Fp) - ((92137904221004991822640747341747548945462418389173665085162488592935043663263 : Nat) : Fp))⁻¹ = ((70266392433020164504793062960933616754454765151758262442880704606055585632983 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((23220893035889910636946805781344549261675078085456573395822142317137928410713 : Nat) : Fp) - ((92137904221004991822640747341747548945462418389173665085162488592935043663263 : Nat) : Fp))⁻¹ = ((70266392433020164504793062960933616754454765151758262442880704606055585632983 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_135 : affineAdd acc_135 base_135 = acc_136 := by
  unfold acc_135 base_135 acc_136
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((14986505511071864390751319822613268135838572187452595128300726684100967021470 : Nat) : Fp) - ((110576394165891695959547398864574113324861677782985712232382940604063624860352 : Nat) : Fp))⁻¹ = ((58565782942923802448198888428062330454482047315822191292293807539303823981107 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((14986505511071864390751319822613268135838572187452595128300726684100967021470 : Nat) : Fp) - ((110576394165891695959547398864574113324861677782985712232382940604063624860352 : Nat) : Fp))⁻¹ = ((58565782942923802448198888428062330454482047315822191292293807539303823981107 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_136 : affineAdd acc_136 base_136 = acc_137 := by
  unfold acc_136 base_136 acc_137
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((83640465507401686462263533627622564812678268326224187181898793301565321681751 : Nat) : Fp) - ((63325528419660284613648700910995098077763772416467869706013046991065094742686 : Nat) : Fp))⁻¹ = ((21647113698496543002884976262993402528018564543686363221311388719793892164387 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((83640465507401686462263533627622564812678268326224187181898793301565321681751 : Nat) : Fp) - ((63325528419660284613648700910995098077763772416467869706013046991065094742686 : Nat) : Fp))⁻¹ = ((21647113698496543002884976262993402528018564543686363221311388719793892164387 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_137 : affineAdd acc_137 base_137 = acc_138 := by
  unfold acc_137 base_137 acc_138
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((86130755921611212044147249845724329580220518801808515059278645831102457009272 : Nat) : Fp) - ((16650325658330045346563110008023955204728736149712219077558782426015089744479 : Nat) : Fp))⁻¹ = ((18864932214753109330515315919794333814839076363692691616511410099418348925036 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((86130755921611212044147249845724329580220518801808515059278645831102457009272 : Nat) : Fp) - ((16650325658330045346563110008023955204728736149712219077558782426015089744479 : Nat) : Fp))⁻¹ = ((18864932214753109330515315919794333814839076363692691616511410099418348925036 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_138 : affineAdd acc_138 base_138 = acc_139 := by
  unfold acc_138 base_138 acc_139
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((75330202358275438652442019080086978139032819196890473859747676497570155441290 : Nat) : Fp) - ((131611795964869315746733228552844550837488089277020511476213613441587846562 : Nat) : Fp))⁻¹ = ((25917622048870509608325781982031798541916201595222592727956877601387692611622 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((75330202358275438652442019080086978139032819196890473859747676497570155441290 : Nat) : Fp) - ((131611795964869315746733228552844550837488089277020511476213613441587846562 : Nat) : Fp))⁻¹ = ((25917622048870509608325781982031798541916201595222592727956877601387692611622 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_139 : affineAdd acc_139 base_139 = acc_140 := by
  unfold acc_139 base_139 acc_140
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((71777962321459349406000724597903971388434741523230555797285671830852712859798 : Nat) : Fp) - ((107872043834894622552741642145000578443189656222946491690889504134408605289317 : Nat) : Fp))⁻¹ = ((13358873119697035900920156723018925605693972571663261303336704161393577247454 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((71777962321459349406000724597903971388434741523230555797285671830852712859798 : Nat) : Fp) - ((107872043834894622552741642145000578443189656222946491690889504134408605289317 : Nat) : Fp))⁻¹ = ((13358873119697035900920156723018925605693972571663261303336704161393577247454 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_140 : affineAdd acc_140 base_140 = acc_141 := by
  unfold acc_140 base_140 acc_141
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((41533720893661563846206482311205371897195853024687889444099883272216698110652 : Nat) : Fp) - ((104771248853243272236194848180534099944827442851439463989997715693033419914817 : Nat) : Fp))⁻¹ = ((63709139575747425877548772820776256734020496435733866848246126945127018071507 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((41533720893661563846206482311205371897195853024687889444099883272216698110652 : Nat) : Fp) - ((104771248853243272236194848180534099944827442851439463989997715693033419914817 : Nat) : Fp))⁻¹ = ((63709139575747425877548772820776256734020496435733866848246126945127018071507 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_141 : affineAdd acc_141 base_141 = acc_142 := by
  unfold acc_141 base_141 acc_142
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((50473025432973961967967320146606874116870403908968619853667703910850312319789 : Nat) : Fp) - ((111175281461482630465516451385666215051004681245013976528598462758289754744929 : Nat) : Fp))⁻¹ = ((31061033045431448185167346661798067285005731882019348814772279574461470073857 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((50473025432973961967967320146606874116870403908968619853667703910850312319789 : Nat) : Fp) - ((111175281461482630465516451385666215051004681245013976528598462758289754744929 : Nat) : Fp))⁻¹ = ((31061033045431448185167346661798067285005731882019348814772279574461470073857 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_142 : affineAdd acc_142 base_142 = acc_143 := by
  unfold acc_142 base_142 acc_143
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((87823185991211788184309284762850137952436592112622220988032007483043824662964 : Nat) : Fp) - ((105488831999329979845280202950265439784555002249815723414248217238410787198545 : Nat) : Fp))⁻¹ = ((38036353207506657024094158076187261991438135945547631634422757261049827661808 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((87823185991211788184309284762850137952436592112622220988032007483043824662964 : Nat) : Fp) - ((105488831999329979845280202950265439784555002249815723414248217238410787198545 : Nat) : Fp))⁻¹ = ((38036353207506657024094158076187261991438135945547631634422757261049827661808 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_143 : affineAdd acc_143 base_143 = acc_144 := by
  unfold acc_143 base_143 acc_144
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((90163261311683285674689513851666750706603686918501102041262299506509314620988 : Nat) : Fp) - ((17310420785061577297752661644696441307039468088644562990992232456213652941707 : Nat) : Fp))⁻¹ = ((86369998916529827636965199722574415031411795738333105904275302809953139299951 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((90163261311683285674689513851666750706603686918501102041262299506509314620988 : Nat) : Fp) - ((17310420785061577297752661644696441307039468088644562990992232456213652941707 : Nat) : Fp))⁻¹ = ((86369998916529827636965199722574415031411795738333105904275302809953139299951 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_144 : affineAdd acc_144 base_144 = acc_145 := by
  unfold acc_144 base_144 acc_145
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((22551397232250930154134754775306783641591530410463695625277699798220437219399 : Nat) : Fp) - ((82443941766934163206572457262087615792206098199618204196957878539943664124143 : Nat) : Fp))⁻¹ = ((46363934043012935209166268021736760877115105152702770425666626473490843998288 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((22551397232250930154134754775306783641591530410463695625277699798220437219399 : Nat) : Fp) - ((82443941766934163206572457262087615792206098199618204196957878539943664124143 : Nat) : Fp))⁻¹ = ((46363934043012935209166268021736760877115105152702770425666626473490843998288 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_145 : affineAdd acc_145 base_145 = acc_146 := by
  unfold acc_145 base_145 acc_146
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((100298860435074318269866579939242844366430460264739520744523048625540766996065 : Nat) : Fp) - ((103962888990006132945402596005118657935911401245401713878311715854693536019743 : Nat) : Fp))⁻¹ = ((108075583647064523523245629300410829694855345142879361729311225034160867593858 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((100298860435074318269866579939242844366430460264739520744523048625540766996065 : Nat) : Fp) - ((103962888990006132945402596005118657935911401245401713878311715854693536019743 : Nat) : Fp))⁻¹ = ((108075583647064523523245629300410829694855345142879361729311225034160867593858 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_146 : affineAdd acc_146 base_146 = acc_147 := by
  unfold acc_146 base_146 acc_147
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((17848721041874530924046462006098247088013963003544838587581308688097280151280 : Nat) : Fp) - ((76798050358113205419697175833140553167147138571698176181621558826323550756452 : Nat) : Fp))⁻¹ = ((24240723211554246774184742847461488603005540521331564208944403072092039624283 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((17848721041874530924046462006098247088013963003544838587581308688097280151280 : Nat) : Fp) - ((76798050358113205419697175833140553167147138571698176181621558826323550756452 : Nat) : Fp))⁻¹ = ((24240723211554246774184742847461488603005540521331564208944403072092039624283 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_147 : affineAdd acc_147 base_147 = acc_148 := by
  unfold acc_147 base_147 acc_148
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((45623407705562943711880395222077400353581483244328863799912097202000040865402 : Nat) : Fp) - ((47484798214816784752283428012568388928491303787309098798019624575261039535228 : Nat) : Fp))⁻¹ = ((52081706058517892589376950824801772350924322188665810277850990338270062001382 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((45623407705562943711880395222077400353581483244328863799912097202000040865402 : Nat) : Fp) - ((47484798214816784752283428012568388928491303787309098798019624575261039535228 : Nat) : Fp))⁻¹ = ((52081706058517892589376950824801772350924322188665810277850990338270062001382 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_148 : affineAdd acc_148 base_148 = acc_149 := by
  unfold acc_148 base_148 acc_149
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((65611104680918539788679488399408385865507511853104175426681765416774357510107 : Nat) : Fp) - ((97039663311497459657247911541193759080562874005661443810591707745986428879848 : Nat) : Fp))⁻¹ = ((70166373463093335283993950461951917562495770786588310321032484970070025554167 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((65611104680918539788679488399408385865507511853104175426681765416774357510107 : Nat) : Fp) - ((97039663311497459657247911541193759080562874005661443810591707745986428879848 : Nat) : Fp))⁻¹ = ((70166373463093335283993950461951917562495770786588310321032484970070025554167 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_149 : affineAdd acc_149 base_149 = acc_150 := by
  unfold acc_149 base_149 acc_150
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((9175530125303015082993852518922959453678574958986082937661837288658019653921 : Nat) : Fp) - ((109195128225849040977606835881519875573565462568688209681805403608282150647549 : Nat) : Fp))⁻¹ = ((23626277447376755351288367852986749794804469722339198127447889725154233713495 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((9175530125303015082993852518922959453678574958986082937661837288658019653921 : Nat) : Fp) - ((109195128225849040977606835881519875573565462568688209681805403608282150647549 : Nat) : Fp))⁻¹ = ((23626277447376755351288367852986749794804469722339198127447889725154233713495 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_150 : affineAdd acc_150 base_150 = acc_151 := by
  unfold acc_150 base_150 acc_151
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((99405957026185278736888962341521709440058377180351135776332231411165316932338 : Nat) : Fp) - ((29549999707259271673252605691545279799740052232833339972136839518663945868516 : Nat) : Fp))⁻¹ = ((72767176887292941970321404263060106868052720806279590697174121605669220437745 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((99405957026185278736888962341521709440058377180351135776332231411165316932338 : Nat) : Fp) - ((29549999707259271673252605691545279799740052232833339972136839518663945868516 : Nat) : Fp))⁻¹ = ((72767176887292941970321404263060106868052720806279590697174121605669220437745 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_151 : affineAdd acc_151 base_151 = acc_152 := by
  unfold acc_151 base_151 acc_152
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((385323763397091340965387960723257533269278287453460106838431826015871103476 : Nat) : Fp) - ((82879960253585350000979087803723632982965447634585893737399105385978335789638 : Nat) : Fp))⁻¹ = ((32871291287839051145034987546701971963512066822557210937317007093920005182545 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((385323763397091340965387960723257533269278287453460106838431826015871103476 : Nat) : Fp) - ((82879960253585350000979087803723632982965447634585893737399105385978335789638 : Nat) : Fp))⁻¹ = ((32871291287839051145034987546701971963512066822557210937317007093920005182545 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_152 : affineAdd acc_152 base_152 = acc_153 := by
  unfold acc_152 base_152 acc_153
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((37913721730568578793482317157181727653930256717449208778212425598522088421245 : Nat) : Fp) - ((22748028221779319076176510624118970842784515483405130895360428655102883872093 : Nat) : Fp))⁻¹ = ((105138783483464832797602042703195271823520384890042300944928708596176331293633 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((37913721730568578793482317157181727653930256717449208778212425598522088421245 : Nat) : Fp) - ((22748028221779319076176510624118970842784515483405130895360428655102883872093 : Nat) : Fp))⁻¹ = ((105138783483464832797602042703195271823520384890042300944928708596176331293633 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_153 : affineAdd acc_153 base_153 = acc_154 := by
  unfold acc_153 base_153 acc_154
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((101033778425503574014684099111759490344154621228683854436296107272222670739677 : Nat) : Fp) - ((22971131504152232323989187247411808869683627396897027961368542431926019004233 : Nat) : Fp))⁻¹ = ((5697570252922288305502778424625440424059189284753445975871702123340967422867 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((101033778425503574014684099111759490344154621228683854436296107272222670739677 : Nat) : Fp) - ((22971131504152232323989187247411808869683627396897027961368542431926019004233 : Nat) : Fp))⁻¹ = ((5697570252922288305502778424625440424059189284753445975871702123340967422867 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_154 : affineAdd acc_154 base_154 = acc_155 := by
  unfold acc_154 base_154 acc_155
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((62694638710103142966512874778432251245752677992976717721765521316164604626861 : Nat) : Fp) - ((106366286125714711143514653622793217383752466534676761043495549248010028815844 : Nat) : Fp))⁻¹ = ((98638576378853071357337855316187785058148271249286015152713112480342255932966 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((62694638710103142966512874778432251245752677992976717721765521316164604626861 : Nat) : Fp) - ((106366286125714711143514653622793217383752466534676761043495549248010028815844 : Nat) : Fp))⁻¹ = ((98638576378853071357337855316187785058148271249286015152713112480342255932966 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_155 : affineAdd acc_155 base_155 = acc_156 := by
  unfold acc_155 base_155 acc_156
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((81413426396105580183786943568605611210297419672204161304267129474314778869714 : Nat) : Fp) - ((75243349452409400390670867080265400955826636238534964912250945418780832972765 : Nat) : Fp))⁻¹ = ((112818322966711059359493449479537718816955796107747411343482346566433965869674 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((81413426396105580183786943568605611210297419672204161304267129474314778869714 : Nat) : Fp) - ((75243349452409400390670867080265400955826636238534964912250945418780832972765 : Nat) : Fp))⁻¹ = ((112818322966711059359493449479537718816955796107747411343482346566433965869674 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_156 : affineAdd acc_156 base_156 = acc_157 := by
  unfold acc_156 base_156 acc_157
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((21064159776649894241607833220796825188513353040509085695513938191477550484029 : Nat) : Fp) - ((35269368267879876076917370410294906058734293247594447113822550857168296692886 : Nat) : Fp))⁻¹ = ((6645890212555271619156343115189993793115989415904235507472475571405562203107 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((21064159776649894241607833220796825188513353040509085695513938191477550484029 : Nat) : Fp) - ((35269368267879876076917370410294906058734293247594447113822550857168296692886 : Nat) : Fp))⁻¹ = ((6645890212555271619156343115189993793115989415904235507472475571405562203107 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_157 : affineAdd acc_157 base_157 = acc_158 := by
  unfold acc_157 base_157 acc_158
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((8067130280375955498155270582300992518528567789421409511369299258617075631199 : Nat) : Fp) - ((107287887465783333787672797357624470089624197428007725918345876586585458515460 : Nat) : Fp))⁻¹ = ((33917142326106607441360529782606538305250183667173662781718421417648130026899 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((8067130280375955498155270582300992518528567789421409511369299258617075631199 : Nat) : Fp) - ((107287887465783333787672797357624470089624197428007725918345876586585458515460 : Nat) : Fp))⁻¹ = ((33917142326106607441360529782606538305250183667173662781718421417648130026899 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_158 : affineAdd acc_158 base_158 = acc_159 := by
  unfold acc_158 base_158 acc_159
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((45761152285074963888706750847007678101194029126391568292164862834287743236260 : Nat) : Fp) - ((104996070104664638505320040442013632557530551413809799698237157067229055154261 : Nat) : Fp))⁻¹ = ((79242134661610478768103906655066478671445551471045971085472607780762394678386 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((45761152285074963888706750847007678101194029126391568292164862834287743236260 : Nat) : Fp) - ((104996070104664638505320040442013632557530551413809799698237157067229055154261 : Nat) : Fp))⁻¹ = ((79242134661610478768103906655066478671445551471045971085472607780762394678386 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_159 : affineAdd acc_159 base_159 = acc_160 := by
  unfold acc_159 base_159 acc_160
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((18560929348648493496902303852929981826943633598245840785444694875193215692174 : Nat) : Fp) - ((28519628026037066657027912209611592939997525521524547924497404284374169515054 : Nat) : Fp))⁻¹ = ((41203005336695993624526582462380562568136540197201117590268195013576952701 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((18560929348648493496902303852929981826943633598245840785444694875193215692174 : Nat) : Fp) - ((28519628026037066657027912209611592939997525521524547924497404284374169515054 : Nat) : Fp))⁻¹ = ((41203005336695993624526582462380562568136540197201117590268195013576952701 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_160 : affineAdd acc_160 base_160 = acc_161 := by
  unfold acc_160 base_160 acc_161
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((82573376505735398797749460473420703975557479532007200170569724442995876740115 : Nat) : Fp) - ((70661691742434068036519986667419907196041281127668848645928138120846244813005 : Nat) : Fp))⁻¹ = ((108853197125971009563366884477325458653928848282405599575984416349853600115688 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((82573376505735398797749460473420703975557479532007200170569724442995876740115 : Nat) : Fp) - ((70661691742434068036519986667419907196041281127668848645928138120846244813005 : Nat) : Fp))⁻¹ = ((108853197125971009563366884477325458653928848282405599575984416349853600115688 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_161 : affineAdd acc_161 base_161 = acc_162 := by
  unfold acc_161 base_161 acc_162
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((50613684197574533383325475395772840295275209808597143405520121315576830549186 : Nat) : Fp) - ((20912437725801942983686217293131152237262404596163037810613525995454376577516 : Nat) : Fp))⁻¹ = ((88899371733804217873743281143878819256649704711864067759318608161809565038215 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((50613684197574533383325475395772840295275209808597143405520121315576830549186 : Nat) : Fp) - ((20912437725801942983686217293131152237262404596163037810613525995454376577516 : Nat) : Fp))⁻¹ = ((88899371733804217873743281143878819256649704711864067759318608161809565038215 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_162 : affineAdd acc_162 base_162 = acc_163 := by
  unfold acc_162 base_162 acc_163
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((62248462504263467714584230639972138759161200691249656819712187384075316604332 : Nat) : Fp) - ((105337008461688988395496963115550441795554320308823072776506794583685171281126 : Nat) : Fp))⁻¹ = ((100054210163338896239875721739371323095016802538682799682745646506047696148899 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((62248462504263467714584230639972138759161200691249656819712187384075316604332 : Nat) : Fp) - ((105337008461688988395496963115550441795554320308823072776506794583685171281126 : Nat) : Fp))⁻¹ = ((100054210163338896239875721739371323095016802538682799682745646506047696148899 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_163 : affineAdd acc_163 base_163 = acc_164 := by
  unfold acc_163 base_163 acc_164
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((94304331522273496808116349343247115097055453840393084609261207752741124358128 : Nat) : Fp) - ((75685728382744045810490612211978229115853638039525209649070995925887462388674 : Nat) : Fp))⁻¹ = ((93307197374415787349693296025328060606432412359732646715837011266400224611123 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((94304331522273496808116349343247115097055453840393084609261207752741124358128 : Nat) : Fp) - ((75685728382744045810490612211978229115853638039525209649070995925887462388674 : Nat) : Fp))⁻¹ = ((93307197374415787349693296025328060606432412359732646715837011266400224611123 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_164 : affineAdd acc_164 base_164 = acc_165 := by
  unfold acc_164 base_164 acc_165
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((114749105857829616057603277433445827949030992454201980219292508691539427079064 : Nat) : Fp) - ((43575908198494793243005774075373759548810068549539444933972772880645886663141 : Nat) : Fp))⁻¹ = ((45891621481201147318985095702665522390399275500734325336036944583160390080385 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((114749105857829616057603277433445827949030992454201980219292508691539427079064 : Nat) : Fp) - ((43575908198494793243005774075373759548810068549539444933972772880645886663141 : Nat) : Fp))⁻¹ = ((45891621481201147318985095702665522390399275500734325336036944583160390080385 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_165 : affineAdd acc_165 base_165 = acc_166 := by
  unfold acc_165 base_165 acc_166
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((73156421406644187235081997026000499221545159563463308076613754647691436301708 : Nat) : Fp) - ((46793159748319014521754592728195492543648682627431155803053172123841138087004 : Nat) : Fp))⁻¹ = ((76535405150117600753192183791459190159453537991719070123083179574723266435519 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((73156421406644187235081997026000499221545159563463308076613754647691436301708 : Nat) : Fp) - ((46793159748319014521754592728195492543648682627431155803053172123841138087004 : Nat) : Fp))⁻¹ = ((76535405150117600753192183791459190159453537991719070123083179574723266435519 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_166 : affineAdd acc_166 base_166 = acc_167 := by
  unfold acc_166 base_166 acc_167
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((62734468877395534755757165923205128268653264925969806142579124920023589270036 : Nat) : Fp) - ((101757012457202265442783729516325848567041695344201435111479322003948473610273 : Nat) : Fp))⁻¹ = ((31220531487909877169988466596264696714585060747481735585090834575969600912889 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((62734468877395534755757165923205128268653264925969806142579124920023589270036 : Nat) : Fp) - ((101757012457202265442783729516325848567041695344201435111479322003948473610273 : Nat) : Fp))⁻¹ = ((31220531487909877169988466596264696714585060747481735585090834575969600912889 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_167 : affineAdd acc_167 base_167 = acc_168 := by
  unfold acc_167 base_167 acc_168
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((112172446824784397943995176919888054471487948449592980499391769875633346581368 : Nat) : Fp) - ((30209700677164570836251569796863977697827501003939778269324249569134489792003 : Nat) : Fp))⁻¹ = ((68250901006927563246622190275032859964824268075700880170571069519405129605158 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((112172446824784397943995176919888054471487948449592980499391769875633346581368 : Nat) : Fp) - ((30209700677164570836251569796863977697827501003939778269324249569134489792003 : Nat) : Fp))⁻¹ = ((68250901006927563246622190275032859964824268075700880170571069519405129605158 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_168 : affineAdd acc_168 base_168 = acc_169 := by
  unfold acc_168 base_168 acc_169
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((93912565785139307016161950679622968781046914571229830494986975930576605778711 : Nat) : Fp) - ((74841650891382527078449938271109455202772530131693735678356618476847598486118 : Nat) : Fp))⁻¹ = ((18988983908015899195006736307188576132764386858049141884066684202484329325325 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((93912565785139307016161950679622968781046914571229830494986975930576605778711 : Nat) : Fp) - ((74841650891382527078449938271109455202772530131693735678356618476847598486118 : Nat) : Fp))⁻¹ = ((18988983908015899195006736307188576132764386858049141884066684202484329325325 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_169 : affineAdd acc_169 base_169 = acc_170 := by
  unfold acc_169 base_169 acc_170
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((35226059335101933311749405272571863457568325597634905831690332789817180515430 : Nat) : Fp) - ((71631157476704051659259801706240663560508572801269375166786124610215506626710 : Nat) : Fp))⁻¹ = ((98595601953659141033272492743511601286529178010102811823100757566773313878762 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((35226059335101933311749405272571863457568325597634905831690332789817180515430 : Nat) : Fp) - ((71631157476704051659259801706240663560508572801269375166786124610215506626710 : Nat) : Fp))⁻¹ = ((98595601953659141033272492743511601286529178010102811823100757566773313878762 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_170 : affineAdd acc_170 base_170 = acc_171 := by
  unfold acc_170 base_170 acc_171
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((113149396721675226183785687199223313575294111180927885353779286447025943321527 : Nat) : Fp) - ((75928542468193195488721590741574481272714198891253064800438184108329627778720 : Nat) : Fp))⁻¹ = ((65111304026727919797351979263332624930066414445158960162590549589767278355690 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((113149396721675226183785687199223313575294111180927885353779286447025943321527 : Nat) : Fp) - ((75928542468193195488721590741574481272714198891253064800438184108329627778720 : Nat) : Fp))⁻¹ = ((65111304026727919797351979263332624930066414445158960162590549589767278355690 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_171 : affineAdd acc_171 base_171 = acc_172 := by
  unfold acc_171 base_171 acc_172
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((2070204883874586979755513349640918964830615684643216416182655782655758594541 : Nat) : Fp) - ((87929611941466450580474503142124427241088012317746799540322218015595119056635 : Nat) : Fp))⁻¹ = ((21338942316243590186713972784738127644470407206062892067146266256386508934726 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((2070204883874586979755513349640918964830615684643216416182655782655758594541 : Nat) : Fp) - ((87929611941466450580474503142124427241088012317746799540322218015595119056635 : Nat) : Fp))⁻¹ = ((21338942316243590186713972784738127644470407206062892067146266256386508934726 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_172 : affineAdd acc_172 base_172 = acc_173 := by
  unfold acc_172 base_172 acc_173
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((29873748141905807058024221897945895150426782627928752455872311607406879110292 : Nat) : Fp) - ((54038406999518685708957755903010924118312453838615747233838912018122735660401 : Nat) : Fp))⁻¹ = ((3291068362066723207429139003522351778576822332670375016317315074559510518608 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((29873748141905807058024221897945895150426782627928752455872311607406879110292 : Nat) : Fp) - ((54038406999518685708957755903010924118312453838615747233838912018122735660401 : Nat) : Fp))⁻¹ = ((3291068362066723207429139003522351778576822332670375016317315074559510518608 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_173 : affineAdd acc_173 base_173 = acc_174 := by
  unfold acc_173 base_173 acc_174
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((52711587612775625797697341722512137836488587027913421465260586332499447009502 : Nat) : Fp) - ((104811972735495353830322167991327219943131946744088941348424456729187245615225 : Nat) : Fp))⁻¹ = ((69244804050599715289332812552750229651040291103253916767875528574454557115707 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((52711587612775625797697341722512137836488587027913421465260586332499447009502 : Nat) : Fp) - ((104811972735495353830322167991327219943131946744088941348424456729187245615225 : Nat) : Fp))⁻¹ = ((69244804050599715289332812552750229651040291103253916767875528574454557115707 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_174 : affineAdd acc_174 base_174 = acc_175 := by
  unfold acc_174 base_174 acc_175
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((114929085248450553725830617566960843911747044598908522223285933841276842744276 : Nat) : Fp) - ((3215551885474507458266292022538992596230437910109015106438584379300426977039 : Nat) : Fp))⁻¹ = ((19843999862106051120767045926630556380101096617905873861441183663562449223860 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((114929085248450553725830617566960843911747044598908522223285933841276842744276 : Nat) : Fp) - ((3215551885474507458266292022538992596230437910109015106438584379300426977039 : Nat) : Fp))⁻¹ = ((19843999862106051120767045926630556380101096617905873861441183663562449223860 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_175 : affineAdd acc_175 base_175 = acc_176 := by
  unfold acc_175 base_175 acc_176
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((42506850229344260533699254673607416329486700005533824580814509045108411872876 : Nat) : Fp) - ((947390502650680957920869582008711724723808429374401610775941200653824958689 : Nat) : Fp))⁻¹ = ((101465364464290200697308480159985337332073612507279640673014777298430851964818 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((42506850229344260533699254673607416329486700005533824580814509045108411872876 : Nat) : Fp) - ((947390502650680957920869582008711724723808429374401610775941200653824958689 : Nat) : Fp))⁻¹ = ((101465364464290200697308480159985337332073612507279640673014777298430851964818 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_176 : affineAdd acc_176 base_176 = acc_177 := by
  unfold acc_176 base_176 acc_177
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((22688283644905229582878684955816599114744435964831567715612498102492263638185 : Nat) : Fp) - ((4142520438525914541011842624208056062406705649998025173845082041682105009068 : Nat) : Fp))⁻¹ = ((60161004446221059394771016197804238763497729095594868229414568348775166753216 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((22688283644905229582878684955816599114744435964831567715612498102492263638185 : Nat) : Fp) - ((4142520438525914541011842624208056062406705649998025173845082041682105009068 : Nat) : Fp))⁻¹ = ((60161004446221059394771016197804238763497729095594868229414568348775166753216 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_177 : affineAdd acc_177 base_177 = acc_178 := by
  unfold acc_177 base_177 acc_178
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((56313531445760181520291524148546735166936497593520315965293404361066917373463 : Nat) : Fp) - ((35976083938318534650029463496695503152893117754555618189020557340809841204638 : Nat) : Fp))⁻¹ = ((89573377283628261466453552940626466504435739430573715533514401742470838954235 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((56313531445760181520291524148546735166936497593520315965293404361066917373463 : Nat) : Fp) - ((35976083938318534650029463496695503152893117754555618189020557340809841204638 : Nat) : Fp))⁻¹ = ((89573377283628261466453552940626466504435739430573715533514401742470838954235 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_178 : affineAdd acc_178 base_178 = acc_179 := by
  unfold acc_178 base_178 acc_179
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((61395379527807154589910593530388813956074296196146759454533147536489311870064 : Nat) : Fp) - ((92099574356616060718641758322300714450252979003106256663913657963750974558615 : Nat) : Fp))⁻¹ = ((18071558580930824252325113941449708364396478135557002264565350740337439166880 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((61395379527807154589910593530388813956074296196146759454533147536489311870064 : Nat) : Fp) - ((92099574356616060718641758322300714450252979003106256663913657963750974558615 : Nat) : Fp))⁻¹ = ((18071558580930824252325113941449708364396478135557002264565350740337439166880 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_179 : affineAdd acc_179 base_179 = acc_180 := by
  unfold acc_179 base_179 acc_180
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((60602008552774070692677442494729302278814488972178655463377434598891056704362 : Nat) : Fp) - ((102652556215175073222018368450968179239643399116479030486157396231787228507330 : Nat) : Fp))⁻¹ = ((21252119201427211932154814696056698961395735041651773455274750532190016967653 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((60602008552774070692677442494729302278814488972178655463377434598891056704362 : Nat) : Fp) - ((102652556215175073222018368450968179239643399116479030486157396231787228507330 : Nat) : Fp))⁻¹ = ((21252119201427211932154814696056698961395735041651773455274750532190016967653 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_180 : affineAdd acc_180 base_180 = acc_181 := by
  unfold acc_180 base_180 acc_181
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((63486259634284010518869700171992398503661545992267646023489026482566456550680 : Nat) : Fp) - ((60526872670786283833918632266282189958727983389364017821054603492994282170193 : Nat) : Fp))⁻¹ = ((109842439443402363391336068412857113924029189597686642247673950707666226211821 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((63486259634284010518869700171992398503661545992267646023489026482566456550680 : Nat) : Fp) - ((60526872670786283833918632266282189958727983389364017821054603492994282170193 : Nat) : Fp))⁻¹ = ((109842439443402363391336068412857113924029189597686642247673950707666226211821 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_181 : affineAdd acc_181 base_181 = acc_182 := by
  unfold acc_181 base_181 acc_182
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((54101560700677057488529534741850644660042807169323832715061677300725817542945 : Nat) : Fp) - ((48611368844139479430646292898246827799543615133757497943303942111011000011486 : Nat) : Fp))⁻¹ = ((43146862088719298559572586568173400851826987406405918237382418416472361311611 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((54101560700677057488529534741850644660042807169323832715061677300725817542945 : Nat) : Fp) - ((48611368844139479430646292898246827799543615133757497943303942111011000011486 : Nat) : Fp))⁻¹ = ((43146862088719298559572586568173400851826987406405918237382418416472361311611 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_182 : affineAdd acc_182 base_182 = acc_183 := by
  unfold acc_182 base_182 acc_183
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((58803828977889904056958201134416749289453418644284312180892862150470978232871 : Nat) : Fp) - ((29436743060920481988952312356424937775284815172144744489261980482023293444299 : Nat) : Fp))⁻¹ = ((71928911070843367941301810484939002347937551514338963008180693041964205593433 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((58803828977889904056958201134416749289453418644284312180892862150470978232871 : Nat) : Fp) - ((29436743060920481988952312356424937775284815172144744489261980482023293444299 : Nat) : Fp))⁻¹ = ((71928911070843367941301810484939002347937551514338963008180693041964205593433 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_183 : affineAdd acc_183 base_183 = acc_184 := by
  unfold acc_183 base_183 acc_184
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((66518931987740708092984178574691790016917337737952891688123449635061325216156 : Nat) : Fp) - ((94976567038575040138507300949054306311784168683241399150467020165872178418684 : Nat) : Fp))⁻¹ = ((1078092320179157286493339517493633871902442908982202175663643268196656026816 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((66518931987740708092984178574691790016917337737952891688123449635061325216156 : Nat) : Fp) - ((94976567038575040138507300949054306311784168683241399150467020165872178418684 : Nat) : Fp))⁻¹ = ((1078092320179157286493339517493633871902442908982202175663643268196656026816 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_184 : affineAdd acc_184 base_184 = acc_185 := by
  unfold acc_184 base_184 acc_185
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((114989896324114142582880091593198513170996485363105493920687794509420983332961 : Nat) : Fp) - ((115415846104970316816674669646231381722554829723945808246505339409944432478334 : Nat) : Fp))⁻¹ = ((113628986204163545027594076938298838009917531616542344038704783938450271194139 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((114989896324114142582880091593198513170996485363105493920687794509420983332961 : Nat) : Fp) - ((115415846104970316816674669646231381722554829723945808246505339409944432478334 : Nat) : Fp))⁻¹ = ((113628986204163545027594076938298838009917531616542344038704783938450271194139 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_185 : affineAdd acc_185 base_185 = acc_186 := by
  unfold acc_185 base_185 acc_186
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((103027176964090739901348021419433442083819779335333888871571742362270166514167 : Nat) : Fp) - ((18776033471282089014310671094577787458033563645391456854929614351132929947887 : Nat) : Fp))⁻¹ = ((110272872051869070114382282310761764129424411573318330834489176729341117937538 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((103027176964090739901348021419433442083819779335333888871571742362270166514167 : Nat) : Fp) - ((18776033471282089014310671094577787458033563645391456854929614351132929947887 : Nat) : Fp))⁻¹ = ((110272872051869070114382282310761764129424411573318330834489176729341117937538 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_186 : affineAdd acc_186 base_186 = acc_187 := by
  unfold acc_186 base_186 acc_187
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((4204695906946780589313791879208530286494667006376374838986876141639449894612 : Nat) : Fp) - ((11832388558031419782808688022015883762691763226078981998965787321613871498267 : Nat) : Fp))⁻¹ = ((12143224076899706010784843425410562291197017324655310437498678924234611873297 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((4204695906946780589313791879208530286494667006376374838986876141639449894612 : Nat) : Fp) - ((11832388558031419782808688022015883762691763226078981998965787321613871498267 : Nat) : Fp))⁻¹ = ((12143224076899706010784843425410562291197017324655310437498678924234611873297 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_187 : affineAdd acc_187 base_187 = acc_188 := by
  unfold acc_187 base_187 acc_188
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((54242991660078524246918591746260064059264467522232695105655327418938766831688 : Nat) : Fp) - ((5674256344222473770316337151722717121901524681814366176584467328211802271911 : Nat) : Fp))⁻¹ = ((56120660580177721301335641827243460340976355921690086317672841931278083391363 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((54242991660078524246918591746260064059264467522232695105655327418938766831688 : Nat) : Fp) - ((5674256344222473770316337151722717121901524681814366176584467328211802271911 : Nat) : Fp))⁻¹ = ((56120660580177721301335641827243460340976355921690086317672841931278083391363 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_188 : affineAdd acc_188 base_188 = acc_189 := by
  unfold acc_188 base_188 acc_189
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((47641762048130959225463157744936741734004477513581969797239495873127107041545 : Nat) : Fp) - ((59026356685222097294628395983368866596266777678130656463811370893799945855553 : Nat) : Fp))⁻¹ = ((7262561139955443793437268117434230281350018003379033965910228068328915125444 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((47641762048130959225463157744936741734004477513581969797239495873127107041545 : Nat) : Fp) - ((59026356685222097294628395983368866596266777678130656463811370893799945855553 : Nat) : Fp))⁻¹ = ((7262561139955443793437268117434230281350018003379033965910228068328915125444 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_189 : affineAdd acc_189 base_189 = acc_190 := by
  unfold acc_189 base_189 acc_190
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((69472768068364136774272514248217981945764793800798781763504648168259253466708 : Nat) : Fp) - ((82997769624973021721207329827925752179285999209160244580518381248798973329757 : Nat) : Fp))⁻¹ = ((21721045048987011201093357784390767639239629945480579601818571664655366261719 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((69472768068364136774272514248217981945764793800798781763504648168259253466708 : Nat) : Fp) - ((82997769624973021721207329827925752179285999209160244580518381248798973329757 : Nat) : Fp))⁻¹ = ((21721045048987011201093357784390767639239629945480579601818571664655366261719 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_190 : affineAdd acc_190 base_190 = acc_191 := by
  unfold acc_190 base_190 acc_191
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((7479663366765373719254913328326893330953174271598814660940401003642652305012 : Nat) : Fp) - ((32833730202948453445551585602227016221189718115335492475756041315423310145004 : Nat) : Fp))⁻¹ = ((52267751777366758791814252354642272005017981014984635831787060366911903466477 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((7479663366765373719254913328326893330953174271598814660940401003642652305012 : Nat) : Fp) - ((32833730202948453445551585602227016221189718115335492475756041315423310145004 : Nat) : Fp))⁻¹ = ((52267751777366758791814252354642272005017981014984635831787060366911903466477 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_191 : affineAdd acc_191 base_191 = acc_192 := by
  unfold acc_191 base_191 acc_192
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((93214559303503295622146213850162265162499163294906951100460861720335563037717 : Nat) : Fp) - ((105475728434031409379183406694662903881450546214247029555786593600199689335290 : Nat) : Fp))⁻¹ = ((103058029251629410146062178544611021149635485256602727985626951102478112777370 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((93214559303503295622146213850162265162499163294906951100460861720335563037717 : Nat) : Fp) - ((105475728434031409379183406694662903881450546214247029555786593600199689335290 : Nat) : Fp))⁻¹ = ((103058029251629410146062178544611021149635485256602727985626951102478112777370 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_192 : affineAdd acc_192 base_192 = acc_193 := by
  unfold acc_192 base_192 acc_193
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((19436059746748227418925458231805909355641770432714992717682190711891460146984 : Nat) : Fp) - ((106135013536326263233204638779771538367307463662639765758785315935371743257267 : Nat) : Fp))⁻¹ = ((8879185418153478979486305229954286412038278791846721905284530584363815516087 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((19436059746748227418925458231805909355641770432714992717682190711891460146984 : Nat) : Fp) - ((106135013536326263233204638779771538367307463662639765758785315935371743257267 : Nat) : Fp))⁻¹ = ((8879185418153478979486305229954286412038278791846721905284530584363815516087 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_193 : affineAdd acc_193 base_193 = acc_194 := by
  unfold acc_193 base_193 acc_194
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((113244355352594671284226941655179016027454160970747784394405576931970465735633 : Nat) : Fp) - ((26622173145108500381473837459513401868318671376325266944487505521378511663272 : Nat) : Fp))⁻¹ = ((2205035472295119087969296286724060866640246294511554335415800932147833311525 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((113244355352594671284226941655179016027454160970747784394405576931970465735633 : Nat) : Fp) - ((26622173145108500381473837459513401868318671376325266944487505521378511663272 : Nat) : Fp))⁻¹ = ((2205035472295119087969296286724060866640246294511554335415800932147833311525 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_194 : affineAdd acc_194 base_194 = acc_195 := by
  unfold acc_194 base_194 acc_195
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((103323434291070884810043926593444845888906981086108116030348704516931883710008 : Nat) : Fp) - ((8421370599800668602652103103676786751239058426611888163586601660098353727225 : Nat) : Fp))⁻¹ = ((76659248105670552820755341575565564010316363111886160026810190375603279870032 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((103323434291070884810043926593444845888906981086108116030348704516931883710008 : Nat) : Fp) - ((8421370599800668602652103103676786751239058426611888163586601660098353727225 : Nat) : Fp))⁻¹ = ((76659248105670552820755341575565564010316363111886160026810190375603279870032 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_195 : affineAdd acc_195 base_195 = acc_196 := by
  unfold acc_195 base_195 acc_196
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((80822841823700864217117565279855889926619437465175519975430218626939254678860 : Nat) : Fp) - ((43457843735276724612075728233726406612249501219998543099634755887188281768154 : Nat) : Fp))⁻¹ = ((89997006308756290461065067505594950366217440120303658218218309112878572732252 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((80822841823700864217117565279855889926619437465175519975430218626939254678860 : Nat) : Fp) - ((43457843735276724612075728233726406612249501219998543099634755887188281768154 : Nat) : Fp))⁻¹ = ((89997006308756290461065067505594950366217440120303658218218309112878572732252 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_196 : affineAdd acc_196 base_196 = acc_197 := by
  unfold acc_196 base_196 acc_197
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((51096724926566392371895137521611104302365830865332930293042238411804011589445 : Nat) : Fp) - ((103417404801342136514940355813672218236352240817568397971691640510748940358223 : Nat) : Fp))⁻¹ = ((69969442398284733338964593958781511413114391414718537460806160263775718935603 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((51096724926566392371895137521611104302365830865332930293042238411804011589445 : Nat) : Fp) - ((103417404801342136514940355813672218236352240817568397971691640510748940358223 : Nat) : Fp))⁻¹ = ((69969442398284733338964593958781511413114391414718537460806160263775718935603 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_197 : affineAdd acc_197 base_197 = acc_198 := by
  unfold acc_197 base_197 acc_198
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((90681586653169617779724882027536820663872472108929860672486884584989353164892 : Nat) : Fp) - ((114612401220431600857626100267884543594407662822495910668441731424729600844475 : Nat) : Fp))⁻¹ = ((90135773715411718086314408565051360781842220377078857437736757931441067373367 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((90681586653169617779724882027536820663872472108929860672486884584989353164892 : Nat) : Fp) - ((114612401220431600857626100267884543594407662822495910668441731424729600844475 : Nat) : Fp))⁻¹ = ((90135773715411718086314408565051360781842220377078857437736757931441067373367 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_198 : affineAdd acc_198 base_198 = acc_199 := by
  unfold acc_198 base_198 acc_199
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((41097730418687468851840028126570808766847487756664368122837651685823309251855 : Nat) : Fp) - ((13990119276603863648855793891913240987255865021321113597676024132284912134507 : Nat) : Fp))⁻¹ = ((63987752683982649458635192431524308123612798230801350522751171244520950556859 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((41097730418687468851840028126570808766847487756664368122837651685823309251855 : Nat) : Fp) - ((13990119276603863648855793891913240987255865021321113597676024132284912134507 : Nat) : Fp))⁻¹ = ((63987752683982649458635192431524308123612798230801350522751171244520950556859 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_199 : affineAdd acc_199 base_199 = acc_200 := by
  unfold acc_199 base_199 acc_200
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((100704980427187950776566009868772393822532287775712850841327750834699511142076 : Nat) : Fp) - ((92297683643826826163064140665368589970769892635084083631213834209281061470421 : Nat) : Fp))⁻¹ = ((88124043092446520567738746147020728400799491054832504671447353945981754931048 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((100704980427187950776566009868772393822532287775712850841327750834699511142076 : Nat) : Fp) - ((92297683643826826163064140665368589970769892635084083631213834209281061470421 : Nat) : Fp))⁻¹ = ((88124043092446520567738746147020728400799491054832504671447353945981754931048 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_200 : affineAdd acc_200 base_200 = acc_201 := by
  unfold acc_200 base_200 acc_201
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((41963437398022779394570776873507781528187696448205583322868397102405779089972 : Nat) : Fp) - ((13922864845768229163833387034770518418928910654248512738626529054912919158553 : Nat) : Fp))⁻¹ = ((383480225141101630050460138894634914935486625178804902844152791702514976058 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((41963437398022779394570776873507781528187696448205583322868397102405779089972 : Nat) : Fp) - ((13922864845768229163833387034770518418928910654248512738626529054912919158553 : Nat) : Fp))⁻¹ = ((383480225141101630050460138894634914935486625178804902844152791702514976058 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_201 : affineAdd acc_201 base_201 = acc_202 := by
  unfold acc_201 base_201 acc_202
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((64419789759124835279729547014899220968818131819816898784308065307874796862988 : Nat) : Fp) - ((41570227333295029806389479208245314517359112018029925112212608294602008426980 : Nat) : Fp))⁻¹ = ((49790284171841397450154978450965412305994050113933397936704449284999676580092 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((64419789759124835279729547014899220968818131819816898784308065307874796862988 : Nat) : Fp) - ((41570227333295029806389479208245314517359112018029925112212608294602008426980 : Nat) : Fp))⁻¹ = ((49790284171841397450154978450965412305994050113933397936704449284999676580092 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_202 : affineAdd acc_202 base_202 = acc_203 := by
  unfold acc_202 base_202 acc_203
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((62762142072396476060995371274969129115807131197458019781481479852775245520736 : Nat) : Fp) - ((40228630408040464220910435747595136926324159053542900046172368281189438159800 : Nat) : Fp))⁻¹ = ((99527230852046696571638344830668688238594463334032165550028722780605184231650 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((62762142072396476060995371274969129115807131197458019781481479852775245520736 : Nat) : Fp) - ((40228630408040464220910435747595136926324159053542900046172368281189438159800 : Nat) : Fp))⁻¹ = ((99527230852046696571638344830668688238594463334032165550028722780605184231650 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_203 : affineAdd acc_203 base_203 = acc_204 := by
  unfold acc_203 base_203 acc_204
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((81615542260013623080339118753093837651874029535279762844239949691510089428628 : Nat) : Fp) - ((80048584874349841980004729440562797202284935506199377684670339908062345334316 : Nat) : Fp))⁻¹ = ((71762829398879345316442086298898711153261823758105932931456914996811838700942 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((81615542260013623080339118753093837651874029535279762844239949691510089428628 : Nat) : Fp) - ((80048584874349841980004729440562797202284935506199377684670339908062345334316 : Nat) : Fp))⁻¹ = ((71762829398879345316442086298898711153261823758105932931456914996811838700942 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_204 : affineAdd acc_204 base_204 = acc_205 := by
  unfold acc_204 base_204 acc_205
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((48726931970016250047517938777773102332101668546633360222010741296033996096059 : Nat) : Fp) - ((9234367843203278475460402406049705063687486936070061072085337642077459464894 : Nat) : Fp))⁻¹ = ((59588638951776202098518588831743462771329860287415613431493238580831384947153 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((48726931970016250047517938777773102332101668546633360222010741296033996096059 : Nat) : Fp) - ((9234367843203278475460402406049705063687486936070061072085337642077459464894 : Nat) : Fp))⁻¹ = ((59588638951776202098518588831743462771329860287415613431493238580831384947153 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_205 : affineAdd acc_205 base_205 = acc_206 := by
  unfold acc_205 base_205 acc_206
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((54035609470183790619350063949481307628740160218997884888697305595486899105681 : Nat) : Fp) - ((39490693885239044366982942241753219569930195973938085206409539076747633253548 : Nat) : Fp))⁻¹ = ((50680992848193936821522650099889565886078124654376549144769149029997225225385 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((54035609470183790619350063949481307628740160218997884888697305595486899105681 : Nat) : Fp) - ((39490693885239044366982942241753219569930195973938085206409539076747633253548 : Nat) : Fp))⁻¹ = ((50680992848193936821522650099889565886078124654376549144769149029997225225385 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_206 : affineAdd acc_206 base_206 = acc_207 := by
  unfold acc_206 base_206 acc_207
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((71920580694916078600878092949303681142291501514878757409581660259274225713408 : Nat) : Fp) - ((95822289762910972444474447423403522943496613059597976864337566726465943856851 : Nat) : Fp))⁻¹ = ((96763701360216495830802840835927505154667995291717533904737321959026911585123 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((71920580694916078600878092949303681142291501514878757409581660259274225713408 : Nat) : Fp) - ((95822289762910972444474447423403522943496613059597976864337566726465943856851 : Nat) : Fp))⁻¹ = ((96763701360216495830802840835927505154667995291717533904737321959026911585123 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_207 : affineAdd acc_207 base_207 = acc_208 := by
  unfold acc_207 base_207 acc_208
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((110649361901339181582290433203418318532663230954106722444955944360769864936149 : Nat) : Fp) - ((80360436639024982802108928438318908385607328476345612824787216050095821450571 : Nat) : Fp))⁻¹ = ((2668245512067086836767650795553489498708424151055161226754243900932290179949 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((110649361901339181582290433203418318532663230954106722444955944360769864936149 : Nat) : Fp) - ((80360436639024982802108928438318908385607328476345612824787216050095821450571 : Nat) : Fp))⁻¹ = ((2668245512067086836767650795553489498708424151055161226754243900932290179949 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_208 : affineAdd acc_208 base_208 = acc_209 := by
  unfold acc_208 base_208 acc_209
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((109961148091824176007590053632285201349622686517333656494286472429021334697930 : Nat) : Fp) - ((113220891681512744492539364929916345410061947313878915456447722256969001660153 : Nat) : Fp))⁻¹ = ((44671888373603338565049029283249698617355207720800782252605342924322595350257 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((109961148091824176007590053632285201349622686517333656494286472429021334697930 : Nat) : Fp) - ((113220891681512744492539364929916345410061947313878915456447722256969001660153 : Nat) : Fp))⁻¹ = ((44671888373603338565049029283249698617355207720800782252605342924322595350257 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_209 : affineAdd acc_209 base_209 = acc_210 := by
  unfold acc_209 base_209 acc_210
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((46951501587352933349155760188503284574509445044054321376621673100514231210604 : Nat) : Fp) - ((45044543832417204813964322358265561912289006474729602217500750943638473625672 : Nat) : Fp))⁻¹ = ((16458380386291940365457429353551309115234708094674211290246834818446816027486 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((46951501587352933349155760188503284574509445044054321376621673100514231210604 : Nat) : Fp) - ((45044543832417204813964322358265561912289006474729602217500750943638473625672 : Nat) : Fp))⁻¹ = ((16458380386291940365457429353551309115234708094674211290246834818446816027486 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_210 : affineAdd acc_210 base_210 = acc_211 := by
  unfold acc_210 base_210 acc_211
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((97720067671541014565491635141056425321913971719848552697820062655710295564581 : Nat) : Fp) - ((40815729452528180238295637155137130875534812174241845066103240363483841899109 : Nat) : Fp))⁻¹ = ((82547652485297470537254773973050704181006782103777117567734690113725689944034 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((97720067671541014565491635141056425321913971719848552697820062655710295564581 : Nat) : Fp) - ((40815729452528180238295637155137130875534812174241845066103240363483841899109 : Nat) : Fp))⁻¹ = ((82547652485297470537254773973050704181006782103777117567734690113725689944034 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_211 : affineAdd acc_211 base_211 = acc_212 := by
  unfold acc_211 base_211 acc_212
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((58456002847219606930033165567268340163347895955202507410521224552567431240037 : Nat) : Fp) - ((42019196137391938823787938398084615301261359872699590349124401997914530858192 : Nat) : Fp))⁻¹ = ((29597163191747850857214648509245780190716142011899704306643268935108753211773 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((58456002847219606930033165567268340163347895955202507410521224552567431240037 : Nat) : Fp) - ((42019196137391938823787938398084615301261359872699590349124401997914530858192 : Nat) : Fp))⁻¹ = ((29597163191747850857214648509245780190716142011899704306643268935108753211773 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_212 : affineAdd acc_212 base_212 = acc_213 := by
  unfold acc_212 base_212 acc_213
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((93710686539520880202642124984978698613172097623838661478597627527919706519903 : Nat) : Fp) - ((98656114654415212951351030182220503262040501999861380370740706389056647757506 : Nat) : Fp))⁻¹ = ((70242384552636953633245836247242730219942619490046635166617343282074357388092 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((93710686539520880202642124984978698613172097623838661478597627527919706519903 : Nat) : Fp) - ((98656114654415212951351030182220503262040501999861380370740706389056647757506 : Nat) : Fp))⁻¹ = ((70242384552636953633245836247242730219942619490046635166617343282074357388092 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_213 : affineAdd acc_213 base_213 = acc_214 := by
  unfold acc_213 base_213 acc_214
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((13729583756584371036628625429921855110250353243232558895041351865827625664590 : Nat) : Fp) - ((70779672864013442204047147619761736872402708735011963696772144922503503135593 : Nat) : Fp))⁻¹ = ((75714056605586852655480713934245039743399279545309578486587976705526482681784 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((13729583756584371036628625429921855110250353243232558895041351865827625664590 : Nat) : Fp) - ((70779672864013442204047147619761736872402708735011963696772144922503503135593 : Nat) : Fp))⁻¹ = ((75714056605586852655480713934245039743399279545309578486587976705526482681784 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_214 : affineAdd acc_214 base_214 = acc_215 := by
  unfold acc_214 base_214 acc_215
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((10446955228596413538270086605964137190912466144578740813346210569455704801609 : Nat) : Fp) - ((7147807088254754984115277020319280513928719273510749291220264632533393132003 : Nat) : Fp))⁻¹ = ((5184950478887645754535772479797338131547060019146914745143572119549501281989 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((10446955228596413538270086605964137190912466144578740813346210569455704801609 : Nat) : Fp) - ((7147807088254754984115277020319280513928719273510749291220264632533393132003 : Nat) : Fp))⁻¹ = ((5184950478887645754535772479797338131547060019146914745143572119549501281989 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_215 : affineAdd acc_215 base_215 = acc_216 := by
  unfold acc_215 base_215 acc_216
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((41708199630613563533857844054749904790579703403714948734142644304174964773257 : Nat) : Fp) - ((51318518135047612923054807776796525309348753908885584948123548636564953982193 : Nat) : Fp))⁻¹ = ((7631339381660025773460426601048824929700340568494733285192657169605832991999 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((41708199630613563533857844054749904790579703403714948734142644304174964773257 : Nat) : Fp) - ((51318518135047612923054807776796525309348753908885584948123548636564953982193 : Nat) : Fp))⁻¹ = ((7631339381660025773460426601048824929700340568494733285192657169605832991999 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_216 : affineAdd acc_216 base_216 = acc_217 := by
  unfold acc_216 base_216 acc_217
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((95367128378517088778906915528758206507061675325718874859459424551456925441454 : Nat) : Fp) - ((76388770101766026847299654420802367216385774412973782315160485495908694642195 : Nat) : Fp))⁻¹ = ((77722214715261935504647130234482185352142777803316833187404255187998744569553 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((95367128378517088778906915528758206507061675325718874859459424551456925441454 : Nat) : Fp) - ((76388770101766026847299654420802367216385774412973782315160485495908694642195 : Nat) : Fp))⁻¹ = ((77722214715261935504647130234482185352142777803316833187404255187998744569553 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_217 : affineAdd acc_217 base_217 = acc_218 := by
  unfold acc_217 base_217 acc_218
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((104772712857957687009810078163398532492793836342123717975543767946170854974007 : Nat) : Fp) - ((91718707606862637550154068541437645781425587687664226689694763206157559813025 : Nat) : Fp))⁻¹ = ((36088369341230772326698137715122183375785055102904828943941731043364146859199 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((104772712857957687009810078163398532492793836342123717975543767946170854974007 : Nat) : Fp) - ((91718707606862637550154068541437645781425587687664226689694763206157559813025 : Nat) : Fp))⁻¹ = ((36088369341230772326698137715122183375785055102904828943941731043364146859199 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_218 : affineAdd acc_218 base_218 = acc_219 := by
  unfold acc_218 base_218 acc_219
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((10161864771496804080798517767423742549677304171259080353233424123274977274833 : Nat) : Fp) - ((104427496169569391842377213290478515885839261332812951511591855258537350660157 : Nat) : Fp))⁻¹ = ((63173233223943623651991128978916557571247185001715292259064849035532125387224 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((10161864771496804080798517767423742549677304171259080353233424123274977274833 : Nat) : Fp) - ((104427496169569391842377213290478515885839261332812951511591855258537350660157 : Nat) : Fp))⁻¹ = ((63173233223943623651991128978916557571247185001715292259064849035532125387224 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_219 : affineAdd acc_219 base_219 = acc_220 := by
  unfold acc_219 base_219 acc_220
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((74331454221247671029245522801737699388867226471994116703508684088775243649882 : Nat) : Fp) - ((27276644428692416698688499014810854312801165379030850386665499374796427550985 : Nat) : Fp))⁻¹ = ((42163125879044274810369280265471462669546635181003406465883771062342417448914 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((74331454221247671029245522801737699388867226471994116703508684088775243649882 : Nat) : Fp) - ((27276644428692416698688499014810854312801165379030850386665499374796427550985 : Nat) : Fp))⁻¹ = ((42163125879044274810369280265471462669546635181003406465883771062342417448914 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_220 : affineAdd acc_220 base_220 = acc_221 := by
  unfold acc_220 base_220 acc_221
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((100359178303740786438883038125571840410727210042578402665267813525668086889985 : Nat) : Fp) - ((10534520053980272543867405036685817400667875723664235737120499452559222196604 : Nat) : Fp))⁻¹ = ((85613509556059385206275684878733623134510068425541969790602509270972312795159 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((100359178303740786438883038125571840410727210042578402665267813525668086889985 : Nat) : Fp) - ((10534520053980272543867405036685817400667875723664235737120499452559222196604 : Nat) : Fp))⁻¹ = ((85613509556059385206275684878733623134510068425541969790602509270972312795159 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_221 : affineAdd acc_221 base_221 = acc_222 := by
  unfold acc_221 base_221 acc_222
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((101715476756552087767187807538033124532838833535719454646948903410609456669352 : Nat) : Fp) - ((14881952017843508107868018207655541299293805975448542164953269149202864001651 : Nat) : Fp))⁻¹ = ((72197868155196105245711292438031931707226049022125491055079666978784931665589 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((101715476756552087767187807538033124532838833535719454646948903410609456669352 : Nat) : Fp) - ((14881952017843508107868018207655541299293805975448542164953269149202864001651 : Nat) : Fp))⁻¹ = ((72197868155196105245711292438031931707226049022125491055079666978784931665589 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_222 : affineAdd acc_222 base_222 = acc_223 := by
  unfold acc_222 base_222 acc_223
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((26201990199447264150340244601088843223044207513721979159517717223349558797573 : Nat) : Fp) - ((64250787150254837153343438979016395164129717520259441534727718215719657633396 : Nat) : Fp))⁻¹ = ((26926521875960496160070654788722846679758399987560644018300381323508488601643 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((26201990199447264150340244601088843223044207513721979159517717223349558797573 : Nat) : Fp) - ((64250787150254837153343438979016395164129717520259441534727718215719657633396 : Nat) : Fp))⁻¹ = ((26926521875960496160070654788722846679758399987560644018300381323508488601643 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_223 : affineAdd acc_223 base_223 = acc_224 := by
  unfold acc_223 base_223 acc_224
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((14921441360743431835062401086497095963484503041023341661521987401860874976443 : Nat) : Fp) - ((112052232026769664929658561660710941635228959956787050473536200851071191032897 : Nat) : Fp))⁻¹ = ((36721715015856848406898333586949695748730920839029489684660332751683536669233 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((14921441360743431835062401086497095963484503041023341661521987401860874976443 : Nat) : Fp) - ((112052232026769664929658561660710941635228959956787050473536200851071191032897 : Nat) : Fp))⁻¹ = ((36721715015856848406898333586949695748730920839029489684660332751683536669233 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_224 : affineAdd acc_224 base_224 = acc_225 := by
  unfold acc_224 base_224 acc_225
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((78286964671916748464002077903524610882307428783999554209283543510913862216099 : Nat) : Fp) - ((67655380319953589260148826173219524241109847135242745518793369102772071675834 : Nat) : Fp))⁻¹ = ((14726048928459371916841882954199586121087722667955654521847324213713941126982 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((78286964671916748464002077903524610882307428783999554209283543510913862216099 : Nat) : Fp) - ((67655380319953589260148826173219524241109847135242745518793369102772071675834 : Nat) : Fp))⁻¹ = ((14726048928459371916841882954199586121087722667955654521847324213713941126982 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_225 : affineAdd acc_225 base_225 = acc_226 := by
  unfold acc_225 base_225 acc_226
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((32105100545289841423885087965333143227423632123747622691327036134947413387996 : Nat) : Fp) - ((92240156060407253479030676529662381214111644319002643127826873158938047083835 : Nat) : Fp))⁻¹ = ((65492616832720931424899613386967215226372639986325535081381875215779937201894 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((32105100545289841423885087965333143227423632123747622691327036134947413387996 : Nat) : Fp) - ((92240156060407253479030676529662381214111644319002643127826873158938047083835 : Nat) : Fp))⁻¹ = ((65492616832720931424899613386967215226372639986325535081381875215779937201894 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_226 : affineAdd acc_226 base_226 = acc_227 := by
  unfold acc_226 base_226 acc_227
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((53684246945455233892169494117752543755515973407332488164311693838822716083874 : Nat) : Fp) - ((78627750631242170634484650157951616270326041285698762428910452596338546905565 : Nat) : Fp))⁻¹ = ((97172869760078288683365041052143087857081720806654304497516408343931046777166 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((53684246945455233892169494117752543755515973407332488164311693838822716083874 : Nat) : Fp) - ((78627750631242170634484650157951616270326041285698762428910452596338546905565 : Nat) : Fp))⁻¹ = ((97172869760078288683365041052143087857081720806654304497516408343931046777166 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_227 : affineAdd acc_227 base_227 = acc_228 := by
  unfold acc_227 base_227 acc_228
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((51408690339641306259502862117523444905541421107318686013500544629508968693518 : Nat) : Fp) - ((37970007016072384636196615568949856628931570059897898485017028997234414061945 : Nat) : Fp))⁻¹ = ((106933334873840036434927140571892165916637946559864770646898678058053793887685 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((51408690339641306259502862117523444905541421107318686013500544629508968693518 : Nat) : Fp) - ((37970007016072384636196615568949856628931570059897898485017028997234414061945 : Nat) : Fp))⁻¹ = ((106933334873840036434927140571892165916637946559864770646898678058053793887685 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_228 : affineAdd acc_228 base_228 = acc_229 := by
  unfold acc_228 base_228 acc_229
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((52786968606586592704978338159563606167635515874663699931786977412781890025330 : Nat) : Fp) - ((95279397291673716158331856496563878128970306290864555825308960160147858174289 : Nat) : Fp))⁻¹ = ((322629972529987554228941769582982117477175811506951818735024790289313421102 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((52786968606586592704978338159563606167635515874663699931786977412781890025330 : Nat) : Fp) - ((95279397291673716158331856496563878128970306290864555825308960160147858174289 : Nat) : Fp))⁻¹ = ((322629972529987554228941769582982117477175811506951818735024790289313421102 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_229 : affineAdd acc_229 base_229 = acc_230 := by
  unfold acc_229 base_229 acc_230
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((86156646838761427890073982424487469968465991327301981509193839358381582224146 : Nat) : Fp) - ((84556908620397086490574354609607180077068693777212695160113645418094198446687 : Nat) : Fp))⁻¹ = ((74039606187942204371589421961987444221919650260144689108597205915425669241496 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((86156646838761427890073982424487469968465991327301981509193839358381582224146 : Nat) : Fp) - ((84556908620397086490574354609607180077068693777212695160113645418094198446687 : Nat) : Fp))⁻¹ = ((74039606187942204371589421961987444221919650260144689108597205915425669241496 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_230 : affineAdd acc_230 base_230 = acc_231 := by
  unfold acc_230 base_230 acc_231
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((97860223995786388436718584398015194619729937254824459850925401805715135240037 : Nat) : Fp) - ((112030421148703629201942613873270492163488999678896447559274774208446269765955 : Nat) : Fp))⁻¹ = ((105444513964662884583251302117489985003623976571995583601020091109239396716572 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((97860223995786388436718584398015194619729937254824459850925401805715135240037 : Nat) : Fp) - ((112030421148703629201942613873270492163488999678896447559274774208446269765955 : Nat) : Fp))⁻¹ = ((105444513964662884583251302117489985003623976571995583601020091109239396716572 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_231 : affineAdd acc_231 base_231 = acc_232 := by
  unfold acc_231 base_231 acc_232
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((97543033203699496180030109729025514517779016973665982852482659210135496439562 : Nat) : Fp) - ((101186060051338727518238790300531351495613041202762303390359395316390096421977 : Nat) : Fp))⁻¹ = ((48466937618903611483743428288877683879290189102831217916679966473541040745312 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((97543033203699496180030109729025514517779016973665982852482659210135496439562 : Nat) : Fp) - ((101186060051338727518238790300531351495613041202762303390359395316390096421977 : Nat) : Fp))⁻¹ = ((48466937618903611483743428288877683879290189102831217916679966473541040745312 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_232 : affineAdd acc_232 base_232 = acc_233 := by
  unfold acc_232 base_232 acc_233
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((102830533340956686198994875465671816784497224723621699776483958495310423492487 : Nat) : Fp) - ((45387637969275774150653095889876699672169323470095019346305801601969322188915 : Nat) : Fp))⁻¹ = ((105025943384784058202913583116680300017125538828075357750858201454251682707916 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((102830533340956686198994875465671816784497224723621699776483958495310423492487 : Nat) : Fp) - ((45387637969275774150653095889876699672169323470095019346305801601969322188915 : Nat) : Fp))⁻¹ = ((105025943384784058202913583116680300017125538828075357750858201454251682707916 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_233 : affineAdd acc_233 base_233 = acc_234 := by
  unfold acc_233 base_233 acc_234
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((30296781290666500851168272802295872378717872596910351160793153249076866250067 : Nat) : Fp) - ((83407264292599769979907512419974269146592549057292719108468866098684905146381 : Nat) : Fp))⁻¹ = ((74170822056531343106395539267171307105583497685090777469050655863600930809882 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((30296781290666500851168272802295872378717872596910351160793153249076866250067 : Nat) : Fp) - ((83407264292599769979907512419974269146592549057292719108468866098684905146381 : Nat) : Fp))⁻¹ = ((74170822056531343106395539267171307105583497685090777469050655863600930809882 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_234 : affineAdd acc_234 base_234 = acc_235 := by
  unfold acc_234 base_234 acc_235
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((112315026525901017482762550793305442477113960914535610904227469025227247239111 : Nat) : Fp) - ((106823080507094536302171587221364767641207071699356594725100487456618775186796 : Nat) : Fp))⁻¹ = ((82163484551982946162824744132430795244051340481242472683697203592751797620927 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((112315026525901017482762550793305442477113960914535610904227469025227247239111 : Nat) : Fp) - ((106823080507094536302171587221364767641207071699356594725100487456618775186796 : Nat) : Fp))⁻¹ = ((82163484551982946162824744132430795244051340481242472683697203592751797620927 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_235 : affineAdd acc_235 base_235 = acc_236 := by
  unfold acc_235 base_235 acc_236
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((46569867216501492463829635190455011087054375636727173037363205698031811292777 : Nat) : Fp) - ((51458812640674469987191057145664724195213971571581134911909867396919133773071 : Nat) : Fp))⁻¹ = ((99246147325207983258534074014418801755734148318972747317611056249294876036065 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((46569867216501492463829635190455011087054375636727173037363205698031811292777 : Nat) : Fp) - ((51458812640674469987191057145664724195213971571581134911909867396919133773071 : Nat) : Fp))⁻¹ = ((99246147325207983258534074014418801755734148318972747317611056249294876036065 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_236 : affineAdd acc_236 base_236 = acc_237 := by
  unfold acc_236 base_236 acc_237
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((30460618184285782433506524833173452821317744234050953035479650134294695229687 : Nat) : Fp) - ((59934529777540515900169509345926368831906655562972450327405481276732036473944 : Nat) : Fp))⁻¹ = ((8526946730542916063856317320157397050530484522370813318306284909551607773774 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((30460618184285782433506524833173452821317744234050953035479650134294695229687 : Nat) : Fp) - ((59934529777540515900169509345926368831906655562972450327405481276732036473944 : Nat) : Fp))⁻¹ = ((8526946730542916063856317320157397050530484522370813318306284909551607773774 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_237 : affineAdd acc_237 base_237 = acc_238 := by
  unfold acc_237 base_237 acc_238
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((71270092845352995479434385129475437865313439324845947026235006874099517319235 : Nat) : Fp) - ((67920502080269633306026372339646975598405744544879176039587252097767227126036 : Nat) : Fp))⁻¹ = ((44484015878447711199691899145826560038121259933041388698812847458875624052880 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((71270092845352995479434385129475437865313439324845947026235006874099517319235 : Nat) : Fp) - ((67920502080269633306026372339646975598405744544879176039587252097767227126036 : Nat) : Fp))⁻¹ = ((44484015878447711199691899145826560038121259933041388698812847458875624052880 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_238 : affineAdd acc_238 base_238 = acc_239 := by
  unfold acc_238 base_238 acc_239
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((16618556853955496303621456858521371789817942603952389038933742455201500272862 : Nat) : Fp) - ((82877690455795689589323624744144337630277711329294127826630078132465967983811 : Nat) : Fp))⁻¹ = ((17295430877061107715367824535024442111123634980019254982367410570100582072415 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((16618556853955496303621456858521371789817942603952389038933742455201500272862 : Nat) : Fp) - ((82877690455795689589323624744144337630277711329294127826630078132465967983811 : Nat) : Fp))⁻¹ = ((17295430877061107715367824535024442111123634980019254982367410570100582072415 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_239 : affineAdd acc_239 base_239 = acc_240 := by
  unfold acc_239 base_239 acc_240
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((74742492579009244357905242041687175457775327266132249497268901437517232845332 : Nat) : Fp) - ((107647080929067738343525460704633213843414790178366076706967300283813568943072 : Nat) : Fp))⁻¹ = ((8418140341624430260307586526023173184057003721638716789423299404437857132329 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((74742492579009244357905242041687175457775327266132249497268901437517232845332 : Nat) : Fp) - ((107647080929067738343525460704633213843414790178366076706967300283813568943072 : Nat) : Fp))⁻¹ = ((8418140341624430260307586526023173184057003721638716789423299404437857132329 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_240 : affineAdd acc_240 base_240 = acc_241 := by
  unfold acc_240 base_240 acc_241
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((1081612414056764282020452592787223287568754890085769046997177576205063339491 : Nat) : Fp) - ((8718136510001795340016406650816398436241492966773881626425334457414292825707 : Nat) : Fp))⁻¹ = ((66275548193863837695351556979690494732036727730899057801908550282814624496878 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((1081612414056764282020452592787223287568754890085769046997177576205063339491 : Nat) : Fp) - ((8718136510001795340016406650816398436241492966773881626425334457414292825707 : Nat) : Fp))⁻¹ = ((66275548193863837695351556979690494732036727730899057801908550282814624496878 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_241 : affineAdd acc_241 base_241 = acc_242 := by
  unfold acc_241 base_241 acc_242
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((49811277349567224411985508482634174791584736505241552453091834927605838997743 : Nat) : Fp) - ((106401248484515799960476859862399114279959120497224302323517862298350223656110 : Nat) : Fp))⁻¹ = ((71828170150031925554229850595657073780236974781138631105537956088304732343933 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((49811277349567224411985508482634174791584736505241552453091834927605838997743 : Nat) : Fp) - ((106401248484515799960476859862399114279959120497224302323517862298350223656110 : Nat) : Fp))⁻¹ = ((71828170150031925554229850595657073780236974781138631105537956088304732343933 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_242 : affineAdd acc_242 base_242 = acc_243 := by
  unfold acc_242 base_242 acc_243
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((77706397775829796206513053180104330003887931466756047681323827121198156235594 : Nat) : Fp) - ((85914087585702408016005337307470673574025858586827994345031653897824524412368 : Nat) : Fp))⁻¹ = ((65431284931205801273055160732872373816317400998553531152042437107722133419750 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((77706397775829796206513053180104330003887931466756047681323827121198156235594 : Nat) : Fp) - ((85914087585702408016005337307470673574025858586827994345031653897824524412368 : Nat) : Fp))⁻¹ = ((65431284931205801273055160732872373816317400998553531152042437107722133419750 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_243 : affineAdd acc_243 base_243 = acc_244 := by
  unfold acc_243 base_243 acc_244
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((23785567577982762677578830488290362080656906729902214709880944246705510538322 : Nat) : Fp) - ((47276261486337148374827016504378500997420604221918318826137905934201132672881 : Nat) : Fp))⁻¹ = ((37023524279868236475233168612224589754419845055605576925195018956658401308517 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((23785567577982762677578830488290362080656906729902214709880944246705510538322 : Nat) : Fp) - ((47276261486337148374827016504378500997420604221918318826137905934201132672881 : Nat) : Fp))⁻¹ = ((37023524279868236475233168612224589754419845055605576925195018956658401308517 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_244 : affineAdd acc_244 base_244 = acc_245 := by
  unfold acc_244 base_244 acc_245
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((14090046075950136180562018246382077790895898809530716464155275291397585164913 : Nat) : Fp) - ((85166652415091435001797631336388904339331836647982294920464378555175360787302 : Nat) : Fp))⁻¹ = ((96385836085415310359062867028327518014560035480321583951854876971832852447212 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((14090046075950136180562018246382077790895898809530716464155275291397585164913 : Nat) : Fp) - ((85166652415091435001797631336388904339331836647982294920464378555175360787302 : Nat) : Fp))⁻¹ = ((96385836085415310359062867028327518014560035480321583951854876971832852447212 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_245 : affineAdd acc_245 base_245 = acc_246 := by
  unfold acc_245 base_245 acc_246
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((37828421047972008774017066608768410609187446689017066363359154428044810742785 : Nat) : Fp) - ((98723003287129746819861849635856388307092482938644489660108201582085516618521 : Nat) : Fp))⁻¹ = ((54762673345927077484589456049860716946381615671795397921437046901042796004795 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((37828421047972008774017066608768410609187446689017066363359154428044810742785 : Nat) : Fp) - ((98723003287129746819861849635856388307092482938644489660108201582085516618521 : Nat) : Fp))⁻¹ = ((54762673345927077484589456049860716946381615671795397921437046901042796004795 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_246 : affineAdd acc_246 base_246 = acc_247 := by
  unfold acc_246 base_246 acc_247
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((20842789763102640913372864025301593491814512580224379177912388102803212159731 : Nat) : Fp) - ((1410924839106319455438998906475131322254088508411264224845861103682022500650 : Nat) : Fp))⁻¹ = ((56004025793636265115578303884033943891549704951275347431086023804423668714653 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((20842789763102640913372864025301593491814512580224379177912388102803212159731 : Nat) : Fp) - ((1410924839106319455438998906475131322254088508411264224845861103682022500650 : Nat) : Fp))⁻¹ = ((56004025793636265115578303884033943891549704951275347431086023804423668714653 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_247 : affineAdd acc_247 base_247 = acc_248 := by
  unfold acc_247 base_247 acc_248
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((110539463342885515017316615115704012034156315028293057517191961487462828970401 : Nat) : Fp) - ((76680320804797823168246424599385182501909051371397652720933062691171176057014 : Nat) : Fp))⁻¹ = ((40371787454197089500984454654079820828872666746133364705945189125980995350057 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((110539463342885515017316615115704012034156315028293057517191961487462828970401 : Nat) : Fp) - ((76680320804797823168246424599385182501909051371397652720933062691171176057014 : Nat) : Fp))⁻¹ = ((40371787454197089500984454654079820828872666746133364705945189125980995350057 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_248 : affineAdd acc_248 base_248 = acc_249 := by
  unfold acc_248 base_248 acc_249
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((60514053294911466398737601314427703479018544726564927088684814673373104577301 : Nat) : Fp) - ((63395642421589016740518975608504846303065672135176650115036476193363423546538 : Nat) : Fp))⁻¹ = ((41390656511924316008396061222235340727516708674092024817032084999303075280034 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((60514053294911466398737601314427703479018544726564927088684814673373104577301 : Nat) : Fp) - ((63395642421589016740518975608504846303065672135176650115036476193363423546538 : Nat) : Fp))⁻¹ = ((41390656511924316008396061222235340727516708674092024817032084999303075280034 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_249 : affineAdd acc_249 base_249 = acc_250 := by
  unfold acc_249 base_249 acc_250
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((32052271579092252526176234927591189443293762247044804283344858953002472806271 : Nat) : Fp) - ((77392770812506936202877798844009338869624245327085260572871517211271361583330 : Nat) : Fp))⁻¹ = ((52627566599437068597975168745519215041555614434019825833785691678602238833449 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((32052271579092252526176234927591189443293762247044804283344858953002472806271 : Nat) : Fp) - ((77392770812506936202877798844009338869624245327085260572871517211271361583330 : Nat) : Fp))⁻¹ = ((52627566599437068597975168745519215041555614434019825833785691678602238833449 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_250 : affineAdd acc_250 base_250 = acc_251 := by
  unfold acc_250 base_250 acc_251
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((103456305090242564895712946172826220978932802667151275263999199465000893101440 : Nat) : Fp) - ((16914017336104237881775315886787930831164045006039241266138286261112962921466 : Nat) : Fp))⁻¹ = ((58341617383367292486831211994914909050857938182283755701516104346620409870648 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((103456305090242564895712946172826220978932802667151275263999199465000893101440 : Nat) : Fp) - ((16914017336104237881775315886787930831164045006039241266138286261112962921466 : Nat) : Fp))⁻¹ = ((58341617383367292486831211994914909050857938182283755701516104346620409870648 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_251 : affineAdd acc_251 base_251 = acc_252 := by
  unfold acc_251 base_251 acc_252
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((46530563348586613959865991838199016313984999584228385081042307393336696728902 : Nat) : Fp) - ((115448225011842706572960659933294318341945799523635471708109888288281266225256 : Nat) : Fp))⁻¹ = ((113502473223005638420273352494018505980043861713404147209560767047769576981161 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((46530563348586613959865991838199016313984999584228385081042307393336696728902 : Nat) : Fp) - ((115448225011842706572960659933294318341945799523635471708109888288281266225256 : Nat) : Fp))⁻¹ = ((113502473223005638420273352494018505980043861713404147209560767047769576981161 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_252 : affineAdd acc_252 base_252 = acc_253 := by
  unfold acc_252 base_252 acc_253
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((27037594016997265388276663112501048648670817957697121730841628104825126763212 : Nat) : Fp) - ((4032983015753143990395647783770666587927265353624430905763286836981504199392 : Nat) : Fp))⁻¹ = ((7678013618503851705343480170178535183768692119681506605136450902753437033619 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((27037594016997265388276663112501048648670817957697121730841628104825126763212 : Nat) : Fp) - ((4032983015753143990395647783770666587927265353624430905763286836981504199392 : Nat) : Fp))⁻¹ = ((7678013618503851705343480170178535183768692119681506605136450902753437033619 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_253 : affineAdd acc_253 base_253 = acc_254 := by
  unfold acc_253 base_253 acc_254
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((77692363628108059885443663784710924525445718788147207068968950173471674635534 : Nat) : Fp) - ((87917229428110789366561422587307072970088695150214603900351294636804298290738 : Nat) : Fp))⁻¹ = ((52026892244712232825847303272754523128411799751685051109660067243361322427518 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((77692363628108059885443663784710924525445718788147207068968950173471674635534 : Nat) : Fp) - ((87917229428110789366561422587307072970088695150214603900351294636804298290738 : Nat) : Fp))⁻¹ = ((52026892244712232825847303272754523128411799751685051109660067243361322427518 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_254 : affineAdd acc_254 base_254 = acc_255 := by
  unfold acc_254 base_254 acc_255
  apply certifiedAdd
  · unfold Fp p
    reduce_mod_char
    decide
  · have hinv : (((51523398464344358728983437505968609663784806853362284802296319167775841330559 : Nat) : Fp) - ((19277281477197177963613685635111727513957886411799201238917757645493897712993 : Nat) : Fp))⁻¹ = ((52930340780772157752151754127259614250158220358694739801364889971522288825614 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char
  · have hinv : (((51523398464344358728983437505968609663784806853362284802296319167775841330559 : Nat) : Fp) - ((19277281477197177963613685635111727513957886411799201238917757645493897712993 : Nat) : Fp))⁻¹ = ((52930340780772157752151754127259614250158220358694739801364889971522288825614 : Nat) : Fp) := by
      apply inv_eq_of_mul_eq_one_left
      unfold Fp p
      reduce_mod_char
    unfold genericY genericX genericSlope genericDenominator
    rw [hinv]
    unfold genericNumerator
    unfold Fp p
    reduce_mod_char

private theorem acc_add_inverse_255 : affineAdd acc_255 base_255 = 0 := by
  unfold acc_255 base_255
  apply certifiedInverseAdd
  · unfold Fp p
    reduce_mod_char
  · unfold Fp p
    reduce_mod_char

private theorem affineNsmulBinRec_order_eq_zero :
    affineNsmulBinRec order G = 0 := by
  rw [← base_0_eq_G]
  change affineNsmulBinRec.go order 0 base_0 = 0
  rw [show order = Nat.bit true 57896044618658097711785492504343953926418782139537452191302581570759080747168 by
    unfold order
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [affineAdd_zero_left]
  rw [base_double_0]
  rw [show 57896044618658097711785492504343953926418782139537452191302581570759080747168 = Nat.bit false 28948022309329048855892746252171976963209391069768726095651290785379540373584 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_1]
  rw [show 28948022309329048855892746252171976963209391069768726095651290785379540373584 = Nat.bit false 14474011154664524427946373126085988481604695534884363047825645392689770186792 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_2]
  rw [show 14474011154664524427946373126085988481604695534884363047825645392689770186792 = Nat.bit false 7237005577332262213973186563042994240802347767442181523912822696344885093396 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_3]
  rw [show 7237005577332262213973186563042994240802347767442181523912822696344885093396 = Nat.bit false 3618502788666131106986593281521497120401173883721090761956411348172442546698 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_4]
  rw [show 3618502788666131106986593281521497120401173883721090761956411348172442546698 = Nat.bit false 1809251394333065553493296640760748560200586941860545380978205674086221273349 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_5]
  rw [show 1809251394333065553493296640760748560200586941860545380978205674086221273349 = Nat.bit true 904625697166532776746648320380374280100293470930272690489102837043110636674 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_6]
  rw [base_double_6]
  rw [show 904625697166532776746648320380374280100293470930272690489102837043110636674 = Nat.bit false 452312848583266388373324160190187140050146735465136345244551418521555318337 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_7]
  rw [show 452312848583266388373324160190187140050146735465136345244551418521555318337 = Nat.bit true 226156424291633194186662080095093570025073367732568172622275709260777659168 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_8]
  rw [base_double_8]
  rw [show 226156424291633194186662080095093570025073367732568172622275709260777659168 = Nat.bit false 113078212145816597093331040047546785012536683866284086311137854630388829584 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_9]
  rw [show 113078212145816597093331040047546785012536683866284086311137854630388829584 = Nat.bit false 56539106072908298546665520023773392506268341933142043155568927315194414792 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_10]
  rw [show 56539106072908298546665520023773392506268341933142043155568927315194414792 = Nat.bit false 28269553036454149273332760011886696253134170966571021577784463657597207396 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_11]
  rw [show 28269553036454149273332760011886696253134170966571021577784463657597207396 = Nat.bit false 14134776518227074636666380005943348126567085483285510788892231828798603698 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_12]
  rw [show 14134776518227074636666380005943348126567085483285510788892231828798603698 = Nat.bit false 7067388259113537318333190002971674063283542741642755394446115914399301849 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_13]
  rw [show 7067388259113537318333190002971674063283542741642755394446115914399301849 = Nat.bit true 3533694129556768659166595001485837031641771370821377697223057957199650924 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_14]
  rw [base_double_14]
  rw [show 3533694129556768659166595001485837031641771370821377697223057957199650924 = Nat.bit false 1766847064778384329583297500742918515820885685410688848611528978599825462 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_15]
  rw [show 1766847064778384329583297500742918515820885685410688848611528978599825462 = Nat.bit false 883423532389192164791648750371459257910442842705344424305764489299912731 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_16]
  rw [show 883423532389192164791648750371459257910442842705344424305764489299912731 = Nat.bit true 441711766194596082395824375185729628955221421352672212152882244649956365 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_17]
  rw [base_double_17]
  rw [show 441711766194596082395824375185729628955221421352672212152882244649956365 = Nat.bit true 220855883097298041197912187592864814477610710676336106076441122324978182 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_18]
  rw [base_double_18]
  rw [show 220855883097298041197912187592864814477610710676336106076441122324978182 = Nat.bit false 110427941548649020598956093796432407238805355338168053038220561162489091 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_19]
  rw [show 110427941548649020598956093796432407238805355338168053038220561162489091 = Nat.bit true 55213970774324510299478046898216203619402677669084026519110280581244545 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_20]
  rw [base_double_20]
  rw [show 55213970774324510299478046898216203619402677669084026519110280581244545 = Nat.bit true 27606985387162255149739023449108101809701338834542013259555140290622272 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_21]
  rw [base_double_21]
  rw [show 27606985387162255149739023449108101809701338834542013259555140290622272 = Nat.bit false 13803492693581127574869511724554050904850669417271006629777570145311136 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_22]
  rw [show 13803492693581127574869511724554050904850669417271006629777570145311136 = Nat.bit false 6901746346790563787434755862277025452425334708635503314888785072655568 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_23]
  rw [show 6901746346790563787434755862277025452425334708635503314888785072655568 = Nat.bit false 3450873173395281893717377931138512726212667354317751657444392536327784 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_24]
  rw [show 3450873173395281893717377931138512726212667354317751657444392536327784 = Nat.bit false 1725436586697640946858688965569256363106333677158875828722196268163892 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_25]
  rw [show 1725436586697640946858688965569256363106333677158875828722196268163892 = Nat.bit false 862718293348820473429344482784628181553166838579437914361098134081946 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_26]
  rw [show 862718293348820473429344482784628181553166838579437914361098134081946 = Nat.bit false 431359146674410236714672241392314090776583419289718957180549067040973 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_27]
  rw [show 431359146674410236714672241392314090776583419289718957180549067040973 = Nat.bit true 215679573337205118357336120696157045388291709644859478590274533520486 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_28]
  rw [base_double_28]
  rw [show 215679573337205118357336120696157045388291709644859478590274533520486 = Nat.bit false 107839786668602559178668060348078522694145854822429739295137266760243 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_29]
  rw [show 107839786668602559178668060348078522694145854822429739295137266760243 = Nat.bit true 53919893334301279589334030174039261347072927411214869647568633380121 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_30]
  rw [base_double_30]
  rw [show 53919893334301279589334030174039261347072927411214869647568633380121 = Nat.bit true 26959946667150639794667015087019630673536463705607434823784316690060 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_31]
  rw [base_double_31]
  rw [show 26959946667150639794667015087019630673536463705607434823784316690060 = Nat.bit false 13479973333575319897333507543509815336768231852803717411892158345030 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_32]
  rw [show 13479973333575319897333507543509815336768231852803717411892158345030 = Nat.bit false 6739986666787659948666753771754907668384115926401858705946079172515 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_33]
  rw [show 6739986666787659948666753771754907668384115926401858705946079172515 = Nat.bit true 3369993333393829974333376885877453834192057963200929352973039586257 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_34]
  rw [base_double_34]
  rw [show 3369993333393829974333376885877453834192057963200929352973039586257 = Nat.bit true 1684996666696914987166688442938726917096028981600464676486519793128 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_35]
  rw [base_double_35]
  rw [show 1684996666696914987166688442938726917096028981600464676486519793128 = Nat.bit false 842498333348457493583344221469363458548014490800232338243259896564 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_36]
  rw [show 842498333348457493583344221469363458548014490800232338243259896564 = Nat.bit false 421249166674228746791672110734681729274007245400116169121629948282 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_37]
  rw [show 421249166674228746791672110734681729274007245400116169121629948282 = Nat.bit false 210624583337114373395836055367340864637003622700058084560814974141 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_38]
  rw [show 210624583337114373395836055367340864637003622700058084560814974141 = Nat.bit true 105312291668557186697918027683670432318501811350029042280407487070 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_39]
  rw [base_double_39]
  rw [show 105312291668557186697918027683670432318501811350029042280407487070 = Nat.bit false 52656145834278593348959013841835216159250905675014521140203743535 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_40]
  rw [show 52656145834278593348959013841835216159250905675014521140203743535 = Nat.bit true 26328072917139296674479506920917608079625452837507260570101871767 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_41]
  rw [base_double_41]
  rw [show 26328072917139296674479506920917608079625452837507260570101871767 = Nat.bit true 13164036458569648337239753460458804039812726418753630285050935883 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_42]
  rw [base_double_42]
  rw [show 13164036458569648337239753460458804039812726418753630285050935883 = Nat.bit true 6582018229284824168619876730229402019906363209376815142525467941 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_43]
  rw [base_double_43]
  rw [show 6582018229284824168619876730229402019906363209376815142525467941 = Nat.bit true 3291009114642412084309938365114701009953181604688407571262733970 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_44]
  rw [base_double_44]
  rw [show 3291009114642412084309938365114701009953181604688407571262733970 = Nat.bit false 1645504557321206042154969182557350504976590802344203785631366985 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_45]
  rw [show 1645504557321206042154969182557350504976590802344203785631366985 = Nat.bit true 822752278660603021077484591278675252488295401172101892815683492 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_46]
  rw [base_double_46]
  rw [show 822752278660603021077484591278675252488295401172101892815683492 = Nat.bit false 411376139330301510538742295639337626244147700586050946407841746 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_47]
  rw [show 411376139330301510538742295639337626244147700586050946407841746 = Nat.bit false 205688069665150755269371147819668813122073850293025473203920873 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_48]
  rw [show 205688069665150755269371147819668813122073850293025473203920873 = Nat.bit true 102844034832575377634685573909834406561036925146512736601960436 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_49]
  rw [base_double_49]
  rw [show 102844034832575377634685573909834406561036925146512736601960436 = Nat.bit false 51422017416287688817342786954917203280518462573256368300980218 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_50]
  rw [show 51422017416287688817342786954917203280518462573256368300980218 = Nat.bit false 25711008708143844408671393477458601640259231286628184150490109 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_51]
  rw [show 25711008708143844408671393477458601640259231286628184150490109 = Nat.bit true 12855504354071922204335696738729300820129615643314092075245054 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_52]
  rw [base_double_52]
  rw [show 12855504354071922204335696738729300820129615643314092075245054 = Nat.bit false 6427752177035961102167848369364650410064807821657046037622527 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_53]
  rw [show 6427752177035961102167848369364650410064807821657046037622527 = Nat.bit true 3213876088517980551083924184682325205032403910828523018811263 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_54]
  rw [base_double_54]
  rw [show 3213876088517980551083924184682325205032403910828523018811263 = Nat.bit true 1606938044258990275541962092341162602516201955414261509405631 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_55]
  rw [base_double_55]
  rw [show 1606938044258990275541962092341162602516201955414261509405631 = Nat.bit true 803469022129495137770981046170581301258100977707130754702815 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_56]
  rw [base_double_56]
  rw [show 803469022129495137770981046170581301258100977707130754702815 = Nat.bit true 401734511064747568885490523085290650629050488853565377351407 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_57]
  rw [base_double_57]
  rw [show 401734511064747568885490523085290650629050488853565377351407 = Nat.bit true 200867255532373784442745261542645325314525244426782688675703 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_58]
  rw [base_double_58]
  rw [show 200867255532373784442745261542645325314525244426782688675703 = Nat.bit true 100433627766186892221372630771322662657262622213391344337851 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_59]
  rw [base_double_59]
  rw [show 100433627766186892221372630771322662657262622213391344337851 = Nat.bit true 50216813883093446110686315385661331328631311106695672168925 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_60]
  rw [base_double_60]
  rw [show 50216813883093446110686315385661331328631311106695672168925 = Nat.bit true 25108406941546723055343157692830665664315655553347836084462 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_61]
  rw [base_double_61]
  rw [show 25108406941546723055343157692830665664315655553347836084462 = Nat.bit false 12554203470773361527671578846415332832157827776673918042231 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_62]
  rw [show 12554203470773361527671578846415332832157827776673918042231 = Nat.bit true 6277101735386680763835789423207666416078913888336959021115 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_63]
  rw [base_double_63]
  rw [show 6277101735386680763835789423207666416078913888336959021115 = Nat.bit true 3138550867693340381917894711603833208039456944168479510557 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_64]
  rw [base_double_64]
  rw [show 3138550867693340381917894711603833208039456944168479510557 = Nat.bit true 1569275433846670190958947355801916604019728472084239755278 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_65]
  rw [base_double_65]
  rw [show 1569275433846670190958947355801916604019728472084239755278 = Nat.bit false 784637716923335095479473677900958302009864236042119877639 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_66]
  rw [show 784637716923335095479473677900958302009864236042119877639 = Nat.bit true 392318858461667547739736838950479151004932118021059938819 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_67]
  rw [base_double_67]
  rw [show 392318858461667547739736838950479151004932118021059938819 = Nat.bit true 196159429230833773869868419475239575502466059010529969409 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_68]
  rw [base_double_68]
  rw [show 196159429230833773869868419475239575502466059010529969409 = Nat.bit true 98079714615416886934934209737619787751233029505264984704 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_69]
  rw [base_double_69]
  rw [show 98079714615416886934934209737619787751233029505264984704 = Nat.bit false 49039857307708443467467104868809893875616514752632492352 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_70]
  rw [show 49039857307708443467467104868809893875616514752632492352 = Nat.bit false 24519928653854221733733552434404946937808257376316246176 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_71]
  rw [show 24519928653854221733733552434404946937808257376316246176 = Nat.bit false 12259964326927110866866776217202473468904128688158123088 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_72]
  rw [show 12259964326927110866866776217202473468904128688158123088 = Nat.bit false 6129982163463555433433388108601236734452064344079061544 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_73]
  rw [show 6129982163463555433433388108601236734452064344079061544 = Nat.bit false 3064991081731777716716694054300618367226032172039530772 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_74]
  rw [show 3064991081731777716716694054300618367226032172039530772 = Nat.bit false 1532495540865888858358347027150309183613016086019765386 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_75]
  rw [show 1532495540865888858358347027150309183613016086019765386 = Nat.bit false 766247770432944429179173513575154591806508043009882693 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_76]
  rw [show 766247770432944429179173513575154591806508043009882693 = Nat.bit true 383123885216472214589586756787577295903254021504941346 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_77]
  rw [base_double_77]
  rw [show 383123885216472214589586756787577295903254021504941346 = Nat.bit false 191561942608236107294793378393788647951627010752470673 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_78]
  rw [show 191561942608236107294793378393788647951627010752470673 = Nat.bit true 95780971304118053647396689196894323975813505376235336 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_79]
  rw [base_double_79]
  rw [show 95780971304118053647396689196894323975813505376235336 = Nat.bit false 47890485652059026823698344598447161987906752688117668 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_80]
  rw [show 47890485652059026823698344598447161987906752688117668 = Nat.bit false 23945242826029513411849172299223580993953376344058834 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_81]
  rw [show 23945242826029513411849172299223580993953376344058834 = Nat.bit false 11972621413014756705924586149611790496976688172029417 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_82]
  rw [show 11972621413014756705924586149611790496976688172029417 = Nat.bit true 5986310706507378352962293074805895248488344086014708 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_83]
  rw [base_double_83]
  rw [show 5986310706507378352962293074805895248488344086014708 = Nat.bit false 2993155353253689176481146537402947624244172043007354 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_84]
  rw [show 2993155353253689176481146537402947624244172043007354 = Nat.bit false 1496577676626844588240573268701473812122086021503677 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_85]
  rw [show 1496577676626844588240573268701473812122086021503677 = Nat.bit true 748288838313422294120286634350736906061043010751838 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_86]
  rw [base_double_86]
  rw [show 748288838313422294120286634350736906061043010751838 = Nat.bit false 374144419156711147060143317175368453030521505375919 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_87]
  rw [show 374144419156711147060143317175368453030521505375919 = Nat.bit true 187072209578355573530071658587684226515260752687959 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_88]
  rw [base_double_88]
  rw [show 187072209578355573530071658587684226515260752687959 = Nat.bit true 93536104789177786765035829293842113257630376343979 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_89]
  rw [base_double_89]
  rw [show 93536104789177786765035829293842113257630376343979 = Nat.bit true 46768052394588893382517914646921056628815188171989 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_90]
  rw [base_double_90]
  rw [show 46768052394588893382517914646921056628815188171989 = Nat.bit true 23384026197294446691258957323460528314407594085994 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_91]
  rw [base_double_91]
  rw [show 23384026197294446691258957323460528314407594085994 = Nat.bit false 11692013098647223345629478661730264157203797042997 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_92]
  rw [show 11692013098647223345629478661730264157203797042997 = Nat.bit true 5846006549323611672814739330865132078601898521498 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_93]
  rw [base_double_93]
  rw [show 5846006549323611672814739330865132078601898521498 = Nat.bit false 2923003274661805836407369665432566039300949260749 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_94]
  rw [show 2923003274661805836407369665432566039300949260749 = Nat.bit true 1461501637330902918203684832716283019650474630374 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_95]
  rw [base_double_95]
  rw [show 1461501637330902918203684832716283019650474630374 = Nat.bit false 730750818665451459101842416358141509825237315187 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_96]
  rw [show 730750818665451459101842416358141509825237315187 = Nat.bit true 365375409332725729550921208179070754912618657593 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_97]
  rw [base_double_97]
  rw [show 365375409332725729550921208179070754912618657593 = Nat.bit true 182687704666362864775460604089535377456309328796 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_98]
  rw [base_double_98]
  rw [show 182687704666362864775460604089535377456309328796 = Nat.bit false 91343852333181432387730302044767688728154664398 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_99]
  rw [show 91343852333181432387730302044767688728154664398 = Nat.bit false 45671926166590716193865151022383844364077332199 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_100]
  rw [show 45671926166590716193865151022383844364077332199 = Nat.bit true 22835963083295358096932575511191922182038666099 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_101]
  rw [base_double_101]
  rw [show 22835963083295358096932575511191922182038666099 = Nat.bit true 11417981541647679048466287755595961091019333049 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_102]
  rw [base_double_102]
  rw [show 11417981541647679048466287755595961091019333049 = Nat.bit true 5708990770823839524233143877797980545509666524 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_103]
  rw [base_double_103]
  rw [show 5708990770823839524233143877797980545509666524 = Nat.bit false 2854495385411919762116571938898990272754833262 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_104]
  rw [show 2854495385411919762116571938898990272754833262 = Nat.bit false 1427247692705959881058285969449495136377416631 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_105]
  rw [show 1427247692705959881058285969449495136377416631 = Nat.bit true 713623846352979940529142984724747568188708315 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_106]
  rw [base_double_106]
  rw [show 713623846352979940529142984724747568188708315 = Nat.bit true 356811923176489970264571492362373784094354157 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_107]
  rw [base_double_107]
  rw [show 356811923176489970264571492362373784094354157 = Nat.bit true 178405961588244985132285746181186892047177078 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_108]
  rw [base_double_108]
  rw [show 178405961588244985132285746181186892047177078 = Nat.bit false 89202980794122492566142873090593446023588539 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_109]
  rw [show 89202980794122492566142873090593446023588539 = Nat.bit true 44601490397061246283071436545296723011794269 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_110]
  rw [base_double_110]
  rw [show 44601490397061246283071436545296723011794269 = Nat.bit true 22300745198530623141535718272648361505897134 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_111]
  rw [base_double_111]
  rw [show 22300745198530623141535718272648361505897134 = Nat.bit false 11150372599265311570767859136324180752948567 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_112]
  rw [show 11150372599265311570767859136324180752948567 = Nat.bit true 5575186299632655785383929568162090376474283 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_113]
  rw [base_double_113]
  rw [show 5575186299632655785383929568162090376474283 = Nat.bit true 2787593149816327892691964784081045188237141 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_114]
  rw [base_double_114]
  rw [show 2787593149816327892691964784081045188237141 = Nat.bit true 1393796574908163946345982392040522594118570 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_115]
  rw [base_double_115]
  rw [show 1393796574908163946345982392040522594118570 = Nat.bit false 696898287454081973172991196020261297059285 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_116]
  rw [show 696898287454081973172991196020261297059285 = Nat.bit true 348449143727040986586495598010130648529642 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_117]
  rw [base_double_117]
  rw [show 348449143727040986586495598010130648529642 = Nat.bit false 174224571863520493293247799005065324264821 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_118]
  rw [show 174224571863520493293247799005065324264821 = Nat.bit true 87112285931760246646623899502532662132410 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_119]
  rw [base_double_119]
  rw [show 87112285931760246646623899502532662132410 = Nat.bit false 43556142965880123323311949751266331066205 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_120]
  rw [show 43556142965880123323311949751266331066205 = Nat.bit true 21778071482940061661655974875633165533102 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_121]
  rw [base_double_121]
  rw [show 21778071482940061661655974875633165533102 = Nat.bit false 10889035741470030830827987437816582766551 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_122]
  rw [show 10889035741470030830827987437816582766551 = Nat.bit true 5444517870735015415413993718908291383275 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_123]
  rw [base_double_123]
  rw [show 5444517870735015415413993718908291383275 = Nat.bit true 2722258935367507707706996859454145691637 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_124]
  rw [base_double_124]
  rw [show 2722258935367507707706996859454145691637 = Nat.bit true 1361129467683753853853498429727072845818 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_125]
  rw [base_double_125]
  rw [show 1361129467683753853853498429727072845818 = Nat.bit false 680564733841876926926749214863536422909 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_126]
  rw [show 680564733841876926926749214863536422909 = Nat.bit true 340282366920938463463374607431768211454 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_127]
  rw [base_double_127]
  rw [show 340282366920938463463374607431768211454 = Nat.bit false 170141183460469231731687303715884105727 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_false]
  rw [base_double_128]
  rw [show 170141183460469231731687303715884105727 = Nat.bit true 85070591730234615865843651857942052863 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_129]
  rw [base_double_129]
  rw [show 85070591730234615865843651857942052863 = Nat.bit true 42535295865117307932921825928971026431 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_130]
  rw [base_double_130]
  rw [show 42535295865117307932921825928971026431 = Nat.bit true 21267647932558653966460912964485513215 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_131]
  rw [base_double_131]
  rw [show 21267647932558653966460912964485513215 = Nat.bit true 10633823966279326983230456482242756607 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_132]
  rw [base_double_132]
  rw [show 10633823966279326983230456482242756607 = Nat.bit true 5316911983139663491615228241121378303 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_133]
  rw [base_double_133]
  rw [show 5316911983139663491615228241121378303 = Nat.bit true 2658455991569831745807614120560689151 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_134]
  rw [base_double_134]
  rw [show 2658455991569831745807614120560689151 = Nat.bit true 1329227995784915872903807060280344575 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_135]
  rw [base_double_135]
  rw [show 1329227995784915872903807060280344575 = Nat.bit true 664613997892457936451903530140172287 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_136]
  rw [base_double_136]
  rw [show 664613997892457936451903530140172287 = Nat.bit true 332306998946228968225951765070086143 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_137]
  rw [base_double_137]
  rw [show 332306998946228968225951765070086143 = Nat.bit true 166153499473114484112975882535043071 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_138]
  rw [base_double_138]
  rw [show 166153499473114484112975882535043071 = Nat.bit true 83076749736557242056487941267521535 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_139]
  rw [base_double_139]
  rw [show 83076749736557242056487941267521535 = Nat.bit true 41538374868278621028243970633760767 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_140]
  rw [base_double_140]
  rw [show 41538374868278621028243970633760767 = Nat.bit true 20769187434139310514121985316880383 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_141]
  rw [base_double_141]
  rw [show 20769187434139310514121985316880383 = Nat.bit true 10384593717069655257060992658440191 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_142]
  rw [base_double_142]
  rw [show 10384593717069655257060992658440191 = Nat.bit true 5192296858534827628530496329220095 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_143]
  rw [base_double_143]
  rw [show 5192296858534827628530496329220095 = Nat.bit true 2596148429267413814265248164610047 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_144]
  rw [base_double_144]
  rw [show 2596148429267413814265248164610047 = Nat.bit true 1298074214633706907132624082305023 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_145]
  rw [base_double_145]
  rw [show 1298074214633706907132624082305023 = Nat.bit true 649037107316853453566312041152511 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_146]
  rw [base_double_146]
  rw [show 649037107316853453566312041152511 = Nat.bit true 324518553658426726783156020576255 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_147]
  rw [base_double_147]
  rw [show 324518553658426726783156020576255 = Nat.bit true 162259276829213363391578010288127 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_148]
  rw [base_double_148]
  rw [show 162259276829213363391578010288127 = Nat.bit true 81129638414606681695789005144063 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_149]
  rw [base_double_149]
  rw [show 81129638414606681695789005144063 = Nat.bit true 40564819207303340847894502572031 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_150]
  rw [base_double_150]
  rw [show 40564819207303340847894502572031 = Nat.bit true 20282409603651670423947251286015 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_151]
  rw [base_double_151]
  rw [show 20282409603651670423947251286015 = Nat.bit true 10141204801825835211973625643007 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_152]
  rw [base_double_152]
  rw [show 10141204801825835211973625643007 = Nat.bit true 5070602400912917605986812821503 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_153]
  rw [base_double_153]
  rw [show 5070602400912917605986812821503 = Nat.bit true 2535301200456458802993406410751 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_154]
  rw [base_double_154]
  rw [show 2535301200456458802993406410751 = Nat.bit true 1267650600228229401496703205375 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_155]
  rw [base_double_155]
  rw [show 1267650600228229401496703205375 = Nat.bit true 633825300114114700748351602687 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_156]
  rw [base_double_156]
  rw [show 633825300114114700748351602687 = Nat.bit true 316912650057057350374175801343 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_157]
  rw [base_double_157]
  rw [show 316912650057057350374175801343 = Nat.bit true 158456325028528675187087900671 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_158]
  rw [base_double_158]
  rw [show 158456325028528675187087900671 = Nat.bit true 79228162514264337593543950335 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_159]
  rw [base_double_159]
  rw [show 79228162514264337593543950335 = Nat.bit true 39614081257132168796771975167 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_160]
  rw [base_double_160]
  rw [show 39614081257132168796771975167 = Nat.bit true 19807040628566084398385987583 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_161]
  rw [base_double_161]
  rw [show 19807040628566084398385987583 = Nat.bit true 9903520314283042199192993791 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_162]
  rw [base_double_162]
  rw [show 9903520314283042199192993791 = Nat.bit true 4951760157141521099596496895 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_163]
  rw [base_double_163]
  rw [show 4951760157141521099596496895 = Nat.bit true 2475880078570760549798248447 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_164]
  rw [base_double_164]
  rw [show 2475880078570760549798248447 = Nat.bit true 1237940039285380274899124223 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_165]
  rw [base_double_165]
  rw [show 1237940039285380274899124223 = Nat.bit true 618970019642690137449562111 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_166]
  rw [base_double_166]
  rw [show 618970019642690137449562111 = Nat.bit true 309485009821345068724781055 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_167]
  rw [base_double_167]
  rw [show 309485009821345068724781055 = Nat.bit true 154742504910672534362390527 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_168]
  rw [base_double_168]
  rw [show 154742504910672534362390527 = Nat.bit true 77371252455336267181195263 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_169]
  rw [base_double_169]
  rw [show 77371252455336267181195263 = Nat.bit true 38685626227668133590597631 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_170]
  rw [base_double_170]
  rw [show 38685626227668133590597631 = Nat.bit true 19342813113834066795298815 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_171]
  rw [base_double_171]
  rw [show 19342813113834066795298815 = Nat.bit true 9671406556917033397649407 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_172]
  rw [base_double_172]
  rw [show 9671406556917033397649407 = Nat.bit true 4835703278458516698824703 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_173]
  rw [base_double_173]
  rw [show 4835703278458516698824703 = Nat.bit true 2417851639229258349412351 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_174]
  rw [base_double_174]
  rw [show 2417851639229258349412351 = Nat.bit true 1208925819614629174706175 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_175]
  rw [base_double_175]
  rw [show 1208925819614629174706175 = Nat.bit true 604462909807314587353087 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_176]
  rw [base_double_176]
  rw [show 604462909807314587353087 = Nat.bit true 302231454903657293676543 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_177]
  rw [base_double_177]
  rw [show 302231454903657293676543 = Nat.bit true 151115727451828646838271 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_178]
  rw [base_double_178]
  rw [show 151115727451828646838271 = Nat.bit true 75557863725914323419135 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_179]
  rw [base_double_179]
  rw [show 75557863725914323419135 = Nat.bit true 37778931862957161709567 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_180]
  rw [base_double_180]
  rw [show 37778931862957161709567 = Nat.bit true 18889465931478580854783 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_181]
  rw [base_double_181]
  rw [show 18889465931478580854783 = Nat.bit true 9444732965739290427391 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_182]
  rw [base_double_182]
  rw [show 9444732965739290427391 = Nat.bit true 4722366482869645213695 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_183]
  rw [base_double_183]
  rw [show 4722366482869645213695 = Nat.bit true 2361183241434822606847 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_184]
  rw [base_double_184]
  rw [show 2361183241434822606847 = Nat.bit true 1180591620717411303423 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_185]
  rw [base_double_185]
  rw [show 1180591620717411303423 = Nat.bit true 590295810358705651711 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_186]
  rw [base_double_186]
  rw [show 590295810358705651711 = Nat.bit true 295147905179352825855 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_187]
  rw [base_double_187]
  rw [show 295147905179352825855 = Nat.bit true 147573952589676412927 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_188]
  rw [base_double_188]
  rw [show 147573952589676412927 = Nat.bit true 73786976294838206463 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_189]
  rw [base_double_189]
  rw [show 73786976294838206463 = Nat.bit true 36893488147419103231 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_190]
  rw [base_double_190]
  rw [show 36893488147419103231 = Nat.bit true 18446744073709551615 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_191]
  rw [base_double_191]
  rw [show 18446744073709551615 = Nat.bit true 9223372036854775807 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_192]
  rw [base_double_192]
  rw [show 9223372036854775807 = Nat.bit true 4611686018427387903 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_193]
  rw [base_double_193]
  rw [show 4611686018427387903 = Nat.bit true 2305843009213693951 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_194]
  rw [base_double_194]
  rw [show 2305843009213693951 = Nat.bit true 1152921504606846975 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_195]
  rw [base_double_195]
  rw [show 1152921504606846975 = Nat.bit true 576460752303423487 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_196]
  rw [base_double_196]
  rw [show 576460752303423487 = Nat.bit true 288230376151711743 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_197]
  rw [base_double_197]
  rw [show 288230376151711743 = Nat.bit true 144115188075855871 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_198]
  rw [base_double_198]
  rw [show 144115188075855871 = Nat.bit true 72057594037927935 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_199]
  rw [base_double_199]
  rw [show 72057594037927935 = Nat.bit true 36028797018963967 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_200]
  rw [base_double_200]
  rw [show 36028797018963967 = Nat.bit true 18014398509481983 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_201]
  rw [base_double_201]
  rw [show 18014398509481983 = Nat.bit true 9007199254740991 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_202]
  rw [base_double_202]
  rw [show 9007199254740991 = Nat.bit true 4503599627370495 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_203]
  rw [base_double_203]
  rw [show 4503599627370495 = Nat.bit true 2251799813685247 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_204]
  rw [base_double_204]
  rw [show 2251799813685247 = Nat.bit true 1125899906842623 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_205]
  rw [base_double_205]
  rw [show 1125899906842623 = Nat.bit true 562949953421311 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_206]
  rw [base_double_206]
  rw [show 562949953421311 = Nat.bit true 281474976710655 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_207]
  rw [base_double_207]
  rw [show 281474976710655 = Nat.bit true 140737488355327 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_208]
  rw [base_double_208]
  rw [show 140737488355327 = Nat.bit true 70368744177663 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_209]
  rw [base_double_209]
  rw [show 70368744177663 = Nat.bit true 35184372088831 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_210]
  rw [base_double_210]
  rw [show 35184372088831 = Nat.bit true 17592186044415 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_211]
  rw [base_double_211]
  rw [show 17592186044415 = Nat.bit true 8796093022207 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_212]
  rw [base_double_212]
  rw [show 8796093022207 = Nat.bit true 4398046511103 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_213]
  rw [base_double_213]
  rw [show 4398046511103 = Nat.bit true 2199023255551 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_214]
  rw [base_double_214]
  rw [show 2199023255551 = Nat.bit true 1099511627775 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_215]
  rw [base_double_215]
  rw [show 1099511627775 = Nat.bit true 549755813887 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_216]
  rw [base_double_216]
  rw [show 549755813887 = Nat.bit true 274877906943 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_217]
  rw [base_double_217]
  rw [show 274877906943 = Nat.bit true 137438953471 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_218]
  rw [base_double_218]
  rw [show 137438953471 = Nat.bit true 68719476735 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_219]
  rw [base_double_219]
  rw [show 68719476735 = Nat.bit true 34359738367 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_220]
  rw [base_double_220]
  rw [show 34359738367 = Nat.bit true 17179869183 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_221]
  rw [base_double_221]
  rw [show 17179869183 = Nat.bit true 8589934591 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_222]
  rw [base_double_222]
  rw [show 8589934591 = Nat.bit true 4294967295 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_223]
  rw [base_double_223]
  rw [show 4294967295 = Nat.bit true 2147483647 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_224]
  rw [base_double_224]
  rw [show 2147483647 = Nat.bit true 1073741823 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_225]
  rw [base_double_225]
  rw [show 1073741823 = Nat.bit true 536870911 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_226]
  rw [base_double_226]
  rw [show 536870911 = Nat.bit true 268435455 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_227]
  rw [base_double_227]
  rw [show 268435455 = Nat.bit true 134217727 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_228]
  rw [base_double_228]
  rw [show 134217727 = Nat.bit true 67108863 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_229]
  rw [base_double_229]
  rw [show 67108863 = Nat.bit true 33554431 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_230]
  rw [base_double_230]
  rw [show 33554431 = Nat.bit true 16777215 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_231]
  rw [base_double_231]
  rw [show 16777215 = Nat.bit true 8388607 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_232]
  rw [base_double_232]
  rw [show 8388607 = Nat.bit true 4194303 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_233]
  rw [base_double_233]
  rw [show 4194303 = Nat.bit true 2097151 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_234]
  rw [base_double_234]
  rw [show 2097151 = Nat.bit true 1048575 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_235]
  rw [base_double_235]
  rw [show 1048575 = Nat.bit true 524287 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_236]
  rw [base_double_236]
  rw [show 524287 = Nat.bit true 262143 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_237]
  rw [base_double_237]
  rw [show 262143 = Nat.bit true 131071 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_238]
  rw [base_double_238]
  rw [show 131071 = Nat.bit true 65535 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_239]
  rw [base_double_239]
  rw [show 65535 = Nat.bit true 32767 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_240]
  rw [base_double_240]
  rw [show 32767 = Nat.bit true 16383 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_241]
  rw [base_double_241]
  rw [show 16383 = Nat.bit true 8191 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_242]
  rw [base_double_242]
  rw [show 8191 = Nat.bit true 4095 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_243]
  rw [base_double_243]
  rw [show 4095 = Nat.bit true 2047 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_244]
  rw [base_double_244]
  rw [show 2047 = Nat.bit true 1023 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_245]
  rw [base_double_245]
  rw [show 1023 = Nat.bit true 511 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_246]
  rw [base_double_246]
  rw [show 511 = Nat.bit true 255 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_247]
  rw [base_double_247]
  rw [show 255 = Nat.bit true 127 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_248]
  rw [base_double_248]
  rw [show 127 = Nat.bit true 63 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_249]
  rw [base_double_249]
  rw [show 63 = Nat.bit true 31 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_250]
  rw [base_double_250]
  rw [show 31 = Nat.bit true 15 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_251]
  rw [base_double_251]
  rw [show 15 = Nat.bit true 7 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_252]
  rw [base_double_252]
  rw [show 7 = Nat.bit true 3 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_253]
  rw [base_double_253]
  rw [show 3 = Nat.bit true 1 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_254]
  rw [base_double_254]
  rw [show 1 = Nat.bit true 0 by
    norm_num]
  rw [affineNsmulBinRec_go_bit_true]
  rw [acc_add_inverse_255]
  rw [affineNsmulBinRec_go_zero]

/-- Once the published order is shown to kill `G`, its primality and `G_ne_zero` identify
the additive order of `G` exactly. -/
theorem generator_order_of_nsmul_eq_zero (h : order • G = 0) :
    addOrderOf G = order :=
  addOrderOf_eq_prime h G_ne_zero

/-- The published secp256k1 subgroup order kills the published generator. -/
theorem generator_nsmul_eq_zero : order • G = 0 := by
  rw [← affineNsmulBinRec_eq order G]
  exact affineNsmulBinRec_order_eq_zero

/-- The published secp256k1 generator has the published prime subgroup order. -/
theorem generator_order : addOrderOf G = order :=
  generator_order_of_nsmul_eq_zero generator_nsmul_eq_zero
end Secp256k1
end ShorECDLP
