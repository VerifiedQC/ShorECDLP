import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
import ShorECDLP.Submission.«2607_13816».EEA.LengthBlocks
import ShorECDLP.Submission.«2607_13816».EEA.ShiftCounter

/-! # Logical lengths at the quotient counter boundaries -/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem truthMinusOne_increment (width Q : Nat) :
    (truthMinusOneValue width Q+1)%2^width = truthMinusOneValue width (Q+1) := by
  cases width with
  | zero =>
    change ((_ % 1)+1)%1 = _%1
    simp only [Nat.mod_one]
  | succ width =>
    have hm : 1 < 2^(width+1) := Nat.one_lt_two_pow (by omega)
    change (((Q+2^(width+1)-1%2^(width+1))%2^(width+1))+1)%2^(width+1) =
      (Q+1+2^(width+1)-1%2^(width+1))%2^(width+1)
    rw [Nat.mod_eq_of_lt hm]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    omega
private theorem truthMinusOne_decrement (width Q : Nat) (hQ : 0 < Q) :
    (truthMinusOneValue width Q+2^width-1)%2^width = truthMinusOneValue width (Q-1) := by
  cases width with
  | zero =>
    change ((_ % 1)+1-1)%1 = _%1
    simp only [Nat.mod_one]
  | succ width =>
    have hm : 1 < 2^(width+1) := Nat.one_lt_two_pow (by omega)
    change (((Q+2^(width+1)-1%2^(width+1))%2^(width+1))+2^(width+1)-1)%2^(width+1) =
      (Q-1+2^(width+1)-1%2^(width+1))%2^(width+1)
    rw [Nat.mod_eq_of_lt hm]
    have he := (Nat.mod_modEq (Q+2^(width+1)-1) (2^(width+1))).add_right (2^(width+1)-1)
    change _%_ = _%_ at he
    rw [show (Q+2^(width+1)-1)%2^(width+1)+2^(width+1)-1 =
      (Q+2^(width+1)-1)%2^(width+1)+(2^(width+1)-1) by omega,he]
    rw [show Q+2^(width+1)-1+(2^(width+1)-1) = (Q-1+2^(width+1)-1)+2^(width+1) by omega]
    simp only [Nat.add_mod_right]
/-- Logical quotient length after the source's phase-2 increment, retaining
its complete external frame and clean auxiliaries. -/
theorem blockD1Forward_logicalLength (r : IndexedStepRegisters) (n index Q : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux s)
    (hq : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length Q) :
    let final := run (blockD1Forward r) s
    boolWordToNat (wireValues r.lengthQ final) = truthMinusOneValue r.lengthQ.length
      (if !s r.phase1 && s r.phase2 then Q+1 else Q) ∧
    AgreesOutside r.lengthQ final s ∧ Clean r.aux final := by
  have hb := blockD1Forward_contract r n index s h hc
  refine ⟨?_,hb.2⟩
  rw [hb.1,boolWordToNat_incrementBits]
  simp only [wireValues,List.length_map]
  change ((!s r.phase1 && s r.phase2).toNat+boolWordToNat (wireValues r.lengthQ s))%2^r.lengthQ.length = _
  cases he : !s r.phase1 && s r.phase2 with
  | false =>
    simp only [Bool.toNat_false,Nat.zero_add,Bool.false_eq_true,if_false]
    rw [Nat.mod_eq_of_lt (by simpa [wireValues] using boolWordToNat_lt_pow_two (wireValues r.lengthQ s))]
    exact hq
  | true =>
    simp only [Bool.toNat_true,if_true]
    rw [hq,Nat.add_comm]
    exact truthMinusOne_increment _ _

private theorem decrement_false (bits : List Bool) : decrementBits false bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [decrementBits,ih]

/-- The phase-3 counter decrements a positive logical quotient length, while
preserving the complete external frame and clean auxiliaries. -/
theorem blockD3Forward_logicalLength (r : IndexedStepRegisters) (n index Q : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux s)
    (hq : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length Q)
    (hpositive : (s r.phase1 && !s r.phase2) = true → 0 < Q) :
    let final := run (blockD3Forward r) s
    boolWordToNat (wireValues r.lengthQ final) = truthMinusOneValue r.lengthQ.length
      (if s r.phase1 && !s r.phase2 then Q-1 else Q) ∧
    AgreesOutside r.lengthQ final s ∧ Clean r.aux final := by
  have hb := blockD3Forward_contract r n index s h hc
  refine ⟨?_,hb.2⟩
  rw [hb.1]
  cases he : s r.phase1 && !s r.phase2 with
  | false => simpa only [Bool.false_eq_true,if_false,decrement_false] using hq
  | true =>
    simp only [if_true,boolWordToNat_decrementBits,wireValues,List.length_map]
    change (boolWordToNat (wireValues r.lengthQ s)+2^r.lengthQ.length-1)%2^r.lengthQ.length = _
    rw [hq]
    exact truthMinusOne_decrement _ _ (hpositive he)
end ShorECDLP.Paper2607_13816
