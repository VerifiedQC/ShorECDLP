import ShorECDLP.Submission.«2607_13816».EEA.TBoundary
import ShorECDLP.Submission.«2607_13816».EEA.LengthBlocks
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep

/-! # Logical interpretation of the prepared coefficient boundary
Stored lengths use the modular truth-minus-one encoding, including logical zero.
The decoded endpoints are `T+1` and `n+3-R-S`; phase 2 selects their order.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem subtraction_balance (m a b : Nat) (ha : a ≤ b + m) :
    (b + m - a) % m + a ≡ b [MOD m] := by
  calc
    (b + m - a) % m + a ≡ (b + m - a) + a [MOD m] :=
      (Nat.mod_modEq _ _).add_right a
    _ = b + m := Nat.sub_add_cancel ha
    _ ≡ b [MOD m] := by simp

private theorem subtractWord_balance (a b : List Bool) (h : a.length = b.length) :
    boolWordToNat (cuccaroSubBits false a b) + boolWordToNat a ≡
      boolWordToNat b [MOD 2^a.length] := by
  rw [boolWordToNat_cuccaroSubBits_false a b h]
  exact subtraction_balance _ _ _ (by have := boolWordToNat_lt_pow_two a; omega)

private theorem addWord_balance (a b : List Bool) (h : a.length = b.length) :
    boolWordToNat (cuccaroAddBits false a b) ≡
      boolWordToNat a + boolWordToNat b [MOD 2^a.length] := by
  rw [boolWordToNat_cuccaroAddBits false a b h]
  simpa using Nat.mod_modEq (boolWordToNat a + boolWordToNat b) (2^a.length)

private theorem truthMinusOne_balance (width value : Nat) (hw : 0 < width) :
    truthMinusOneValue width value + 1 ≡ value [MOD 2^width] := by
  have hm : 1 < 2^width := Nat.one_lt_two_pow hw.ne'
  change (value + 2^width - 1 % 2^width) % 2^width + 1 ≡ value [MOD 2^width]
  rw [Nat.mod_eq_of_lt hm]
  exact subtraction_balance _ _ _ (by omega)


private theorem preparedT_value (t : List Bool) (T : Nat) (hw : 0 < t.length)
    (ht : boolWordToNat t = truthMinusOneValue t.length T) (hh : T+1 < 2^t.length) :
    boolWordToNat (cuccaroAddBits false (constantBits t.length 2) t) = T+1 := by
  have hb := addWord_balance (constantBits t.length 2) t (by simp)
  simp only [constantBits_length,boolWordToNat_constantBits] at hb
  have ht' := truthMinusOne_balance t.length T hw
  rw [← ht] at ht'
  have he : 2%2^t.length + boolWordToNat t ≡ T+1 [MOD 2^t.length] := by
    have hm := (Nat.mod_modEq 2 (2^t.length)).add_right (boolWordToNat t)
    have hh' := ht'.add_right 1
    have heq : boolWordToNat t + 1 + 1 = 2 + boolWordToNat t := by omega
    rw [heq] at hh'
    exact hm.trans hh'
  exact (hb.trans he).eq_of_lt_of_lt (by
    have hl := boolWordToNat_lt_pow_two (cuccaroAddBits false (constantBits t.length 2) t)
    simpa only [cuccaroAddBits_length false (constantBits t.length 2) t (by simp),constantBits_length] using hl) hh

private theorem preparedRP_value (rp ls : List Bool) (R S n : Nat)
    (hlen : rp.length = ls.length) (hw : 0 < rp.length)
    (hr : boolWordToNat rp = truthMinusOneValue rp.length R)
    (hs : boolWordToNat ls = truthMinusOneValue rp.length S)
    (hlo : R+S ≤ n+3) (hhi : n+3-R-S < 2^rp.length) :
    boolWordToNat (cuccaroSubBits false ls (constMinusBits rp (n+1))) = n+3-R-S := by
  have hb := subtractWord_balance ls (constMinusBits rp (n+1)) (by simp [hlen])
  rw [← hlen] at hb
  have hc : boolWordToNat (constMinusBits rp (n+1)) + boolWordToNat rp ≡ n+1 [MOD 2^rp.length] := by
    rw [boolWordToNat_constMinusBits]
    exact subtraction_balance _ _ _ (by have := boolWordToNat_lt_pow_two rp; omega)
  have ht' := truthMinusOne_balance rp.length R hw
  have hs' := truthMinusOne_balance rp.length S hw
  rw [← hr] at ht'
  rw [← hs] at hs'
  have he : boolWordToNat (cuccaroSubBits false ls (constMinusBits rp (n+1))) + (R+S) ≡ n+3 [MOD 2^rp.length] := by
    have hsum := ((hb.add_right (boolWordToNat rp)).trans hc).add_right 2
    have henc := (ht'.add hs').add_left (boolWordToNat (cuccaroSubBits false ls (constMinusBits rp (n+1))))
    have hnorm : boolWordToNat (cuccaroSubBits false ls (constMinusBits rp (n+1))) +
        (boolWordToNat rp + 1 + (boolWordToNat ls + 1)) =
        (boolWordToNat (cuccaroSubBits false ls (constMinusBits rp (n+1))) + boolWordToNat ls + boolWordToNat rp) + 2 := by omega
    have hrhs : n+1+2 = n+3 := by omega
    rw [hrhs] at hsum
    exact henc.symm.trans (by rw [hnorm]; exact hsum)
  have heq : n+3 = (n+3-R-S)+(R+S) := by omega
  rw [heq] at he
  exact (Nat.ModEq.add_right_cancel' (R+S) he).eq_of_lt_of_lt (by
    have hl := boolWordToNat_lt_pow_two (cuccaroSubBits false ls (constMinusBits rp (n+1)))
    simpa only [cuccaroSubBits_length false ls (constMinusBits rp (n+1)) (by simp [hlen]),← hlen] using hl) hhi

private theorem prepared_values (phase : Bool) (t rp ls : List Bool) (T R S n : Nat)
    (htr : t.length = rp.length) (hts : t.length = ls.length) (hw : 0 < t.length)
    (ht : boolWordToNat t = truthMinusOneValue t.length T)
    (hr : boolWordToNat rp = truthMinusOneValue t.length R)
    (hs : boolWordToNat ls = truthMinusOneValue t.length S)
    (hthi : T+1 < 2^t.length) (hlo : R+S ≤ n+3) (hhi : n+3-R-S < 2^t.length) :
    let words := prepareLatestPaperTBoundaryWords phase t rp ls n
    (boolWordToNat words.1,boolWordToNat words.2) =
      if phase then (n+3-R-S,T+1) else (T+1,n+3-R-S) := by
  have ht' := preparedT_value t T hw ht hthi
  have hr' := preparedRP_value rp ls R S n (htr.symm.trans hts)
    (by simpa only [← htr] using hw) (by simpa only [← htr] using hr)
    (by simpa only [← htr] using hs) hlo (by simpa only [← htr] using hhi)
  cases phase <;> simp only [prepareLatestPaperTBoundaryWords,Bool.false_eq_true,
    if_false,if_true,ht',hr']

/-- The actual boundary preparation decodes both stored lengths, including the
zero sentinel, provided the resulting endpoints fit the word. -/
theorem prepareLatestPaperTBoundary_arithmetic (r : TBoundaryRegisters) (n T R S : Nat)
    (s : BasisState) (h : TBoundaryLayout r) (hc : TBoundaryReady r s)
    (ht : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.width T)
    (hr : boolWordToNat (wireValues r.lengthRP s) = truthMinusOneValue r.width R)
    (hs : boolWordToNat (wireValues r.lengthSLow s) = truthMinusOneValue r.width S)
    (hthi : T+1 < 2^r.width) (hlo : R+S ≤ n+3) (hhi : n+3-R-S < 2^r.width) :
    let final := run (prepareLatestPaperTBoundary r n) s
    (boolWordToNat (wireValues r.lengthT final),boolWordToNat (wireValues r.lengthRP final)) =
      (if s r.phase2 then (n+3-R-S,T+1) else (T+1,n+3-R-S)) ∧
      TBoundaryReady r final ∧
      (∀ w, w ∉ r.lengthT → w ∉ r.lengthRP → final w = s w) := by
  have hv := prepareLatestPaperTBoundary_correct r n s h hc
  refine ⟨?_,hv.2⟩
  have hp := prepared_values (s r.phase2) (wireValues r.lengthT s)
    (wireValues r.lengthRP s) (wireValues r.lengthSLow s) T R S n
    (by simp only [wireValues,List.length_map,h.lengthRP_length]; rfl)
    (by simp only [wireValues,List.length_map,TBoundaryRegisters.lengthSLow,List.length_take,Nat.min_eq_left h.lengthS_capacity]; rfl)
    (by simpa only [wireValues,List.length_map] using h.positive)
    (by simpa only [wireValues,List.length_map] using ht)
    (by simpa only [wireValues,List.length_map] using hr)
    (by simpa only [wireValues,List.length_map] using hs)
    (by simpa only [wireValues,List.length_map] using hthi) hlo
    (by simpa only [wireValues,List.length_map] using hhi)
  have he := congrArg (fun p : List Bool × List Bool => (boolWordToNat p.1,boolWordToNat p.2)) hv.1
  exact he.trans hp

/-- The source Block E prefix selects its arithmetic boundary from the logical
lengths. Control and scratch conclusions belong to the same preparation circuit. -/
theorem blockEPrepareForward_arithmetic (r : IndexedStepRegisters) (n index T R S : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index)
    (hc : Clean r.blockScratch s) (hz : s r.terminal = false)
    (ht : boolWordToNat (wireValues r.lengthT s) = truthMinusOneValue r.lengthT.length T)
    (hr : boolWordToNat (wireValues r.lengthRPrime s) = truthMinusOneValue r.lengthT.length R)
    (hs : boolWordToNat (wireValues r.tBoundary.lengthSLow s) = truthMinusOneValue r.lengthT.length S)
    (hthi : T+1 < 2^r.lengthT.length) (hlo : R+S ≤ n+3) (hhi : n+3-R-S < 2^r.lengthT.length) :
    let final := run (blockEPrepareForward r n) s
    (boolWordToNat (wireValues r.lengthT final),boolWordToNat (wireValues r.lengthRPrime final)) =
      (if s r.phase2 then (n+3-R-S,T+1) else (T+1,n+3-R-S)) ∧
      final r.control = (s r.control ^^ (s r.phase1 && !(!s r.phase2 && s r.sign))) ∧
      AgreesOutside (r.control :: r.lengthT ++ r.lengthRPrime) final s ∧
      Clean r.blockScratch final := by
  have hv := blockEPrepareForward_contract r n index s h hc hz
  refine ⟨?_,hv.2⟩
  have hp := prepared_values (s r.phase2) (wireValues r.lengthT s)
    (wireValues r.lengthRPrime s) (wireValues r.tBoundary.lengthSLow s) T R S n
    (by simpa only [wireValues,List.length_map] using h.tBoundary.lengthRP_length.symm)
    (by simp only [wireValues,List.length_map,TBoundaryRegisters.lengthSLow,List.length_take,
        Nat.min_eq_left h.tBoundary.lengthS_capacity]; rfl)
    (by simpa only [wireValues,List.length_map] using h.tBoundary.positive)
    (by simpa only [wireValues,List.length_map] using ht)
    (by simpa only [wireValues,List.length_map] using hr)
    (by simpa only [wireValues,List.length_map] using hs)
    (by simpa only [wireValues,List.length_map] using hthi) hlo
    (by simpa only [wireValues,List.length_map] using hhi)
  have he := congrArg (fun p : List Bool × List Bool => (boolWordToNat p.1,boolWordToNat p.2)) hv.1
  exact he.trans hp
end ShorECDLP.Paper2607_13816
