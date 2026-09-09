import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem truthMinusOne_zero_iff (width value : Nat) (hv : value < 2^width) :
    truthMinusOneValue width value = 2^width-1 ↔ value = 0 := by
  by_cases hw : width = 0
  · subst width
    have hz : value = 0 := by simpa using hv
    subst value
    decide
  have hm : 1 < 2^width := Nat.one_lt_two_pow hw
  change (value+2^width-1%2^width)%2^width = 2^width-1 ↔ value=0
  rw [Nat.mod_eq_of_lt hm]
  by_cases hz : value = 0
  · subst value
    simp only [Nat.zero_add,Nat.mod_eq_of_lt (by omega : 2^width-1 < 2^width)]
  · rw [show value+2^width-1 = value-1+2^width by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : value-1 < 2^width)]
    omega
/-- A bounded logical length is zero exactly when its encoding is all ones. -/
theorem wireAnd_encoded_zero (wires : List Wire) (s : BasisState) (value : Nat)
    (hvalue : boolWordToNat (wireValues wires s) = truthMinusOneValue wires.length value)
    (hfit : value < 2^wires.length) : wireAnd wires s = decide (value=0) := by
  rw [wireAnd_eq_numeric_allOnes,hvalue]
  simp only [truthMinusOne_zero_iff _ _ hfit]

/-- The actual epoch-aware phase update is the logical zero-test transition on
bounded truth-minus-one length encodings, with complete state and readiness. -/
theorem blockGForward_logical (r : IndexedStepRegisters) (n index Q R S : Nat)
    (s : BasisState) (h : IndexedStepLayout r n index) (hr : IndexedStepReady r s)
    (hepoch : s r.shiftEpoch = false)
    (hq : boolWordToNat (wireValues r.lengthQ s) = truthMinusOneValue r.lengthQ.length Q)
    (hrp : boolWordToNat (wireValues r.lengthRPrime s) = truthMinusOneValue r.lengthRPrime.length R)
    (hs : boolWordToNat (wireValues r.lengthS s) = truthMinusOneValue r.lengthS.length S)
    (hqfit : Q < 2^r.lengthQ.length) (hrfit : R < 2^r.lengthRPrime.length)
    (hsfit : S < 2^r.lengthS.length) :
    let condition := decide (Q=0) && !decide (R=0)
    let next2 := s r.phase2 ^^ (condition && (s r.sign ^^ s r.phase1))
    let nextSign := s r.sign ^^ (condition && next2)
    run (blockGForward r) s =
      s[r.phase1 ↦ s r.phase1 ^^ decide (S=0)]
       [r.phase2 ↦ next2 ^^ decide (S=0)][r.sign ↦ nextSign] ∧
    IndexedStepReady r (run (blockGForward r) s) := by
  have hready := blockGForward_readiness r n index s h hr
  have hg := run_phaseUpdateEpochUnitary r.phaseUpdate r.shiftEpoch s h.phaseUpdate hready.1
  rw [phaseUpdateEpochState_spec _ _ _ h.phaseUpdate] at hg
  have hQ := wireAnd_encoded_zero r.lengthQ s Q hq hqfit
  have hR := wireAnd_encoded_zero r.lengthRPrime s R hrp hrfit
  have hS := wireAnd_encoded_zero r.lengthS s S hs hsfit
  dsimp only
  refine ⟨?_,hready.2⟩
  simpa only [IndexedStepRegisters.phaseUpdate,hQ,hR,hS,hepoch,Bool.not_false,Bool.and_true] using hg
end ShorECDLP.Paper2607_13816
