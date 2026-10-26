import ShorECDLP.Challenge.Template
import Mathlib.Order.Interval.Finset.Nat

namespace ShorECDLP.Challenge
/-- Fixed menu for this initial release. Additional algorithms require protected
code review, not a submission-provided callback. -/
inductive DecoderKind where
  | wrappedShift
  deriving DecidableEq, Repr

/-- Fixed bounded menu of precisions; no submitted algorithm. -/
structure DecoderParams where
  leftBits : Nat
  rightBits : Nat
  left_lower : 1 ≤ leftBits
  left_upper : leftBits ≤ 512
  right_lower : 1 ≤ rightBits
  right_upper : rightBits ≤ 512

structure TrialPositions (params : DecoderParams) where
  left : Vector Nat params.leftBits
  right : Vector Nat params.rightBits

structure DecodeLayout where
  kind : DecoderKind
  params : DecoderParams
  trials : List (TrialPositions params)
  trials_le : trials.length ≤ 56

/-- Little-endian bit extraction. Missing history positions reject the trial. -/
def readWord (history : List Bool) : List Nat → Option Nat
  | [] => some 0
  | i :: rest => do
    let bit ← history[i]?
    let tail ← readWord history rest
    pure ((if bit then 1 else 0) + 2 * tail)

/-- Same half-bin formula as the fixed upstream reduced-precision decoder. -/
def numeratorInterval (r precision value : Nat) : Finset Nat :=
  Finset.Icc ((2*r*value-r)/(2*2^precision)) ((2*r*value+r)/(2*2^precision))

theorem numeratorInterval_card (r precision value : Nat) :
    (numeratorInterval r precision value).card ≤ r / 2^precision + 2 := by
  let N := 2^precision
  let a := 2*r*value
  have hN : 0 < N := by dsimp [N]; positivity
  have hlo := Nat.lt_mul_div_succ (a-r) (by omega : 0<2*N)
  have hhi := Nat.div_mul_le_self (a+r) (2*N)
  have hr := Nat.lt_mul_div_succ r hN
  have hsub : a ≤ (a-r)+r := by omega
  have hwidth : (a+r)/(2*N) ≤ (a-r)/(2*N) + r/N + 1 := by nlinarith
  simp only [numeratorInterval, Nat.card_Icc]
  change (a+r)/(2*N) + 1 - (a-r)/(2*N) ≤ r/N+2
  exact Nat.sub_le_of_le_add (by omega)

def wrappedNumerators (r precision value : Nat) : Finset Nat :=
  numeratorInterval r precision value ∪
    if value=0 then numeratorInterval r precision (2^precision) else ∅

theorem wrappedNumerators_card (r precision value : Nat) :
    (wrappedNumerators r precision value).card ≤ 2*(r/2^precision+2) := by
  unfold wrappedNumerators
  apply (Finset.card_union_le _ _).trans
  have h₁ := numeratorInterval_card r precision value
  split_ifs
  · have h₂ := numeratorInterval_card r precision (2^precision)
    omega
  · simp only [Finset.card_empty, Nat.add_zero]
    omega

def nearestNumerator (r precision value : Nat) : Nat :=
  (2*r*value+2^precision)/(2*2^precision)

noncomputable def fixedCandidates (params : DecoderParams) (left right : Nat) : Finset (ZMod order) :=
  (wrappedNumerators order params.rightBits right).image
    (fun (l : Nat) => (l : ZMod order) * (nearestNumerator order params.leftBits left : ZMod order)⁻¹)

def trialCandidateLimit (params : DecoderParams) : Nat := 2*(order / 2^params.rightBits + 2)

theorem fixedCandidates_card (params : DecoderParams) (left right : Nat) :
    (fixedCandidates params left right).card ≤ trialCandidateLimit params := by
  apply (Finset.card_image_le).trans
  exact wrappedNumerators_card order params.rightBits right

theorem fixedCandidates_take (params : DecoderParams) (left right : Nat) :
    (fixedCandidates params left right).toList.take (trialCandidateLimit params) =
      (fixedCandidates params left right).toList := by
  apply List.take_of_length_le
  simpa using fixedCandidates_card params left right

/-- The protected cap never truncates the fixed candidate set (fixedCandidates_take).
The submitted data cannot change the algorithm or the cap. -/
noncomputable def trialCandidates (params : DecoderParams) (history : List Bool) (positions : TrialPositions params) :
    List (ZMod order) :=
  match readWord history positions.left.toList, readWord history positions.right.toList with
  | some left, some right => (fixedCandidates params left right).toList.take (trialCandidateLimit params)
  | _, _ => []

theorem trialCandidates_length (params : DecoderParams) (history : List Bool) (positions : TrialPositions params) :
    (trialCandidates params history positions).length ≤ trialCandidateLimit params := by
  unfold trialCandidates
  split <;> simp [List.length_take]

noncomputable def candidates (layout : DecodeLayout) (history : List Bool) : List (ZMod order) :=
  match layout.kind with
  | .wrappedShift => layout.trials.flatMap (trialCandidates layout.params history)

theorem candidates_length_trials (layout : DecodeLayout) (history : List Bool) :
    (candidates layout history).length ≤ layout.trials.length * trialCandidateLimit layout.params := by
  have aux : ∀ ps : List (TrialPositions layout.params),
      (ps.flatMap (trialCandidates layout.params history)).length ≤ ps.length * trialCandidateLimit layout.params := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
      have h := trialCandidates_length layout.params history p
      omega
  cases hk : layout.kind
  simpa [candidates, hk] using
    aux layout.trials
theorem candidates_length (layout : DecodeLayout) (history : List Bool) :
    (candidates layout history).length ≤ 56 * trialCandidateLimit layout.params :=
  (candidates_length_trials layout history).trans
    (Nat.mul_le_mul_right _ layout.trials_le)

end ShorECDLP.Challenge
