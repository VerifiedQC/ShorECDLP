import ShorECDLP.Challenge.Contract
open ShorECDLP ShorECDLP.Challenge
example : ShorECDLP.Challenge.readWord ([true, false, true] : List Bool) ([0,1,2] : List Nat) = some 5 := rfl
example : ShorECDLP.Challenge.readWord ([true] : List Bool) ([1] : List Nat) = none := rfl
def baselineParams : DecoderParams := ⟨256, 208, by decide, by decide, by decide, by decide⟩
def fullParams : DecoderParams := ⟨256, 256, by decide, by decide, by decide, by decide⟩
example : trialCandidateLimit baselineParams = 2^49+2 := by decide +kernel
example : trialCandidateLimit fullParams = 4 := by decide +kernel
example : 56 * trialCandidateLimit baselineParams = budget55 := by decide +kernel
example : budget48 < 56 * trialCandidateLimit baselineParams := by decide +kernel
#print axioms fixedCandidates_card
#print axioms fixedCandidates_take
#print axioms candidates_length
#print axioms verifiedCandidate_sound
#check Certificate

example : decoderCandidateLimit .nearestPair fullParams = 1 := rfl
example : 26 * decoderCandidateLimit .nearestPair fullParams = 26 := rfl
example (left right : Nat) : nearestPairCandidates baselineParams left right = [] := by
  simp [nearestPairCandidates, baselineParams]
example (left right : Fin (2^256)) :
    nearestPairCandidates fullParams left.val right.val =
      (Quantum.OrderFinding.orderFindingPostprocess order 256
        Secp256k1.order_prime (left, right)).toList :=
  nearestPairCandidates_eq_postprocess fullParams rfl left right
