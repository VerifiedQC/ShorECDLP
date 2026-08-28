import ShorECDLP.Framework.Bitcoin
import ShorECDLP.Framework.CostModel
import ShorECDLP.Framework.Quantum.Measurement

/-!
# Bitcoin ECDLP submission contract

The Framework fixes the mathematical Bitcoin problem and its observable
success criterion.  A submission remains free to choose the point encoding,
oracle implementation, and complete trial circuit, but it must prove that the
submitted circuit recovers the discrete logarithm of the specified public key.
-/

namespace ShorECDLP

open scoped BigOperators

/--
The fixed single-trial Bitcoin correctness predicate.

The recovered number must be the discrete logarithm of the specified nonzero
public key.  The submitted circuit must preserve normalization, and the joint
Born probability of measured pairs `(a,b)` whose canonical postprocessing
recovers that secret must be at least the submission's proposed one-run lower
bound.  The proposed number is itself required to lie in `[0,1]`.
-/
noncomputable def BitcoinECDLPTrialCorrect
    [Fact (Nat.Prime p)]
    (publicKey : Secp256k1.Point)
    (secret : Nat)
    (primeOrder : Nat.Prime order)
    (aReg bReg : List Wire)
    (program : Circuit)
    (singleRunSuccessLowerBound : Real) : Prop :=
  publicKey = secret • Secp256k1.G ∧
    publicKey ≠ 0 ∧
    0 ≤ singleRunSuccessLowerBound ∧
    singleRunSuccessLowerBound ≤ 1 ∧
    Quantum.normSq
      (Quantum.run program (Quantum.ket zeroBasisState)) = 1 ∧
    singleRunSuccessLowerBound ≤
      ∑ a : Fin (2 ^ 256),
        ∑ b : Fin (2 ^ 256),
          if Quantum.OrderFinding.orderFindingPostprocess
              order 256 primeOrder (a, b) = some (secret : ZMod order)
          then
            Quantum.OrderFinding.jointRegisterProbability
              aReg bReg a.val b.val
              (Quantum.run program (Quantum.ket zeroBasisState))
          else 0

/--
The fixed Bitcoin repetition criterion.  A submission's proposed one-run
success lower bound and trial count must give at least 99% success under
independent measured repetition.
-/
def BitcoinECDLPTrialsSufficient
    (singleRunSuccessLowerBound : Real)
    (trials : Nat) : Prop :=
  (99 / 100 : Real) ≤
    1 - (1 - singleRunSuccessLowerBound) ^ trials

/--
A verified submission for every nonzero Bitcoin public key.

The correctness predicates are fixed by the Framework.  A submitter supplies
one public-key-indexed circuit family, its uniform exact T-count, a trial
count, and proofs that the same family achieves a proposed one-run success
lower bound for every valid key and reaches 99% after the submitted number of
trials.  The circuit family receives the public key but never the secret, and
every circuit is evaluated from `zeroBasisState`.
-/
structure BitcoinECDLPSubmission
    [Fact (Nat.Prime p)]
    (primeOrder : Nat.Prime order)
    (aReg bReg : List Wire) where
  program : Secp256k1.Point → Circuit
  singleRunSuccessLowerBound : Real
  correct :
    ∀ (publicKey : Secp256k1.Point) (secret : Nat),
      publicKey = secret • Secp256k1.G →
      publicKey ≠ 0 →
      BitcoinECDLPTrialCorrect publicKey secret primeOrder
        aReg bReg (program publicKey) singleRunSuccessLowerBound
  gateCount : Nat
  gateCount_correct :
    ∀ (publicKey : Secp256k1.Point) (secret : Nat),
      publicKey = secret • Secp256k1.G →
      publicKey ≠ 0 →
      tCount (program publicKey) = gateCount
  trialCount : Nat
  trialCount_correct :
    BitcoinECDLPTrialsSufficient singleRunSuccessLowerBound trialCount

end ShorECDLP
