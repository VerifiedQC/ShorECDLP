import ShorECDLP.Math.Bitcoin
import ShorECDLP.Math.BitcoinPrimes
import ShorECDLP.Framework.CostModel
import ShorECDLP.Framework.Quantum.Measurement

/-!
# Bitcoin ECDLP submission contract

The shared mathematical layer fixes the Bitcoin problem. This contract fixes the observable
success criterion for the naive unitary implementation, which remains free to choose its point encoding,
oracle implementation, and complete trial circuit, but it must prove that the
submitted circuit recovers the discrete logarithm of the specified public key.
-/

namespace ShorECDLP

open scoped BigOperators

/--
A verified submission for every nonzero Bitcoin public key.

One public-key-indexed circuit family must work for every valid nonzero key;
the circuit receives the public key but never the secret.  Each run starts in
`zeroBasisState`.  The submitted one-run lower bound must lie in `[0,1]`, the
circuit must preserve normalization, and the joint Born probability of
measured pairs `(a,b)` whose canonical postprocessing recovers the secret must
reach that bound.  Finally, independent repetition must raise the same bound
to at least 99%.  The exact T-count and a static qubit upper bound must both be
certified for that same circuit family.  These requirements are written
directly in the fields below so a submission cannot replace or weaken them.
-/
structure BitcoinECDLPSubmission
    (primeOrder : Nat.Prime order)
    (aReg bReg : List Wire) where
  program : Secp256k1.Point → Circuit
  singleRunSuccessLowerBound : Real
  correct :
    ∀ (publicKey : Secp256k1.Point) (secret : Nat),
      publicKey = secret • Secp256k1.G →
      publicKey ≠ 0 →
      0 ≤ singleRunSuccessLowerBound ∧
      singleRunSuccessLowerBound ≤ 1 ∧
      Quantum.normSq
        (Quantum.run (program publicKey) (Quantum.ket zeroBasisState)) = 1 ∧
      singleRunSuccessLowerBound ≤
        ∑ a : Fin (2 ^ 256),
          ∑ b : Fin (2 ^ 256),
            if Quantum.OrderFinding.orderFindingPostprocess
                order 256 primeOrder (a, b) = some (secret : ZMod order)
            then
              Quantum.OrderFinding.jointRegisterProbability
                aReg bReg a.val b.val
                (Quantum.run (program publicKey) (Quantum.ket zeroBasisState))
            else 0
  gateCount : Nat
  gateCount_correct :
    ∀ (publicKey : Secp256k1.Point) (secret : Nat),
      publicKey = secret • Secp256k1.G →
      publicKey ≠ 0 →
      tCount (program publicKey) = gateCount
  qubitCount : Nat
  qubitCount_correct :
    ∀ (publicKey : Secp256k1.Point) (secret : Nat),
      publicKey = secret • Secp256k1.G →
      publicKey ≠ 0 →
      ShorECDLP.qubitCount (program publicKey) ≤ qubitCount
  trialCount : Nat
  trialCount_correct :
    (99 / 100 : Real) ≤
      1 - (1 - singleRunSuccessLowerBound) ^ trialCount

end ShorECDLP
