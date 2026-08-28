import ShorECDLP.Framework.Bitcoin

/-!
# Submission contract

The framework fixes the Bitcoin ECDLP problem and defines the shape of a
verified submission for it.  A submitter supplies one circuit, its T-count,
and its trial count, but cannot choose the correctness predicates those
objects are checked against.
-/

namespace ShorECDLP

/--
In one run, the joint Born probability of measuring registers `(a,b)` whose
canonical ECDLP postprocessing recovers the secret.  The Bitcoin order and
256-bit precision are fixed here; `program` is the submitted trial circuit.
-/
noncomputable def bitcoinOrderFindingSuccessProbability
    (secret : Nat)
    (primeOrder : Nat.Prime order)
    (aReg bReg : List Wire)
    (input : BasisState)
    (program : Circuit) : Real :=
  Quantum.OrderFinding.orderFindingSuccessProbability
    order 256 secret primeOrder aReg bReg
    (Quantum.run program (Quantum.ket input))

/--
Probability that at least one of `trials` independent measured runs recovers
the secret from its measured `(a,b)` pair.
-/
noncomputable def bitcoinRepeatedSuccessProbability
    (secret : Nat)
    (primeOrder : Nat.Prime order)
    (aReg bReg : List Wire)
    (input : BasisState)
    (program : Circuit)
    (trials : Nat) : Real :=
  1 - (1 - bitcoinOrderFindingSuccessProbability
    secret primeOrder aReg bReg input program) ^ trials

/--
The fixed single-trial Bitcoin correctness predicate.  The submitted circuit
must preserve normalization and meet the proved secp256k1 order-finding lower
bound.
-/
def BitcoinECDLPTrialCorrect
    (secret : Nat)
    (primeOrder : Nat.Prime order)
    (aReg bReg : List Wire)
    (input : BasisState)
    (program : Circuit) : Prop :=
  Quantum.normSq (Quantum.run program (Quantum.ket input)) = 1 ∧
    ((order - 1 : Real) / order) *
        ((4 : Real) / Real.pi ^ 2) ^ 2 ≤
      bitcoinOrderFindingSuccessProbability
        secret primeOrder aReg bReg input program

/--
The fixed Bitcoin repetition criterion: the submitted number of independent
measured trials must recover the secret with probability at least 99%.
-/
def BitcoinECDLPTrialsSufficient
    (secret : Nat)
    (primeOrder : Nat.Prime order)
    (aReg bReg : List Wire)
    (input : BasisState)
    (program : Circuit)
    (trials : Nat) : Prop :=
  (99 / 100 : Real) ≤
    bitcoinRepeatedSuccessProbability
      secret primeOrder aReg bReg input program trials

/--
A verified Bitcoin ECDLP submission.  Every proof refers to the same
`program` field, and the correctness and 99%-success predicates are fixed by
the Framework rather than supplied by the submitter.
-/
structure BitcoinECDLPSubmission
    (secret : Nat)
    (primeOrder : Nat.Prime order)
    (aReg bReg : List Wire)
    (input : BasisState) where
  program : Circuit
  correct :
    BitcoinECDLPTrialCorrect secret primeOrder aReg bReg input program
  gateCount : Nat
  gateCount_correct : tCount program = gateCount
  trialCount : Nat
  trialCount_correct :
    BitcoinECDLPTrialsSufficient secret primeOrder aReg bReg input
      program trialCount

end ShorECDLP
