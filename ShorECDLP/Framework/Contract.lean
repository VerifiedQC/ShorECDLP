import ShorECDLP.Framework.CostModel

/-!
# Submission contract

The framework defines only the shape of a verified circuit submission.  It is
independent of every particular problem and correctness statement.  A
submission supplies its single-trial specification and repetition criterion,
then packages one circuit with proofs of its correctness, its claimed T-count,
and the number of trials needed to meet that criterion.
-/

namespace ShorECDLP

/--
A verified submission packages one circuit, a proof that it meets the chosen
single-trial specification, one claimed gate count with its proof, and one
trial count with a proof that those trials meet the chosen success criterion.
Every proof refers to the same `program` field.
-/
structure Submission (Spec : Circuit → Prop)
    (TrialsSufficient : Circuit → Nat → Prop) where
  program : Circuit
  correct : Spec program
  gateCount : Nat
  gateCount_correct : tCount program = gateCount
  trialCount : Nat
  trialCount_correct : TrialsSufficient program trialCount

end ShorECDLP
