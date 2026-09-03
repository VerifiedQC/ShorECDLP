import ShorECDLP.Submission.Naive.OrderFinding.OracleSpec

/-!
# Refining a reversible circuit into an ECDLP oracle

This module isolates the quantum proof obligation for the concrete ECDLP oracle.  An H/P-free,
well-formed circuit whose classical action satisfies the exact whole-state oracle equation gives
an `ECDLPOracleSpec` for the quantum semantics of that same circuit.
-/

namespace ShorECDLP.ECDLPOracleSpec

/--
Refine a classical reversible oracle circuit into the abstract quantum ECDLP-oracle contract.

The whole-state hypothesis states both functional correctness and cleanup: the point register is
translated by `a • P + b • Q`, while the exponent registers, oracle workspace, and every wire
outside the point register are restored exactly.
-/
theorem ofCircuit
    {G : Type*} [AddCommGroup G]
    {w : ℕ}
    (enc : PointEncoding G w)
    (oracleCircuit : Circuit)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (hpointWidth : pointReg.length = w)
    (hregistersNodup :
      (aReg ++ bReg ++ pointReg ++ oracleWork).Nodup)
    (hHPFree : Classical.HPFree oracleCircuit)
    (hwellFormed : CircuitWellFormed oracleCircuit)
    (hclassical :
      ∀ (s : BasisState) (a b : ℕ) (R : G),
        regValue aReg s = a →
        regValue bReg s = b →
        regValue pointReg s = (enc.encode R).val →
        Clean oracleWork s →
        Classical.run oracleCircuit s =
          writeReg pointReg
            (enc.encode (R + ecdlpFunction P Q a b)).val s) :
    ECDLPOracleSpec enc (Quantum.run oracleCircuit) P Q
      aReg bReg pointReg oracleWork where
  point_width := hpointWidth
  registers_nodup := hregistersNodup
  preservesInner := Quantum.run_preservesInner oracleCircuit hwellFormed
  onKet := by
    intro s a b R ha hb hpoint hclean
    rw [Quantum.run_ket_agrees_classical oracleCircuit s hHPFree]
    rw [hclassical s a b R ha hb hpoint hclean]

end ShorECDLP.ECDLPOracleSpec
