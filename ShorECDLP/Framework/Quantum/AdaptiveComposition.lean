import ShorECDLP.Framework.Quantum.Adaptive
namespace ShorECDLP.Quantum
noncomputable section
theorem circuit_seq_done (a : AdaptiveCircuit) : a.seq .done = a := by
  induction a with
  | done => rfl
  | unitary c a ih => simp only [AdaptiveCircuit.seq, ih]
  | xMeasureReset w a b ia ib => simp only [AdaptiveCircuit.seq, ia, ib]
theorem circuit_seq_assoc (a b c : AdaptiveCircuit) : (a.seq b).seq c=a.seq (b.seq c) := by
  induction a with
  | done => rfl
  | unitary d a ih => simp only [AdaptiveCircuit.seq,ih]
  | xMeasureReset w a b ia ib => simp only [AdaptiveCircuit.seq,ia,ib]
end
end ShorECDLP.Quantum
