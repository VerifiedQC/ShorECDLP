import ShorECDLP.Submission.«2607_13816».Challenge.BatchExecution
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] endpointTranspositionCircuit batchOpCircuit batchStepCircuit
theorem batchStep_HPFree {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (op : BatchOp) :
    HPFree (batchStepCircuit read rows base tree control paths op) := by
  cases op with
  | query sources target =>
    unfold batchStepCircuit
    apply unaryActionUnitary_HPFree
    intro l q
    unfold batchLeafCircuit
    rw [Classical.hpFree_append]
    exact ⟨tableXorGates_HPFree _ _,tableXorGates_HPFree _ _⟩
  | swap source target =>
    unfold batchStepCircuit batchOpCircuit
    unfold endpointTranspositionCircuit
    rw [Classical.hpFree_append, Classical.hpFree_append]
    exact ⟨⟨endpointTests_HPFree _ _ _ _ _,endpointWordCircuit_HPFree _ _⟩,
      endpointTests_HPFree _ _ _ _ _⟩
private theorem coherentRestrict {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P Q : BasisState → Prop} (h : CoherentlyImplementsOn a v P)
    (hp : ∀ s, Q s → P s) : CoherentlyImplementsOn a v Q := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

private theorem coherentSeq {a b : AdaptiveCircuit} {u v : Circuit} {P Q : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) Q)
    (hu : HPFree u) (hp : ∀ s, P s → Q (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical u s hu]
    exact supportedOn_ket Q _ (hp s hs))
  apply h.congrIdeal
  intro s _
  exact (Quantum.run_append u v (ket s)).symm


theorem batchSource_coherent {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base)
    (ops : List BatchOp) (hv : ∀ op ∈ ops, op.Valid) :
    CoherentlyImplementsOn (batchSource (readConstant coeffs Q) rows base tree control paths ops)
      (Quantum.run (batchUnitary (readConstant coeffs Q) rows base tree control paths ops))
      (BatchReady base control paths) := by
  induction ops with
  | nil =>
    refine ⟨[1],?_,by simp⟩
    apply List.Forall₂.cons
    · intro st hs; simp [batchUnitary,Quantum.run]
    · exact .nil
  | cons op ops ih =>
    have ht := ih (fun o ho => hv o (by simp [ho]))
    have hp := fun st hs => (batchStep_model coeffs Q rows base tree control paths hl hd op
      (hv op (by simp)) st hs).2.1
    have hf := batchStep_HPFree (readConstant coeffs Q) rows base tree control paths op
    cases op with
    | query sources target =>
      have hq := batchQuery_coherent (readConstant coeffs Q) rows base tree control paths
        (batchSelection sources target) (batchSelection_nodup sources target) hl
        (fun w hw => Or.inl (hd w hw))
      have hq' := coherentRestrict hq (fun st (hs : BatchReady base control paths st) => hs.1)
      simp only [batchStepCircuit] at hf hp
      simpa only [batchSource,batchUnitary,batchStepCircuit] using coherentSeq hq' ht hf hp
    | swap source target =>
      have hu := CoherentlyImplementsOn.unitary (batchOpCircuit base source target)
        (BatchReady base control paths)
      simp only [batchStepCircuit] at hf hp
      simpa only [batchSource,batchUnitary,batchStepCircuit,AdaptiveCircuit.seq] using coherentSeq hu ht hf hp

end ShorECDLP.Paper2607_13816.ChallengeMigration
