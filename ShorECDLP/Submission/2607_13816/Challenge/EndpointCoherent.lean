import ShorECDLP.Submission.«2607_13816».Challenge.EndpointSandwich
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

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

theorem coherentQuerySandwich (query : AdaptiveCircuit) (load middle : Circuit)
    (paths : List Wire) (P : BasisState → Prop)
    (hq : CoherentlyImplementsOn query (Quantum.run load) (Clean paths))
    (hl : HPFree load) (hm : HPFree middle)
    (hbefore : ∀ s, P s → Clean paths s)
    (hafter : ∀ s, P s → Clean paths (Classical.run middle (Classical.run load s))) :
    CoherentlyImplementsOn ((query.seq (.unitary middle .done)).seq query)
      (Quantum.run (load ++ middle ++ load)) P := by
  have hfirst := coherentSeq (coherentRestrict hq hbefore)
    (CoherentlyImplementsOn.unitary middle (fun _ => True)) hl (by intro _ _; trivial)
  apply coherentSeq hfirst hq
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hl g h
    · exact hm g h
  · intro s hs
    simpa only [Classical.run_append] using hafter s hs

theorem endpointQuery_HPFree {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) :
    HPFree (endpointQuery coeffs Q rows base tree control paths) := by
  apply unaryActionUnitary_HPFree
  intro l q g hg
  rcases List.mem_append.mp hg with h | h
  · exact tableXorGates_HPFree _ _ g h
  · exact tableXorGates_HPFree _ _ g h

noncomputable def endpointQueryAdaptive {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) : AdaptiveCircuit :=
  unaryAction .inc
    (fun l q => endpointLookupLeafCircuit (readConstant coeffs Q) (rows l) base q) tree control paths

noncomputable def endpointQueryMatchingAdaptive {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) : AdaptiveCircuit :=
  let query := endpointQueryAdaptive coeffs Q rows base tree control paths
  (query.seq (.unitary (matchingCircuit (matchingRows base) (matchingFlag base) (matchingScratch base)) .done)).seq query

noncomputable def EndpointQueryReady {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (s : BasisState) : Prop :=
  Clean paths s ∧
  Clean (matchingScratch base) (Classical.run (endpointQuery coeffs Q rows base tree control paths) s) ∧
  Classical.run (endpointQuery coeffs Q rows base tree control paths) s (matchingFlag base) = false

theorem endpointQueryMatching_coherent {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (hdata : ∀ w ∈ control::tree.indexWires.dedup++paths, ∀ i, w ≠ matchingRows base 8 i) :
    CoherentlyImplementsOn (endpointQueryMatchingAdaptive coeffs Q rows base tree control paths)
      (Quantum.run (endpointQueryMatching coeffs Q rows base tree control paths))
      (EndpointQueryReady coeffs Q rows base tree control paths) := by
  apply coherentQuerySandwich
    (endpointQueryAdaptive coeffs Q rows base tree control paths)
    (endpointQuery coeffs Q rows base tree control paths)
    (matchingCircuit (matchingRows base) (matchingFlag base) (matchingScratch base)) paths
  · exact endpointLookup_coherent (readConstant coeffs Q) rows base tree control paths hl hd
  · exact endpointQuery_HPFree coeffs Q rows base tree control paths
  · exact matchingMovesCircuit_HPFree _ _ _ _
  · intro s hs
    exact hs.1
  · intro s hs w hw
    have hp : w ∈ control::tree.indexWires.dedup++paths := by simp [hw]
    rw [matchingCircuit_frame (matchingRows base) (matchingFlag base) (matchingScratch base)
      (matchingNetwork_geometry base) (matchingRows_apart base) _ hs.2.1 hs.2.2 w (hdata w hp),
      endpointQuery_frame coeffs Q rows base tree control paths hl hd s hs.1 w (hd w hp)]
    exact hs.1 w hw

def endpointQueryMatchingOps {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) : List (LookupOp n) :=
  let query := unaryLookupOps (fun l q => endpointLookupLeaf (rows l) base q) tree control paths
  query ++ [ordinaryOp (matchingCircuit (matchingRows base) (matchingFlag base) (matchingScratch base))] ++ query

def endpointQueryMatchingProgram {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let ops := endpointQueryMatchingOps rows base tree control paths
  ⟨lookupMeasurements ops,lookupProgram n ops start⟩

theorem endpointQueryMatchingProgram_run {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (start : Nat) (history : Fin start → Bool) :
    compiledRun (endpointQueryMatchingProgram rows base tree control paths start)
      (readConstant coeffs Q) history =
      (endpointQueryMatchingAdaptive coeffs Q rows base tree control paths).run := by
  simp only [endpointQueryMatchingProgram,compiledRun,lookupProgram_run,endpointQueryMatchingOps,
    lookupCircuit_append,unaryLookupOps_circuit,endpointLookupLeaf_source,
    lookupCircuit,ordinaryOp,literal_gates,endpointQueryMatchingAdaptive,endpointQueryAdaptive]

theorem endpointQueryMatchingProgram_measurements {n : Nat} (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (start : Nat) (hl : tree.Layout control paths) :
    (endpointQueryMatchingProgram rows base tree control paths start).1 = 2 * tree.internalNodes := by
  simp only [endpointQueryMatchingProgram,endpointQueryMatchingOps,lookupMeasurements_append,
    ordinaryOp,lookupMeasurements,unaryLookupOps_measurements _ tree control paths hl]
  omega

theorem endpointQueryMatchingProgram_coherent {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (hdata : ∀ w ∈ control::tree.indexWires.dedup++paths, ∀ i, w ≠ matchingRows base 8 i)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn
      ((endpointQueryMatchingProgram rows base tree control paths start).2.instantiate
        (readConstant coeffs Q) history)
      (Quantum.run (endpointQueryMatching coeffs Q rows base tree control paths))
      (EndpointQueryReady coeffs Q rows base tree control paths) := by
  have h := endpointQueryMatching_coherent coeffs Q rows base tree control paths hl hd hdata
  unfold CoherentlyImplementsOn at h ⊢
  have hr := endpointQueryMatchingProgram_run coeffs Q rows base tree control paths start history
  unfold compiledRun at hr
  rw [hr]
  exact h

theorem endpointQueryMatchingProgram_history_length {n : Nat} (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire)
    (start : Nat) (hl : tree.Layout control paths)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (branch : InstrumentBranch)
    (hb : branch ∈ compiledRun (endpointQueryMatchingProgram rows base tree control paths start) read history) :
    branch.history.length = 2 * tree.internalNodes := by
  have h := lookupProgram_history_length n (endpointQueryMatchingOps rows base tree control paths)
    start read history branch hb
  exact h.trans (endpointQueryMatchingProgram_measurements rows base tree control paths start hl)

end ShorECDLP.Paper2607_13816.ChallengeMigration
