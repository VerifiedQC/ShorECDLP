import ShorECDLP.Submission.«2607_13816».Challenge.BatchCoherent
import ShorECDLP.Submission.«2607_13816».Challenge.BatchPlacement
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

theorem batchWindowTree_below :
    ∀ w ∈ 836::batchWindowTree.indexWires.dedup++pointLookupPath, w < 1024 := by
  unfold batchWindowTree
  rw [tableAddressTree_index pointLookupAddress 0 1 (by decide)]
  intro w hw
  simp only [List.mem_cons,List.mem_append,pointLookupAddress,pointLookupPath,List.mem_range'] at hw
  dsimp only [Wire] at *
  omega

noncomputable def batchWindowUnitary (Q : Point) (w : OddWindow) : Circuit :=
  batchUnitary (readConstant coefficientAt Q) (batchWindowRows w) 1024
    batchWindowTree 836 pointLookupPath batchSchedule

attribute [local irreducible] batchUnitary batchWindowUnitary

theorem batchWindow_coherent (Q : Point) (w : OddWindow) :
    CoherentlyImplementsOn
      (batchSource (readConstant coefficientAt Q) (batchWindowRows w) 1024
        batchWindowTree 836 pointLookupPath batchSchedule)
      (Quantum.run (batchWindowUnitary Q w)) (BatchReady 1024 836 pointLookupPath) := by
  unfold batchWindowUnitary
  exact batchSource_coherent coefficientAt Q (batchWindowRows w) 1024 _ _ _
    batchWindowTree_layout batchWindowTree_below batchSchedule batchSchedule_valid

theorem placedBatchSource_coherent (Q : Point) (w : OddWindow) :
    CoherentlyImplementsOn (placedBatchSource Q w)
      ((relabelState batchPlacement).comp
        ((Quantum.run (batchWindowUnitary Q w)).comp (relabelState batchPlacement.symm)))
      (fun st => BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm st)) :=
  (batchWindow_coherent Q w).relabel batchPlacement

noncomputable def placedBatchState (Q : Point) (w : OddWindow) (st : BasisState) : BasisState :=
  relabelBasis batchPlacement (Classical.run (batchWindowUnitary Q w)
    (relabelBasis batchPlacement.symm st))

theorem batchPlacement_read (st : BasisState) :
    (relabelBasis batchPlacement.symm st) ∘ batchWord 1024 5 = st ∘ accumulatorPort := by
  funext i
  change st (batchPlacement (batchWord 1024 5 i)) = _
  rw [batchPlacement_data]
  rfl

theorem placedBatchState_data (Q : Point) (w : OddWindow) (st : BasisState) :
    placedBatchState Q w st ∘ accumulatorPort =
      Classical.run (batchWindowUnitary Q w) (relabelBasis batchPlacement.symm st) ∘ batchWord 1024 5 := by
  funext i
  change Classical.run _ _ (batchPlacement.symm (accumulatorPort i)) = _
  rw [← batchPlacement_data,Equiv.symm_apply_apply]
  rfl

theorem placedBatchState_finite (Q : Point) (w : OddWindow) (st : BasisState)
    (hs : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm st))
    (hz : ∀ j : Fin 6, j ≠ 5 → (relabelBasis batchPlacement.symm st) ∘ batchWord 1024 j = fun _ => false)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm st)))) = .some hC)
    (P : Point) (hdata : st ∘ accumulatorPort = coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P))) :
    placedBatchState Q w st ∘ accumulatorPort = coordinateWordBits (fig14PointEncoding (P + .some hC)) := by
  rw [placedBatchState_data]
  unfold batchWindowUnitary
  apply batchUnitary_finite coefficientAt Q (batchWindowRows w) 1024 _ _ _
    batchWindowTree_layout batchWindowTree_below _ hs hz hC hr P
  exact (batchPlacement_read st).trans hdata

theorem batchUnitary_HPFree {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (ops : List BatchOp) :
    HPFree (batchUnitary read rows base tree control paths ops) := by
  induction ops with
  | nil => intro g hg; unfold batchUnitary at hg; cases hg
  | cons op ops ih =>
    unfold batchUnitary
    exact (Classical.hpFree_append _ _).mpr ⟨batchStep_HPFree read rows base tree control paths op,ih⟩


private theorem coherentRelabelState {program : AdaptiveCircuit} {c : Circuit} {P : BasisState → Prop}
    (h : CoherentlyImplementsOn program (Quantum.run c) P) (hc : HPFree c) (e : Wire ≃ Wire) :
    CoherentlyImplementsOn (program.relabel e)
      (Finsupp.lmapDomain ℂ ℂ (fun st => relabelBasis e (Classical.run c (relabelBasis e.symm st))))
      (fun st => P (relabelBasis e.symm st)) := by
  apply (h.relabel e).congrIdeal
  intro st hs
  simp only [LinearMap.comp_apply,relabelState_ket]
  rw [run_ket_agrees_classical c _ hc,relabelState_ket]
  simp only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem placedBatchSource_state (Q : Point) (w : OddWindow) :
    CoherentlyImplementsOn (placedBatchSource Q w) (Finsupp.lmapDomain ℂ ℂ (placedBatchState Q w))
      (fun st => BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm st)) := by
  exact coherentRelabelState (batchWindow_coherent Q w)
    (by unfold batchWindowUnitary; exact batchUnitary_HPFree _ _ _ _ _ _ _) batchPlacement
end ShorECDLP.Paper2607_13816.ChallengeMigration
