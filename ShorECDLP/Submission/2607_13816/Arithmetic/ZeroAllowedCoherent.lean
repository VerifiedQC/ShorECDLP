import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowed
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem zeroPrepare_HPFree : HPFree fig15ZeroPrepare := by
  rw [fig15ZeroPrepare,nonzeroInputPrepare,hpFree_append]
  exact ⟨computeEqConst_HPFree _ _ _ _,by simp [HPFree]⟩
private theorem zeroRestore_HPFree : HPFree fig15ZeroRestore := by
  rw [fig15ZeroRestore,nonzeroInputRestore,hpFree_append]
  exact ⟨by simp [HPFree],computeEqConst_HPFree _ _ _ _⟩
private theorem basis_lift_ket (f : BasisState → BasisState) (s : BasisState) :
    (Finsupp.lmapDomain ℂ ℂ f) (ket s)=ket (f s) := by simp [ket]

attribute [local irreducible] fig15ZeroPrepare fig15ZeroRestore
  secp256k1InPlaceDivision secp256k1InPlaceMultiplication
  fig15DivisionOutputState fig15MultiplicationOutputState

private theorem coherent_prepare_restore
    (pre post : Circuit) (program : AdaptiveCircuit)
    (prepare ideal restore : BasisState → BasisState) (Valid Ready : BasisState → Prop)
    (hpre : ∀ s, Valid s → Quantum.run pre (ket s)=ket (prepare s))
    (hpost : ∀ s, Quantum.run post (ket s)=ket (restore s))
    (hready : ∀ s, Valid s → Ready (prepare s))
    (h : CoherentlyImplementsOn program (Finsupp.lmapDomain ℂ ℂ ideal) Ready) :
    CoherentlyImplementsOn
      (((AdaptiveCircuit.unitary pre .done).seq program).seq (.unitary post .done))
      (Finsupp.lmapDomain ℂ ℂ (fun s => restore (ideal (prepare s)))) Valid := by
  have first := (CoherentlyImplementsOn.unitary pre Valid).seq h (by
    intro s hs
    rw [hpre s hs]
    exact supportedOn_ket _ _ (hready s hs))
  have all := first.seq (CoherentlyImplementsOn.unitary post (fun _ => True)) (by
    intro s hs w hw
    trivial)
  apply all.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,hpre s hs,basis_lift_ket,hpost]

private theorem zeroAllowed_coherent (program : AdaptiveCircuit) (ideal : BasisState → BasisState)
    (h : CoherentlyImplementsOn program (Finsupp.lmapDomain ℂ ℂ ideal) Secp256k1InPlaceInputValid) :
    CoherentlyImplementsOn
      (((AdaptiveCircuit.unitary fig15ZeroPrepare .done).seq program).seq (.unitary fig15ZeroRestore .done))
      (Finsupp.lmapDomain ℂ ℂ (fun s => Classical.run fig15ZeroRestore (ideal (fig15ZeroPrepareState s))))
      Secp256k1ZeroAllowedInputValid := by
  apply coherent_prepare_restore _ _ _ _ _ _ _ _ ?_ ?_ fig15ZeroPrepareState_ready h
  · intro s hs
    rw [Quantum.run_ket_agrees_classical _ _ zeroPrepare_HPFree,fig15ZeroPrepare_run s hs]
  · intro s
    exact Quantum.run_ket_agrees_classical _ _ zeroRestore_HPFree

/-- Normalized coherent division on every canonical X, using X=1 when the original X is zero. -/
theorem secp256k1ZeroAllowedDivision_coherent :
    CoherentlyImplementsOn secp256k1ZeroAllowedDivision
      (Finsupp.lmapDomain ℂ ℂ zeroAllowedDivisionOutputState) Secp256k1ZeroAllowedInputValid :=
  zeroAllowed_coherent _ _ secp256k1InPlaceDivision_coherent

/-- Normalized coherent multiplication on every canonical X, using X=1 when the original X is zero. -/
theorem secp256k1ZeroAllowedMultiplication_coherent :
    CoherentlyImplementsOn secp256k1ZeroAllowedMultiplication
      (Finsupp.lmapDomain ℂ ℂ zeroAllowedMultiplicationOutputState) Secp256k1ZeroAllowedInputValid :=
  zeroAllowed_coherent _ _ secp256k1InPlaceMultiplication_coherent
end ShorECDLP.Paper2607_13816
