import ShorECDLP.Submission.«2607_13816».Window.PreparedOrder
import ShorECDLP.Submission.«2607_13816».Window.FirstWindowReplacement
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
def firstPreparedState (A P : Point) (hP : P≠0) (hr : order • P=0) (s : BasisState) :=
  preparedWindowCallState (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
    (fun k => oddWindowTable_valid P hP hr (k-0)) 0 (pointWrite A s)
theorem firstPreparedState_ready (A P : Point) (hP : P≠0) (hr : order • P=0)
    (s : BasisState) (hs : PointInitializeValid s) :
    WindowPointValid (firstPreparedState A P hP hr s) :=
  preparedWindowCallState_ready _ _ _ _ _ (pointInitialize_ready A s hs)
theorem directOrderedTail_coherent (A P : Point) (hP : P≠0) (hr : order • P=0)
    (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a,curve.toAffine.Nonsingular (x j a) (y j a)) (js : List Nat) :
    CoherentlyImplementsOn
      ((physicalPointLookup (firstWindowTable A P)).seq
        (preparedWindowListProgram x y hc js.reverse))
      (Finsupp.lmapDomain ℂ ℂ (fun s =>
        preparedWindowListState x y hc js (firstPreparedState A P hP hr s)))
      PointInitializeValid := by
  have h := (firstWindowLookup_coherent A P hP hr).seq
    (preparedWindowList_reverse_coherent x y hc js) (by
      intro s hs
      simpa [ket,firstPreparedState] using
        supportedOn_ket _ _ (firstPreparedState_ready A P hP hr s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket,firstPreparedState]
end
end ShorECDLP.Paper2607_13816
