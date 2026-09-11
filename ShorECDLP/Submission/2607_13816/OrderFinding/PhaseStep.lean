import ShorECDLP.Submission.«2607_13816».OrderFinding.PointEigenstates
import ShorECDLP.Submission.«2607_13816».Fourier.FeedForward
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Classical Quantum
open scoped BigOperators
noncomputable section
private theorem control_not_point : 836∉pointLogicalWires := by decide +kernel
private theorem control_upd_twice (s : BasisState) (a b : Bool) :
    s[836 ↦ a][836 ↦ b]=s[836 ↦ b] := by
  funext w
  by_cases h : w=836 <;> simp [upd,h]
theorem pointWrite_control (P : Secp256k1.Point) (s : BasisState) (b : Bool) :
    (pointWrite P s)[836 ↦ b]=pointWrite P (s[836 ↦ b]) := by
  funext w
  by_cases h : w=836
  · subst w; simp [upd,pointWrite,control_not_point]
  · by_cases hp : w∈pointLogicalWires <;> simp [upd,pointWrite,h,hp]
theorem pointControl_valid (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (b : Bool) :
    Secp256k1ZeroAllowedInputValid (s[836 ↦ b]) := by
  refine ⟨?_,by simpa [upd] using hs.2.1,?_,?_⟩
  · intro w hw
    have hn : w≠836 := by
      intro h; subst w; norm_num at hw
    simpa [upd,hn] using hs.1 w hw
  · have he : wireValues (List.range' 263 256) (s[836 ↦ b])=wireValues (List.range' 263 256) s := by
      apply List.map_congr_left
      intro w hw
      have hn : w≠836 := by intro h; subst w; norm_num at hw
      simp [upd,hn]
    rw [he]; exact hs.2.2.1
  · have he : wireValues (List.range' 580 256) (s[836 ↦ b])=wireValues (List.range' 580 256) s := by
      apply List.map_congr_left
      intro w hw
      have hn : w≠836 := by intro h; subst w; norm_num at hw
      simp [upd,hn]
    rw [he]; exact hs.2.2.2

theorem pointCyclicState_hadamard {r : Nat} (P : Secp256k1.Point) (s : BasisState) (k : Fin r) :
    Quantum.run [.H 836] (pointCyclicState P (s[836 ↦ false]) k)=
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) • (pointCyclicState P (s[836 ↦ false]) k + pointCyclicState P (s[836 ↦ true]) k) := by
  unfold pointCyclicState cyclicState
  rw [map_smul,map_sum]
  simp only [map_smul,pointCyclicBasis,Quantum.run_cons,Quantum.run_nil,applyGate_H_ket,
    pointWrite_frame _ _ 836 control_not_point,upd_same,Bool.false_eq_true,if_false,mul_one,
    pointWrite_control,control_upd_twice]
  simp only [smul_add,Finset.sum_add_distrib]
  simp_rw [smul_comm _ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ))]
  simp only [← Finset.smul_sum]
  module

theorem pointCyclicState_rotations {r : Nat} (P : Secp256k1.Point) (s : BasisState) (k : Fin r)
    (dir : PhaseDir) (prior : List Bool) (b : Bool) :
    Quantum.run (fourierHistoryRotations dir 836 prior 2) (pointCyclicState P (s[836 ↦ b]) k)=
      (if b then Complex.exp (Complex.I*(fourierHistoryAngle dir prior 2:ℂ)) else 1) •
        pointCyclicState P (s[836 ↦ b]) k := by
  unfold pointCyclicState cyclicState
  rw [map_smul,map_sum]
  simp only [map_smul,pointCyclicBasis,fourierHistoryRotations_ket,
    pointWrite_frame _ _ 836 control_not_point,upd_same]
  rw [smul_comm]
  congr 1
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

theorem pointCyclicState_reset {r : Nat} (P : Secp256k1.Point) (s : BasisState) (k : Fin r) (b out : Bool) :
    xResetKraus 836 out (pointCyclicState P (s[836 ↦ b]) k)=
      xResetCoeff out b • pointCyclicState P (s[836 ↦ false]) k := by
  unfold pointCyclicState cyclicState
  rw [map_smul,map_sum]
  simp only [map_smul,pointCyclicBasis,xResetKraus_ket,
    pointWrite_frame _ _ 836 control_not_point,upd_same,pointWrite_control,control_upd_twice]
  rw [smul_comm]
  congr 1
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _
def pointPhaseStepCoeff (r k t : Nat) (prior : List Bool) (out : Bool) : ℂ :=
  (((Real.sqrt 2)⁻¹:ℝ):ℂ) * (xResetCoeff out false +
    ShorECDLP.Quantum.PhaseEstimation.eigenvalue (((k*t:Nat):ℝ)/(r:ℝ)) *
      Complex.exp (Complex.I*(fourierHistoryAngle .inverse prior 2:ℂ)) * xResetCoeff out true)
def pointPhaseIdeal (C : Secp256k1.Point) (prior : List Bool) (out : Bool) : State →ₗ[ℂ] State :=
  (xResetKraus 836 out).comp ((Quantum.run (fourierHistoryRotations .inverse 836 prior 2)).comp
    ((Finsupp.lmapDomain ℂ ℂ (pointAddState C)).comp (Quantum.run [.H 836])))
theorem pointPhaseIdeal_eigenstate {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (t : Nat) (k : Fin r) (prior : List Bool) (out : Bool) :
    pointPhaseIdeal (t • P) prior out (pointCyclicState P (s[836 ↦ false]) k)=
      pointPhaseStepCoeff r k.val t prior out • pointCyclicState P (s[836 ↦ false]) k := by
  unfold pointPhaseIdeal
  simp only [LinearMap.comp_apply]
  rw [pointCyclicState_hadamard,map_smul,map_add,
    pointCyclicState_disabled P (t • P) _ (pointControl_valid s hs false) (upd_same s 836 false) k,
    pointCyclicState_shift hr P horder _ (pointControl_valid s hs true) (upd_same s 836 true) t k]
  simp only [map_smul,map_add,pointCyclicState_rotations,pointCyclicState_reset,
    Bool.false_eq_true,if_false,if_true,one_smul]
  unfold pointPhaseStepCoeff
  module
private theorem pointPrepared_supported {r : Nat} (P : Secp256k1.Point) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (k : Fin r) :
    SupportedOn Secp256k1ZeroAllowedInputValid
      (Quantum.run [.H 836] (pointCyclicState P (s[836 ↦ false]) k)) := by
  rw [pointCyclicState_hadamard]
  intro u hu
  by_contra hn
  have hf : pointCyclicState P (s[836 ↦ false]) k u=0 := by
    by_contra h
    exact hn (pointCyclicState_supported P _ (pointControl_valid s hs false) k u h)
  have ht : pointCyclicState P (s[836 ↦ true]) k u=0 := by
    by_contra h
    exact hn (pointCyclicState_supported P _ (pointControl_valid s hs true) k u h)
  apply hu
  simp [hf,ht]
def pointPhaseBranch (prior : List Bool) (out : Bool) (branch : InstrumentBranch) : InstrumentBranch where
  history := branch.history ++ [out]
  kraus := (xResetKraus 836 out).comp ((Quantum.run (fourierHistoryRotations .inverse 836 prior 2)).comp
    (branch.kraus.comp (Quantum.run [.H 836])))
def pointPhaseStep (C : Secp256k1.Point) (prior : List Bool) : AdaptiveCircuit :=
  .unitary [.H 836] ((pointAddProgram C).seq
    (.unitary (fourierHistoryRotations .inverse 836 prior 2) (.xMeasureReset 836 .done .done)))
theorem pointPhaseStep_run (C : Secp256k1.Point) (prior : List Bool) :
    (pointPhaseStep C prior).run=(pointAddProgram C).run.flatMap
      (fun branch => [pointPhaseBranch prior false branch,pointPhaseBranch prior true branch]) := by
  simp only [pointPhaseStep,AdaptiveCircuit.run,AdaptiveCircuit.run_seq,
    Instrument.seq,List.map_flatMap,List.map_append,List.map_cons,List.map_nil]
  rfl
theorem pointPhaseBranch_eigenstate {r : Nat} (hr : Nat.Prime r) (P : Secp256k1.Point)
    (horder : addOrderOf P=r) (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (t : Nat) (prior : List Bool) :
    ∃ cs : List ℂ, List.Forall₂
      (fun branch c => ∀ (k : Fin r) out, (pointPhaseBranch prior out branch).kraus (pointCyclicState P (s[836 ↦ false]) k)=
        (c * pointPhaseStepCoeff r k.val t prior out) • pointCyclicState P (s[836 ↦ false]) k)
      (pointAddProgram (t • P)).run cs ∧ (cs.map Complex.normSq).sum=1 := by
  obtain ⟨cs,hcs,hm⟩ := pointAddProgram_coherent (t • P)
  refine ⟨cs,?_,hm⟩
  apply hcs.imp
  intro branch c hbranch k out
  have hc := hbranch.on_supported (pointPrepared_supported P s hs k)
  simp only [pointPhaseBranch,LinearMap.comp_apply]
  rw [hc,map_smul,map_smul]
  change c • pointPhaseIdeal (t • P) prior out (pointCyclicState P (s[836 ↦ false]) k)=_
  rw [pointPhaseIdeal_eigenstate hr P horder s hs t k prior out,smul_smul]

end
end ShorECDLP.Paper2607_13816
