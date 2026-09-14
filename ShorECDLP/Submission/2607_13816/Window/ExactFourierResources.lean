import ShorECDLP.Submission.«2607_13816».Window.FourierResources
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem history_exact (dir : PhaseDir) (w : Wire) (bs : List Bool) (k : Nat) :
    tCount (fourierHistoryRotations dir w bs k)=bs.count true := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih =>
    unfold tCount at ih
    cases b <;> simp [fourierHistoryRotations,fourierFeedForward,tCount,tCost,ih,Nat.add_comm]
private def phaseCount : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, k => k+phaseCount n (k+1)
private theorem phase_mono (n : Nat) {k l : Nat} (h : k≤l) : phaseCount n k≤phaseCount n l := by
  induction n generalizing k l with
  | zero => exact le_rfl
  | succ n ih => exact Nat.add_le_add h (ih (by omega))
private theorem fourier_exact (dir : PhaseDir) (ws : List Wire) (prior : List Bool) :
    (semiclassicalFourier dir ws prior).tCount=phaseCount ws.length (prior.count true) := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih =>
    simp only [semiclassicalFourier,AdaptiveCircuit.tCount,history_exact,ih,List.length_cons,phaseCount]
    simp only [List.count_cons,show (false == true)=false from rfl,show (true == true)=true from rfl,
      Bool.false_eq_true,ite_false,ite_true,Nat.add_zero]
    rw [max_eq_right (phase_mono ws.length (by omega))]


theorem scalarFourierProgram_tCount_exact : scalarFourierProgram.tCount=65792 := by
  have h := modularGateCount_seq tCost
    (semiclassicalFourier .inverse scalarFourierLeft List.nil)
    (semiclassicalFourier .inverse scalarFourierRight List.nil)
  simp only [gidneyGateCount_tCount,fourier_exact,scalarFourierLeft,scalarFourierRight,
    List.length_reverse,List.length_range',List.count_nil] at h
  have hv : phaseCount 257 0=32896 := by decide +kernel
  rw [hv] at h
  exact h
private theorem exact_vector (r : PrimitiveResources)
    (h : r.x=0 ∧ r.h=0 ∧ r.cnot=0 ∧ r.toffoli=0 ∧ r.phase≤65792 ∧ r.measurements=514)
    (hp : 65792≤7*r.toffoli+r.phase) : r=⟨0,0,0,0,65792,514⟩ := by
  cases r
  simp_all only
  congr
  omega
/-- Exact worst-case primitive vector of both physical Fourier measurements. -/
theorem scalarFourierProgram_primitive_exact :
    primitiveResources scalarFourierProgram=⟨0,0,0,0,65792,514⟩ := by
  have h := primitiveResources_T_le scalarFourierProgram
  rw [scalarFourierProgram_tCount_exact] at h
  exact exact_vector _ scalarFourierProgram_resources h
end ShorECDLP.Paper2607_13816
