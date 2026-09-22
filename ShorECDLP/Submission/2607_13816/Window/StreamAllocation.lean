import ShorECDLP.Submission.«2607_13816».Fourier.Continuation
import ShorECDLP.Submission.«2607_13816».Window.ReducedPrimitives
namespace ShorECDLP.Paper2607_13816
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq preparedWindowCall physicalPointLookup
/-- One reusable 16-bit address bank, disjoint from the full point-add core. -/
def streamAddress : List Wire := List.range' 855 16
def streamAllocation : List Wire := List.range 839++streamAddress
/-- Prepare, execute, Fourier-measure and reset the same address bank at every window.
The classical Fourier history persists through the axis, then the supplied tail begins. -/
def streamAxis : List AdaptiveCircuit → List Bool → AdaptiveCircuit → AdaptiveCircuit
  | List.nil, _, tail => tail
  | call::calls, prior, tail => (AdaptiveCircuit.unitary (streamAddress.map Gate.H) .done).seq
      (call.seq (fourierContinue .inverse streamAddress.reverse prior
        (fun history => streamAxis calls history tail)))
private theorem hadamards_support (ws : List Wire) : circuitWires (ws.map Gate.H) ⊆ ws := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  exact hw ▸ hv

theorem streamAxis_support (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit)
    (hc : ∀ c∈calls,c.wires ⊆ streamAllocation) (ht : tail.wires ⊆ streamAllocation) :
    (streamAxis calls prior tail).wires ⊆ streamAllocation := by
  induction calls generalizing prior with
  | nil => exact ht
  | cons c cs ih =>
    intro w hw
    rw [streamAxis,modularWires_seq,modularWires_seq] at hw
    rcases hw with hw | hw | hw
    · exact List.mem_append_right _ (hadamards_support streamAddress
        (by simpa [AdaptiveCircuit.wires] using hw))
    · exact hc c (by simp) hw
    · exact fourierContinue_support .inverse streamAddress.reverse prior _ streamAllocation
        (by intro v hv; exact List.mem_append_right _ (List.mem_reverse.mp hv))
        (fun history => ih history (by intro a ha; exact hc a (by simp [ha]))) hw

theorem streamAxis_measurements (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit) :
    (streamAxis calls prior tail).measurementCount=
      (calls.map AdaptiveCircuit.measurementCount).sum+16*calls.length+tail.measurementCount := by
  induction calls generalizing prior with
  | nil => simp [streamAxis]
  | cons c cs ih =>
    rw [streamAxis,modularMeasurements_seq,modularMeasurements_seq,
      fourierContinue_measurements _ _ _ _ _ ih]
    simp only [AdaptiveCircuit.measurementCount,List.map_cons,List.sum_cons,List.length_cons,
      List.length_reverse,streamAddress,List.length_range']
    omega
/-- The table changes with the window weight; its physical address remains bank zero. -/
def streamPointCall (P : Point) (hP : P≠0) (hrP : order • P=0) (j : Nat) : AdaptiveCircuit :=
  preparedWindowCall (fun _ => oddWindowX P j) (fun _ => oddWindowY P j)
    (fun _ => oddWindowTable_valid P hP hrP j) 0

theorem streamPointCall_support (P : Point) (hP : P≠0) (hrP : order • P=0) (j : Nat) :
    (streamPointCall P hP hrP j).wires ⊆ streamAllocation := by
  exact preparedWindowCall_support _ _ _ 0

/-- Proposed MSB-first left axis: one direct load and fifteen total point additions. -/
def streamLeftCalls (P Q : Point) (hP : P≠0) (hrP : order • P=0) : List AdaptiveCircuit :=
  physicalPointLookup (firstWindowTable (axisWindowOffset P 16+axisWindowOffset Q 13)
    ((2^(16*15)) • P)) :: (List.range 15).reverse.map (streamPointCall P hP hrP)
def streamRightCalls (Q : Point) (hQ : Q≠0) (hrQ : order • Q=0) : List AdaptiveCircuit :=
  (List.range 13).reverse.map (streamPointCall Q hQ hrQ)
/-- Allocation candidate only: full sampling equivalence is a separate obligation. -/
def streamScalarTrial (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary [.X 836] .done).seq
    (streamAxis (streamLeftCalls P Q hP hrP) List.nil
      (streamAxis (streamRightCalls Q hQ hrQ) List.nil (AdaptiveCircuit.unitary [.X 836] .done)))

theorem streamPointLookup_support (table : Nat → Point) : (physicalPointLookup table).wires ⊆ streamAllocation := by
  intro w hw
  rw [physicalPointLookup] at hw
  have h := directPointLookup_support table (List.range' 855 16) (List.range' 519 16) 836 hw
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at h
  simp only [streamAllocation,streamAddress,List.mem_append,List.mem_range,List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem streamScalarTrial_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (streamScalarTrial P Q hP hQ hrP hrQ).wires ⊆ streamAllocation := by
  have hx : (AdaptiveCircuit.unitary [.X 836] .done).wires ⊆ streamAllocation := by
    intro w hw
    simp [AdaptiveCircuit.wires,circuitWires,gateWires] at hw
    subst w
    exact List.mem_append_left _ (List.mem_range.mpr (by decide))
  intro w hw
  rw [streamScalarTrial,modularWires_seq] at hw
  rcases hw with hw | hw
  · exact hx hw
  · apply streamAxis_support _ List.nil _ ?_ ?_ hw
    · intro c hc
      simp only [streamLeftCalls,List.mem_cons,List.mem_map] at hc
      rcases hc with rfl | ⟨j,hj,rfl⟩
      · exact streamPointLookup_support _
      · exact streamPointCall_support _ _ _ _
    · apply streamAxis_support _ List.nil _ ?_ hx
      intro c hc
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
      exact streamPointCall_support _ _ _ _

theorem streamScalarTrial_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (streamScalarTrial P Q hP hQ hrP hrQ).qubitCount≤855 := by
  have hs : (streamScalarTrial P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆ streamAllocation.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (streamScalarTrial_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,streamAllocation,streamAddress,List.length_append,
    List.length_range,List.length_range'] using hc

theorem streamLeftCalls_length (P Q : Point) (hP : P≠0) (hrP : order • P=0) :
    (streamLeftCalls P Q hP hrP).length=16 := by simp [streamLeftCalls]
theorem streamRightCalls_length (Q : Point) (hQ : Q≠0) (hrQ : order • Q=0) :
    (streamRightCalls Q hQ hrQ).length=13 := by simp [streamRightCalls]
/-- Each retained Fourier branch leaves every address wire clean, even on entangled input. -/
theorem streamFourier_clean (prior bs : List Bool) (ψ : State) :
    SupportedOn (Clean streamAddress)
      (fourierBranch .inverse streamAddress.reverse prior bs ψ) := by
  induction ψ using Finsupp.induction with
  | zero => simpa only [map_zero] using supportedOn_zero (Clean streamAddress)
  | @single_add s a ψ hs ha ih =>
    have he : Finsupp.single s a=a • ket s := by simp [ket]
    rw [map_add,he,map_smul,fourierBranch_ket]
    intro t ht w hw
    by_cases ht' : t=fourierClear streamAddress.reverse s
    · subst t
      simp [fourierClear_apply,List.mem_reverse,hw]
    · have hz : (a • (fourierBranchCoeff .inverse streamAddress.reverse prior bs s •
          ket (fourierClear streamAddress.reverse s))) t=0 := by
        simp [ket,ht']
      have hn : (fourierBranch .inverse streamAddress.reverse prior bs ψ) t≠0 := by
        simpa only [Finsupp.add_apply,hz,zero_add] using ht
      exact ih t hn w hw

/-- Arithmetic measurements plus all 256+208 Fourier outcomes; address reuse removes none. -/
theorem streamScalarTrial_measurements (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (streamScalarTrial P Q hP hQ hrP hrQ).measurementCount=
      ((streamLeftCalls P Q hP hrP).map AdaptiveCircuit.measurementCount).sum+
      ((streamRightCalls Q hQ hrQ).map AdaptiveCircuit.measurementCount).sum+464 := by
  rw [streamScalarTrial,modularMeasurements_seq,streamAxis_measurements,streamAxis_measurements,
    streamLeftCalls_length,streamRightCalls_length]
  simp only [AdaptiveCircuit.measurementCount]
  omega

end
end ShorECDLP.Paper2607_13816
