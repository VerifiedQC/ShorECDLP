import ShorECDLP.Submission.«2607_13816».Window.ReducedScalar
import ShorECDLP.Submission.«2607_13816».Window.PhasePrepare
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
theorem scalarRootFlip_register (n j : Nat) (s : BasisState) :
    scalarRegisterValue n j (scalarRootFlip s)=scalarRegisterValue n j s := by
  unfold scalarRegisterValue
  rw [scalarRootFlip_word]
  intro w hw
  simp only [List.mem_range'_1,windowBankStart] at hw
  dsimp only [Wire] at *
  omega
private theorem reducedRootWrap_coherent (body : AdaptiveCircuit) (P Q : Point)
    (hb : CoherentlyImplementsOn body
      (Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) PointInitializeValid) :
    CoherentlyImplementsOn
      (((AdaptiveCircuit.unitary [.X 836] .done).seq body).seq (.unitary [.X 836] .done))
      (Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) ScalarComputeValid := by
  have h1 := (scalarRootFlip_coherent ScalarComputeValid).seq
    hb (by
      intro s hs
      simpa [ket] using supportedOn_ket _ _ (scalarRootFlip_ready s hs).1)
  have h2 := h1.seq (scalarRootFlip_coherent (fun _ => True)) (by
    intro s hs
    simp only [LinearMap.comp_apply,ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    exact supportedOn_ket _ _ trivial)
  apply h2.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  change Finsupp.single (scalarRootFlip (reducedScalarOutput P Q (scalarRootFlip s))) 1 =
    Finsupp.single (reducedScalarOutput P Q s) 1
  simp only [reducedScalarOutput,scalarRootFlip_register,scalarRootFlip_pointWrite,scalarRootFlip_twice]

def reducedPhaseWires : List Wire := List.range' 855 256++List.range' 1127 208
def reducedPhasePrepare : Circuit := reducedPhaseWires.map Gate.H
private theorem phase_subset : reducedPhaseWires ⊆ scalarPhaseWires := by
  intro w hw
  simp only [reducedPhaseWires,scalarPhaseWires,List.mem_append,List.mem_range'_1] at hw ⊢
  omega
private theorem reducedPhaseWires_nodup : reducedPhaseWires.Nodup := by decide +kernel
theorem reducedPhasePrepare_supported (s : BasisState) (hs : ScalarComputeValid s)
    (hz : Clean reducedPhaseWires s) :
    SupportedOn ScalarComputeValid (Quantum.run reducedPhasePrepare (ket s)) := by
  exact hadamardInputs_supported ScalarComputeValid reducedPhaseWires reducedPhaseWires_nodup
    (fun w hw => scalarPhase_update_ready w (phase_subset hw)) s hs hz

def reducedScalarComputeProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary [.X 836] .done).seq
    (reducedScalarProgram P Q hP hQ hrP hrQ)).seq (.unitary [.X 836] .done)
theorem reducedScalarCompute_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (reducedScalarComputeProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) ScalarComputeValid :=
  reducedRootWrap_coherent _ P Q (reducedScalar_registers_coherent P Q hP hQ hrP hrQ)
def ReducedPhaseInitial (s : BasisState) : Prop := ScalarComputeValid s ∧ Clean reducedPhaseWires s
def reducedPreparedScalarProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary reducedPhasePrepare .done).seq (reducedScalarComputeProgram P Q hP hQ hrP hrQ)
theorem reducedPreparedScalar_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (reducedPreparedScalarProgram P Q hP hQ hrP hrQ)
      ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)).comp (Quantum.run reducedPhasePrepare))
      ReducedPhaseInitial :=
  (CoherentlyImplementsOn.unitary reducedPhasePrepare ReducedPhaseInitial).seq
    (reducedScalarCompute_coherent P Q hP hQ hrP hrQ) (fun s hs => reducedPhasePrepare_supported s hs.1 hs.2)

theorem reducedPhasePrepare_length : reducedPhasePrepare.length=464 := by
  simp [reducedPhasePrepare,reducedPhaseWires]

theorem reducedPhasePrepare_support : circuitWires reducedPhasePrepare ⊆ reducedPhaseWires := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  exact hw ▸ hv

theorem reducedPreparedScalar_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (reducedPreparedScalarProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++reducedPhaseWires := by
  intro w hw
  rw [reducedPreparedScalarProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · exact List.mem_append_right _ (reducedPhasePrepare_support (by simpa [AdaptiveCircuit.wires] using hw))
  · rw [reducedScalarComputeProgram,modularWires_seq,modularWires_seq] at hw
    rcases hw with (hw | hw) | hw
    · simp [AdaptiveCircuit.wires,circuitWires,gateWires] at hw
      subst w
      exact List.mem_append_left _ (by decide +kernel)
    · exact reducedScalar_support P Q hP hQ hrP hrQ hw
    · simp [AdaptiveCircuit.wires,circuitWires,gateWires] at hw
      subst w
      exact List.mem_append_left _ (by decide +kernel)

end
end ShorECDLP.Paper2607_13816
