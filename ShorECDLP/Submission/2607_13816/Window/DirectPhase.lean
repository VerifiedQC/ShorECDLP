import ShorECDLP.Submission.«2607_13816».Window.DirectScalar
import ShorECDLP.Submission.«2607_13816».Window.PhasePrepare
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
theorem directScalar_registers_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (directScalarProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)) ScalarRegistersValid := by
  obtain ⟨cs,ha,hm⟩ := directScalar_coherent P Q hP hQ hrP hrQ
  have h : CoherentlyImplementsOn (directScalarProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (initializedScalarState P Q hP hQ hrP hrQ)) ScalarRegistersValid :=
    ⟨cs,ha.imp (fun b c h s hs => h s hs.1),hm⟩
  apply h.congrIdeal
  intro s hs
  simp only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  rw [initializedScalarState_registers P Q hP hQ hrP hrQ s hs.1 hs.2.1 hs.2.2]
  rfl

def directScalarComputeProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary [.X 836] .done).seq
    (directScalarProgram P Q hP hQ hrP hrQ)).seq (.unitary [.X 836] .done)

theorem directScalarCompute_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (directScalarComputeProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)) ScalarComputeValid :=
  scalarRootWrap_coherent _ P Q (directScalar_registers_coherent P Q hP hQ hrP hrQ)

def directPreparedScalarProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary scalarPhasePrepare .done).seq (directScalarComputeProgram P Q hP hQ hrP hrQ)

theorem directPreparedScalar_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (directPreparedScalarProgram P Q hP hQ hrP hrQ)
      ((Finsupp.lmapDomain ℂ ℂ (scalarRegisterOutput P Q)).comp (Quantum.run scalarPhasePrepare))
      ScalarPhaseInitial :=
  (CoherentlyImplementsOn.unitary scalarPhasePrepare ScalarPhaseInitial).seq
    (directScalarCompute_coherent P Q hP hQ hrP hrQ) (fun s hs => scalarPhasePrepare_supported s hs.1 hs.2)

theorem directScalarCompute_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directScalarComputeProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++List.range' 855 544 :=
  scalarRootWrap_support _ (directScalar_support P Q hP hQ hrP hrQ)

theorem directScalarCompute_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directScalarComputeProgram P Q hP hQ hrP hrQ).qubitCount≤1383 := by
  have hs : (directScalarComputeProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 544).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (directScalarCompute_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

theorem directPreparedScalar_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directPreparedScalarProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++List.range' 855 544 := by
  intro w hw
  rw [directPreparedScalarProgram,modularWires_seq] at hw
  rcases hw with hw | hw
  · simp only [AdaptiveCircuit.wires,List.append_nil] at hw
    have h := scalarPhasePrepare_support hw
    apply List.mem_append_right
    simp only [scalarPhaseWires,List.mem_append,List.mem_range'_1] at h
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *; omega
  · exact directScalarCompute_support P Q hP hQ hrP hrQ hw

theorem directPreparedScalar_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directPreparedScalarProgram P Q hP hQ hrP hrQ).qubitCount≤1383 := by
  have hs : (directPreparedScalarProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 544).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (directPreparedScalar_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

theorem directPreparedScalar_tCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directPreparedScalarProgram P Q hP hQ hrP hrQ).tCount+
      (preparedWindowCall (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
        (fun k => oddWindowTable_valid P hP hrP (k-0)) 0).tCount=
      (preparedScalarProgram P Q hP hQ hrP hrQ).tCount+458745 := by
  rw [directPreparedScalarProgram,scalarPhasePrefix_tCount,directScalarComputeProgram,scalarRootWrap_tCount,
    directScalar_tCount,initializedScalar_tCount,preparedScalar_tCount]

theorem directPreparedScalar_measurementCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directPreparedScalarProgram P Q hP hQ hrP hrQ).measurementCount+
      (preparedWindowCall (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
        (fun k => oddWindowTable_valid P hP hrP (k-0)) 0).measurementCount=
      (preparedScalarProgram P Q hP hQ hrP hrQ).measurementCount+65535 := by
  rw [directPreparedScalarProgram,scalarPhasePrefix_measurementCount,directScalarComputeProgram,scalarRootWrap_measurementCount,
    directScalar_measurementCount,initializedScalar_measurementCount,preparedScalar_measurementCount]
end
end ShorECDLP.Paper2607_13816
