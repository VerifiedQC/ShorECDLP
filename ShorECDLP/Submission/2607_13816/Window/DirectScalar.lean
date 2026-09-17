import ShorECDLP.Submission.«2607_13816».Window.FirstWindowReplacement
/-!
The first of 34 signed-window additions is replaced by a direct point lookup.
The resulting circuit has the same complete-state semantics and uses the same
wire allocation. Counts below compare actual adaptive circuits; they retain
all 257 phase bits on each axis and do not claim the paper's 28-addition bound.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq physicalPointLookup preparedWindowCall preparedWindowSchedule axisWindowProgram

def directScalarProgram (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : AdaptiveCircuit :=
  ((physicalPointLookup (firstWindowTable (axisWindowOffset P 17+axisWindowOffset Q 17) P)).seq
    (preparedWindowSchedule (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
      (fun k => oddWindowTable_valid P hP hrP (k-0)) 16 1)).seq
    (axisWindowProgram Q hQ hrQ 17 17)

private theorem compose_maps {a b : AdaptiveCircuit} {f g : BasisState → BasisState}
    {V W : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) V)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) W)
    (hr : ∀ s, V s → W (f s)) :
    CoherentlyImplementsOn (a.seq b) (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) V := by
  apply (ha.seq hb (by intro s hs; simpa [ket] using supportedOn_ket W (f s) (hr s hs))).congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket]

theorem directSchedule_coherent (A P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (n start m : Nat) :
    CoherentlyImplementsOn
      (((physicalPointLookup (firstWindowTable A P)).seq
        (preparedWindowSchedule (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
          (fun k => oddWindowTable_valid P hP hrP (k-0)) n 1)).seq
        (axisWindowProgram Q hQ hrQ start m))
      (Finsupp.lmapDomain ℂ ℂ (fun s => axisWindowState Q hQ hrQ start m
        (preparedWindowScheduleState (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
          (fun k => oddWindowTable_valid P hP hrP (k-0)) n 1
          (preparedWindowCallState (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
            (fun k => oddWindowTable_valid P hP hrP (k-0)) 0 (pointWrite A s)))))
      PointInitializeValid := by
  let x := fun k => oddWindowX P (k-0)
  let y := fun k => oddWindowY P (k-0)
  let hv := fun k => oddWindowTable_valid P hP hrP (k-0)
  have hc := compose_maps (firstWindowLookup_coherent A P hP hrP)
    (preparedWindowSchedule_coherent x y hv n 1) (by
      intro s hs
      exact preparedWindowCallState_ready x y hv 0 (pointWrite A s) (pointInitialize_ready A s hs))
  have hall := compose_maps hc (axisWindow_coherent Q hQ hrQ start m) (by
    intro s hs
    exact preparedWindowScheduleState_ready x y hv n 1 _
      (preparedWindowCallState_ready x y hv 0 (pointWrite A s) (pointInitialize_ready A s hs)))
  exact hall

theorem axisWindowState_split (P : Point) (hP : P≠0) (hr : order • P=0)
    (n : Nat) (s : BasisState) :
    axisWindowState P hP hr 0 (n+1) s=
      preparedWindowScheduleState (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
        (fun k => oddWindowTable_valid P hP hr (k-0)) n 1
        (preparedWindowCallState (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
          (fun k => oddWindowTable_valid P hP hr (k-0)) 0 s) := by
  exact preparedWindowScheduleState.eq_2 _ _ _ 0 s n

theorem directScalar_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (directScalarProgram P Q hP hQ hrP hrQ)
      (Finsupp.lmapDomain ℂ ℂ (initializedScalarState P Q hP hQ hrP hrQ))
      PointInitializeValid := by
  have h := directSchedule_coherent (axisWindowOffset P 17+axisWindowOffset Q 17)
    P Q hP hQ hrP hrQ 16 17 17
  apply h.congrIdeal
  intro s hs
  have he := axisWindowState_split P hP hrP 16
    (pointWrite (axisWindowOffset P 17+axisWindowOffset Q 17) s)
  have he' := congrArg (axisWindowState Q hQ hrQ 17 17) he
  simpa only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
    initializedScalarState,scalarWindowsState] using congrArg ket he'.symm

theorem directScalar_support (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directScalarProgram P Q hP hQ hrP hrQ).wires ⊆ List.range 839++List.range' 855 544 := by
  intro w hw
  rw [directScalarProgram,modularWires_seq,modularWires_seq] at hw
  rcases hw with (hw | hw) | hw
  · rw [physicalPointLookup] at hw
    have h := directPointLookup_support
      (firstWindowTable (axisWindowOffset P 17+axisWindowOffset Q 17) P)
      (List.range' 855 16) (List.range' 519 16) 836 hw
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at h
    simp only [List.mem_append,List.mem_range,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · have h := preparedWindowSchedule_support (fun k => oddWindowX P (k-0))
      (fun k => oddWindowY P (k-0)) (fun k => oddWindowTable_valid P hP hrP (k-0)) 16 1 hw
    simp only [List.mem_append,List.mem_range,List.mem_range'_1] at h ⊢
    dsimp only [Wire] at *
    omega
  · rw [axisWindowProgram] at hw
    exact preparedWindowSchedule_support _ _ _ 17 17 hw

theorem directScalar_qubitCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directScalarProgram P Q hP hQ hrP hrQ).qubitCount≤1383 := by
  have hs : (directScalarProgram P Q hP hQ hrP hrQ).wires.dedup.toFinset ⊆
      (List.range 839++List.range' 855 544).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (directScalar_support P Q hP hQ hrP hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_range,List.length_range'] using hc

private theorem seq_T (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b

theorem directScalar_tCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directScalarProgram P Q hP hQ hrP hrQ).tCount+
      (preparedWindowCall (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
        (fun k => oddWindowTable_valid P hP hrP (k-0)) 0).tCount=
      (initializedScalarProgram P Q hP hQ hrP hrQ).tCount+458745 := by
  rw [initializedScalar_tCount,scalarWindowsProgram,seq_T]
  rw [axisWindowProgram, preparedWindowSchedule.eq_2]
  rw [seq_T,directScalarProgram,seq_T,seq_T,
    (physicalPointLookup_resources (firstWindowTable (axisWindowOffset P 17+axisWindowOffset Q 17) P)).1]
  simp only [Nat.zero_add] at *
  omega

theorem directScalar_measurementCount (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    (directScalarProgram P Q hP hQ hrP hrQ).measurementCount+
      (preparedWindowCall (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
        (fun k => oddWindowTable_valid P hP hrP (k-0)) 0).measurementCount=
      (initializedScalarProgram P Q hP hQ hrP hrQ).measurementCount+65535 := by
  rw [initializedScalar_measurementCount,scalarWindowsProgram,modularMeasurements_seq]
  rw [axisWindowProgram, preparedWindowSchedule.eq_2]
  rw [modularMeasurements_seq,directScalarProgram,modularMeasurements_seq,modularMeasurements_seq,
    (physicalPointLookup_resources (firstWindowTable (axisWindowOffset P 17+axisWindowOffset Q 17) P)).2.1]
  simp only [Nat.zero_add] at *
  omega
end
end ShorECDLP.Paper2607_13816
