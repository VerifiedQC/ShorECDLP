import ShorECDLP.Submission.«2607_13816».Window.RawNormalization
import ShorECDLP.Framework.Quantum.Interference
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem sum_kets_supported (V : BasisState → Prop) (xs : List BasisState)
    (h : ∀ s ∈ xs, V s) : SupportedOn V (xs.map ket).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    intro s hs
    by_cases he : s=a
    · subst s; exact h a (by simp)
    · apply ih (fun u hu => h u (by simp [hu])) s
      simpa [ket, Finsupp.single_apply, he, Ne.symm he] using hs

/-- The entire physical entry is in the clean initialization subspace. -/
theorem reducedRawEntryState_supported : SupportedOn PointInitializeValid reducedRawEntryState := by
  rw [reducedRawEntryState_uniform]
  have hh : SupportedOn PointInitializeValid
      (phaseUniformSum reducedPhaseWires (scalarRootFlip zeroBasisState)) := by
    have hh := sum_kets_supported PointInitializeValid
      ((fourierOutcomes reducedPhaseWires.length).map
        (fun bs => phaseWordState reducedPhaseWires bs (scalarRootFlip zeroBasisState))) (by
          intro s hs
          obtain ⟨bs, _, rfl⟩ := List.mem_map.mp hs
          exact reducedRawEntryWord_ready bs)
    simpa only [List.map_map, Function.comp_def, phaseUniformSum] using hh
  intro s hs
  apply hh s
  intro hz
  exact hs (by simp [hz])

/-- The ideal event weight contributed by the good input component, after a post-circuit. -/
def reducedRawGoodEventMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (c : Circuit) (event : BasisState → Prop) : ℝ :=
  normSq ((Quantum.run c ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q))
    (reducedRawEntryState.filter (reducedRawExclusions P Q hP hQ hrP hrQ)))).filter event)

theorem reducedRawGoodEventMass_eq (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (c : Circuit) (event : BasisState → Prop) :
    ((reducedRawProgram P Q).seq (.unitary c .done)).run.eventMass event
      (reducedRawEntryState.filter (reducedRawExclusions P Q hP hQ hrP hrQ)) =
    reducedRawGoodEventMass P Q hP hQ hrP hrQ c event := by
  apply CoherentlyImplementsOn.eventMass
    ((reducedRaw_registers_coherent P Q hP hQ hrP hrQ).seq
      (CoherentlyImplementsOn.unitary c (fun _ => True)) (fun _ _ _ _ => trivial))
  intro s hs
  have he : reducedRawExclusions P Q hP hQ hrP hrQ s := by
    by_contra hn
    exact hs (by simp [hn])
  have hn : reducedRawEntryState s ≠ 0 := by simpa [he] using hs
  exact ⟨reducedRawEntryState_supported s hn, he⟩

/-- A two-sided event bound for the full coherent input, including interference.
The comparison is to the ideal good component, not the full ideal sampling distribution. -/
theorem reducedRawEvent_interference (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (c : Circuit) (hc : CircuitWellFormed c)
    (event : BasisState → Prop) :
    (3/4:ℝ)*reducedRawGoodEventMass P Q hP hQ hrP hrQ c event - 21/4096 ≤
      ((reducedRawProgram P Q).seq (.unitary c .done)).run.eventMass event reducedRawEntryState ∧
    ((reducedRawProgram P Q).seq (.unitary c .done)).run.eventMass event reducedRawEntryState ≤
      (5/4:ℝ)*reducedRawGoodEventMass P Q hP hQ hrP hrQ c event + 35/4096 := by
  let good := reducedRawEntryState.filter (reducedRawExclusions P Q hP hQ hrP hrQ)
  let bad := reducedRawEntryState.filter (fun s => ¬reducedRawExclusions P Q hP hQ hrP hrQ s)
  let program := (reducedRawProgram P Q).seq (.unitary c .done)
  have hw : program.WellFormed := (reducedRawProgram_wellFormed P Q).seq ⟨hc, trivial⟩
  have hb : program.run.eventMass event bad ≤ (7:ℝ)/4096 := by
    apply (Instrument.eventMass_le_bornMass _ _ _).trans
    rw [AdaptiveCircuit.run_preservesBornMass _ hw]
    exact reducedRawEntry_excluded_mass P Q hP hQ hrP hrQ
  have hi := Instrument.eventMass_interference program.run event good bad
  have he : good+bad=reducedRawEntryState := Finsupp.filter_pos_add_filter_neg _ _
  have hg : program.run.eventMass event good = reducedRawGoodEventMass P Q hP hQ hrP hrQ c event :=
    reducedRawGoodEventMass_eq P Q hP hQ hrP hrQ c event
  rw [he, hg] at hi
  constructor <;> linarith [hi.1, hi.2]
private theorem output_injective (P Q : Point) :
    Set.InjOn (reducedScalarOutput P Q) {s | PointInitializeValid s} := by
  intro s hs t ht he
  funext w
  by_cases hw : w∈pointLogicalWires
  · have hz (u : BasisState) (hu : PointInitializeValid u) : u w=false := by
      have hm : u w∈wireValues pointLogicalWires u := List.mem_map.mpr ⟨w, hw, rfl⟩
      rw [hu.2] at hm
      exact List.eq_of_mem_replicate hm
    rw [hz s hs, hz t ht]
  · have hh := congrFun he w
    simpa only [reducedScalarOutput, pointWrite_frame _ _ _ hw] using hh

/-- On the clean-entry subspace the full ideal scalar map preserves norm. -/
theorem reducedScalarOutput_normSq (P Q : Point) (ψ : State)
    (hψ : SupportedOn PointInitializeValid ψ) :
    normSq ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) ψ) = normSq ψ := by
  apply normSq_mapDomain
  intro s hs t ht he
  exact output_injective P Q (hψ s (Finsupp.mem_support_iff.mp hs))
    (hψ t (Finsupp.mem_support_iff.mp ht)) he

/-- Event weight of the full ideal scalar output after a post-circuit. -/
def reducedRawIdealEventMass (P Q : Point) (c : Circuit) (event : BasisState → Prop) : ℝ :=
  normSq ((Quantum.run c ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q))
    reducedRawEntryState)).filter event)

/-- Explicit event-probability comparison to the full ideal output.
These conservative constants include both coherent interference comparisons. -/
theorem reducedRawEvent_ideal_bounds (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (c : Circuit) (hc : CircuitWellFormed c)
    (event : BasisState → Prop) :
    (9/16:ℝ)*reducedRawIdealEventMass P Q c event - 147/16384 ≤
      ((reducedRawProgram P Q).seq (.unitary c .done)).run.eventMass event reducedRawEntryState ∧
    ((reducedRawProgram P Q).seq (.unitary c .done)).run.eventMass event reducedRawEntryState ≤
      (25/16:ℝ)*reducedRawIdealEventMass P Q c event + 315/16384 := by
  let good := reducedRawEntryState.filter (reducedRawExclusions P Q hP hQ hrP hrQ)
  let bad := reducedRawEntryState.filter (fun s => ¬reducedRawExclusions P Q hP hQ hrP hrQ s)
  let ideal := (Quantum.run c).comp (Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q))
  have hb : normSq ((ideal bad).filter event) ≤ (7:ℝ)/4096 := by
    apply (normSq_filter_le event _).trans
    change normSq (Quantum.run c ((Finsupp.lmapDomain ℂ ℂ (reducedScalarOutput P Q)) bad)) ≤ _
    rw [normSq_run _ hc, reducedScalarOutput_normSq P Q bad (by
      intro s hs
      apply reducedRawEntryState_supported s
      intro hz
      exact hs (by simp [bad, Finsupp.filter_apply, hz]))]
    exact reducedRawEntry_excluded_mass P Q hP hQ hrP hrQ
  have he : good+bad=reducedRawEntryState := Finsupp.filter_pos_add_filter_neg _ _
  have hd : (ideal good).filter event =
      (ideal reducedRawEntryState).filter event + -((ideal bad).filter event) := by
    rw [← he, map_add, Finsupp.filter_add]
    abel
  have hi := normSq_interference ((ideal reducedRawEntryState).filter event)
    (-((ideal bad).filter event))
  rw [← hd, normSq_neg] at hi
  have hr := reducedRawEvent_interference P Q hP hQ hrP hrQ c hc event
  change (3/4:ℝ)*reducedRawIdealEventMass P Q c event - 3*normSq ((ideal bad).filter event) ≤
      reducedRawGoodEventMass P Q hP hQ hrP hrQ c event ∧
    reducedRawGoodEventMass P Q hP hQ hrP hrQ c event ≤
      (5/4:ℝ)*reducedRawIdealEventMass P Q c event + 5*normSq ((ideal bad).filter event) at hi
  constructor <;> linarith [hi.1, hi.2, hr.1, hr.2]

end
end ShorECDLP.Paper2607_13816
