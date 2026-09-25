import ShorECDLP.Submission.«2607_13816».Window.StreamScalar
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local instance] Classical.propDecidable
/-- Every word in the actual 464-Hadamard preparation satisfies initialization. -/
theorem streamPreparedEntryWord_ready (bs : List Bool) :
    PointInitializeValid (phaseWordState (List.range' 871 464) bs (scalarRootFlip zeroBasisState)) := by
  have frame (w : Wire) (hw : w<855) :
      phaseWordState (List.range' 871 464) bs (scalarRootFlip zeroBasisState) w =
        scalarRootFlip zeroBasisState w := by
    apply phaseWordState_frame
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  have word (ws : List Wire) (h : ∀ w∈ws,w<855) :
      wireValues ws (phaseWordState (List.range' 871 464) bs (scalarRootFlip zeroBasisState))=
        wireValues ws (scalarRootFlip zeroBasisState) := by
    apply List.map_congr_left
    intro w hw
    exact frame w (h w hw)
  have base := reducedRawEntryWord_ready []
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩
  · intro w hw
    rw [frame w (by simp only [List.mem_append,List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)]
    exact base.1.1.1 w hw
  · rw [frame 837 (by decide)]; exact base.1.1.2.1
  · rw [word _ (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)]
    exact base.1.1.2.2.1
  · rw [word _ (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)]
    exact base.1.1.2.2.2
  · rw [frame 836 (by decide)]; exact base.1.2
  · rw [word _ (by
      intro w hw
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
        List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hw
      dsimp only [Wire] at *
      omega)]
    exact base.2
private theorem sum_supported (V : BasisState → Prop) (xs : List BasisState)
    (h : ∀ s∈xs,V s) : SupportedOn V (xs.map ket).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    intro s hs
    by_cases he : s=a
    · subst s; exact h a (by simp)
    · apply ih (fun u hu => h u (by simp [hu])) s
      simpa [ket,Finsupp.single_apply,he,Ne.symm he] using hs
/-- The actual prepared superposition is supported on clean arithmetic inputs. -/
theorem streamPreparedEntry_supported (P Q : Point) : SupportedOn PointInitializeValid
    (Quantum.run (streamRawPreparation P Q) (ket (scalarRootFlip zeroBasisState))) := by
  rw [streamRawPreparation_eq,phaseHadamards_uniform _ (by decide +kernel)]
  · have h := sum_supported PointInitializeValid
      ((fourierOutcomes 464).map (fun bs => phaseWordState (List.range' 871 464) bs
        (scalarRootFlip zeroBasisState))) (by
          intro s hs
          obtain ⟨bs,_,rfl⟩ := List.mem_map.mp hs
          exact streamPreparedEntryWord_ready bs)
    simp only [List.map_map,Function.comp_def] at h
    intro s hs
    apply h s
    intro hz
    exact hs (by simp only [Finsupp.smul_apply,phaseUniformSum,List.length_range',hz,smul_zero])
  · intro w hw
    have hn : w≠836 := by simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega
    simp [scalarRootFlip,upd,hn,zeroBasisState]
/-- The very preparation that occurs in the physical two-axis decomposition. -/
def streamPreparedEntry (P Q : Point) : State :=
  Quantum.run (streamRawPreparation P Q) (ket (scalarRootFlip zeroBasisState))

/-- The good input component excludes precisely the previously counted paths. -/
def streamPreparedGoodEntry (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) : State :=
  (streamPreparedEntry P Q).filter
    (fun s => streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire))

/-- Full point write, with the two scalar values read from parked physical banks. -/
def streamPreparedScalarOutput (P Q : Point) (s : BasisState) : BasisState :=
  pointWrite (streamScalarValue 16 0 (s ∘ streamPreparedWire) • P+
    streamScalarValue 13 16 (s ∘ streamPreparedWire) • Q) s

theorem streamPreparedGoodEntry_supported (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    SupportedOn (fun s => PointInitializeValid s ∧
      streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire))
      (streamPreparedGoodEntry P Q hP hQ hrP hrQ) := by
  intro s hs
  have he : streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire) := by
    by_contra hn
    exact hs (by simp [streamPreparedGoodEntry,hn])
  have hn : streamPreparedEntry P Q s≠0 := by
    simpa [streamPreparedGoodEntry,he] using hs
  exact ⟨streamPreparedEntry_supported P Q s (by simpa only [streamPreparedEntry] using hn),he⟩

/-- Every original arithmetic branch acts on the same actual good superposition;
its input-independent coefficient list retains total mass one. -/
theorem streamPreparedGoodEntry_arithmetic (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    ∃ coefficients : List ℂ,
      List.Forall₂ (fun branch coefficient =>
        branch.kraus (streamPreparedGoodEntry P Q hP hQ hrP hrQ) =
          coefficient • Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q)
            (streamPreparedGoodEntry P Q hP hQ hrP hrQ))
        ((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q)).run coefficients ∧
      (coefficients.map Complex.normSq).sum=1 :=
  coherent_on_supported_state (streamPreparedArithmetic_scalars_coherent P Q hP hQ hrP hrQ)
    (streamPreparedGoodEntry_supported P Q hP hQ hrP hrQ)

/-- Exact good-component mass after any terminal instrument. No identification
with the interleaved streaming Fourier paths is asserted here. -/
theorem streamPreparedGoodEntry_terminalMass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (J : Instrument) :
    ((((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q)).run).seq J).bornMass
      (streamPreparedGoodEntry P Q hP hQ hrP hrQ) =
    J.bornMass (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput P Q)
      (streamPreparedGoodEntry P Q hP hQ hrP hrQ)) :=
  (streamPreparedArithmetic_scalars_coherent P Q hP hQ hrP hrQ).terminalMass
    (streamPreparedGoodEntry_supported P Q hP hQ hrP hrQ) J

end
end ShorECDLP.Paper2607_13816
