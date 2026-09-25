import ShorECDLP.Submission.«2607_13816».Window.PreparedArithmetic
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

private theorem point_wire_bound (w : Wire) (hw : w ∈ pointLogicalWires) : w<839 := by
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

private theorem bank_pointWrite (k : Nat) (P : Point) (s : BasisState) :
    relabelBasis (streamBankPerm k)
      (pointWrite P (relabelBasis (streamBankPerm k).symm s)) = pointWrite P s := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · simp only [relabelBasis, streamBankPerm_symm,
      streamBankPerm_core k w (point_wire_bound w hw), pointWrite, if_pos hw]
  · have hn : (streamBankPerm k).symm w ∉ pointLogicalWires := by
      intro h
      have he := streamBankPerm_core k _ (point_wire_bound _ h)
      rw [Equiv.apply_symm_apply] at he
      exact hw (he ▸ h)
    simp only [relabelBasis, pointWrite, if_neg hn, if_neg hw, Equiv.symm_symm,
      Equiv.apply_symm_apply]

private theorem bank_address (k : Nat) (s : BasisState) :
    tableAddressValue (List.range' 855 16) (relabelBasis (streamBankPerm k).symm s) =
      tableAddressValue (List.range' (windowBankStart k) 16) s := by
  have h (n i : Nat) (hi : i+n≤16) :
      tableAddressValue (List.range' (855+i) n) (relabelBasis (streamBankPerm k).symm s) =
        tableAddressValue (List.range' (windowBankStart k+i) n) s := by
    induction n generalizing i with
    | zero => rfl
    | succ n ih =>
      simp only [List.range'_succ, tableAddressValue, relabelBasis, Equiv.symm_symm,
        streamBankPerm_address k i (by omega)]
      rw [show 855+i+1=855+(i+1) by omega,
        show windowBankStart k+i+1=windowBankStart k+(i+1) by omega, ih (i+1) (by omega)]
  simpa using h 16 0 (by decide)

/-- Relocated direct lookup writes the selected point and preserves every other
wire, with the original lookup input condition expressed in physical addresses. -/
theorem streamBankLookup_coherent (table : Nat → Point) (k : Nat) :
    CoherentlyImplementsOn ((physicalPointLookup table).relabel (streamBankPerm k))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite
        (table (tableAddressValue (List.range' (windowBankStart k) 16) s)) s))
      (DirectPointLookupValid (List.range' 519 16) 836) := by
  obtain ⟨cs,ha,hm⟩ := (physicalPointLookup_coherent table).relabel (streamBankPerm k)
  refine ⟨cs,ha.imp ?_,hm⟩
  intro b c hb s hs
  have hv : DirectPointLookupValid (List.range' 519 16) 836
      (relabelBasis (streamBankPerm k).symm s) := by
    refine ⟨?_,?_,?_⟩
    · intro w hw
      have hlt : w<839 := by simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega
      simpa only [relabelBasis, Equiv.symm_symm, streamBankPerm_core k w hlt] using hs.1 w hw
    · intro w hw
      simpa only [relabelBasis, Equiv.symm_symm,
        streamBankPerm_core k w (point_wire_bound w hw)] using hs.2.1 w hw
    · simpa only [relabelBasis, Equiv.symm_symm, streamBankPerm_core k 836 (by decide)] using hs.2.2
  have hh := hb s hv
  have hi : ((relabelState (streamBankPerm k)).comp
      ((Finsupp.lmapDomain ℂ ℂ (fun t => pointWrite
        (table (tableAddressValue (List.range' 855 16) t)) t)).comp
        (relabelState (streamBankPerm k).symm))) (ket s) =
      ket (pointWrite (table (tableAddressValue (List.range' (windowBankStart k) 16) s)) s) := by
    simp only [LinearMap.comp_apply, relabelState_ket]
    have hmap (f : BasisState → BasisState) (t : BasisState) :
        (Finsupp.lmapDomain ℂ ℂ f) (ket t) = ket (f t) := by simp [ket]
    rw [hmap, relabelState_ket, bank_address, bank_pointWrite]
  rw [hi] at hh
  simpa only [Finsupp.lmapDomain_apply, ket, Finsupp.mapDomain_single] using hh
private theorem initial_address (s : BasisState) :
    tableAddressValue streamAddress (s ∘ streamPreparedWire) =
      tableAddressValue (List.range' (windowBankStart 1) 16) s := by
  have h (n i : Nat) :
      tableAddressValue (List.range' (windowBankStart 0+i) n) (s ∘ streamPreparedWire) =
      tableAddressValue (List.range' (windowBankStart 1+i) n) s := by
    induction n generalizing i with
    | zero => rfl
    | succ n ih =>
      simp only [List.range'_succ, tableAddressValue, Function.comp_apply, streamPreparedWire_bank]
      rw [show windowBankStart 0+i+1=windowBankStart 0+(i+1) by omega,
        show windowBankStart 1+i+1=windowBankStart 1+(i+1) by omega, ih]
  exact h 16 0

private theorem initialize_lookup_valid (s : BasisState) (hs : PointInitializeValid s) :
    DirectPointLookupValid (List.range' 519 16) 836 s := by
  refine ⟨?_,?_,hs.1.2⟩
  · intro w hw
    apply hs.1.1.1 w
    simp only [List.mem_append, List.mem_range'_1] at hw ⊢
    omega
  · intro w hw
    have h : s w ∈ wireValues pointLogicalWires s := List.mem_map.mpr ⟨w,hw,rfl⟩
    rw [hs.2] at h
    exact (List.mem_replicate.mp h).2

def streamPreparedInitialState (P Q : Point) (s : BasisState) : BasisState :=
  pointWrite (streamRawInitialPoint P Q (s ∘ streamPreparedWire)) s

def streamPreparedLookup (P Q : Point) : AdaptiveCircuit :=
  (physicalPointLookup (firstWindowTable (axisWindowOffset P 16+axisWindowOffset Q 13)
    ((2^(16*15)) • P))).relabel (streamBankPerm 1)

/-- The actual direct-load call on bank 1 establishes the counted initial point. -/
theorem streamPreparedLookup_coherent (P Q : Point) :
    CoherentlyImplementsOn (streamPreparedLookup P Q)
      (Finsupp.lmapDomain ℂ ℂ (streamPreparedInitialState P Q)) PointInitializeValid := by
  obtain ⟨cs,ha,hm⟩ := streamBankLookup_coherent
    (firstWindowTable (axisWindowOffset P 16+axisWindowOffset Q 13) ((2^(16*15)) • P)) 1
  refine ⟨cs,ha.imp ?_,hm⟩
  intro b c hb s hs
  simpa only [streamPreparedInitialState, streamRawInitialPoint, initial_address,
    Finsupp.lmapDomain_apply, ket, Finsupp.mapDomain_single] using hb s (initialize_lookup_valid s hs)

/-- Initialization establishes the readiness and point encoding needed by the
28-call arithmetic theorem; nonexceptional inputs remain a separate condition. -/
theorem streamPreparedInitialState_ready (P Q : Point) (s : BasisState)
    (hs : PointInitializeValid s) :
    PointLookupValid (streamPreparedInitialState P Q s) ∧
      pointStateCoordinates (streamPreparedInitialState P Q s) =
        fig14PointEncoding (streamRawInitialPoint P Q (s ∘ streamPreparedWire)) :=
  ⟨(pointInitialize_ready _ s hs).1, pointWrite_coordinates _ s⟩

private theorem preparedWire_pointWrite (A : Point) (s : BasisState) :
    (pointWrite A s) ∘ streamPreparedWire = pointWrite A (s ∘ streamPreparedWire) := by
  funext w
  by_cases hw : w∈pointLogicalWires
  · have he : streamPreparedWire w=w := by
      unfold streamPreparedWire
      rw [if_pos (by have := point_wire_bound w hw; dsimp only [Wire] at *; omega)]
    simp only [Function.comp_apply, he, pointWrite, if_pos hw]
  · have hn : streamPreparedWire w ∉ pointLogicalWires := by
      intro h
      have hb := point_wire_bound _ h
      have he : streamPreparedWire w=w := by
        unfold streamPreparedWire at *
        dsimp only [Wire] at *
        split_ifs at * <;> omega
      exact hw (he ▸ h)
    simp only [Function.comp_apply, pointWrite, if_neg hw, if_neg hn]

private theorem initial_write (P Q A : Point) (s : BasisState) :
    streamRawInitialPoint P Q (pointWrite A s)=streamRawInitialPoint P Q s := by
  have h (n i : Nat) : tableAddressValue (List.range' (855+i) n) (pointWrite A s) =
      tableAddressValue (List.range' (855+i) n) s := by
    induction n generalizing i with
    | zero => rfl
    | succ n ih =>
      simp only [List.range'_succ, tableAddressValue]
      rw [pointWrite_frame A s (855+i) (by
        intro hw; have := point_wire_bound _ hw; dsimp only [Wire] at *; omega)]
      rw [show 855+i+1=855+(i+1) by omega, ih]
  unfold streamRawInitialPoint
  rw [show streamAddress=List.range' (855+0) 16 by rfl, h]

private theorem exclusions_write' (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a))
    (js : List Nat) (A B : Point) (s : BasisState) :
    rawAlgebraicExclusions x y hc js A (pointWrite B s) = rawAlgebraicExclusions x y hc js A s := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih => simp only [rawAlgebraicExclusions, preparedWindowDelta_pointWrite, ih]

private theorem end_write' (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a))
    (js : List Nat) (A B : Point) (s : BasisState) :
    rawAlgebraicEnd x y hc js A (pointWrite B s) = rawAlgebraicEnd x y hc js A s := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih => simp only [rawAlgebraicEnd, preparedWindowDelta_pointWrite, ih]

/-- Direct loading preserves the counted exclusions on the original inputs. -/
theorem streamPreparedInitialState_exclusions (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    streamRawExclusions P Q hP hQ hrP hrQ ((streamPreparedInitialState P Q s) ∘ streamPreparedWire) =
      streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire) := by
  simp only [streamPreparedInitialState, preparedWire_pointWrite, streamRawExclusions,
    initial_write, exclusions_write']

/-- First lookup and all 28 actual relocated additions form one coherent map. -/
theorem streamPreparedArithmetic_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn ((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (streamPreparedRawEnd P Q hP hQ hrP hrQ s) s))
      (fun s => PointInitializeValid s ∧
        streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire)) := by
  obtain ⟨cs,ha,hm⟩ := streamPreparedLookup_coherent P Q
  have h : CoherentlyImplementsOn (streamPreparedLookup P Q)
      (Finsupp.lmapDomain ℂ ℂ (streamPreparedInitialState P Q))
      (fun s => PointInitializeValid s ∧ streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire)) :=
    ⟨cs,ha.imp (fun b c hb s hs => hb s hs.1),hm⟩
  have hh := h.seq (streamPreparedRaw_coherent P Q hP hQ hrP hrQ) (by
    intro s hs
    have ready := streamPreparedInitialState_ready P Q s hs.1
    have hv : PointLookupValid (streamPreparedInitialState P Q s) ∧
        pointStateCoordinates (streamPreparedInitialState P Q s) =
          fig14PointEncoding (streamRawInitialPoint P Q ((streamPreparedInitialState P Q s) ∘ streamPreparedWire)) ∧
        streamRawExclusions P Q hP hQ hrP hrQ ((streamPreparedInitialState P Q s) ∘ streamPreparedWire) := by
      refine ⟨ready.1, ?_, ?_⟩
      · simpa only [streamPreparedInitialState, preparedWire_pointWrite, initial_write] using ready.2
      · rw [streamPreparedInitialState_exclusions]; exact hs.2
    simpa [ket] using supportedOn_ket _ _ hv)
  apply hh.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, ket, Finsupp.mapDomain_single,
    streamPreparedRawEnd, streamPreparedInitialState, preparedWire_pointWrite, initial_write,
    end_write', pointWrite_overwrite]

end
end ShorECDLP.Paper2607_13816
