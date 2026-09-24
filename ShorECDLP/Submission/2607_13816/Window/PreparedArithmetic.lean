import ShorECDLP.Submission.«2607_13816».Window.PreparedWeight
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

/-- Address preparation reads the same digit after shifting the parked banks. -/
theorem streamPreparedWire_prepare (j i : Nat) (s : BasisState) :
    windowPrepareState j (s ∘ streamPreparedWire) (windowBankStart j+i) =
      windowPrepareState (j+1) s (windowBankStart (j+1)+i) := by
  simp only [windowPrepareState, signedAddressState, tableXorState,
    Function.comp_apply, streamPreparedWire_bank, windowAddressBits, List.mem_range'_1]
  have hr : streamPreparedWire 836 = 836 := by decide
  rw [hr]
  simp only [windowBankStart]
  simp

private theorem address_shift (j : Nat) (s : BasisState) :
    tableAddressValue (List.range' (windowBankStart j) 15)
      (windowPrepareState j (s ∘ streamPreparedWire)) =
    tableAddressValue (List.range' (windowBankStart (j+1)) 15)
      (windowPrepareState (j+1) s) := by
  have h (n i : Nat) :
      tableAddressValue (List.range' (windowBankStart j+i) n)
        (windowPrepareState j (s ∘ streamPreparedWire)) =
      tableAddressValue (List.range' (windowBankStart (j+1)+i) n)
        (windowPrepareState (j+1) s) := by
    induction n generalizing i with
    | zero => rfl
    | succ n ih =>
      simp only [List.range'_succ, tableAddressValue, streamPreparedWire_prepare]
      rw [show windowBankStart j+i+1=windowBankStart j+(i+1) by omega,
        show windowBankStart (j+1)+i+1=windowBankStart (j+1)+(i+1) by omega, ih]
  simpa using h 15 0

/-- Both the magnitude and sign of a selected table point survive bank shifting. -/
theorem preparedWindowDelta_streamPreparedWire (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (j : Nat) (s : BasisState) :
    preparedWindowDelta x y hc j (s ∘ streamPreparedWire) =
      preparedWindowDelta (fun k => x (k-1)) (fun k => y (k-1))
        (fun k a => hc (k-1) a) (j+1) s := by
  simp only [preparedWindowDelta, windowPointDelta, streamPreparedWire_prepare,
    address_shift, Nat.add_sub_cancel]

/-- The group walk uses identical selected points in the prepared bank layout. -/
theorem rawAlgebraicEnd_streamPreparedWire (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a))
    (js : List Nat) (A : Point) (s : BasisState) :
    rawAlgebraicEnd x y hc js A (s ∘ streamPreparedWire) =
      rawAlgebraicEnd (fun k => x (k-1)) (fun k => y (k-1))
        (fun k a => hc (k-1) a) (js.map (·+1)) A s := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih =>
    simp only [rawAlgebraicEnd, List.map_cons, preparedWindowDelta_streamPreparedWire, ih]

/-- Transport the counted exclusions to the banks of the actual prepared body. -/
theorem rawAlgebraicExclusions_streamPreparedWire (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a))
    (js : List Nat) (A : Point) (s : BasisState) :
    rawAlgebraicExclusions x y hc js A (s ∘ streamPreparedWire) ↔
      rawAlgebraicExclusions (fun k => x (k-1)) (fun k => y (k-1))
        (fun k a => hc (k-1) a) (js.map (·+1)) A s := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih =>
    simp only [rawAlgebraicExclusions, List.map_cons,
      preparedWindowDelta_streamPreparedWire, ih]

/-- Actual prepared banks 2..29 execute the 28 additions after direct loading. -/
def streamPreparedRawProgram (P Q : Point) : AdaptiveCircuit :=
  rawWindowSchedule (fun k a => (streamRawX P Q (k-1) a).val)
    (fun k a => (streamRawY P Q (k-1) a).val) ((List.range' 1 28).map (·+1))

private theorem shifted_call (P Q : Point) (j : Nat) :
    preparedRawProgram (fun k a => (streamRawX P Q (k-1) a).val)
      (fun k a => (streamRawY P Q (k-1) a).val) (j+1) =
    (streamRawIndexedCall P Q j).relabel (streamBankPerm (j+1)) := by
  rw [streamRawIndexedCall, preparedRawProgram_reuse]
  simp only [preparedRawProgram, parkedRawProgram, Nat.add_sub_cancel]

private theorem schedule_fold (x y : Nat → Nat → Nat) (f : Nat → Nat) (js : List Nat) :
    rawWindowSchedule x y (js.map f) = js.foldr
      (fun j tail => (preparedRawProgram x y (f j)).seq tail) .done := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    rw [List.map_cons, rawWindowSchedule, List.foldr_cons, ih]

private theorem shifted_calls (P Q : Point) (js : List Nat) :
    rawWindowSchedule (fun k a => (streamRawX P Q (k-1) a).val)
      (fun k a => (streamRawY P Q (k-1) a).val) (js.map (·+1)) = js.foldr
      (fun j tail => ((streamRawIndexedCall P Q j).relabel (streamBankPerm (j+1))).seq tail)
      .done := by
  rw [schedule_fold]
  congr 1
  funext j tail
  exact congrArg (fun c => AdaptiveCircuit.seq c tail) (shifted_call P Q j)

/-- These are the relocated raw calls, rather than newly substituted arithmetic. -/
theorem streamPreparedRawProgram_calls (P Q : Point) :
    streamPreparedRawProgram P Q = (List.range' 1 28).foldr
      (fun j tail => ((streamRawIndexedCall P Q j).relabel (streamBankPerm (j+1))).seq tail)
      .done := shifted_calls P Q _

def streamPreparedRawEnd (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) : Point :=
  rawAlgebraicEnd (streamRawX P Q) (streamRawY P Q)
    (streamRawTable_valid P Q hP hQ hrP hrQ) (List.range' 1 28)
    (streamRawInitialPoint P Q (s ∘ streamPreparedWire)) (s ∘ streamPreparedWire)

/-- Counted exclusions suffice for all operational raw-addition conditions in
this layout, and the complete output preserves every non-point wire. -/
theorem streamPreparedRaw_correct (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState)
    (hs : PointLookupValid s)
    (he : pointStateCoordinates s =
      fig14PointEncoding (streamRawInitialPoint P Q (s ∘ streamPreparedWire)))
    (good : streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire)) :
    RawWindowScheduleDomain (fun k a => (streamRawX P Q (k-1) a).val)
      (fun k a => (streamRawY P Q (k-1) a).val) ((List.range' 1 28).map (·+1)) s ∧
    rawWindowScheduleState (fun k a => (streamRawX P Q (k-1) a).val)
      (fun k a => (streamRawY P Q (k-1) a).val) ((List.range' 1 28).map (·+1)) s =
      pointWrite (streamPreparedRawEnd P Q hP hQ hrP hrQ s) s := by
  have hg := (rawAlgebraicExclusions_streamPreparedWire (streamRawX P Q)
    (streamRawY P Q) (streamRawTable_valid P Q hP hQ hrP hrQ) (List.range' 1 28)
    (streamRawInitialPoint P Q (s ∘ streamPreparedWire)) s).mp good
  have hp := rawAlgebraicExclusions_path _ _ _ _ _ _ hg
  have hc := rawPointPath_correct _ _ hp hs he
  simpa only [streamPreparedRawEnd, rawAlgebraicEnd_streamPreparedWire] using hc

/-- Coherent arithmetic semantics, with the counted input exclusions explicit.
This is the group walk endpoint, not yet its scalar reconstruction. -/
theorem streamPreparedRaw_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (streamPreparedRawProgram P Q)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (streamPreparedRawEnd P Q hP hQ hrP hrQ s) s))
      (fun s => PointLookupValid s ∧
        pointStateCoordinates s = fig14PointEncoding (streamRawInitialPoint P Q (s ∘ streamPreparedWire)) ∧
        streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire)) := by
  obtain ⟨cs, ha, hm⟩ := rawWindowSchedule_coherent
    (fun k a => (streamRawX P Q (k-1) a).val)
    (fun k a => (streamRawY P Q (k-1) a).val) ((List.range' 1 28).map (·+1))
  refine ⟨cs, ha.imp ?_, hm⟩
  intro b c hb s hs
  have hc := streamPreparedRaw_correct P Q hP hQ hrP hrQ s hs.1 hs.2.1 hs.2.2
  simpa only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ket, hc.2] using hb s hc.1

end
end ShorECDLP.Paper2607_13816
