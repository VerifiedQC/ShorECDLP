import ShorECDLP.Submission.«2607_13816».Window.RawTwoAxis
import ShorECDLP.Submission.«2607_13816».Window.StreamWeight
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Read reference banks 0..28 from the prepared body's banks 1..29.
Arithmetic wires below the logical register retain their original addresses. -/
def streamPreparedWire (w : Wire) : Wire := if w < 855 then w else w + 16

theorem streamPreparedWire_injective : Function.Injective streamPreparedWire := by
  intro a b h
  unfold streamPreparedWire at h
  split_ifs at h <;> dsimp only [Wire] at * <;> omega

/-- The address translation preserves the bit index within every logical bank. -/
theorem streamPreparedWire_bank (k i : Nat) :
    streamPreparedWire (windowBankStart k + i) = windowBankStart (k+1) + i := by
  unfold streamPreparedWire windowBankStart
  dsimp only [Wire]
  split_ifs <;> omega

private theorem word_pullback (f : Wire → Wire) (hf : Function.Injective f)
    (ws : List Wire) (bs : List Bool) (s : BasisState) :
    (phaseWordState (ws.map f) bs s) ∘ f = phaseWordState ws bs (s ∘ f) := by
  induction ws generalizing bs s with
  | nil => rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [List.map_cons, phaseWordState]
      rw [ih]
      congr 1
      funext q
      simp only [Function.comp_apply, upd, hf.eq_iff]

/-- Consecutive parked banks prepare one contiguous register. -/
theorem indexedStreamCalls_preparation (start : Nat) (calls : List AdaptiveCircuit) :
    streamPreparationWires (indexedStreamCalls start calls) =
      List.range' (windowBankStart start) (16 * calls.length) := by
  induction calls generalizing start with
  | nil => simp [indexedStreamCalls, streamPreparationWires]
  | cons c cs ih =>
    simp only [indexedStreamCalls, List.zipIdx_cons, List.map_cons,
      streamPreparationWires, List.flatMap_cons]
    change List.range' (windowBankStart start) 16 ++
      streamPreparationWires (indexedStreamCalls (start+1) cs) = _
    rw [ih]
    have he : windowBankStart (start+1) = windowBankStart start + 16 := by
      simp [windowBankStart]; omega
    rw [he, List.range'_append]
    congr 1
    simp [Nat.mul_add, Nat.add_comm]

theorem streamRawPreparation_eq (P Q : Point) :
    streamRawPreparation P Q = (List.range' 871 464).map Gate.H := by
  unfold streamRawPreparation
  rw [indexedStreamCalls_preparation, indexedStreamCalls_preparation]
  simp only [streamRawLeftCalls, streamRawRightCalls, List.length_cons,
    List.length_map, List.length_reverse, List.length_range, windowBankStart]
  exact congrArg (List.map Gate.H)
    (List.range'_append (s:=871) (m:=256) (n:=208) (step:=1))

private theorem prepared_wires : streamLogicalPhaseWires.map streamPreparedWire =
    List.range' 871 464 := by
  apply List.ext_getElem
  · simp [streamLogicalPhaseWires]
  · intro i hi hj
    simp only [streamLogicalPhaseWires, List.getElem_map, List.getElem_range', Nat.one_mul]
    change streamPreparedWire (855+i) = 871+i
    unfold streamPreparedWire
    dsimp only [Wire]
    split_ifs <;> omega

private theorem prepared_root : (scalarRootFlip zeroBasisState) ∘ streamPreparedWire =
    scalarRootFlip zeroBasisState := by
  funext w
  simp only [Function.comp_apply, scalarRootFlip, upd, zeroBasisState]
  have he : streamPreparedWire w = 836 ↔ w = 836 := by
    unfold streamPreparedWire
    split_ifs <;> dsimp only [Wire] at * <;> omega
  simp only [he]

/-- Excluded input mass for the preparation used by the actual two-axis body.
This concerns an input predicate, not yet a physical failure/decoder event. -/
theorem streamRawPrepared_excluded_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    normSq ((Quantum.run (streamRawPreparation P Q) (ket (scalarRootFlip zeroBasisState))).filter
      (fun s => ¬streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire))) ≤ (7:ℝ)/4096 := by
  rw [streamRawPreparation_eq]
  have hz : Clean (List.range' 871 464) (scalarRootFlip zeroBasisState) := by
    intro w hw
    have hn : w ≠ 836 := by
      simp only [List.mem_range'_1] at hw
      dsimp only [Wire] at *
      omega
    simp [scalarRootFlip, upd, hn, zeroBasisState]
  rw [phaseHadamards_filtered_mass _ List.nodup_range' _ hz]
  have he (bs : List Bool) :
      (phaseWordState (List.range' 871 464) bs (scalarRootFlip zeroBasisState)) ∘
        streamPreparedWire =
      phaseWordState streamLogicalPhaseWires bs (scalarRootFlip zeroBasisState) := by
    rw [← prepared_wires, word_pullback _ streamPreparedWire_injective, prepared_root]
  simp only [he, List.length_range']
  have h := streamLogicalEntry_excluded_mass P Q hP hQ hrP hrQ
  rw [streamLogicalEntry_filtered_mass] at h
  exact h
end
end ShorECDLP.Paper2607_13816
