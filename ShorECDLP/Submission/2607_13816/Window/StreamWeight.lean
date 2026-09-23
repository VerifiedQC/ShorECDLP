import ShorECDLP.Submission.«2607_13816».Window.StreamFibers
import ShorECDLP.Submission.«2607_13816».Window.RawWeight
/-! Born-weight bounds for separately prepared logical MSB-first assignments.
The 464 logical wires are not the reused 16-wire physical stream. Transporting
these bounds through the full adaptive streaming execution remains unproved. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local instance] Classical.propDecidable

def streamLogicalPhaseWires : List Wire := List.range' 855 464
/-- A reference preparation with all logical windows present simultaneously. -/
def streamLogicalEntryState : State :=
  Quantum.run (streamLogicalPhaseWires.map Gate.H) (ket (scalarRootFlip zeroBasisState))

/-- Count all logical assignments using the fixed-suffix bound from StreamFibers. -/
theorem streamRawExclusions_word_count (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    ((fourierOutcomes 464).filter (fun bs =>
      ¬streamRawExclusions P Q hP hQ hrP hrQ
        (phaseWordState streamLogicalPhaseWires bs s))).length ≤ 2^448*112 := by
  have hd : List.Disjoint (List.range' 855 16) (List.range' 871 448) := by
    apply List.disjoint_left.mpr
    intro w hw hv
    simp only [List.mem_range'_1] at hw hv
    omega
  have h := rawFirstWord_full_count (streamRawExclusions P Q hP hQ hrP hrQ) 112
    (List.range' 871 448) hd (streamRawExclusions_firstWord_card P Q hP hQ hrP hrQ) s
  simp only [List.length_range'] at h
  have hw : streamLogicalPhaseWires = List.range' 855 16 ++ List.range' 871 448 := by
    unfold streamLogicalPhaseWires
    exact (List.range'_append (s:=855) (m:=16) (n:=448) (step:=1)).symm
  rw [hw]
  exact h

/-- Every event at the logical reference preparation has its normalized count. -/
theorem streamLogicalEntry_filtered_mass (p : BasisState → Prop) [DecidablePred p] :
    normSq (streamLogicalEntryState.filter p) =
      (((fourierOutcomes 464).filter (fun bs =>
        p (phaseWordState streamLogicalPhaseWires bs (scalarRootFlip zeroBasisState)))).length : ℝ)/2^464 := by
  have hz : Clean streamLogicalPhaseWires (scalarRootFlip zeroBasisState) := by
    intro w hw
    have hn : w≠836 := by
      simp only [streamLogicalPhaseWires,List.mem_range'_1] at hw
      dsimp only [Wire] at *
      omega
    simp only [scalarRootFlip,upd,if_neg hn,zeroBasisState]
  have h := phaseHadamards_filtered_mass streamLogicalPhaseWires (List.nodup_range')
    (scalarRootFlip zeroBasisState) hz p
  simpa only [streamLogicalEntryState,streamLogicalPhaseWires,List.length_range'] using h

/-- Excluded Born mass of the fully prepared logical reference input, not yet
of a history event in the reused-bank stream. -/
theorem streamLogicalEntry_excluded_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    normSq (streamLogicalEntryState.filter
      (fun s => ¬streamRawExclusions P Q hP hQ hrP hrQ s)) ≤ (7:ℝ)/4096 := by
  rw [streamLogicalEntry_filtered_mass]
  have hc := streamRawExclusions_word_count P Q hP hQ hrP hrQ (scalarRootFlip zeroBasisState)
  have hr : (((fourierOutcomes 464).filter (fun bs =>
      ¬streamRawExclusions P Q hP hQ hrP hrQ
        (phaseWordState streamLogicalPhaseWires bs (scalarRootFlip zeroBasisState)))).length : ℝ)
      ≤ (2:ℝ)^448*112 := by exact_mod_cast hc
  calc
    _ ≤ ((2:ℝ)^448*112)/2^464 := div_le_div_of_nonneg_right hr (by positivity)
    _ = 7/4096 := by
      rw [show 464=448+16 from rfl,pow_add,mul_div_mul_left _ _ (by positivity : (2:ℝ)^448≠0)]
      norm_num

/-- The actual 16-wire Hadamard block obeys the conditional bound on a basis
background. Future logical windows are fixed by that background, not yet sampled. -/
theorem streamFirstWord_excluded_mass (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) (hs : Clean streamAddress s) :
    normSq ((Quantum.run (streamAddress.map Gate.H) (ket s)).filter
      (fun t => ¬streamRawExclusions P Q hP hQ hrP hrQ t)) ≤ (7:ℝ)/4096 := by
  rw [phaseHadamards_filtered_mass streamAddress (List.nodup_range') s hs]
  have hc := rawFirstWord_filter_count (streamRawExclusions P Q hP hQ hrP hrQ) 112 s
    (streamRawExclusions_firstWord_card P Q hP hQ hrP hrQ s)
  have hr : (((fourierOutcomes 16).filter (fun bs =>
      ¬streamRawExclusions P Q hP hQ hrP hrQ
        (phaseWordState streamAddress bs s))).length : ℝ) ≤ 112 := by exact_mod_cast hc
  change _ / (2:ℝ)^16 ≤ _
  calc
    _ ≤ (112:ℝ)/2^16 := div_le_div_of_nonneg_right hr (by positivity)
    _ = 7/4096 := by norm_num
end
end ShorECDLP.Paper2607_13816
