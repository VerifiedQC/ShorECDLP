import ShorECDLP.Submission.«2607_13816».Challenge.CrossWindowPoint
import ShorECDLP.Submission.«2607_13816».Window.Uniform
import ShorECDLP.Submission.«2607_13816».Challenge.TwoAxisProbability
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1
noncomputable section
attribute [local irreducible] fourierOutcomes actualBatchedWindowState

/-- Physical Fourier coefficients retain the full previous measurement history. -/
theorem branchCoeff_amplitude (dir : PhaseDir) (ws : List Wire)
    (hws : ws.Nodup) (prior bs : List Bool) (s : BasisState) :
    fourierBranchCoeff dir ws prior bs s = fourierBitAmplitude dir (ws.map s) prior bs := by
  induction ws generalizing prior bs s with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [fourierBranchCoeff, List.map_cons, fourierBitAmplitude]
      rw [ih hws.tail]
      have hm : ws.map (s[w ↦ false]) = ws.map s := by
        apply List.map_congr_left
        intro v hv
        have hvw : v ≠ w := by intro he; subst v; exact (List.nodup_cons.mp hws).1 hv
        simp [upd, hvw]
      rw [hm]

theorem window_branch_uniform (dir : PhaseDir) (ws : List Wire) (hn : ws.Nodup)
    (f : BasisState → BasisState) (prior output : List Bool)
    (s : BasisState) (hz : Clean ws s)
    (hf : ∀ input ∈ fourierOutcomes ws.length,
      ws.map (f (phaseWordState ws input s)) = input) :
    fourierBranch dir ws.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ f (Quantum.run (ws.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ ws.length) •
        ((fourierOutcomes ws.length).map (fun input =>
          fourierBitAmplitude dir input.reverse prior output •
            ket (fourierClear ws.reverse (f (phaseWordState ws input s))))).sum := by
  classical
  rw [phaseHadamards_uniform ws hn s hz, map_smul, map_smul]
  congr 1
  simp only [phaseUniformSum, map_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [show Finsupp.lmapDomain ℂ ℂ f (ket (phaseWordState ws input s)) =
      ket (f (phaseWordState ws input s)) by simp [ket],
    fourierBranch_ket, branchCoeff_amplitude dir ws.reverse (List.nodup_reverse.mpr hn)]
  rw [List.map_reverse, hf input hi]

theorem phaseWordState_preserves (V : BasisState → Prop) (ws : List Wire)
    (hV : ∀ s, V s → ∀ w ∈ ws, ∀ b, V (s[w ↦ b]))
    (input : List Bool) (s : BasisState) (hs : V s) :
    V (phaseWordState ws input s) := by
  induction ws generalizing s input with
  | nil => exact hs
  | cons w ws ih =>
    cases input with
    | nil => exact hs
    | cons b input =>
      exact ih (fun t ht v hv c => hV t ht v (List.mem_cons_of_mem w hv) c)
        input _ (hV s hs w (by simp) b)

theorem actual_window_address_word (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : BatchedWindowValid s)
    (input : List Bool) (hi : input.length = streamAddress.length) :
    streamAddress.map (actualBatchedWindowState Q w (phaseWordState streamAddress input s)) = input := by
  have hv : BatchedWindowValid (phaseWordState streamAddress input s) :=
    phaseWordState_preserves BatchedWindowValid streamAddress
      (fun t ht v hv b => batchedWindowValid_address_update t ht v hv b) input s hs
  calc
    _ = streamAddress.map (phaseWordState streamAddress input s) := by
      apply List.map_congr_left
      intro v hva
      exact actualBatchedWindowState_frame Q hQ hn w _ hv v
        ((show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hva)
    _ = input := phaseWordState_word streamAddress (by decide +kernel) input hi s

/-- Exact amplitude sum for an actual corrected window and one fixed Fourier
output. All input amplitudes are added before any Born mass is taken. -/
theorem actual_window_branch_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (prior output : List Bool) (s : BasisState)
    (hs : BatchedWindowValid s) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (fourierClear streamAddress.reverse
              (actualBatchedWindowState Q w (phaseWordState streamAddress input s))))).sum := by
  simpa only [show streamAddress.length = 16 by decide +kernel] using
    window_branch_uniform .inverse streamAddress (by decide +kernel)
      (actualBatchedWindowState Q w) prior output s hz
      (fun input hi => actual_window_address_word Q hQ hn w s hs input
        ((fourierOutcomes_mem _ _).mp hi))

theorem actual_first_address_word (Q : Point) (s : BasisState)
    (input : List Bool) (hi : input.length = streamAddress.length) :
    streamAddress.map (actualFirstWindowState Q (phaseWordState streamAddress input s)) = input := by
  calc
    _ = streamAddress.map (phaseWordState streamAddress input s) := by
      apply List.map_congr_left
      intro v hva
      have hp := (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hva
      simp only [actualFirstWindowState, pointWrite, if_neg hp]
    _ = input := phaseWordState_word streamAddress (by decide +kernel) input hi s

/-- The first direct-load window obeys the same amplitude-sum rule, including
infinity rows in its mixed table. -/
theorem actual_first_branch_sum (Q : Point) (prior output : List Bool)
    (s : BasisState) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (fourierClear streamAddress.reverse
              (actualFirstWindowState Q (phaseWordState streamAddress input s))))).sum := by
  simpa only [show streamAddress.length = 16 by decide +kernel] using
    window_branch_uniform .inverse streamAddress (by decide +kernel)
      (actualFirstWindowState Q) prior output s hz
      (fun input hi => actual_first_address_word Q s input ((fourierOutcomes_mem _ _).mp hi))

theorem clear_assigned_point (ws : List Wire) (input : List Bool) (s : BasisState)
    (hz : Clean ws s) (hd : ∀ v ∈ ws, v ∉ pointLogicalWires) (P : Point) :
    fourierClear ws.reverse (pointWrite P (phaseWordState ws input s)) = pointWrite P s := by
  funext v
  rw [fourierClear_apply]
  by_cases hv : v ∈ ws
  · have hp := hd v hv
    simp only [List.mem_reverse, hv, if_true, pointWrite, if_neg hp]
    exact (hz v hv).symm
  · simp only [List.mem_reverse, hv, if_false, pointWrite]
    split
    · rfl
    · exact phaseWordState_frame ws input s v hv

theorem assigned_window_digit (input : List Bool) (hi : input.length = streamAddress.length)
    (s : BasisState) :
    windowRawDigit 0 (phaseWordState streamAddress input s) = boolWordToNat input := by
  have ha (t : BasisState) : tableAddressValue streamAddress t = windowRawDigit 0 t := by
    simp [streamAddress, tableAddressValue, windowRawDigit, windowAddressBits, windowBankStart,
      List.range', wireValues, boolWordToNat]
    omega
  rw [← ha]
  have word := phaseWordState_word streamAddress (by decide +kernel) input hi s
  change boolWordToNat (wireValues streamAddress (phaseWordState streamAddress input s)) = _
  rw [word]


theorem phaseWordState_pointWrite (ws : List Wire) (hd : ∀ w ∈ ws, w ∉ pointLogicalWires)
    (input : List Bool) (P : Point) (s : BasisState) :
    phaseWordState ws input (pointWrite P s) = pointWrite P (phaseWordState ws input s) := by
  induction ws generalizing input s with
  | nil => rfl
  | cons w ws ih =>
    cases input with
    | nil => rfl
    | cons b input =>
      have he : (pointWrite P s)[w ↦ b] = pointWrite P (s[w ↦ b]) := by
        funext v
        have hw := hd w (by simp)
        by_cases hv : v = w
        · subst v; simp [pointWrite, hw, upd]
        · by_cases hp : v ∈ pointLogicalWires <;> simp [pointWrite, hp, upd, hv]
      simp only [phaseWordState, he]
      exact ih (fun v hv => hd v (List.mem_cons_of_mem w hv)) input _

theorem assigned_point_coordinates (input : List Bool) (s : BasisState) (P : Point) :
    pointStateCoordinates (phaseWordState streamAddress input (pointWrite P s)) = fig14PointEncoding P := by
  rw [phaseWordState_pointWrite streamAddress (by decide +kernel), pointWrite_coordinates]

noncomputable def windowDigitPoint (Q : Point) : OddWindow → Nat → Point
  | .left j, digit => signedTableOdd 32768 digit •
      ((2 ^ (16 * j.val)) • signedWindowHalfPoint G order)
  | .right j, digit => signedTableOdd 32768 digit •
      ((2 ^ (16 * j.val)) • signedWindowHalfPoint Q order)

theorem actual_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : BatchedPointReady s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualBatchedWindowState Q w s = pointWrite (P + windowDigitPoint Q w (windowRawDigit 0 s)) s := by
  cases w with
  | left j => exact actual_left_window_digit Q hQ hn j s hs P hP
  | right j => exact actual_right_window_digit Q hQ hn j s hs P hP

theorem actual_window_assigned_clear (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (P : Point) (s : BasisState) (hs : FirstWindowInput s)
    (hz : Clean streamAddress s) (input : List Bool) (hi : input.length = streamAddress.length) :
    fourierClear streamAddress.reverse
      (actualBatchedWindowState Q w (phaseWordState streamAddress input (pointWrite P s))) =
      pointWrite (P + windowDigitPoint Q w (boolWordToNat input)) s := by
  have hv : BatchedWindowValid (phaseWordState streamAddress input (pointWrite P s)) :=
    phaseWordState_preserves BatchedWindowValid streamAddress
      (fun t ht v hv b => batchedWindowValid_address_update t ht v hv b)
      input _ (firstWindowInput_pointWrite s hs P)
  have hc : Clean streamAddress (pointWrite P s) := by
    intro v hv
    have hp := (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hv
    simpa only [pointWrite, if_neg hp] using hz v hv
  rw [actual_window_digit Q hQ hn w _ hv.1 P (assigned_point_coordinates input s P),
    assigned_window_digit input hi,
    clear_assigned_point streamAddress input (pointWrite P s) hc (by decide +kernel)]
  funext v
  simp only [pointWrite]
  split <;> rfl

theorem actual_first_assigned_clear (Q : Point) (s : BasisState) (hz : Clean streamAddress s)
    (input : List Bool) (hi : input.length = streamAddress.length) :
    fourierClear streamAddress.reverse (actualFirstWindowState Q (phaseWordState streamAddress input s)) =
      pointWrite (axisWindowOffset G 16 + axisWindowOffset Q 13 +
        signedTableOdd 32768 (boolWordToNat input) •
          ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)) s := by
  rw [actual_first_window_digit, assigned_window_digit input hi,
    clear_assigned_point streamAddress input s hz (by decide +kernel)]

theorem actual_window_point_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (prior output : List Bool) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)
        (Quantum.run (streamAddress.map Gate.H) (ket (pointWrite P s)))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (P + windowDigitPoint Q w (boolWordToNat input)) s))).sum := by
  have hc : Clean streamAddress (pointWrite P s) := by
    intro v hv
    have hp := (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hv
    simpa only [pointWrite, if_neg hp] using hz v hv
  rw [actual_window_branch_sum Q hQ hn w prior output _
    (firstWindowInput_pointWrite s hs P) hc]
  apply congrArg (fun φ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) • φ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [actual_window_assigned_clear Q hQ hn w P s hs hz input
    (by simpa only [show streamAddress.length = 16 by decide +kernel] using (fourierOutcomes_mem 16 input).mp hi)]

theorem actual_first_point_sum (Q : Point) (prior output : List Bool)
    (s : BasisState) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (axisWindowOffset G 16 + axisWindowOffset Q 13 +
              signedTableOdd 32768 (boolWordToNat input) •
                ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)) s))).sum := by
  rw [actual_first_branch_sum Q prior output s hz]
  apply congrArg (fun φ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) • φ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [actual_first_assigned_clear Q s hz input
    (by simpa only [show streamAddress.length = 16 by decide +kernel] using (fourierOutcomes_mem 16 input).mp hi)]

/-- Fixed Fourier outputs for an axis, before the terminal event is selected. -/
noncomputable def actualAxisBranch (Q : Point) :
    List (OddWindow × List Bool) → List Bool → State →ₗ[ℂ] State
  | [], _ => LinearMap.id
  | (w, output) :: windows, prior =>
      (actualAxisBranch Q windows (output.reverse ++ prior)).comp
        ((fourierBranch .inverse streamAddress.reverse prior output).comp
          ((Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)).comp
            (Quantum.run (streamAddress.map Gate.H))))

/-- The exact coherent point-state sum, retaining interference between inputs. -/
noncomputable def pointAxisKernel (Q : Point) (s : BasisState) :
    List (OddWindow × List Bool) → List Bool → Point → State
  | [], _, P => ket (pointWrite P s)
  | (w, output) :: windows, prior, P =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            pointAxisKernel Q s windows (output.reverse ++ prior)
              (P + windowDigitPoint Q w (boolWordToNat input)))).sum

/-- Induction over the actual windows reduces execution to a coherent point sum;
there is no classical mixture over inputs and no exceptional-event loss. -/
theorem actualAxisBranch_point (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s)
    (windows : List (OddWindow × List Bool)) (prior : List Bool) (P : Point) :
    actualAxisBranch Q windows prior (ket (pointWrite P s)) =
      pointAxisKernel Q s windows prior P := by
  induction windows generalizing prior P with
  | nil => rfl
  | cons w windows ih =>
    simp only [actualAxisBranch, LinearMap.comp_apply]
    rw [actual_window_point_sum Q hQ hn w.1 prior w.2 P s hs hz]
    simp only [map_smul, map_list_sum, List.map_map, Function.comp_def, ih, pointAxisKernel]

noncomputable def windowOutputPaths : List OddWindow → List (List (OddWindow × List Bool))
  | [] => [[]]
  | w :: windows => (fourierOutcomes 16).flatMap (fun bits =>
      (windowOutputPaths windows).map (fun path => (w, bits) :: path))

theorem selectedIdealAxis_paths (Q : Point) (windows : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) :
    selectedIdealAxis Q windows prior terminal =
      (windowOutputPaths windows).flatMap (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).map (fun b =>
          InstrumentBranch.seq ⟨(path.map Prod.snd).flatten, actualAxisBranch Q path prior⟩ b)) := by
  induction windows generalizing prior with
  | nil =>
    simp only [selectedIdealAxis, windowOutputPaths, List.flatMap_cons, List.flatMap_nil,
      List.map_nil, List.flatten_nil, List.reverse_nil, List.nil_append, List.append_nil,
      actualAxisBranch]
    apply Eq.symm
    exact List.map_id' _
  | cons w windows ih =>
    simp only [selectedIdealAxis, fourierContinuationInstrument, ih, windowOutputPaths,
      List.map_flatMap, List.flatMap_map, List.flatMap_assoc, List.map_map,
      Function.comp_def, List.map_cons, List.flatten_cons, List.reverse_append,
      List.append_assoc, actualAxisBranch]
    apply List.flatMap_congr
    intro output ho
    apply List.flatMap_congr
    intro path hp
    apply List.map_congr_left
    intro b hb
    cases b
    simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem selectedIdealAxis_paths_mass (Q : Point) (windows : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) (ψ : State) :
    (selectedIdealAxis Q windows prior terminal).bornMass ψ =
      ((windowOutputPaths windows).map (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).bornMass
          (actualAxisBranch Q path prior ψ))).sum := by
  rw [selectedIdealAxis_paths]
  simp only [Instrument.bornMass, List.map_flatMap, List.map_map,
    Function.comp_def, InstrumentBranch.seq, LinearMap.comp_apply]
  generalize windowOutputPaths windows = paths
  induction paths with
  | nil => rfl
  | cons path paths ih =>
    simpa only [List.flatMap_cons, List.map_cons, List.sum_cons, List.sum_append] using
      congrArg (_ + ·) ih

theorem selectedIdealAxis_point_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (windows : List OddWindow) (prior : List Bool) (terminal : List Bool → Instrument)
    (P : Point) (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    (selectedIdealAxis Q windows prior terminal).bornMass (ket (pointWrite P s)) =
      ((windowOutputPaths windows).map (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).bornMass
          (pointAxisKernel Q s path prior P))).sum := by
  rw [selectedIdealAxis_paths_mass]
  simp only [actualAxisBranch_point Q hQ hn s hs hz]

end
end ShorECDLP.Paper2607_13816.ChallengeMigration
