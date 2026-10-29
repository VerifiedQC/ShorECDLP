import ShorECDLP.Submission.«2607_13816».Challenge.FirstValidity
import ShorECDLP.Submission.«2607_13816».Challenge.ActualExecution
import ShorECDLP.Submission.«2607_13816».Challenge.AxisProbability
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

theorem selectedIdealAxis_terminal_congr (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (ws : List OddWindow) (prior : List Bool)
    (terminal terminal' : List Bool → Instrument)
    (he : ∀ prior ψ, SupportedOn BatchedWindowValid ψ →
      (terminal prior).bornMass ψ = (terminal' prior).bornMass ψ)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    (selectedIdealAxis Q ws prior terminal).bornMass ψ =
      (selectedIdealAxis Q ws prior terminal').bornMass ψ := by
  induction ws generalizing prior ψ with
  | nil => exact he prior ψ hψ
  | cons w ws ih =>
    rw [selectedIdealAxis_cons_mass,selectedIdealAxis_cons_mass]
    apply fourierContinuationInstrument_mass_congr
    intro bits _
    apply ih
    apply batchedWindowValid_fourierBranch
    · intro v hv; simpa only [List.mem_reverse] using hv
    · exact actualBatchedWindowState_supported Q hQ hn w _
        (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ)

theorem selectedSourceAxis_terminal_congr (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (call : OddWindow → AdaptiveCircuit) (ws : List OddWindow)
    (hcall : ∀ w ∈ ws, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid)
    (prior : List Bool) (terminal terminal' : List Bool → Instrument)
    (he : ∀ prior ψ, SupportedOn BatchedWindowValid ψ →
      (terminal prior).bornMass ψ = (terminal' prior).bornMass ψ)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    (selectedSourceAxis call ws prior terminal).bornMass ψ =
      (selectedIdealAxis Q ws prior terminal').bornMass ψ := by
  rw [selectedSourceAxis_mass Q hQ hn call ws hcall prior terminal ψ hψ]
  exact selectedIdealAxis_terminal_congr Q hQ hn ws prior terminal terminal' he ψ hψ

noncomputable def selectedSourceTwoAxes (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  streamBlockContinuation first List.nil (fun bits =>
    selectedSourceAxis call left bits.reverse (fun lhs =>
      selectedSourceAxis call right List.nil (terminal lhs)))

noncomputable def selectedIdealTwoAxes (Q : Point) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  (fourierContinuationInstrument List.nil (fun bits =>
    selectedIdealAxis Q left bits.reverse (fun lhs =>
      selectedIdealAxis Q right List.nil (terminal lhs)))).map
    (fun b => InstrumentBranch.seq
      ⟨List.nil, (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)).comp
        (Quantum.run (streamAddress.map Gate.H))⟩ b)

/-- Exact selected-event probability for both axes, with Fourier history reset between axes. -/
theorem selectedSourceTwoAxes_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (first : AdaptiveCircuit)
    (hfirst : CoherentlyImplementsOn first
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)) FirstWindowInput)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (hcall : ∀ w ∈ left ++ right, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid)
    (terminal : List Bool → List Bool → Instrument)
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ) :
    (selectedSourceTwoAxes first call left right terminal).bornMass ψ =
      (selectedIdealTwoAxes Q left right terminal).bornMass ψ := by
  rw [selectedSourceTwoAxes,streamBlockContinuation_mass hfirst _ _ _
    (firstWindowInput_prepare _ (fun _ h => h) ψ hψ)]
  have hm : (selectedIdealTwoAxes Q left right terminal).bornMass ψ =
      (fourierContinuationInstrument List.nil (fun bits =>
        selectedIdealAxis Q left bits.reverse (fun lhs =>
          selectedIdealAxis Q right List.nil (terminal lhs)))).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
    simp only [selectedIdealTwoAxes,Instrument.bornMass,List.map_map,Function.comp_def,
      InstrumentBranch.seq,LinearMap.comp_apply]
  rw [hm]
  apply fourierContinuationInstrument_mass_congr
  intro bits _
  apply selectedSourceAxis_terminal_congr Q hQ hn call left
    (fun w hw => hcall w (List.mem_append_left _ hw))
  · intro lhs φ hφ
    exact selectedSourceAxis_mass Q hQ hn call right
      (fun w hw => hcall w (List.mem_append_right _ hw)) List.nil (terminal lhs) φ hφ
  · apply batchedWindowValid_fourierBranch
    · intro v hv; simpa only [List.mem_reverse] using hv
    · exact actualFirstWindowState_supported Q _
        (firstWindowInput_prepare _ (fun _ h => h) ψ hψ)



theorem selectedSourceTwoAxes_constant (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (tail : AdaptiveCircuit) :
    selectedSourceTwoAxes first call left right (fun _ _ => tail.run) =
      (streamAxis (first :: left.map call) List.nil
        (streamAxis (right.map call) List.nil tail)).run := by
  simp only [selectedSourceTwoAxes,selectedSourceAxis_constant,
    streamAxis_cons_run,streamBlockContinuation,List.append_nil]

theorem actualOddSource_coherent (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) :
    CoherentlyImplementsOn (actualOddSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid := by
  have h := actualBatchedWindow_coherent Q hQ hn w 0 Fin.elim0
  unfold CoherentlyImplementsOn at h ⊢
  rw [actualBatchedWindow_run w 0 Q hQ Fin.elim0] at h
  exact h

theorem actualFirstSource_coherent_input (Q : Point) (hQ : order • Q = 0) :
    CoherentlyImplementsOn (actualFirstSource Q)
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)) FirstWindowInput := by
  have h := actualFirstWindow_coherent_input Q hQ 0 Fin.elim0
  unfold CoherentlyImplementsOn at h ⊢
  rw [actualFirstWindow_run 0 Q hQ Fin.elim0] at h
  exact h

theorem actualSourcesTwoAxes_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (left right : List OddWindow) (terminal : List Bool → List Bool → Instrument) :
    (selectedSourceTwoAxes (actualFirstSource Q) (actualOddSource Q) left right terminal).bornMass
      (ket (zeroBasisState[836 ↦ true])) =
    (selectedIdealTwoAxes Q left right terminal).bornMass (ket (zeroBasisState[836 ↦ true])) :=
  selectedSourceTwoAxes_mass Q hQ hn _ (actualFirstSource_coherent_input Q hQ)
    _ left right (fun w _ => actualOddSource_coherent Q hQ hn w) terminal _
    (supportedOn_ket _ _ firstWindowInput_start)
end ShorECDLP.Paper2607_13816.ChallengeMigration
