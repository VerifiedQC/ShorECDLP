import ShorECDLP.Submission.«2607_13816».Challenge.ActualPair
import ShorECDLP.Framework.Quantum.AdaptiveFrame
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] streamAddress fourierOutcomes actualFirstSource actualOddSource fourierBranch Quantum.run
private theorem smul_support {V : BasisState → Prop} (c : ℂ) {ψ : State}
    (h : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply h s
  intro he
  exact hs (by simp [he])

/-- Continuation composition preserves reached-state predicates branch by branch. -/
theorem streamBlockContinuation_supported {V W : BasisState → Prop}
    (call : AdaptiveCircuit) (prior : List Bool) (next : List Bool → Instrument)
    (hcall : ∀ b ∈ call.run, ∀ ψ, SupportedOn V ψ → SupportedOn BatchedWindowValid (b.kraus ψ))
    (hnext : ∀ bits b, b ∈ next bits → ∀ ψ, SupportedOn BatchedWindowValid ψ → SupportedOn W (b.kraus ψ))
    (ψ : State) (hψ : SupportedOn V (Quantum.run (streamAddress.map Gate.H) ψ))
    (b : InstrumentBranch) (hb : b ∈ streamBlockContinuation call prior next) :
    SupportedOn W (b.kraus ψ) := by
  rw [streamBlockContinuation_eq] at hb
  have hu : (AdaptiveCircuit.unitary (streamAddress.map Gate.H) .done).run =
      [⟨List.nil, Quantum.run (streamAddress.map Gate.H)⟩] := AdaptiveCircuit.run_unitary_done _
  rw [hu] at hb
  simp only [Instrument.seq,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hb
  obtain ⟨bc,hbc,rfl⟩ := List.mem_map.mp hb
  obtain ⟨c,hc,hmap⟩ := List.mem_flatMap.mp hbc
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hmap
  rw [fourierContinuationInstrument] at hf
  obtain ⟨bits,hbits,hfm⟩ := List.mem_flatMap.mp hf
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hfm
  change SupportedOn W (d.kraus (fourierBranch .inverse streamAddress.reverse prior bits
    (c.kraus (Quantum.run (streamAddress.map Gate.H) ψ))))
  exact hnext bits d hd _ (batchedWindowValid_fourierBranch .inverse streamAddress.reverse
    (fun w hw => List.mem_reverse.mp hw) prior bits _ (hcall c hc _ hψ))

theorem actualSourceAxis_supported (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (ws : List OddWindow) (prior : List Bool) (next : List Bool → Instrument)
    (W : BasisState → Prop)
    (hnext : ∀ bits b, b ∈ next bits → ∀ ψ, SupportedOn BatchedWindowValid ψ → SupportedOn W (b.kraus ψ))
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ)
    (b : InstrumentBranch) (hb : b ∈ selectedSourceAxis (actualOddSource Q) ws prior next) :
    SupportedOn W (b.kraus ψ) := by
  induction ws generalizing prior ψ b with
  | nil => exact hnext prior b hb ψ hψ
  | cons w ws ih =>
    apply streamBlockContinuation_supported (V := BatchedWindowValid) (W := W) (actualOddSource Q w) prior _ ?_ ?_ ψ
      (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ) b hb
    · intro c hc φ hφ
      obtain ⟨a,ha⟩ := (actualOddSource_coherent Q hQ hn w).branch_coefficient c hc
      rw [ha.on_supported hφ]
      exact smul_support a (actualBatchedWindowState_supported Q hQ hn w φ hφ)
    · intro bits c hc φ hφ
      exact ih _ φ hφ c hc

theorem actualSourceTwoAxes_supported (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (left right : List OddWindow) (next : List Bool → List Bool → Instrument)
    (W : BasisState → Prop)
    (hnext : ∀ lhs rhs b, b ∈ next lhs rhs → ∀ ψ,
      SupportedOn BatchedWindowValid ψ → SupportedOn W (b.kraus ψ))
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ)
    (b : InstrumentBranch)
    (hb : b ∈ selectedSourceTwoAxes (actualFirstSource Q) (actualOddSource Q) left right next) :
    SupportedOn W (b.kraus ψ) := by
  apply streamBlockContinuation_supported (V := FirstWindowInput) (W := W)
    (actualFirstSource Q) List.nil _ ?_ ?_ ψ
    (firstWindowInput_prepare _ (fun _ h => h) ψ hψ) b hb
  · intro c hc φ hφ
    obtain ⟨a,ha⟩ := (actualFirstSource_coherent_input Q hQ).branch_coefficient c hc
    rw [ha.on_supported hφ]
    exact smul_support a (actualFirstWindowState_supported Q φ hφ)
  · intro bits c hc φ hφ
    apply actualSourceAxis_supported Q hQ hn left bits.reverse _ W ?_ φ hφ c hc
    intro lhs d hd χ hχ
    exact actualSourceAxis_supported Q hQ hn right List.nil _ W (hnext lhs) χ hχ d hd

theorem batchedReset_flag_absent : 837 ∉ batchedResetWires := by
  simp [batchedResetWires,resetWires]

theorem actualRoundTail_zeroFlag (b : InstrumentBranch)
    (hb : b ∈ (AdaptiveCircuit.unitary [.X 836]
      (measureResetWithCorrection batchedResetWires (fun _ => []))).run)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn (fun s => s 837=false) (b.kraus ψ) := by
  refine AdaptiveCircuit.branch_frame _ 837 false ?_ b hb ψ ?_
  · simp only [AdaptiveCircuit.wires,List.mem_append,not_or]
    constructor
    · simp [circuitWires,gateWires]
    · intro h
      exact batchedReset_flag_absent (resetRegister_support _ h)
  · intro s hs
    exact (hψ s hs).1.1.1.2.1

theorem actualAxesTail_zeroFlag (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (left right : List OddWindow) (b : InstrumentBranch)
    (hb : b ∈ selectedSourceTwoAxes (actualFirstSource Q) (actualOddSource Q) left right
      (fun _ _ => (AdaptiveCircuit.unitary [.X 836]
        (measureResetWithCorrection batchedResetWires (fun _ => []))).run)) :
    SupportedOn (fun s => s 837=false) (b.kraus (ket (zeroBasisState[836 ↦ true]))) := by
  exact actualSourceTwoAxes_supported Q hQ hn left right _ _
    (fun _ _ => actualRoundTail_zeroFlag) _
    (supportedOn_ket _ _ firstWindowInput_start) b hb

theorem actualRoundSource_zeroFlag (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    SupportedOn (fun s => s 837=false) (b.kraus (ket zeroBasisState)) := by
  rw [actualRoundSource,sourceOuterRound_streamAxis,actualLeftSources_indices,actualRightSources_indices] at hb
  rw [AdaptiveCircuit.run, ← selectedSourceTwoAxes_constant] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket (zeroBasisState[836 ↦ true]) := by
    simp [Quantum.run,applyGate_ket,onKet,zeroBasisState]
  change SupportedOn (fun s => s 837=false) (c.kraus (Quantum.run [.X 836] (ket zeroBasisState)))
  rw [hx]
  exact actualAxesTail_zeroFlag Q hQ hn leftOddIndices rightOddIndices c hc

theorem actualCompiledRound_zeroFlag (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run) :
    SupportedOn (fun s => s 837=false) (b.kraus (ket zeroBasisState)) := by
  rw [batchedOuterPlan_round_run Q hQ start history] at hb
  exact actualRoundSource_zeroFlag Q hQ hn b hb
end ShorECDLP.Paper2607_13816.ChallengeMigration
