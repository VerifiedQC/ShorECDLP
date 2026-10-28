import ShorECDLP.Submission.«2607_13816».Challenge.FixedWord
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

noncomputable def taggedSourceAxis (call : OddWindow → AdaptiveCircuit) :
    List OddWindow → List Bool → List (List Bool × InstrumentBranch)
  | [], prior => [(prior,⟨[],LinearMap.id⟩)]
  | w :: ws, prior => (streamBlockOutcomes (call w) prior).flatMap (fun a =>
      (taggedSourceAxis call ws (a.1.reverse ++ prior)).map (fun b => (b.1,a.2.seq b.2)))

theorem selectedSourceAxis_tagged (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow) (prior : List Bool) (terminal : List Bool → Instrument) :
    selectedSourceAxis call ws prior terminal =
      (taggedSourceAxis call ws prior).flatMap (fun a =>
        (terminal a.1).map a.2.seq) := by
  induction ws generalizing prior with
  | nil =>
    simp only [selectedSourceAxis,taggedSourceAxis,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    have he : (InstrumentBranch.seq ⟨[],LinearMap.id⟩) = (fun b => b) := by
      funext b
      cases b
      simp [InstrumentBranch.seq]
    rw [he,List.map_id']
  | cons w ws ih =>
    simp only [selectedSourceAxis,streamBlockContinuation,taggedSourceAxis,ih,
      List.flatMap_assoc,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    apply List.flatMap_congr
    intro b hb
    apply List.map_congr_left
    intro c hc
    cases a with | mk atag a =>
      cases b with | mk btag b =>
        cases a; cases b; cases c
        simp only [InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]

theorem streamBlockOutcomes_split (call : AdaptiveCircuit) (count : Nat)
    (hcount : ∀ b ∈ call.run, b.history.length = count) (prior : List Bool)
    (tagged : List Bool × InstrumentBranch) (ht : tagged ∈ streamBlockOutcomes call prior) :
    ∃ a : List Bool, a.length = count ∧ tagged.1.length = 16 ∧
      tagged.2.history = a ++ tagged.1 := by
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp ht
  have hl : bs.length = 16 := by
    simpa only [streamAddress,List.length_range'] using
      (fourierOutcomes_mem streamAddress.length bs).mp hbs
  simp only [AdaptiveCircuit.seq,AdaptiveCircuit.run] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact ⟨b.history,hcount b hb,hl,rfl⟩

theorem taggedSourceAxis_transcript (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow)
    (hcount : ∀ w ∈ ws, ∀ b ∈ (call w).run, b.history.length = (actualBatchedWindow w).count)
    (prior : List Bool) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedSourceAxis call ws prior) :
    ∃ bits, AxisTranscript (ws.map actualBatchedWindow) tagged.2.history bits ∧
      tagged.1 = bits.reverse ++ prior := by
  induction ws generalizing prior tagged with
  | nil =>
    simp only [taggedSourceAxis,List.mem_singleton] at ht
    subst tagged
    exact ⟨[],AxisTranscript.nil,rfl⟩
  | cons w ws ih =>
    obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    obtain ⟨ar,har,hbits,hhist⟩ := streamBlockOutcomes_split (call w) _ (hcount w (by simp)) prior a ha
    obtain ⟨bits,htrans,hprior⟩ := ih (fun v hv => hcount v (List.mem_cons_of_mem w hv)) _ b hb
    refine ⟨a.1 ++ bits,?_,?_⟩
    · simpa only [List.map_cons,InstrumentBranch.seq,hhist,List.append_assoc] using
        AxisTranscript.cons (actualBatchedWindow w) (ws.map actualBatchedWindow)
          ar a.1 b.2.history bits har hbits htrans
    · simpa only [List.reverse_append,List.append_assoc] using hprior

theorem actualOddSource_history_length (Q : Point) (hQ : order • Q = 0) (w : OddWindow)
    (b : InstrumentBranch) (hb : b ∈ (actualOddSource Q w).run) :
    b.history.length = (actualBatchedWindow w).count := by
  have he := actualBatchedWindow_run w 0 Q hQ Fin.elim0
  change _ = (actualOddSource Q w).run at he
  rw [← he] at hb
  simpa only [Nat.zero_add,Nat.sub_zero] using
    straight_history_length ((actualBatchedWindow w).program 0) (readConstant coefficientAt Q) Fin.elim0 b hb


/-- Fixed positions read the same Fourier tag used by selectedSourceAxis, not arithmetic records. -/
theorem taggedSourceAxis_readWord (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow)
    (hcount : ∀ w ∈ ws, ∀ b ∈ (call w).run, b.history.length = (actualBatchedWindow w).count)
    (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedSourceAxis call ws List.nil)
    (before after : List Bool) :
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (ws.map actualBatchedWindow) before.length) =
        some (fourierWordLSB tagged.1.reverse) := by
  obtain ⟨bits,htrans,htag⟩ := taggedSourceAxis_transcript call ws hcount List.nil tagged ht
  rw [htag,List.append_nil,List.reverse_reverse]
  exact htrans.readWord before after

theorem actualTaggedAxis_readWord (Q : Point) (hQ : order • Q = 0)
    (ws : List OddWindow) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedSourceAxis (actualOddSource Q) ws List.nil)
    (before after : List Bool) :
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (ws.map actualBatchedWindow) before.length) =
        some (fourierWordLSB tagged.1.reverse) :=
  taggedSourceAxis_readWord _ ws (fun w _ b hb => actualOddSource_history_length Q hQ w b hb)
    tagged ht before after


/-- Event filtering by fixed record positions is exactly Fourier-tag selection. -/
theorem selectedSourceAxis_fixed_filter (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow)
    (hcount : ∀ w ∈ ws, ∀ b ∈ (call w).run, b.history.length = (actualBatchedWindow w).count)
    (tail : AdaptiveCircuit) (accept : Nat → Bool) :
    selectedSourceAxis call ws List.nil
      (fun tag => if accept (fourierWordLSB tag.reverse) then tail.run else []) =
      (streamAxis (ws.map call) List.nil tail).run.filter
        (fun b => (readWord b.history (axisPositions (ws.map actualBatchedWindow) 0)).any accept) := by
  rw [← selectedSourceAxis_constant call ws List.nil tail]
  rw [selectedSourceAxis_tagged,selectedSourceAxis_tagged,List.filter_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hp (b : InstrumentBranch) :
      (readWord (a.2.seq b).history (axisPositions (ws.map actualBatchedWindow) 0)).any accept =
        accept (fourierWordLSB a.1.reverse) := by
    have h := taggedSourceAxis_readWord call ws hcount a ha List.nil b.history
    change (readWord (a.2.history ++ b.history) _).any accept = _
    simpa only [List.nil_append,List.length_nil,Option.any_some] using congrArg (fun x => x.any accept) h
  rw [List.filter_map]
  simp only [Function.comp_def,hp]
  split <;> simp_all
end ShorECDLP.Paper2607_13816.ChallengeMigration
