import ShorECDLP.Submission.«2607_13816».Challenge.TaggedAxis
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

theorem AxisTranscript.history_length {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits) :
    history.length = axisCount ws := by
  induction h with
  | nil => rfl
  | cons w ws a bs rest out ha hb ht ih =>
    simp only [List.length_append,ha,hb,ih,axisCount]

noncomputable def taggedSourceTwoAxes (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow) :
    List ((List Bool × List Bool) × InstrumentBranch) :=
  (streamBlockOutcomes first List.nil).flatMap (fun a =>
    (taggedSourceAxis call left a.1.reverse).flatMap (fun l =>
      (taggedSourceAxis call right List.nil).map (fun r => ((l.1,r.1),a.2.seq (l.2.seq r.2)))))

theorem selectedSourceTwoAxes_tagged (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) :
    selectedSourceTwoAxes first call left right terminal =
      (taggedSourceTwoAxes first call left right).flatMap (fun a =>
        (terminal a.1.1 a.1.2).map a.2.seq) := by
  simp only [selectedSourceTwoAxes,streamBlockContinuation,selectedSourceAxis_tagged,
    taggedSourceTwoAxes,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,
    List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro l hl
  apply List.flatMap_congr
  intro r hr
  apply List.map_congr_left
  intro b hb
  rcases a with ⟨atag,a⟩; rcases l with ⟨lt,l⟩; rcases r with ⟨rt,r⟩
  cases a; cases l; cases r; cases b
  simp only [InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]

theorem taggedSourceTwoAxes_readWords (first : AdaptiveCircuit)
    (hfirst : ∀ b ∈ first.run, b.history.length = actualFirstWindow.count)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (hcall : ∀ w ∈ left ++ right, ∀ b ∈ (call w).run,
      b.history.length = (actualBatchedWindow w).count)
    (tagged : (List Bool × List Bool) × InstrumentBranch)
    (ht : tagged ∈ taggedSourceTwoAxes first call left right) (before after : List Bool) :
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) before.length) =
        some (fourierWordLSB tagged.1.1.reverse) ∧
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (right.map actualBatchedWindow)
        (before.length + axisCount (actualFirstWindow :: left.map actualBatchedWindow))) =
        some (fourierWordLSB tagged.1.2.reverse) := by
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨l,hl,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ht
  obtain ⟨ar,har,hbs,hah⟩ := streamBlockOutcomes_split first _ hfirst List.nil a ha
  obtain ⟨lbs,hlt,hltag⟩ := taggedSourceAxis_transcript call left
    (fun w hw => hcall w (List.mem_append_left _ hw)) a.1.reverse l hl
  obtain ⟨rbs,hrt,hrtag⟩ := taggedSourceAxis_transcript call right
    (fun w hw => hcall w (List.mem_append_right _ hw)) List.nil r hr
  have hleft : AxisTranscript (actualFirstWindow :: left.map actualBatchedWindow)
      (a.2.history ++ l.2.history) (a.1 ++ lbs) := by
    rw [hah]
    exact AxisTranscript.cons _ _ ar a.1 l.2.history lbs har hbs hlt
  have hlword := hleft.readWord before (r.2.history ++ after)
  have hrword := hrt.readWord (before ++ a.2.history ++ l.2.history) after
  have hllength := hleft.history_length
  constructor
  · simpa only [InstrumentBranch.seq,List.append_assoc,hltag,← List.reverse_append,
      List.reverse_reverse] using hlword
  · have he : (before ++ a.2.history ++ l.2.history).length =
        before.length + axisCount (actualFirstWindow :: left.map actualBatchedWindow) := by
      simpa only [List.length_append,Nat.add_assoc] using congrArg (before.length + ·) hllength
    rw [he] at hrword
    simpa only [InstrumentBranch.seq,List.append_assoc,hrtag,List.append_nil,
      List.reverse_reverse] using hrword

theorem actualFirstSource_history_length (Q : Point) (hQ : order • Q = 0)
    (b : InstrumentBranch) (hb : b ∈ (actualFirstSource Q).run) :
    b.history.length = actualFirstWindow.count := by
  have he := actualFirstWindow_run 0 Q hQ Fin.elim0
  change _ = (actualFirstSource Q).run at he
  rw [← he] at hb
  simpa only [Nat.zero_add,Nat.sub_zero] using
    straight_history_length (actualFirstWindow.program 0) (readConstant coefficientAt Q) Fin.elim0 b hb


/-- Select a pair of evaluator words, rejecting either missing word. -/
def fixedPairAccept (left right : List Nat) (accept : Nat → Nat → Bool)
    (history : List Bool) : Bool :=
  ((readWord history left).bind (fun lhs => (readWord history right).map (accept lhs))).getD false

theorem selectedSourceTwoAxes_fixed_filter (first : AdaptiveCircuit)
    (hfirst : ∀ b ∈ first.run, b.history.length = actualFirstWindow.count)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (hcall : ∀ w ∈ left ++ right, ∀ b ∈ (call w).run,
      b.history.length = (actualBatchedWindow w).count)
    (tail : AdaptiveCircuit) (accept : Nat → Nat → Bool) :
    selectedSourceTwoAxes first call left right (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then tail.run else []) =
      (streamAxis (first :: left.map call) List.nil
        (streamAxis (right.map call) List.nil tail)).run.filter (fun (b : InstrumentBranch) =>
          fixedPairAccept (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) 0)
            (axisPositions (right.map actualBatchedWindow)
              (axisCount (actualFirstWindow :: left.map actualBatchedWindow))) accept b.history) := by
  rw [← selectedSourceTwoAxes_constant first call left right tail]
  rw [selectedSourceTwoAxes_tagged,selectedSourceTwoAxes_tagged,List.filter_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hp (b : InstrumentBranch) :
      fixedPairAccept (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) 0)
        (axisPositions (right.map actualBatchedWindow)
          (axisCount (actualFirstWindow :: left.map actualBatchedWindow))) accept (a.2.seq b).history =
      accept (fourierWordLSB a.1.1.reverse) (fourierWordLSB a.1.2.reverse) := by
    have h := taggedSourceTwoAxes_readWords first hfirst call left right hcall a ha List.nil b.history
    simp only [List.nil_append,List.length_nil,Nat.zero_add] at h
    simp only [fixedPairAccept,InstrumentBranch.seq,h.1,h.2,Option.bind_some,
      Option.map_some,Option.getD_some]
  rw [List.filter_map]
  simp only [Function.comp_def,hp]
  split <;> simp_all

/-- The same two fixed words drive event selection on the actual source and on its ideal image. -/
theorem actualSources_fixedPair_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (left right : List OddWindow) (tail : AdaptiveCircuit) (accept : Nat → Nat → Bool) :
    Instrument.bornMass ((streamAxis (actualFirstSource Q :: left.map (actualOddSource Q)) List.nil
      (streamAxis (right.map (actualOddSource Q)) List.nil tail)).run.filter (fun (b : InstrumentBranch) =>
        fixedPairAccept (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) 0)
          (axisPositions (right.map actualBatchedWindow)
            (axisCount (actualFirstWindow :: left.map actualBatchedWindow))) accept b.history))
      (ket (zeroBasisState[836 ↦ true])) =
    (selectedIdealTwoAxes Q left right (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then tail.run else [])).bornMass
      (ket (zeroBasisState[836 ↦ true])) := by
  rw [← selectedSourceTwoAxes_fixed_filter (actualFirstSource Q)
    (fun b hb => actualFirstSource_history_length Q hQ b hb) (actualOddSource Q) left right
    (fun w _ b hb => actualOddSource_history_length Q hQ w b hb) tail accept]
  exact actualSourcesTwoAxes_mass Q hQ hn left right _
end ShorECDLP.Paper2607_13816.ChallengeMigration
