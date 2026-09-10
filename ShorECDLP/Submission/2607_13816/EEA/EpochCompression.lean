import ShorECDLP.Submission.«2607_13816».EEA.Canonicalize
namespace ShorECDLP.Paper2607_13816
open _root_.ShorECDLP.Classical
attribute [local irreducible] canonicalWork2Rotation
noncomputable section
/-- The source terminal epoch transposition with the production negative control and one clean scratch wire. -/
def terminalEpochCompression : Circuit :=
  [.X 558] ++ (mcxVChain [541,559,558] (540 : Wire) ([560] : List Wire)) ++
  [.X 540] ++ (mcxVChain [540,559,558] (541 : Wire) ([560] : List Wire)) ++ [.X 540] ++
  [.X 540,.X 541] ++ (mcxVChain [540,541,558] (559 : Wire) ([560] : List Wire)) ++ [.X 541,.X 540] ++
  [.X 540] ++ (mcxVChain [540,559,558] (541 : Wire) ([560] : List Wire)) ++ [.X 540] ++
  (mcxVChain [541,559,558] (540 : Wire) ([560] : List Wire)) ++ [.X 558]
attribute [local irreducible] terminalEpochCompression
private def epochCompressionState (s : BasisState) : BasisState :=
  if !s 558 && ((s 540 && s 541 && s 559) || (!s 540 && !s 541 && !s 559)) then
    s[540 ↦ !s 540][541 ↦ !s 541][559 ↦ !s 559]
  else s
private theorem terminalEpochCompression_correct (s : BasisState) (hc : s 560=false) :
    run terminalEpochCompression s=epochCompressionState s := by
  funext w
  by_cases h0 : w=540
  · subst w
    cases h1 : s 540 <;> cases h2 : s 541 <;> cases h3 : s 559 <;> cases h4 : s 558 <;>
      simp [terminalEpochCompression,mcxVChain,mcxVChainTail,run,applyGate,upd,epochCompressionState,hc,h1,h2,h3,h4]
  by_cases h0 : w=541
  · subst w
    cases h1 : s 540 <;> cases h2 : s 541 <;> cases h3 : s 559 <;> cases h4 : s 558 <;>
      simp [terminalEpochCompression,mcxVChain,mcxVChainTail,run,applyGate,upd,epochCompressionState,hc,h1,h2,h3,h4]
  by_cases h0 : w=559
  · subst w
    cases h1 : s 540 <;> cases h2 : s 541 <;> cases h3 : s 559 <;> cases h4 : s 558 <;>
      simp [terminalEpochCompression,mcxVChain,mcxVChainTail,run,applyGate,upd,epochCompressionState,hc,h1,h2,h3,h4]
  by_cases h0 : w=558
  · subst w
    cases h1 : s 540 <;> cases h2 : s 541 <;> cases h3 : s 559 <;> cases h4 : s 558 <;>
      simp [terminalEpochCompression,mcxVChain,mcxVChainTail,run,applyGate,upd,epochCompressionState,hc,h1,h2,h3,h4]
  by_cases h0 : w=560
  · subst w
    cases h1 : s 540 <;> cases h2 : s 541 <;> cases h3 : s 559 <;> cases h4 : s 558 <;>
      simp [terminalEpochCompression,mcxVChain,mcxVChainTail,run,applyGate,upd,epochCompressionState,hc,h1,h2,h3,h4]
  simp_all [terminalEpochCompression,mcxVChain,mcxVChainTail,run,applyGate,epochCompressionState]
  split <;> simp_all [upd]
private theorem low_word_split (s : BasisState) :
    boolWordToNat (wireValues (List.range' 540 9) s)=
      (s 540).toNat+2*(s 541).toNat+4*boolWordToNat (wireValues (List.range' 542 7) s) := by
  change boolWordToNat (s 540::s 541::wireValues (List.range' 542 7) s)=_
  simp only [boolWordToNat_cons]
  ring
private theorem epochCompressionState_frame (s : BasisState) (w : Wire)
    (h : w∉[540,541,559]) : epochCompressionState s w=s w := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  unfold epochCompressionState
  split <;> simp [upd,h.1,h.2.1,h.2.2]
private theorem epochCompressionState_numeric (s : BasisState) (he : s 558=false) :
    (epochCompressionState s 559,boolWordToNat (wireValues (List.range' 540 9) (epochCompressionState s)))=
      compressBorrowedEpoch (s 559,boolWordToNat (wireValues (List.range' 540 9) s)) := by
  have htail : wireValues (List.range' 542 7) (epochCompressionState s)=
      wireValues (List.range' 542 7) s := by
    apply List.map_congr_left
    intro w hw
    exact epochCompressionState_frame s w ((by decide : ∀ w∈List.range' 542 7,w∉[540,541,559]) w hw)
  rw [low_word_split,low_word_split,htail]
  cases h0 : s 540 <;> cases h1 : s 541 <;> cases h2 : s 559 <;>
    simp [epochCompressionState,he,h0,h1,h2,upd,compressBorrowedEpoch,Nat.add_mod]
  omega
attribute [local irreducible] epochCompressionState
/-- The complete circuit implements the borrowed-epoch encoding and preserves all other wires. -/
theorem terminalEpochCompression_numeric (s : BasisState)
    (hc : s 560=false) (he : s 558=false) :
    let out := run terminalEpochCompression s
    (out 559,boolWordToNat (wireValues (List.range' 540 9) out))=
      compressBorrowedEpoch (s 559,boolWordToNat (wireValues (List.range' 540 9) s)) ∧
    ∀ w∉[540,541,559],out w=s w := by
  rw [terminalEpochCompression_correct s hc]
  exact ⟨epochCompressionState_numeric s he,epochCompressionState_frame s⟩
/-- Exact resources of the same terminal epoch compression circuit. -/
theorem terminalEpochCompression_resources :
    eeaToffoliCount terminalEpochCompression=15 ∧ eeaCnotCount terminalEpochCompression=0 ∧
    eeaXCount terminalEpochCompression=10 ∧ tCount terminalEpochCompression=105 ∧
    qubitCount terminalEpochCompression=5 := by decide +kernel
/-- The complete EEA and canonicalization prefix returns the borrowed epoch while retaining the canonical coefficient and clean scratch. -/
theorem secp256k1EEAForward_canonical_epoch (s : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) s)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p) :
    let initial := paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))
    let out := run (secp256k1EEAForwardUnitary indexedStepProductionRegisters ++
      canonicalWork2Rotation ++ terminalEpochCompression) (eeaPreprocessIdealState s)
    wireValues indexedStepProductionRegisters.work2 out=constantBits 259 (paperRun initial).tPrime ∧
    out 559=false ∧ IndexedStepReady indexedStepProductionRegisters out := by
  let initial := paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))
  let middle := run (secp256k1EEAForwardUnitary indexedStepProductionRegisters) (eeaPreprocessIdealState s)
  let canonical := run canonicalWork2Rotation middle
  have ht := secp256k1EEAForward_terminalState s hclean hx hxp
  have hd := secp256k1EEAForward_payload s hclean hx hxp
  have hc := canonicalWork2Rotation_correct (paperPadding initial)
    (secp256k1_paperPadding_le_596 hx hxp) middle ht (constantBits 259 (paperRun initial).tPrime) hd.2.1
  have h560 : canonical 560=false := (hc.2 _ (by decide)).trans (ht.ready _ (by decide))
  have h558 : canonical 558=false := (hc.2 _ (by decide)).trans (ht.ready _ (by decide))
  have hn := terminalEpochCompression_numeric canonical h560 h558
  have hlow : wireValues (List.range' 540 9) canonical=wireValues (List.range' 540 9) middle := by
    apply List.map_congr_left
    intro w hw
    exact hc.2 w ((by decide : ∀ w∈List.range' 540 9,w∉List.range' 263 259) w hw)
  have hepoch : canonical 559=terminalShiftEpoch (paperPadding initial) :=
    (hc.2 _ (by decide)).trans ht.epoch
  have hpair := hn.1
  have hlo : boolWordToNat (wireValues (List.range' 540 9) middle)=terminalShiftLow (paperPadding initial) := ht.low
  rw [hepoch,hlow,hlo] at hpair
  have hout : run (secp256k1EEAForwardUnitary indexedStepProductionRegisters ++
      canonicalWork2Rotation ++ terminalEpochCompression) (eeaPreprocessIdealState s)=
      run terminalEpochCompression canonical := by rw [run_append,run_append]
  dsimp only
  rw [hout]
  refine ⟨?_,(congrArg Prod.fst hpair).trans
    (compress_terminalShiftEpoch_fst (secp256k1_paperPadding_le_596 hx hxp) (paperPadding_dvd_four initial)),?_⟩
  · have hbank : wireValues indexedStepProductionRegisters.work2 (run terminalEpochCompression canonical)=
        wireValues indexedStepProductionRegisters.work2 canonical := by
      apply List.map_congr_left
      intro w hw
      apply hn.2 w
      change w∈List.range' 263 259 at hw
      obtain ⟨i,hi,he⟩ := List.mem_range'.mp hw
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      dsimp only [Wire] at *
      omega
    exact hbank.trans hc.1
  · intro w hw
    have hcompress := hn.2 w ((by decide : ∀ w∈indexedStepProductionRegisters.sharedScratch,w∉[540,541,559]) w hw)
    have hcanonical := hc.2 w ((by decide : ∀ w∈indexedStepProductionRegisters.sharedScratch,w∉List.range' 263 259) w hw)
    exact hcompress.trans (hcanonical.trans (ht.ready w hw))

end
end ShorECDLP.Paper2607_13816
