import ShorECDLP.Submission.«2607_13816».EEA.ParityCorrection
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
attribute [local irreducible] canonicalWork2Rotation terminalEpochCompression secp256k1EEAForwardUnitary eeaPreprocessIdealState
noncomputable section
/-- The source terminal Work1 clearing stream, including the high remainder bit. -/
def terminalWork1Clear : Circuit := xorConstant (List.range' 4 259) (ShorECDLP.p+2^258)
/-- The known terminal packing is cleared and every other wire is preserved. -/
theorem terminalWork1Clear_correct (s : BasisState)
    (hb : wireValues (List.range' 4 259) s=constantBits 259 (ShorECDLP.p+2^258)) :
    Clean (List.range' 4 259) (run terminalWork1Clear s) ∧
    ∀ w∉List.range' 4 259,run terminalWork1Clear s w=s w := by
  have h := xorConstant_correct (List.range' 4 259) (ShorECDLP.p+2^258) s List.nodup_range'
  have hz : xorConstantBits (constantBits 259 (ShorECDLP.p+2^258)) (ShorECDLP.p+2^258)=
      List.replicate 259 false := by decide +kernel
  have hout := h.1
  rw [hb,hz] at hout
  refine ⟨?_,h.2⟩
  intro w hw
  have hm : run terminalWork1Clear s w∈wireValues (List.range' 4 259) (run terminalWork1Clear s) := List.mem_map.mpr ⟨w,hw,rfl⟩
  change wireValues (List.range' 4 259) (run terminalWork1Clear s)=List.replicate 259 false at hout
  rw [hout] at hm
  exact (List.mem_replicate.mp hm).2
/-- Exact resources of the same terminal clearing circuit. -/
theorem terminalWork1Clear_resources : eeaToffoliCount terminalWork1Clear=0 ∧
    eeaCnotCount terminalWork1Clear=0 ∧ eeaXCount terminalWork1Clear=251 ∧
    tCount terminalWork1Clear=0 ∧ qubitCount terminalWork1Clear=251 := by decide +kernel

private theorem terminalWork1_packed (s : BasisState)
    (hclean : Clean (List.range' 0 263++List.range' 519 61) s)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) s)<ShorECDLP.p) :
    let before := run (secp256k1EEAForwardUnitary indexedStepProductionRegisters ++
      canonicalWork2Rotation ++ terminalEpochCompression) (eeaPreprocessIdealState s)
    wireValues (List.range' 4 259) (secp256k1EEAParityIdealState before)=
      constantBits 259 (ShorECDLP.p+2^258) := by
  let initial := paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))
  let middle := run (secp256k1EEAForwardUnitary indexedStepProductionRegisters) (eeaPreprocessIdealState s)
  let canonical := run canonicalWork2Rotation middle
  let before := run terminalEpochCompression canonical
  have hcan := secp256k1EEAForward_canonical_coefficient s hclean hx hxp
  have hterm := paperRun_terminal ShorECDLP.Secp256k1.p_prime hx hxp
  have hbank : wireValues (List.range' 4 259) canonical=constantBits 259 (ShorECDLP.p+2^258) := by
    have hb := hcan.1
    dsimp only at hterm
    rcases hterm with ⟨_,hr,ht,hq,hlq,_,_,_,hlt,_⟩
    rw [hlt,ht,hlq,hq,hr] at hb
    have hsize : ShorECDLP.p.size=256 := by decide +kernel
    rw [hsize] at hb
    have hpacked : constantBits 256 ShorECDLP.p ++ [false] ++ (constantBits 0 0).reverse ++
        (constantBits 2 1).reverse=constantBits 259 (ShorECDLP.p+2^258) := by decide +kernel
    have hb' : wireValues (List.range' 4 259) canonical=constantBits 256 ShorECDLP.p ++ [false] ++
        (constantBits 0 0).reverse ++ (constantBits 2 1).reverse := by
      simpa only [Classical.run_append] using hb
    exact hb'.trans hpacked
  have ht := secp256k1EEAForward_terminalState s hclean hx hxp
  have hc := canonicalWork2Rotation_correct (paperPadding initial)
    (secp256k1_paperPadding_le_596 hx hxp) middle ht _ (secp256k1EEAForward_payload s hclean hx hxp).2.1
  have hcompression := terminalEpochCompression_numeric canonical
    ((hc.2 560 (by decide)).trans (ht.ready _ (by decide)))
    ((hc.2 558 (by decide)).trans (ht.ready _ (by decide)))
  have hframe : wireValues (List.range' 4 259) (secp256k1EEAParityIdealState before)=
      wireValues (List.range' 4 259) canonical := by
    apply List.map_congr_left
    intro w hw
    have hwi : w∉List.range' 263 256 := by
      intro hm
      obtain ⟨i,hi,he⟩ := List.mem_range'.mp hw
      obtain ⟨j,hj,hf⟩ := List.mem_range'.mp hm
      dsimp only [Wire] at *
      omega
    have hwc : w∉[540,541,559] := by
      obtain ⟨i,hi,he⟩ := List.mem_range'.mp hw
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      dsimp only [Wire] at *
      omega
    exact (secp256k1EEAParityIdealState_preservesOutside before w hwi).trans (hcompression.2 w hwc)
  dsimp only
  rw [Classical.run_append,Classical.run_append]
  exact hframe.trans hbank

/-- The full arithmetic output state through terminal Work1 clearing. -/
def secp256k1EEAOutputIdealState (s : BasisState) : BasisState :=
  run terminalWork1Clear (secp256k1EEAParityIdealState
    (run (secp256k1EEAForwardUnitary indexedStepProductionRegisters ++
      canonicalWork2Rotation ++ terminalEpochCompression) (eeaPreprocessIdealState s)))
/-- The completed arithmetic wrapper exposes the inverse with Work1, epoch, and shared scratch cleared. -/
theorem secp256k1EEAOutputIdealState_correct (s : BasisState)
    (hclean : Clean (List.range' 0 263++List.range' 519 61) s)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) s)<ShorECDLP.p) :
    let out := secp256k1EEAOutputIdealState s
    boolWordToNat (wireValues (List.range' 263 256) out)=
      paperInverse ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s)) ∧
    (boolWordToNat (wireValues (List.range' 263 256) out) : ZMod ShorECDLP.p) *
      (boolWordToNat (wireValues (List.range' 263 256) s) : ZMod ShorECDLP.p)=1 ∧
    Clean (List.range' 4 259) out ∧ out 559=false ∧ IndexedStepReady indexedStepProductionRegisters out := by
  let before := secp256k1EEAParityIdealState
    (run (secp256k1EEAForwardUnitary indexedStepProductionRegisters ++
      canonicalWork2Rotation ++ terminalEpochCompression) (eeaPreprocessIdealState s))
  have hb := terminalWork1_packed s hclean hx hxp
  have hc := terminalWork1Clear_correct before hb
  have hi := secp256k1EEAParity_inverse s hclean hx hxp
  have hframe : wireValues (List.range' 263 256) (secp256k1EEAOutputIdealState s)=
      wireValues (List.range' 263 256) before := by
    apply List.map_congr_left
    intro w hw
    apply hc.2 w
    intro hm
    obtain ⟨i,hi,he⟩ := List.mem_range'.mp hw
    obtain ⟨j,hj,hf⟩ := List.mem_range'.mp hm
    dsimp only [Wire] at *
    omega
  refine ⟨(congrArg boolWordToNat hframe).trans hi.1,?_,hc.1,
    (hc.2 559 (by decide)).trans hi.2.2.1,?_⟩
  · rw [hframe]
    exact hi.2.1
  · intro w hw
    exact (hc.2 w ((by decide : ∀ w∈indexedStepProductionRegisters.sharedScratch,w∉List.range' 4 259) w hw)).trans
      (hi.2.2.2 w hw)

end
end ShorECDLP.Paper2607_13816
