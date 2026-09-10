import ShorECDLP.Submission.«2607_13816».EEA.ProductionRun
import ShorECDLP.Submission.«2607_13816».EEA.InitialPacked
namespace ShorECDLP.Paper2607_13816
open Classical
attribute [local irreducible] eeaPreprocessIdealState correctedInput
/-- Preprocessing establishes the complete packed input required by the actual active run. -/
theorem eeaPreprocess_initial_packed (s : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) s)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p) :
    IndexedPackedState indexedStepProductionRegisters 256 (eeaPreprocessIdealState s)
      (paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))) := by
  have hb := eeaPreprocess_initial_workBanks s hclean hx hxp
  have hm := eeaPreprocess_initial_metadata s hclean hx hxp
  have hc := eeaPreprocessIdealState_correct s hclean hx hxp
  dsimp only at hb hm hc
  rw [show (2^256-2^32-977:Nat)=ShorECDLP.p from rfl] at hb hm
  change _ ∧ _ at hb
  let x := boolWordToNat (wireValues (List.range' 263 256) s)
  have hrpos : 0<(correctedInput ShorECDLP.p x).size :=
    Nat.size_pos.mpr (correctedInput_pos hx hxp)
  have hsize : ShorECDLP.p.size=256 := by
    have hlo := Nat.lt_size.mpr (show 2^255≤ShorECDLP.p by decide)
    have hhi := Nat.size_le.mpr (show ShorECDLP.p<2^256 by decide)
    omega
  change IndexedPackedState _ _ _ (paperInitial ShorECDLP.p x)
  constructor
  · simpa only [indexedStepProductionRegisters,packedView,hsize,paperInitial,Nat.reduceAdd,
      Nat.sub_zero,Nat.add_zero] using hb.1
  · simpa only [indexedStepProductionRegisters,packedView,hsize,paperInitial,Nat.reduceAdd,
      List.rotate_zero] using hb.2
  · change boolWordToNat (wireValues (List.range' 522 9) _)=_
    rw [hm.2.2.2.1]
    norm_num [paperInitial,boolWordToNat_constantBits]
    rfl
  · change boolWordToNat (wireValues (List.range' 531 9) _)=_
    rw [hm.2.2.2.2.1]
    norm_num [paperInitial,boolWordToNat_constantBits]
    rfl
  · change boolWordToNat (wireValues (List.range' 549 9) _)=_
    rw [hm.2.2.2.2.2.2]
    change boolWordToNat (constantBits 9 ((correctedInput ShorECDLP.p x).size-1))=truthMinusOneValue 9 (correctedInput ShorECDLP.p x).size
    rw [boolWordToNat_constantBits]
    change ((correctedInput ShorECDLP.p x).size-1)%512=((correctedInput ShorECDLP.p x).size+512-1)%512
    have he : (correctedInput ShorECDLP.p x).size+512-1=(correctedInput ShorECDLP.p x).size-1+512 := by omega
    rw [he,Nat.add_mod_right]
  · change boolWordToNat (wireValues (List.range' 540 9) _)=_
    rw [hm.2.2.2.2.2.1]
    norm_num [paperInitial,boolWordToNat_constantBits]
    rfl
  · exact congrArg Prod.fst hm.1
  · exact congrArg Prod.snd hm.1
  · exact hm.2.1
  · exact hm.2.2.1
  · intro w hw
    exact hc.2.2.2.2.2.2.2.2.2.2.2.2.1 w
      (by simp only [List.mem_append]; exact Or.inr hw)
/-- Preprocessing supplies the packed input for the complete actual active EEA schedule. -/
theorem eeaPreprocess_active_paperRun (s : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) s)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p) :
    let initial := paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))
    IndexedPackedState indexedStepProductionRegisters 256
      (run (indexedScheduleUnitary indexedStepProductionRegisters 256 1 (paperMicrosteps initial))
        (eeaPreprocessIdealState s)) (paperRun initial) := by
  exact secp256k1EEA_active_paperRun hx hxp .initial _
    (eeaPreprocess_initial_packed s hclean hx hxp)

end ShorECDLP.Paper2607_13816
