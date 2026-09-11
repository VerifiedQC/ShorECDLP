import ShorECDLP.Submission.«2607_13816».EEA.IndexedStepPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleResources
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Interval resource formula using only source labels and their count, without physical trees. -/
def intervalPrimitiveShape9 (n k K : Nat) (mode : RippleMode) (signUpdate : Bool) : PrimitiveResources :=
  let endpoint : PrimitiveResources :=
    ⟨10+2*(constantBits 9 4).count true+2*(constantBits 9 (n+2)).count true+
      4*(constantBits 9 k).count true,0,190,104,0,0⟩
  let top := fun cell => if intervalHasTopSpecial k K then
    (⟨8*zeroBitCount (intervalTopRelative k K) 0 9,58,31,34+cell,0,29⟩ : PrimitiveResources)
    else ⟨0,0,0,0,0,0⟩
  let labels := intervalMainLabels k K
  endpoint.add ((top (rippleFirstCellToffoliCost mode-1)).add
    ((intervalTraversalPrimitiveFormula (rippleFirstCellToffoliCost mode-1)
      (intervalHasTopSpecial k K) labels (labels.length-1)).add
    ((⟨0,0,if signUpdate then 1 else 0,0,0,0⟩ : PrimitiveResources).add
    ((intervalTraversalPrimitiveFormula (rippleSecondCellToffoliCost mode-1)
      (intervalHasTopSpecial k K) labels (labels.length-1)).add
    ((top (rippleSecondCellToffoliCost mode-1)).add endpoint)))))

private theorem interval_primitive_labels (r : IntervalRegisters) (k K : Nat) :
    (intervalTree r k K).labels=intervalMainLabels k K := by
  have hf (n : Nat) : (List.range n).toFinset=Finset.range n := by
    ext i
    simp
  rw [intervalTree_labels]
  unfold intervalMainLabels
  split <;> simp only [hf,Finset.sort_range]

theorem intervalPrimitiveFormula9_eq_shape (r : IntervalRegisters) (n k K : Nat)
    (m : RippleMode) (s : Bool) :
    intervalPrimitiveFormula9 r n k K m s=intervalPrimitiveShape9 n k K m s := by
  have h := dualUnaryAction_internalNodes_add_one (intervalTree r k K)
  have hleaves := dualUnaryAction_leaves_eq_labels_length (intervalTree r k K)
  rw [interval_primitive_labels] at hleaves
  have hn : (intervalTree r k K).internalNodes=(intervalMainLabels k K).length-1 := by omega
  simp only [intervalPrimitiveFormula9,intervalPrimitiveShape9,interval_primitive_labels,hn]

/-- Physical-wire-independent primitive vector for one certified production index. -/
def secp256k1StepPrimitiveShape (T : Nat) : PrimitiveResources :=
  let w := certifiedActiveWindows 256 T
  let ql := w.quotientSwap.stop+1-w.quotientSwap.start
  let qn := ql-1
  let cl := w.coefficient.stop+1-w.coefficient.start
  let cn := cl-1
  let core : PrimitiveResources :=
    ⟨304+4*qn+16*cn,88+8*(cl+cn),3168+2*ql+2*qn+16*cl+12*cn,
      2027+ql+2*qn+10*cl+4*cn,0,44+4*(cl+cn)⟩
  let boundary : PrimitiveResources := if T%4=0 then
    ⟨4+endIterationXFormula 9 256 (endIterationWindowsAt 256 T),0,
      1+endIterationCnotFormula 259 9 256 (endIterationWindowsAt 256 T),
      66+endIterationToffoliFormula 259 9 256 (endIterationWindowsAt 256 T),0,0⟩
    else ⟨0,0,0,0,0,0⟩
  core.add ((intervalPrimitiveShape9 256 w.remainder.start w.remainder.stop .sub true).add
    ((intervalPrimitiveShape9 256 w.remainder.start w.remainder.stop .add false).add boundary))

private theorem quotient_primitive_leaves (r : QuotientSwapRegisters) (k K : Nat)
    (h : QuotientSwapLayout r k K) : (quotientSwapTree r k K).leaves=K+1-k := by
  rw [unaryAction_leaves_eq_labels_length,quotientSwapTree_labels r h.k_le_K,Finset.length_sort]
  simpa only [quotientSwapLabels,List.length_range'] using
    List.toFinset_card_of_nodup (show (List.range' k (K+1-k)).Nodup from List.nodup_range')

theorem indexedStepPrimitiveFormula256_eq_shape (r : IndexedStepRegisters) (T : Nat)
    (h : IndexedStepLayout r 256 T) :
    indexedStepPrimitiveFormula256 r T=secp256k1StepPrimitiveShape T := by
  have hq := quotient_primitive_leaves _ _ _ h.quotient
  have hc := coefficientPrefix_leaf_count _ _ _ h.coefficient
  have hqn := unaryAction_internalNodes_add_one (quotientSwapTree (r.quotient (certifiedActiveWindows 256 T).quotientSwap)
    (certifiedActiveWindows 256 T).quotientSwap.start (certifiedActiveWindows 256 T).quotientSwap.stop)
  have hcn := unaryAction_internalNodes_add_one (coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient)
    (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop)
  have hqn' : (quotientSwapTree (r.quotient (certifiedActiveWindows 256 T).quotientSwap)
    (certifiedActiveWindows 256 T).quotientSwap.start (certifiedActiveWindows 256 T).quotientSwap.stop).internalNodes=
      ((certifiedActiveWindows 256 T).quotientSwap.stop+1-(certifiedActiveWindows 256 T).quotientSwap.start)-1 := by omega
  have hcn' : (coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient)
    (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes=
      ((certifiedActiveWindows 256 T).coefficient.stop+1-(certifiedActiveWindows 256 T).coefficient.start)-1 := by omega
  simp only [indexedStepPrimitiveFormula256,secp256k1StepPrimitiveShape,hq,hc,hqn',hcn',
    intervalPrimitiveFormula9_eq_shape]
/-- The physical-tree fold agrees with the integer-only source-window fold. -/
theorem indexedSchedulePrimitiveFormula256_eq_shape (r : IndexedStepRegisters) (start count : Nat)
    (hl : IndexedScheduleLayout r 256 start count) :
    indexedSchedulePrimitiveFormula256 r start count=
      ((List.range' start count).map secp256k1StepPrimitiveShape).foldr PrimitiveResources.add ⟨0,0,0,0,0,0⟩ := by
  induction hl with
  | done start => simp only [indexedSchedulePrimitiveFormula256, List.range'_zero, List.map_nil, List.foldr_nil]
  | @step start count head tail ih =>
    simp only [indexedSchedulePrimitiveFormula256,List.range'_succ,List.map_cons,List.foldr_cons] at ⊢
    rw [indexedStepPrimitiveFormula256_eq_shape r start head]
    exact congrArg ((secp256k1StepPrimitiveShape start).add) ih

private def primitiveShapeSum (start count : Nat) : PrimitiveResources :=
  ((List.range' start count).map secp256k1StepPrimitiveShape).foldr PrimitiveResources.add ⟨0,0,0,0,0,0⟩
private theorem primitive_add_assoc (a b c : PrimitiveResources) :
    (a.add b).add c=a.add (b.add c) := by
  cases a; cases b; cases c
  simp [PrimitiveResources.add,Nat.add_assoc]
private theorem primitive_foldr_add (xs : List PrimitiveResources) (z : PrimitiveResources) :
    xs.foldr PrimitiveResources.add z=(xs.foldr PrimitiveResources.add ⟨0,0,0,0,0,0⟩).add z := by
  induction xs with
  | nil => simp [PrimitiveResources.add]
  | cons a xs ih =>
    simp only [List.foldr_cons,ih]
    exact (primitive_add_assoc _ _ _).symm
private theorem primitiveShapeSum_append (start a b : Nat) :
    primitiveShapeSum start (a+b)=(primitiveShapeSum start a).add (primitiveShapeSum (start+a) b) := by
  unfold primitiveShapeSum
  rw [← List.range'_append_1, List.map_append, List.foldr_append]
  exact primitive_foldr_add _ _

private theorem primitiveChunk0 : primitiveShapeSum 1 100=(⟨1209864,648400,1804839,1009995,0,324200⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk1 : primitiveShapeSum 101 100=(⟨1280856,688400,1902167,1069155,0,344200⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk2 : primitiveShapeSum 201 100=(⟨1349192,726200,1993897,1126565,0,363100⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk3 : primitiveShapeSum 301 100=(⟨1372712,728704,2024097,1157743,0,364352⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk4 : primitiveShapeSum 401 100=(⟨1384120,723560,2038537,1183005,0,361780⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk5 : primitiveShapeSum 501 100=(⟨1388232,718416,2045509,1202539,0,359208⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk6 : primitiveShapeSum 601 100=(⟨1378200,713248,2040127,1212931,0,356624⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk7 : primitiveShapeSum 701 100=(⟨1370004,708104,2034351,1222954,0,354052⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk8 : primitiveShapeSum 801 100=(⟨1352936,702960,2020155,1226755,0,351480⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk9 : primitiveShapeSum 901 100=(⟨1331500,698856,2003035,1228732,0,349428⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk10 : primitiveShapeSum 1001 100=(⟨1274376,680192,1948285,1199383,0,340096⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk11 : primitiveShapeSum 1101 100=(⟨1134864,635928,1809737,1100573,0,317964⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk12 : primitiveShapeSum 1201 100=(⟨994296,592008,1668059,999459,0,296004⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk13 : primitiveShapeSum 1301 100=(⟨849536,545616,1525635,896743,0,272808⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk14 : primitiveShapeSum 1401 100=(⟨708764,501720,1384007,795610,0,250860⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk15 : primitiveShapeSum 1501 100=(⟨567996,457408,1242313,694248,0,228704⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveChunk16 : primitiveShapeSum 1601 20=(⟨98168,87944,232081,127835,0,43972⟩ : PrimitiveResources) := by
  decide +kernel

private theorem primitiveTail15 : primitiveShapeSum 1501 120=(⟨666164,545352,1474394,822083,0,272676⟩ : PrimitiveResources) := by
  change primitiveShapeSum 1501 (100+20)=_
  rw [primitiveShapeSum_append,primitiveChunk15,primitiveChunk16]
  rfl

private theorem primitiveTail14 : primitiveShapeSum 1401 220=(⟨1374928,1047072,2858401,1617693,0,523536⟩ : PrimitiveResources) := by
  change primitiveShapeSum 1401 (100+120)=_
  rw [primitiveShapeSum_append,primitiveChunk14,primitiveTail15]
  rfl

private theorem primitiveTail13 : primitiveShapeSum 1301 320=(⟨2224464,1592688,4384036,2514436,0,796344⟩ : PrimitiveResources) := by
  change primitiveShapeSum 1301 (100+220)=_
  rw [primitiveShapeSum_append,primitiveChunk13,primitiveTail14]
  rfl

private theorem primitiveTail12 : primitiveShapeSum 1201 420=(⟨3218760,2184696,6052095,3513895,0,1092348⟩ : PrimitiveResources) := by
  change primitiveShapeSum 1201 (100+320)=_
  rw [primitiveShapeSum_append,primitiveChunk12,primitiveTail13]
  rfl

private theorem primitiveTail11 : primitiveShapeSum 1101 520=(⟨4353624,2820624,7861832,4614468,0,1410312⟩ : PrimitiveResources) := by
  change primitiveShapeSum 1101 (100+420)=_
  rw [primitiveShapeSum_append,primitiveChunk11,primitiveTail12]
  rfl

private theorem primitiveTail10 : primitiveShapeSum 1001 620=(⟨5628000,3500816,9810117,5813851,0,1750408⟩ : PrimitiveResources) := by
  change primitiveShapeSum 1001 (100+520)=_
  rw [primitiveShapeSum_append,primitiveChunk10,primitiveTail11]
  rfl

private theorem primitiveTail9 : primitiveShapeSum 901 720=(⟨6959500,4199672,11813152,7042583,0,2099836⟩ : PrimitiveResources) := by
  change primitiveShapeSum 901 (100+620)=_
  rw [primitiveShapeSum_append,primitiveChunk9,primitiveTail10]
  rfl

private theorem primitiveTail8 : primitiveShapeSum 801 820=(⟨8312436,4902632,13833307,8269338,0,2451316⟩ : PrimitiveResources) := by
  change primitiveShapeSum 801 (100+720)=_
  rw [primitiveShapeSum_append,primitiveChunk8,primitiveTail9]
  rfl

private theorem primitiveTail7 : primitiveShapeSum 701 920=(⟨9682440,5610736,15867658,9492292,0,2805368⟩ : PrimitiveResources) := by
  change primitiveShapeSum 701 (100+820)=_
  rw [primitiveShapeSum_append,primitiveChunk7,primitiveTail8]
  rfl

private theorem primitiveTail6 : primitiveShapeSum 601 1020=(⟨11060640,6323984,17907785,10705223,0,3161992⟩ : PrimitiveResources) := by
  change primitiveShapeSum 601 (100+920)=_
  rw [primitiveShapeSum_append,primitiveChunk6,primitiveTail7]
  rfl

private theorem primitiveTail5 : primitiveShapeSum 501 1120=(⟨12448872,7042400,19953294,11907762,0,3521200⟩ : PrimitiveResources) := by
  change primitiveShapeSum 501 (100+1020)=_
  rw [primitiveShapeSum_append,primitiveChunk5,primitiveTail6]
  rfl

private theorem primitiveTail4 : primitiveShapeSum 401 1220=(⟨13832992,7765960,21991831,13090767,0,3882980⟩ : PrimitiveResources) := by
  change primitiveShapeSum 401 (100+1120)=_
  rw [primitiveShapeSum_append,primitiveChunk4,primitiveTail5]
  rfl

private theorem primitiveTail3 : primitiveShapeSum 301 1320=(⟨15205704,8494664,24015928,14248510,0,4247332⟩ : PrimitiveResources) := by
  change primitiveShapeSum 301 (100+1220)=_
  rw [primitiveShapeSum_append,primitiveChunk3,primitiveTail4]
  rfl

private theorem primitiveTail2 : primitiveShapeSum 201 1420=(⟨16554896,9220864,26009825,15375075,0,4610432⟩ : PrimitiveResources) := by
  change primitiveShapeSum 201 (100+1320)=_
  rw [primitiveShapeSum_append,primitiveChunk2,primitiveTail3]
  rfl

private theorem primitiveTail1 : primitiveShapeSum 101 1520=(⟨17835752,9909264,27911992,16444230,0,4954632⟩ : PrimitiveResources) := by
  change primitiveShapeSum 101 (100+1420)=_
  rw [primitiveShapeSum_append,primitiveChunk1,primitiveTail2]
  rfl

private theorem primitiveTail0 : primitiveShapeSum 1 1620=(⟨19045616,10557664,29716831,17454225,0,5278832⟩ : PrimitiveResources) := by
  change primitiveShapeSum 1 (100+1520)=_
  rw [primitiveShapeSum_append,primitiveChunk0,primitiveTail1]
  rfl

/-- The closed sum is kernel-checked in bounded chunks to keep verification memory bounded. -/
theorem secp256k1EEAForwardPrimitive_sum :
    ((List.range' 1 1620).map secp256k1StepPrimitiveShape).foldr PrimitiveResources.add ⟨0,0,0,0,0,0⟩=
      (⟨19045616,10557664,29716831,17454225,0,5278832⟩ : PrimitiveResources) := primitiveTail0

/-- Readable same-program certificate for every primitive of the complete forward EEA run. -/
theorem secp256k1EEAForwardPrimitive_certificate :
    primitiveResources (secp256k1EEAForwardAdaptive indexedStepProductionRegisters)=
      (⟨19045616,10557664,29716831,17454225,0,5278832⟩ : PrimitiveResources) :=
  secp256k1EEAForwardAdaptive_primitive.trans
    ((indexedSchedulePrimitiveFormula256_eq_shape _ _ _ secp256k1ScheduleLayout_production).trans
      secp256k1EEAForwardPrimitive_sum)

end ShorECDLP.Paper2607_13816
