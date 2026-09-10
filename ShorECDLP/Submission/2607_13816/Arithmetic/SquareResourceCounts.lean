import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantResourceCounts

namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem seq_T (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b

private theorem copied_counts (bit copied : Wire) (g : AdaptiveCircuit) :
    (AdaptiveCircuit.unitary [.CX bit copied] (g.seq (.unitary [.CX bit copied] .done))).tCount=g.tCount ∧
    (AdaptiveCircuit.unitary [.CX bit copied] (g.seq (.unitary [.CX bit copied] .done))).measurementCount=g.measurementCount := by
  have hh := (squareWrap_counts ([.CX bit copied] : Circuit) ([.CX bit copied] : Circuit) g).2.2
  simpa only [show ShorECDLP.tCount [.CX bit copied]=0 from rfl,Nat.add_zero,Nat.zero_add] using hh

theorem squareLoops256_counts (controls A B : List Wire) (K : List Bool) (copied c r t f : Wire)
    (hA : A.length=256) (hB : B.length=256) (hK : K.length=256) (hk : boolWordToNat K≠0) :
    ((squareLoop controls A B K ShorECDLP.p copied c r t f).tCount=
      controls.length*19691+(controls.length-1)*10717 ∧
      (squareLoop controls A B K ShorECDLP.p copied c r t f).measurementCount=(controls.length*2-1)*511) ∧
    ((squareLoopInverse controls A B K ShorECDLP.p copied c r t f).tCount=
      controls.length*19691+(controls.length-1)*10717 ∧
      (squareLoopInverse controls A B K ShorECDLP.p copied c r t f).measurementCount=(controls.length*2-1)*511) := by
  have ha := modularArithmetic256_counts B A K copied c r t f hB hA hK hk
  have hd := modularScaling256_counts B A K f r t c hB hA hK hk
  have hcopy (q : Wire) :
      ((squareAdd A B K ShorECDLP.p q copied c r t f).tCount=19691 ∧
        (squareAdd A B K ShorECDLP.p q copied c r t f).measurementCount=511) ∧
      ((squareSub A B K ShorECDLP.p q copied c r t f).tCount=19691 ∧
        (squareSub A B K ShorECDLP.p q copied c r t f).measurementCount=511) := by
    constructor
    · simpa only [squareAdd,ha.1.1,ha.1.2] using copied_counts q copied (controlledModularAdd A B K ShorECDLP.p copied c r t f)
    · simpa only [squareSub,ha.2.1,ha.2.2] using copied_counts q copied (controlledModularSub A B K ShorECDLP.p copied c r t f)
  induction controls with
  | nil => simp [squareLoop,squareLoopInverse,AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount]
  | cons q qs ih =>
    have hc := hcopy q
    have hft : (squareLoop (q::qs) A B K ShorECDLP.p copied c r t f).tCount =
        (squareLoop qs A B K ShorECDLP.p copied c r t f).tCount +
        (if qs=[] then squareAdd A B K ShorECDLP.p q copied c r t f else
          (modularDouble B A K ShorECDLP.p f r t c).seq (squareAdd A B K ShorECDLP.p q copied c r t f)).tCount := seq_T _ _
    have hfm : (squareLoop (q::qs) A B K ShorECDLP.p copied c r t f).measurementCount =
        (squareLoop qs A B K ShorECDLP.p copied c r t f).measurementCount +
        (if qs=[] then squareAdd A B K ShorECDLP.p q copied c r t f else
          (modularDouble B A K ShorECDLP.p f r t c).seq (squareAdd A B K ShorECDLP.p q copied c r t f)).measurementCount := modularMeasurements_seq _ _
    have hrt : (squareLoopInverse (q::qs) A B K ShorECDLP.p copied c r t f).tCount =
        (squareSub A B K ShorECDLP.p q copied c r t f).tCount +
        (if qs=[] then AdaptiveCircuit.done else (modularHalve B A K ShorECDLP.p f r t c).seq
          (squareLoopInverse qs A B K ShorECDLP.p copied c r t f)).tCount := seq_T _ _
    have hrm : (squareLoopInverse (q::qs) A B K ShorECDLP.p copied c r t f).measurementCount =
        (squareSub A B K ShorECDLP.p q copied c r t f).measurementCount +
        (if qs=[] then AdaptiveCircuit.done else (modularHalve B A K ShorECDLP.p f r t c).seq
          (squareLoopInverse qs A B K ShorECDLP.p copied c r t f)).measurementCount := modularMeasurements_seq _ _
    rw [hft,hfm,hrt,hrm,ih.1.1,ih.1.2,hc.2.1,hc.2.2]
    by_cases hz : qs=[]
    · simp only [if_pos hz,hc.1.1,hc.1.2,AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount]
      subst qs
      norm_num only [List.length_nil,List.length_cons]
      exact ⟨⟨trivial,trivial⟩,trivial,trivial⟩
    · have hn : 0<qs.length := List.length_pos_iff.mpr hz
      simp only [if_neg hz,seq_T,modularMeasurements_seq,ih.2.1,ih.2.2,
        hc.1.1,hc.1.2,hd.1.1,hd.1.2,hd.2.1,hd.2.2,List.length_cons]
      omega

theorem squareSubtract256_counts (x y acc : List Wire) (q copied c r t f : Wire)
    (hx : x.length=256) (hy : y.length=256) (ha : acc.length=256) :
    (squareSubtract x y acc secp256k1ReductionConstantBits secp256k1ModulusBits ShorECDLP.p q copied c r t f).tCount=15567153 ∧
    (squareSubtract x y acc secp256k1ReductionConstantBits secp256k1ModulusBits ShorECDLP.p q copied c r t f).measurementCount=522753 := by
  have hf := (squareLoops256_counts y y acc secp256k1ReductionConstantBits copied c r t f hy ha (by decide +kernel) (by decide +kernel)).1
  have hr := (squareLoops256_counts y y acc secp256k1ModulusBits copied c r t f hy ha (by decide +kernel) (by decide +kernel)).2
  have hm := (modularArithmetic256_counts x acc secp256k1ModulusBits q copied f r c hx ha (by decide +kernel) (by decide +kernel)).2
  simp only [hy] at hf hr
  simp only [squareSubtract,seq_T,modularMeasurements_seq,hf.1,hf.2,hr.1,hr.2,hm.1,hm.2]
  constructor <;> trivial

theorem fig14SquareSubtract_counts : fig14SquareSubtract.tCount=15567153 ∧
    fig14SquareSubtract.measurementCount=522753 := by
  have hm : constantBits 256 ShorECDLP.p=secp256k1ModulusBits := by decide +kernel
  simpa only [fig14SquareSubtract,hm] using squareSubtract256_counts
    (List.range' 263 256) (List.range' 580 256) (List.range' 7 256) 836 558 559 561 562 560 (by simp) (by simp) (by simp)
end ShorECDLP.Paper2607_13816
