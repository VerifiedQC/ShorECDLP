import ShorECDLP.Submission.«2607_13816».EEA.CoefficientState
import ShorECDLP.Submission.«2607_13816».EEA.BlockBRemainder
namespace ShorECDLP.Paper2607_13816
open Classical

/-- Logical conditional subtraction and comparison flag performed by Block B. -/
def remainderMicrostep (v : EEAState) : EEAState :=
  { v with
    r := if v.phase.bits.2 && decide (v.rPrime*2^v.shift≤v.r) then v.r-v.rPrime*2^v.shift else v.r
    sign := decide (v.r<v.rPrime*2^v.shift) ^^ v.phase.bits.2 }

private theorem remainder_prefix_disjoint (a b c : List Wire)
    (h : (a++(b++c)).Nodup) : List.Disjoint (a++c) b := by
  obtain ⟨_,hr,ha⟩ := List.nodup_append.mp h
  have hb := (List.nodup_append.mp hr).2.2
  apply List.disjoint_left.mpr
  intro w hw hn
  rcases List.mem_append.mp hw with hw | hw
  · exact ha w hw w (List.mem_append_left _ hn) rfl
  · exact hb w hn w hw rfl

/-- The active remainder block preserves complete packing while subtracting the
aligned divisor conditionally. The input packing determines both compared values. -/
theorem blockBForward_packed (r : IndexedStepRegisters) (n index : Nat)
    (s : BasisState) (v : EEAState) (h : IndexedStepLayout r n index)
    (hp : IndexedPackedState r n s v) (hphase : v.phase.bits.1=false) (hsign : v.sign=false)
    (hR : 0<v.lRPrime) (hRfit : v.lRPrime<2^r.lengthRPrime.length)
    (hspan : v.lT+v.lQ+1+v.shift+v.lRPrime≤n+3)
    (htp : v.tPrime<2^(v.lT+v.lQ+1+v.shift))
    (hrp : v.rPrime<2^v.lRPrime) (hrem : v.r<2^(n+3-(v.lT+v.lQ+1)))
    (hleftLow : (certifiedActiveWindows n index).remainder.start≤v.lT+v.lQ+2)
    (hleftHigh : v.lT+v.lQ+2-(certifiedActiveWindows n index).remainder.start<2^r.lengthQ.length)
    (hrightLow : v.shift+(certifiedActiveWindows n index).remainder.start≤n+3)
    (hrightHigh : n+3-v.shift-(certifiedActiveWindows n index).remainder.start<2^r.lengthS.length) :
    IndexedPackedState r n (run (blockBForward r n (certifiedActiveWindows n index).remainder) s)
      (remainderMicrostep v) := by
  let start := v.lT+v.lQ+1
  let width := n+3-v.shift-start
  let packedPrefix := constantBits v.lT v.t ++ [false] ++ (constantBits v.lQ v.q).reverse
  have hremBound : v.r<2^(n+3-start) := hrem
  let out := run (blockBForward r n (certifiedActiveWindows n index).remainder) s
  have hp1 : s r.phase1=false := hp.phase1.trans hphase
  have hsg : s r.sign=false := hp.sign.trans hsign
  have hrz : wireAnd r.lengthRPrime s=false := by
    rw [wireAnd_encoded_zero r.lengthRPrime s v.lRPrime hp.lengthRP hRfit]
    exact decide_eq_false (by omega)
  have hTmeta : boolWordToNat (wireValues r.lengthT s)=truthMinusOneValue r.lengthQ.length v.lT := by
    have hw : r.lengthT.length=r.lengthQ.length := h.quotient.lengthT_eq_lengthQ
    simpa only [hw] using hp.lengthT
  have horder : v.lT+v.lQ+2-(certifiedActiveWindows n index).remainder.start≤
      n+3-v.shift-(certifiedActiveWindows n index).remainder.start := by omega
  have hwidth : n+3-v.shift-(v.lT+v.lQ+2)+1=width := by dsimp only [width,start]; omega
  have hprefLen : packedPrefix.length=start := by
    simp only [packedPrefix,start,List.length_append,constantBits_length,List.length_singleton,List.length_reverse]
    omega
  have hw1 : wireValues r.work1 s=packedPrefix++(constantBits (n+3-start) v.r).reverse := hp.work1
  have htail : (wireValues r.work1 s).drop start=(constantBits (n+3-start) v.r).reverse := by
    rw [hw1,List.drop_left' hprefLen]
  have hremValue : boolWordToNat ((wireValues r.work1 s).drop start).reverse=v.r := by
    rw [htail,List.reverse_reverse,boolWordToNat_constantBits,Nat.mod_eq_of_lt hremBound]
  have hdivWord : ((wireValues r.work2 s).drop start).take width=(constantBits width v.rPrime).reverse := by
    rw [hp.work2]
    exact packed_remainder_divisor (n+3) start v.shift v.lRPrime v.tPrime v.rPrime hspan htp hrp
  have hdivFit : v.rPrime<2^width := hrp.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp only [width,start]; omega))
  have hdivValue : boolWordToNat (((wireValues r.work2 s).drop start).take width).reverse=v.rPrime := by
    rw [hdivWord,List.reverse_reverse,boolWordToNat_constantBits,Nat.mod_eq_of_lt hdivFit]
  have hhighValue : boolWordToNat (((wireValues r.work1 s).drop start).take width).reverse=v.r/2^v.shift := by
    rw [htail]
    have he := boolWordToNat_reverse_slice (constantBits (n+3-start) v.r).reverse 0 width
      (by simp only [List.length_reverse,constantBits_length]; dsimp only [width,start]; omega)
    simp only [List.drop_zero,List.length_reverse,constantBits_length,Nat.sub_zero,List.reverse_reverse,
      boolWordToNat_constantBits,Nat.mod_eq_of_lt hremBound] at he
    have hlen : n+3-start-width=v.shift := by dsimp only [width,start]; omega
    rw [hlen] at he
    rw [he]
    apply Nat.mod_eq_of_lt
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← Nat.pow_add]
    have hs : width+v.shift=n+3-start := by dsimp only [width,start]; omega
    rw [hs]
    exact hrem
  have hb := blockBForward_remainderValue r n index v.lT v.lQ v.shift s h hp.clean hp1 hsg hrz
    hTmeta hp.lengthQ hp.lengthS hleftLow hleftHigh hrightLow hrightHigh horder
  dsimp only at hb
  rw [hwidth] at hb
  change boolWordToNat ((wireValues r.work1 out).drop start).reverse = _ at hb
  rw [hdivValue,hremValue,hp.phase2] at hb
  have ha := blockBForward_activeArithmetic r n index v.lT v.lQ v.shift s h hp.clean hp1 hsg hrz
    hTmeta hp.lengthQ hp.lengthS hleftLow hleftHigh hrightLow hrightHigh horder
  dsimp only at ha
  rw [hwidth] at ha
  have hsignOut : out r.sign=(remainderMicrostep v).sign := by
    have he := ha.2.1
    change out r.sign=(decide (boolWordToNat (((wireValues r.work1 s).drop start).take width).reverse <
      boolWordToNat (((wireValues r.work2 s).drop start).take width).reverse) ^^ s r.phase2) at he
    rw [hhighValue,hdivValue,hp.phase2] at he
    change out r.sign=(decide (v.r<v.rPrime*2^v.shift) ^^ v.phase.bits.2)
    simpa only [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)] using he
  have hnewFit : (remainderMicrostep v).r<2^(n+3-start) := by
    dsimp only [remainderMicrostep]
    split <;> omega
  have hnewTail : (wireValues r.work1 out).drop start=(constantBits (n+3-start) (remainderMicrostep v).r).reverse := by
    apply List.reverse_injective
    rw [List.reverse_reverse]
    apply boolWordToNat_injective_of_length
    · simp only [wireValues,List.length_reverse,List.length_drop,List.length_map,h.work1_length,constantBits_length]
    · rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt hnewFit]
      exact hb
  have hfield := blockBForward_fieldFrame r n index v.lT v.lQ v.shift s h hp.clean
    hTmeta hp.lengthQ hp.lengthS hleftLow hleftHigh hrightLow hrightHigh horder
  have hprefixOut : (wireValues r.work1 out).take start=packedPrefix := by
    rw [hfield.1,hw1]
    change (packedPrefix++(constantBits (n+3-start) v.r).reverse).take start=packedPrefix
    rw [← hprefLen,List.take_left]
  have hframe := blockBForward_frame r n index s h hp.clean
  have hsep := remainder_prefix_disjoint [r.phase1,r.phase2,r.iter] (r.sign::r.work1)
    (r.work2++r.lengthT++r.lengthQ++r.lengthS++r.lengthRPrime++r.aux)
    (by simpa only [IndexedStepRegisters.allWires,List.append_assoc,List.cons_append,List.nil_append] using h.physical)
  have hstable (wire : Wire) (hw : wire ∈ [r.phase1,r.phase2,r.iter] ++
      (r.work2++r.lengthT++r.lengthQ++r.lengthS++r.lengthRPrime++r.aux)) : out wire=s wire :=
    hframe wire (List.disjoint_left.mp hsep hw)
  have hword (ws : List Wire) (hw : ∀ wire ∈ ws, wire ∈ [r.phase1,r.phase2,r.iter] ++
      (r.work2++r.lengthT++r.lengthQ++r.lengthS++r.lengthRPrime++r.aux)) : wireValues ws out=wireValues ws s := by
    apply List.map_congr_left
    intro wire hm
    exact hstable wire (hw wire hm)
  constructor
  · change wireValues r.work1 out=packedPrefix++(constantBits (n+3-start) (remainderMicrostep v).r).reverse
    rw [← List.take_append_drop start (wireValues r.work1 out),hprefixOut,hnewTail]
  · change wireValues r.work2 out=_
    rw [hword r.work2 (by intro w hw; simp [hw])]
    exact hp.work2
  · change boolWordToNat (wireValues r.lengthT out)=_
    rw [hword r.lengthT (by intro w hw; simp [hw])]
    exact hp.lengthT
  · change boolWordToNat (wireValues r.lengthQ out)=_
    rw [hword r.lengthQ (by intro w hw; simp [hw])]
    exact hp.lengthQ
  · change boolWordToNat (wireValues r.lengthRPrime out)=_
    rw [hword r.lengthRPrime (by intro w hw; simp [hw])]
    exact hp.lengthRP
  · change boolWordToNat (wireValues r.lengthS out)=_
    rw [hword r.lengthS (by intro w hw; simp [hw])]
    exact hp.lengthS
  · exact (hstable _ (by simp)).trans hp.phase1
  · exact (hstable _ (by simp)).trans hp.phase2
  · exact hsignOut
  · exact (hstable _ (by simp)).trans hp.iter
  · exact ha.2.2
end ShorECDLP.Paper2607_13816
