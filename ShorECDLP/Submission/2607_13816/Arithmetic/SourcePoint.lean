import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceInPlace
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointTotal
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem pointSourceThreshold : ¬(ShorECDLP.p=0 ∨ 2^256≤ShorECDLP.p) := by decide +kernel
private theorem pointSourceReduction : secp256k1ReductionConstantBits.all (fun k => !k)=false := by decide +kernel
private theorem pointSourceModulus : (constantBits 256 ShorECDLP.p).all (fun k => !k)=false := by decide +kernel
/-- Exact source correction count for one physical 256-bit constant-add stage. -/
def pointConstantSourceEvents (k : Nat) : Nat :=
  (if (constantBits 256 k).all (fun b => !b) then 0 else 510)+
    ((if boolWordToNat (constantBits 256 k)=0 ∨ 2^256≤boolWordToNat (constantBits 256 k) then 0 else 512)+
      (512+(510+(if boolWordToNat (constantBits 256 k)=0 ∨ 2^256≤boolWordToNat (constantBits 256 k) then 0 else 512))))
theorem pointConstantSourceEvents_le (k : Nat) : pointConstantSourceEvents k≤2556 := by
  unfold pointConstantSourceEvents
  split <;> split <;> omega
def fig14ConstantXSource (k : Nat) : CorrectionProgram :=
  uncontrolledConstantModularAddSource (List.range' 263 256) (List.range' 7 256) (constantBits 256 k)
    secp256k1ReductionConstantBits ShorECDLP.p 559 560 561 558
theorem fig14ConstantXSource_certificate (k : Nat) :
    (fig14ConstantXSource k).erase=fig14ConstantX k ∧ (fig14ConstantXSource k).events=pointConstantSourceEvents k := by
  constructor
  · exact uncontrolledConstantModularAddSource_erase _ _ _ _ _ _ _ _ _
  · rw [fig14ConstantXSource,uncontrolledConstantModularAddSource_events (List.range' 263 256) (List.range' 7 256)
      (constantBits 256 k) secp256k1ReductionConstantBits ShorECDLP.p 559 560 561 558 (by simp) (by simp) (by simp) (by decide +kernel)]
    simp only [List.length_range',pointSourceThreshold,pointSourceReduction,Bool.false_eq_true,if_false,pointConstantSourceEvents]
def fig14ControlledConstantXSource (k : Nat) : CorrectionProgram :=
  controlledConstantModularAddSource (List.range' 263 256) (List.range' 7 256) (constantBits 256 k)
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
theorem fig14ControlledConstantXSource_certificate (k : Nat) :
    (fig14ControlledConstantXSource k).erase=fig14ControlledConstantX k ∧ (fig14ControlledConstantXSource k).events=pointConstantSourceEvents k := by
  constructor
  · exact controlledConstantModularAddSource_erase _ _ _ _ _ _ _ _ _ _
  · rw [fig14ControlledConstantXSource,controlledConstantModularAddSource_events (List.range' 263 256) (List.range' 7 256)
      (constantBits 256 k) secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558 (by simp) (by simp) (by simp) (by decide +kernel)]
    simp only [List.length_range',pointSourceThreshold,pointSourceReduction,Bool.false_eq_true,if_false,pointConstantSourceEvents]
def fig14ControlledConstantYSource (k : Nat) : CorrectionProgram :=
  controlledConstantModularAddSource (List.range' 580 256) (List.range' 7 256) (constantBits 256 k)
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
theorem fig14ControlledConstantYSource_certificate (k : Nat) :
    (fig14ControlledConstantYSource k).erase=fig14ControlledConstantY k ∧ (fig14ControlledConstantYSource k).events=pointConstantSourceEvents k := by
  constructor
  · exact controlledConstantModularAddSource_erase _ _ _ _ _ _ _ _ _ _
  · rw [fig14ControlledConstantYSource,controlledConstantModularAddSource_events (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 k) secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558 (by simp) (by simp) (by simp) (by decide +kernel)]
    simp only [List.length_range',pointSourceThreshold,pointSourceReduction,Bool.false_eq_true,if_false,pointConstantSourceEvents]
def fig14NegateSource : CorrectionProgram :=
  controlledModularNegateSource (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 559 560 561 558
theorem fig14NegateSource_certificate : fig14NegateSource.erase=fig14Negate ∧ fig14NegateSource.events=2044 := by
  constructor
  · exact controlledModularNegateSource_erase _ _ _ _ _ _ _ _
  · rw [fig14NegateSource,controlledModularNegateSource_events _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp)]
    simp only [List.length_range',pointSourceModulus,Bool.false_eq_true,if_false]
def squareSubtractSource (x y acc : List Wire) (correction modulus : List Bool) (p : Nat)
    (q copied c r t f : Wire) : CorrectionProgram :=
  (squareLoopSource y y acc correction p copied c r t f).seq
    ((controlledModularSubSource acc x modulus p q copied f r c).seq
      (squareLoopInverseSource y y acc modulus p copied c r t f))
theorem squareSubtractSource_erase (x y acc : List Wire) (correction modulus : List Bool) (p : Nat)
    (q copied c r t f : Wire) :
    (squareSubtractSource x y acc correction modulus p q copied c r t f).erase=
      squareSubtract x y acc correction modulus p q copied c r t f := by
  simp only [squareSubtractSource,squareSubtract,CorrectionProgram.erase_seq,squareLoopSource_erase,
    controlledModularSubSource_erase,squareLoopInverseSource_erase]
def fig14SquareSubtractSource : CorrectionProgram :=
  squareSubtractSource (List.range' 263 256) (List.range' 580 256) (7::List.range' 8 255)
    secp256k1ReductionConstantBits (constantBits 256 ShorECDLP.p) ShorECDLP.p 836 558 559 561 562 560
theorem fig14SquareSubtractSource_certificate :
    fig14SquareSubtractSource.erase=fig14SquareSubtract ∧ fig14SquareSubtractSource.events=1045506 := by
  constructor
  · exact squareSubtractSource_erase _ _ _ _ _ _ _ _ _ _ _ _
  · have hf := squareLoopSource_events (List.range' 580 256) (List.range' 580 256) 7 (List.range' 8 255)
      secp256k1ReductionConstantBits ShorECDLP.p 558 559 561 562 560 (by simp) (by decide +kernel)
    have hi := squareLoopInverseSource_events (List.range' 580 256) (List.range' 580 256) 7 (List.range' 8 255)
      (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 559 561 562 560 (by simp) (by simp)
    rw [fig14SquareSubtractSource,squareSubtractSource,CorrectionProgram.events_seq,CorrectionProgram.events_seq,
      hf,hi,controlledModularSubSource_events _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp)]
    simp only [List.length_range',List.length_cons,pointSourceThreshold,pointSourceReduction,pointSourceModulus,
      Bool.false_eq_true,if_false]
    simp only [show 255+1=256 from rfl,pointSourceThreshold,if_false]
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
def fig14CoordinateSource (x₂ y₂ : Nat) : CorrectionProgram :=
  (((((((((fig14ConstantXSource ((ShorECDLP.p-x₂)%ShorECDLP.p)).seq (fig14ControlledConstantYSource ((ShorECDLP.p-y₂)%ShorECDLP.p))).seq (secp256k1ZeroAllowedDivisionSource)).seq (fig14SquareSubtractSource)).seq (fig14ControlledConstantXSource ((3*x₂)%ShorECDLP.p))).seq (secp256k1ZeroAllowedMultiplicationSource)).seq (fig14NegateSource)).seq (fig14ConstantXSource (x₂%ShorECDLP.p))).seq (fig14ControlledConstantYSource ((ShorECDLP.p-y₂)%ShorECDLP.p)))
def pointCoordinateSourceEvents (x y : Nat) : Nat :=
  25307050+pointConstantSourceEvents ((ShorECDLP.p-x)%ShorECDLP.p)+
    2*pointConstantSourceEvents ((ShorECDLP.p-y)%ShorECDLP.p)+
    pointConstantSourceEvents ((3*x)%ShorECDLP.p)+pointConstantSourceEvents (x%ShorECDLP.p)
theorem fig14CoordinateSource_certificate (x y : Nat) :
    (fig14CoordinateSource x y).erase=fig14CoordinateProgram x y ∧
      (fig14CoordinateSource x y).events=pointCoordinateSourceEvents x y := by
  constructor
  · simp only [fig14CoordinateSource,fig14CoordinateProgram,CorrectionProgram.erase_seq,
      (fig14ConstantXSource_certificate _).1,(fig14ControlledConstantYSource_certificate _).1,
      secp256k1ZeroAllowedDivisionSource_certificate.1,fig14SquareSubtractSource_certificate.1,
      (fig14ControlledConstantXSource_certificate _).1,secp256k1ZeroAllowedMultiplicationSource_certificate.1,
      fig14NegateSource_certificate.1]
  · simp only [fig14CoordinateSource,CorrectionProgram.events_seq,
      (fig14ConstantXSource_certificate _).2,(fig14ControlledConstantYSource_certificate _).2,
      secp256k1ZeroAllowedDivisionSource_certificate.2,fig14SquareSubtractSource_certificate.2,
      (fig14ControlledConstantXSource_certificate _).2,secp256k1ZeroAllowedMultiplicationSource_certificate.2,
      fig14NegateSource_certificate.2,pointCoordinateSourceEvents]
    omega
theorem pointCoordinateSourceEvents_le (x y : Nat) : pointCoordinateSourceEvents x y≤25319830 := by
  have h1 := pointConstantSourceEvents_le ((ShorECDLP.p-x)%ShorECDLP.p)
  have h2 := pointConstantSourceEvents_le ((ShorECDLP.p-y)%ShorECDLP.p)
  have h3 := pointConstantSourceEvents_le ((3*x)%ShorECDLP.p)
  have h4 := pointConstantSourceEvents_le (x%ShorECDLP.p)
  unfold pointCoordinateSourceEvents
  omega
/-- Attach the unchanged ordinary reversible exceptional-point correction. -/
def totalPointSource {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) : CorrectionProgram :=
  (fig14CoordinateSource x.val y.val).seq (.unitary [.ordinary (pointCorrectionCircuit hC)] .done)
/-- Exact source-event formula on the same complete controlled point-addition circuit. -/
theorem totalPointSource_certificate {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) :
    (totalPointSource hC).erase=totalPointProgram hC ∧
      (totalPointSource hC).events=pointCoordinateSourceEvents x.val y.val ∧
      (totalPointSource hC).events≤25319830 := by
  have he : (totalPointSource hC).events=pointCoordinateSourceEvents x.val y.val := by
    simp [totalPointSource,CorrectionProgram.events_seq,(fig14CoordinateSource_certificate _ _).2,
      CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
  refine ⟨?_,he,he.trans_le (pointCoordinateSourceEvents_le _ _)⟩
  simp [totalPointSource,totalPointProgram,CorrectionProgram.erase_seq,(fig14CoordinateSource_certificate _ _).1,
    CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
/-- Source annotation of addition by any fixed curve point, including infinity. -/
def pointAddSource : ShorECDLP.Secp256k1.Point → CorrectionProgram
  | .zero => .done
  | .some hC => totalPointSource hC

def pointAddSourceEvents : ShorECDLP.Secp256k1.Point → Nat
  | .zero => 0
  | .some (x := x) (y := y) _ => pointCoordinateSourceEvents x.val y.val

theorem pointAddSource_certificate (C : ShorECDLP.Secp256k1.Point) :
    (pointAddSource C).erase = pointAddProgram C ∧
      (pointAddSource C).events = pointAddSourceEvents C ∧
      (pointAddSource C).events ≤ 25319830 := by
  cases C with
  | zero => exact ⟨rfl, rfl, Nat.zero_le _⟩
  | some hC => exact totalPointSource_certificate hC
end ShorECDLP.Paper2607_13816
