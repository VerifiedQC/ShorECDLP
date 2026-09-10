import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareResourceCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointConstantResources
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCorrectionResources
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedResources
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem seq_T (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
/-- Cost of the five classical constant stages and four fixed coordinate stages. -/
def pointCoordinateT (x y : Nat) : Nat :=
  554814253 + pointConstantT ((ShorECDLP.p-x)%ShorECDLP.p) +
    2*pointConstantT ((ShorECDLP.p-y)%ShorECDLP.p) +
    pointConstantT ((3*x)%ShorECDLP.p) + pointConstantT (x%ShorECDLP.p)
def pointCoordinateMeasurements (x y : Nat) : Nat :=
  23211445 + pointConstantMeasurements ((ShorECDLP.p-x)%ShorECDLP.p) +
    2*pointConstantMeasurements ((ShorECDLP.p-y)%ShorECDLP.p) +
    pointConstantMeasurements ((3*x)%ShorECDLP.p) + pointConstantMeasurements (x%ShorECDLP.p)
theorem fig14CoordinateProgram_counts (x y : Nat) :
    (fig14CoordinateProgram x y).tCount=pointCoordinateT x y ∧
    (fig14CoordinateProgram x y).measurementCount=pointCoordinateMeasurements x y := by
  have hp := ShorECDLP.Secp256k1.p_prime.pos
  have h1 := fig14ConstantX_counts ((ShorECDLP.p-x)%ShorECDLP.p) (Nat.mod_lt _ hp)
  have h2 := fig14ControlledConstantY_counts ((ShorECDLP.p-y)%ShorECDLP.p) (Nat.mod_lt _ hp)
  have h3 := secp256k1ZeroAllowedDivision_resources
  have h4 := fig14SquareSubtract_counts
  have h5 := fig14ControlledConstantX_counts ((3*x)%ShorECDLP.p) (Nat.mod_lt _ hp)
  have h6 := secp256k1ZeroAllowedMultiplication_resources
  have h7 := fig14Negate_counts
  have h8 := fig14ConstantX_counts (x%ShorECDLP.p) (Nat.mod_lt _ hp)
  simp only [fig14CoordinateProgram,seq_T,modularMeasurements_seq,h1.1,h1.2,h2.1,h2.2,
    h3.1,h3.2.1,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2.1,h7.1,h7.2,h8.1,h8.2,
    pointCoordinateT,pointCoordinateMeasurements]
  omega

def pointAddT : ShorECDLP.Secp256k1.Point → Nat
  | .zero => 0
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y hC =>
    let edges := pointCorrectionWordEdges hC
    pointCoordinateT x.val y.val + 21371*pointXEdgeCount edges + 21399*(edges.length-pointXEdgeCount edges)
def pointAddMeasurements : ShorECDLP.Secp256k1.Point → Nat
  | .zero => 0
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => pointCoordinateMeasurements x.val y.val

theorem totalPointProgram_counts {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) :
    (totalPointProgram hC).tCount=pointAddT (.some hC) ∧
    (totalPointProgram hC).measurementCount=pointAddMeasurements (.some hC) := by
  have hh := fig14CoordinateProgram_counts x.val y.val
  simp only [totalPointProgram,seq_T,modularMeasurements_seq,AdaptiveCircuit.tCount,
    AdaptiveCircuit.measurementCount,hh.1,hh.2,pointCorrectionCircuit_T,pointAddT,pointAddMeasurements]
  constructor
  · omega
  · rfl

theorem pointAddProgram_counts (C : ShorECDLP.Secp256k1.Point) :
    (pointAddProgram C).tCount=pointAddT C ∧
    (pointAddProgram C).measurementCount=pointAddMeasurements C := by
  cases C with
  | zero => exact ⟨rfl,rfl⟩
  | some hC => exact totalPointProgram_counts hC
end ShorECDLP.Paper2607_13816
