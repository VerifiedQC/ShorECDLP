import ShorECDLP.Submission.«2607_13816».Arithmetic.PointWordProgram
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointWordCorrection
namespace ShorECDLP.Paper2607_13816
open Classical
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩
/-- Physical correction generated from the finite exceptional-point swaps. -/
def pointCorrectionCircuit {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) : Circuit :=
  pointWordProgram (pointCorrectionWordEdges hC)

theorem pointCorrectionCircuit_correct {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) (P : ShorECDLP.Secp256k1.Point)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) (hq : s 836=true)
    (hw : wireValues pointLogicalWires s=
      pointCoordinateWord (fig14EncodedEquiv x₂ y₂ (fig14PointEncoding P))) :
    wireValues pointLogicalWires (run (pointCorrectionCircuit hC) s)=
      pointCoordinateWord (fig14PointEncoding (P+(.some hC))) := by
  rw [pointCorrectionCircuit,pointWordProgram_correct _ (pointCorrectionWordEdges_adjacent hC) s hc hq,
    hw,pointCorrectionWordEdges_correct]

theorem pointCorrectionCircuit_clean {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) :
    Clean (558::559::pointCorrectionScratch) (run (pointCorrectionCircuit hC) s) :=
  pointWordProgram_clean _ (pointCorrectionWordEdges_adjacent hC) s hc

theorem pointCorrectionCircuit_frame {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) :
    ∀ w, w ∉ pointLogicalWires → run (pointCorrectionCircuit hC) s w=s w :=
  pointWordProgram_frame _ (pointCorrectionWordEdges_adjacent hC) s hc

theorem pointCorrectionCircuit_disabled {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) (hq : s 836=false) :
    run (pointCorrectionCircuit hC) s=s :=
  pointWordProgram_disabled _ (pointCorrectionWordEdges_adjacent hC) s hc hq

/-- Conservative cost of the complete physical correction, on the same circuit. -/
theorem pointCorrectionCircuit_tCount {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    ShorECDLP.tCount (pointCorrectionCircuit hC) ≤ 88453512 := by
  have he := pointWordProgram_tCount (pointCorrectionWordEdges hC)
  have hl := pointCorrectionWordEdges_length hC
  exact he.trans (by omega)

theorem pointCorrectionCircuit_usesOnly {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    PaperCircuitUsesOnly (List.range 839) (pointCorrectionCircuit hC) :=
  pointWordProgram_usesOnly _ (pointCorrectionWordEdges_adjacent hC)

theorem pointCorrectionCircuit_qubitCount {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    ShorECDLP.qubitCount (pointCorrectionCircuit hC) ≤ 839 :=
  pointWordProgram_qubitCount _ (pointCorrectionWordEdges_adjacent hC)

theorem pointCorrectionCircuit_HPFree {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    HPFree (pointCorrectionCircuit hC) := pointWordProgram_HPFree _

theorem pointCorrectionCircuit_wellFormed {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    CircuitWellFormed (pointCorrectionCircuit hC) :=
  pointWordProgram_wellFormed _ (pointCorrectionWordEdges_adjacent hC)

theorem pointCorrectionCircuit_ket {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) (s : BasisState) :
    Quantum.run (pointCorrectionCircuit hC) (Quantum.ket s)=
      Quantum.ket (run (pointCorrectionCircuit hC) s) :=
  Quantum.run_ket_agrees_classical _ s (pointCorrectionCircuit_HPFree hC)
end ShorECDLP.Paper2607_13816
