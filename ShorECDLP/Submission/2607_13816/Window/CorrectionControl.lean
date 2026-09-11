import ShorECDLP.Framework.Quantum.Relabel
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointTotalCircuit
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem classical_relabel_run (e : Wire ≃ Wire) (c : Circuit) (s : BasisState) :
    Classical.run (c.map (Gate.relabel e)) (Quantum.relabelBasis e s)=Quantum.relabelBasis e (Classical.run c s) := by
  induction c generalizing s with
  | nil => rfl
  | cons g c ih =>
    simp only [List.map_cons,Classical.run_cons]
    have h : Classical.applyGate (g.relabel e) (Quantum.relabelBasis e s)=Quantum.relabelBasis e (Classical.applyGate g s) := by
      cases g <;> simp [Gate.relabel,Classical.applyGate,Quantum.relabelBasis_upd,Quantum.relabelBasis_at]
    rw [h,ih]

/-- Reassign the existing physical control, with no inserted swap gates. -/
def pointCorrectionAt {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire) : Circuit :=
  (pointCorrectionCircuit hC).map (Gate.relabel (Equiv.swap 836 q))

theorem pointCorrectionAt_run {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire) (s : BasisState) :
    Classical.run (pointCorrectionAt hC q) s =
      Quantum.relabelBasis (Equiv.swap 836 q)
        (Classical.run (pointCorrectionCircuit hC) (Quantum.relabelBasis (Equiv.swap 836 q) s)) := by
  have h := classical_relabel_run (Equiv.swap 836 q) (pointCorrectionCircuit hC)
    (Quantum.relabelBasis (Equiv.swap 836 q) s)
  have hi : Quantum.relabelBasis (Equiv.swap 836 q) (Quantum.relabelBasis (Equiv.swap 836 q) s)=s := by
    funext w
    simp [Quantum.relabelBasis]
  rw [hi] at h
  exact h

private theorem correction_root_outside : 836∉pointLogicalWires ∧
    836∉(558::559::pointCorrectionScratch) := by decide +kernel

private theorem correction_relabel_clean (q : Wire) (hq : q∉(558::559::pointCorrectionScratch))
    (s : BasisState) (hs : Clean (558::559::pointCorrectionScratch) s) :
    Clean (558::559::pointCorrectionScratch) (Quantum.relabelBasis (Equiv.swap 836 q) s) := by
  intro w hw
  have h0 : w≠836 := fun he => correction_root_outside.2 (he ▸ hw)
  have h1 : w≠q := fun he => hq (he ▸ hw)
  simpa [Quantum.relabelBasis,Equiv.swap_apply_def,h0,h1] using hs w hw

private theorem correction_relabel_logical (q : Wire) (hq : q∉pointLogicalWires)
    (w : Wire) (hw : w∈pointLogicalWires) : (Equiv.swap 836 q) w=w := by
  have h0 : w≠836 := fun he => correction_root_outside.1 (he ▸ hw)
  have h1 : w≠q := fun he => hq (he ▸ hw)
  simp [Equiv.swap_apply_def,h0,h1]

theorem pointCorrectionAt_frame {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire)
    (hq : q∉pointLogicalWires) (hqw : q∉(558::559::pointCorrectionScratch))
    (s : BasisState) (hs : Clean (558::559::pointCorrectionScratch) s) :
    ∀ w, w∉pointLogicalWires → Classical.run (pointCorrectionAt hC q) s w=s w := by
  intro w hw
  have hf := pointCorrectionCircuit_frame hC _ (correction_relabel_clean q hqw s hs)
  have ho : (Equiv.swap 836 q) w∉pointLogicalWires := by
    intro hm
    have he := correction_relabel_logical q hq _ hm
    have hh := congrArg (Equiv.swap 836 q) he
    have hew : w=(Equiv.swap 836 q) w := by simpa using hh.symm
    exact hw (hew.symm ▸ hm)
  rw [pointCorrectionAt_run]
  simp only [Quantum.relabelBasis,Equiv.symm_swap]
  rw [hf _ ho]
  simp [Quantum.relabelBasis]


theorem pointCorrectionAt_disabled {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire)
    (hqw : q∉(558::559::pointCorrectionScratch)) (s : BasisState)
    (hs : Clean (558::559::pointCorrectionScratch) s) (hq : s q=false) :
    Classical.run (pointCorrectionAt hC q) s=s := by
  rw [pointCorrectionAt_run,pointCorrectionCircuit_disabled hC _ (correction_relabel_clean q hqw s hs)
    (by simpa [Quantum.relabelBasis] using hq)]
  funext w
  simp [Quantum.relabelBasis]

theorem pointCorrectionAt_HPFree {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire) : HPFree (pointCorrectionAt hC q) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  have hh := pointCorrectionCircuit_HPFree hC a ha
  cases a <;> simp_all [IsClassicalGate,Gate.relabel]

theorem pointCorrectionAt_ket {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire) (s : BasisState) :
    Quantum.run (pointCorrectionAt hC q) (ket s)=ket (Classical.run (pointCorrectionAt hC q) s) :=
  Quantum.run_ket_agrees_classical _ s (pointCorrectionAt_HPFree hC q)


private theorem correction_relabel_word (q : Wire) (hq : q∉pointLogicalWires) (s : BasisState) :
    wireValues pointLogicalWires (Quantum.relabelBasis (Equiv.swap 836 q) s)=wireValues pointLogicalWires s := by
  apply List.map_congr_left
  intro w hw
  simp only [Quantum.relabelBasis,Equiv.symm_swap,correction_relabel_logical q hq w hw]

theorem pointCorrectionAt_correct {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire)
    (hq : q∉pointLogicalWires) (hqw : q∉(558::559::pointCorrectionScratch))
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState)
    (hs : Clean (558::559::pointCorrectionScratch) s) (hactive : s q=true)
    (hw : wireValues pointLogicalWires s=pointCoordinateWord (fig14EncodedEquiv x y (fig14PointEncoding P))) :
    wireValues pointLogicalWires (Classical.run (pointCorrectionAt hC q) s)=
      pointCoordinateWord (fig14PointEncoding (P+(.some hC))) := by
  rw [pointCorrectionAt_run,correction_relabel_word q hq]
  apply pointCorrectionCircuit_correct hC P _ (correction_relabel_clean q hqw s hs)
  · simpa [Quantum.relabelBasis] using hactive
  · rw [correction_relabel_word q hq]; exact hw


theorem pointCorrectionAt_wellFormed {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire) : CircuitWellFormed (pointCorrectionAt hC q) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  have hh := pointCorrectionCircuit_wellFormed hC a ha
  cases a <;> simp_all [Gate.WellFormed,Gate.relabel]

theorem pointCorrectionAt_tCount {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire) :
    ShorECDLP.tCount (pointCorrectionAt hC q)=ShorECDLP.tCount (pointCorrectionCircuit hC) := by
  have h (g : Gate) : tCost (g.relabel (Equiv.swap 836 q))=tCost g := by cases g <;> rfl
  simp only [pointCorrectionAt,ShorECDLP.tCount,List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  exact h g


theorem pointCorrectionAt_wires {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire) :
    circuitWires (pointCorrectionAt hC q)=(circuitWires (pointCorrectionCircuit hC)).map (Equiv.swap 836 q) := by
  have h := AdaptiveCircuit.relabel_wires (Equiv.swap 836 q) (.unitary (pointCorrectionCircuit hC) .done)
  simpa only [AdaptiveCircuit.relabel,AdaptiveCircuit.wires,List.append_nil,pointCorrectionAt] using h

theorem pointCorrectionAt_support {x y : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x y) (q : Wire) (hq : q<855) :
    circuitWires (pointCorrectionAt hC q) ⊆ List.range 855 := by
  intro w hw
  rw [pointCorrectionAt_wires] at hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  obtain ⟨g,hg,hv⟩ := List.mem_flatMap.mp hv
  have hh := pointCorrectionCircuit_usesOnly hC g hg v hv
  simp only [List.mem_range] at hh ⊢
  by_cases h0 : v=836
  · subst v; simpa using hq
  by_cases h1 : v=q
  · subst v; simp
  · simp only [Equiv.swap_apply_def,h0,h1,if_false]
    omega

end
end ShorECDLP.Paper2607_13816
