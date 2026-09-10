import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedCoherent
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedIdentity
import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlaceSupport

namespace ShorECDLP.Paper2607_13816
open Classical Quantum

/-- The original 836 Figure 15 wires plus one external zero flag. Label 836 remains free. -/
def zeroAllowedLayout : List Wire := List.range 836 ++ [837]

private theorem zeroEq_support : PaperCircuitUsesOnly zeroAllowedLayout
    (computeEqConst (263::List.range' 264 255) 0 837 (List.range' 7 254)) := by
  apply (computeEqConst_usesOnly _ _ _ _).mono
  intro w hw
  simp [zeroAllowedLayout] at hw ⊢
  dsimp only [Wire] at *
  omega
private theorem zeroCX_support : PaperCircuitUsesOnly zeroAllowedLayout ([.CX 837 263] : Circuit) := by
  intro g hg w hw
  simp only [List.mem_singleton] at hg
  subst g
  simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl <;> simp [zeroAllowedLayout]
private theorem unitary_support (c : Circuit) (hc : PaperCircuitUsesOnly zeroAllowedLayout c) :
    (AdaptiveCircuit.unitary c .done).wires ⊆ zeroAllowedLayout := by
  intro w hw
  simp only [AdaptiveCircuit.wires,List.append_nil] at hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  exact hc g hg w hw
private theorem seq_support (a b : AdaptiveCircuit)
    (ha : a.wires ⊆ zeroAllowedLayout) (hb : b.wires ⊆ zeroAllowedLayout) :
    (a.seq b).wires ⊆ zeroAllowedLayout := by
  intro w hw
  rw [modularWires_seq] at hw
  exact hw.elim (fun h => ha h) (fun h => hb h)
private theorem zero_wrapper_support (a : AdaptiveCircuit) (ha : a.wires ⊆ List.range 836) :
    (((AdaptiveCircuit.unitary fig15ZeroPrepare .done).seq a).seq (.unitary fig15ZeroRestore .done)).wires ⊆ zeroAllowedLayout := by
  apply seq_support
  · apply seq_support
    · exact unitary_support _ (zeroEq_support.append zeroCX_support)
    · intro w hw
      exact List.mem_append_left _ (ha hw)
  · exact unitary_support _ (zeroCX_support.append zeroEq_support)

theorem secp256k1ZeroAllowedDivision_wires_subset : secp256k1ZeroAllowedDivision.wires ⊆ zeroAllowedLayout :=
  zero_wrapper_support _ secp256k1InPlaceDivision_wires_subset
theorem secp256k1ZeroAllowedMultiplication_wires_subset : secp256k1ZeroAllowedMultiplication.wires ⊆ zeroAllowedLayout :=
  zero_wrapper_support _ secp256k1InPlaceMultiplication_wires_subset
private theorem count837 (a : AdaptiveCircuit) (ha : a.wires ⊆ zeroAllowedLayout) : a.qubitCount≤837 := by
  have hs : a.wires.dedup.toFinset ⊆ zeroAllowedLayout.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (ha (by simpa using hw))
  have hh := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (show zeroAllowedLayout.Nodup by
      simp only [zeroAllowedLayout,List.nodup_append,List.nodup_range,List.nodup_singleton,
        true_and,List.mem_range,List.mem_singleton]
      intro w hw v hv he
      subst v
      subst w
      exact (by decide : ¬((837 : Nat)<836)) hw)] at hh
  simpa only [AdaptiveCircuit.qubitCount,zeroAllowedLayout,List.length_append,List.length_range,
    List.length_singleton] using hh

theorem secp256k1ZeroAllowedDivision_qubitCount : secp256k1ZeroAllowedDivision.qubitCount≤837 :=
  count837 _ secp256k1ZeroAllowedDivision_wires_subset
theorem secp256k1ZeroAllowedMultiplication_qubitCount : secp256k1ZeroAllowedMultiplication.qubitCount≤837 :=
  count837 _ secp256k1ZeroAllowedMultiplication_wires_subset

private theorem zeroPrepare_T : ShorECDLP.tCount fig15ZeroPrepare=3563 := by
  rw [fig15ZeroPrepare,nonzeroInputPrepare,tCount_append,computeEqConst_tCount _ _ _ _ (by simp)]
  simp [mcxVChainToffoliCost,ShorECDLP.tCount,tCost]
private theorem zeroRestore_T : ShorECDLP.tCount fig15ZeroRestore=3563 := by
  rw [fig15ZeroRestore,nonzeroInputRestore,tCount_append,computeEqConst_tCount _ _ _ _ (by simp)]
  simp [mcxVChainToffoliCost,ShorECDLP.tCount,tCost]
private theorem seq_T (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
private theorem zero_wrapper_counts (a : AdaptiveCircuit) :
    (((AdaptiveCircuit.unitary fig15ZeroPrepare .done).seq a).seq (.unitary fig15ZeroRestore .done)).tCount=
      a.tCount+7126 ∧
    (((AdaptiveCircuit.unitary fig15ZeroPrepare .done).seq a).seq (.unitary fig15ZeroRestore .done)).measurementCount=
      a.measurementCount := by
  simp only [seq_T,modularMeasurements_seq,AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount,
    zeroPrepare_T,zeroRestore_T,Nat.add_zero,Nat.zero_add]
  constructor
  · omega
  · trivial
attribute [local irreducible] secp256k1InPlaceDivision secp256k1InPlaceMultiplication

theorem secp256k1ZeroAllowedDivision_resources :
    secp256k1ZeroAllowedDivision.tCount=269612833 ∧
    secp256k1ZeroAllowedDivision.measurementCount=11343835 ∧
    secp256k1ZeroAllowedDivision.qubitCount≤837 := by
  have hh := zero_wrapper_counts secp256k1InPlaceDivision
  rw [secp256k1InPlaceDivision_T,secp256k1InPlaceDivision_measurements] at hh
  exact ⟨hh.1,hh.2,secp256k1ZeroAllowedDivision_qubitCount⟩
theorem secp256k1ZeroAllowedMultiplication_resources :
    secp256k1ZeroAllowedMultiplication.tCount=269612833 ∧
    secp256k1ZeroAllowedMultiplication.measurementCount=11343835 ∧
    secp256k1ZeroAllowedMultiplication.qubitCount≤837 := by
  have hh := zero_wrapper_counts secp256k1InPlaceMultiplication
  rw [secp256k1InPlaceMultiplication_T,secp256k1InPlaceMultiplication_measurements] at hh
  exact ⟨hh.1,hh.2,secp256k1ZeroAllowedMultiplication_qubitCount⟩
/-- Coherence and physical resources of the same zero-extended division program. -/
theorem secp256k1ZeroAllowedDivision_certificate :
    CoherentlyImplementsOn secp256k1ZeroAllowedDivision
      (Finsupp.lmapDomain ℂ ℂ zeroAllowedDivisionOutputState) Secp256k1ZeroAllowedInputValid ∧
    secp256k1ZeroAllowedDivision.tCount=269612833 ∧
    secp256k1ZeroAllowedDivision.measurementCount=11343835 ∧
    secp256k1ZeroAllowedDivision.qubitCount≤837 :=
  ⟨secp256k1ZeroAllowedDivision_coherent,secp256k1ZeroAllowedDivision_resources⟩
/-- Coherence and physical resources of the same zero-extended multiplication program. -/
theorem secp256k1ZeroAllowedMultiplication_certificate :
    CoherentlyImplementsOn secp256k1ZeroAllowedMultiplication
      (Finsupp.lmapDomain ℂ ℂ zeroAllowedMultiplicationOutputState) Secp256k1ZeroAllowedInputValid ∧
    secp256k1ZeroAllowedMultiplication.tCount=269612833 ∧
    secp256k1ZeroAllowedMultiplication.measurementCount=11343835 ∧
    secp256k1ZeroAllowedMultiplication.qubitCount≤837 :=
  ⟨secp256k1ZeroAllowedMultiplication_coherent,secp256k1ZeroAllowedMultiplication_resources⟩
end ShorECDLP.Paper2607_13816
