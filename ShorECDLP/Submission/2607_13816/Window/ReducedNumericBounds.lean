import ShorECDLP.Submission.«2607_13816».Window.ReducedTCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
private theorem table_leaf_bound (bits : List Wire) (base stride q : Nat) (path : List Wire)
    (cost : Nat → Wire → Nat) (n : Nat) (h : ∀ a w, cost a w≤n) :
    (tableAddressTree bits base stride).leafCostSum cost q path≤n*2^bits.length := by
  induction bits generalizing base stride q path with
  | nil => simpa [tableAddressTree,UnaryActionTree.leafCostSum] using h base q
  | cons bit bits ih =>
    cases path with
    | nil => simp [tableAddressTree,UnaryActionTree.leafCostSum]
    | cons p ps =>
      simp only [tableAddressTree,UnaryActionTree.leafCostSum,List.length_cons,pow_succ]
      have h0 := ih base (2*stride) p ps
      have h1 := ih (base+stride) (2*stride) p ps
      rw [←Nat.mul_assoc]
      omega
private theorem correction_bound (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (correctionTablePrimitives x y hc).toffoli≤823285841919 := by
  have h := table_leaf_bound correctionTableBits 0 1 836 correctionTablePath
    (fun a _ => (pointWordPrimitives (pointCorrectionWordEdges (hc a))).toffoli)
    (3061*4104) (by
      intro a w
      have he := (pointCorrectionCircuit_primitive_bounds (hc a)).2.2.2.1
      rw [pointCorrectionCircuit_primitive_exact] at he
      exact he.trans (Nat.mul_le_mul_left 3061 (pointCorrectionWordEdges_length (hc a))))
  change _≤_ at h
  norm_num only [correctionTableBits,List.length_range'] at h
  change (tableAddressTree correctionTableBits 0 1).leafCostSum
    (fun a _ => (pointWordPrimitives (pointCorrectionWordEdges (hc a))).toffoli) 836 correctionTablePath+65535≤_
  unfold correctionTableBits
  omega
private theorem lookup_toffoli (table : Nat → Nat) : (pointLookupPrimitives table).toffoli=68347 := by
  have hn : pointLookupAdderPrimitives.toffoli=2813 := by decide +kernel
  simp only [pointLookupPrimitives,lookupWordPrimitives,PrimitiveResources.add,pointLookupAddress,
    List.length_range',hn]
  norm_num
private theorem coordinate_toffoli (x y : Nat → Nat) : (signedCoordinatePrimitives x y).toffoli=72886218 := by
  simp only [signedCoordinatePrimitives,signedPointLookupPrimitives,PrimitiveResources.add,lookup_toffoli]
private theorem prepared_toffoli (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (preparedCallPrimitives x y hc).toffoli≤823365455081 := by
  have h := correction_bound (signedCorrectionX x) (signedCorrectionY y) (signedCorrection_nonsingular x y hc)
  simp only [preparedCallPrimitives,signedPointPrimitives,PrimitiveResources.add,coordinate_toffoli]
  omega
private theorem schedule_toffoli (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    (preparedSchedulePrimitives x y hc n j).toffoli≤n*823365455081 := by
  induction n generalizing j with
  | zero => simp [preparedSchedulePrimitives]
  | succ n ih =>
    have hh := prepared_toffoli (x j) (y j) (hc j)
    have ht := ih (j+1)
    simp only [preparedSchedulePrimitives,PrimitiveResources.add]
    omega
theorem reducedScalar_toffoli_bound (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    (reducedScalarPrimitives P Q hP hQ hrP hrQ).toffoli≤23054232807803 := by
  have hl := schedule_toffoli (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
    (fun k => oddWindowTable_valid P hP hrP (k-0)) 15 1
  have hr := schedule_toffoli (fun k => oddWindowX Q (k-17)) (fun k => oddWindowY Q (k-17))
    (fun k => oddWindowTable_valid Q hQ hrQ (k-17)) 13 17
  simp only [reducedScalarPrimitives,physicalPointLookupPrimitives,PrimitiveResources.add]
  omega
theorem reducedWindowTrial_tCount_bound (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    (reducedWindowTrialProgram P Q hP hQ hrP hrQ).tCount≤161379629708789 := by
  rw [reducedWindowTrialProgram_tCount_exact]
  have h := reducedScalar_toffoli_bound P Q hP hQ hrP hrQ
  omega
theorem reducedSecpWindow_tCount_bound (Q : ShorECDLP.Secp256k1.Point)
    (hrQ : ShorECDLP.order • Q=0) :
    (reducedSecpWindowProgram Q hrQ).tCount≤161379629708789 := by
  classical
  unfold reducedSecpWindowProgram
  split
  · decide
  · exact reducedWindowTrial_tCount_bound _ _ _ _ _ _

theorem reducedSecpWindowRepeated_tCount_bound (Q : ShorECDLP.Secp256k1.Point)
    (hrQ : ShorECDLP.order • Q=0) :
    (reducedSecpWindowRepeatedProgram Q hrQ).tCount≤4195870372428514 := by
  rw [(reducedSecpWindowRepeatedProgram_resources Q hrQ).1]
  have h := reducedSecpWindow_tCount_bound Q hrQ
  omega
end
end ShorECDLP.Paper2607_13816
