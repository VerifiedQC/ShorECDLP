import ShorECDLP.Submission.«2607_13816».Window.TrialPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
private theorem word_phase (ps : List (List Bool × List Bool)) :
    (pointWordPrimitives ps).phase=0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [pointWordPrimitives,pointWordEdgePrimitives,PrimitiveResources.add,ih]
private theorem leaf_zero (tree : UnaryActionTree) (q : Wire) (ws : List Wire) :
    tree.leafCostSum (fun _ _ => 0) q ws=0 := by
  induction tree generalizing q ws with
  | leaf label => rfl
  | node bit zero one ihz iho =>
    cases ws <;> simp only [UnaryActionTree.leafCostSum,ihz,iho,zero_add]
private theorem correction_phase (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (correctionTablePrimitives x y hc).phase=0 := by
  simp only [correctionTablePrimitives,word_phase,leaf_zero]
private theorem ge_phase (c : Bool) (n : Nat) : (constantGE256Primitives c n).phase=0 := by
  unfold constantGE256Primitives
  split_ifs <;> rfl
private theorem add_phase (c : Bool) (bs : List Bool) : (constantAdder256Primitives c bs).phase=0 := by
  unfold constantAdder256Primitives
  split_ifs <;> rfl
private theorem lookup_phase (table : Nat → Nat) : (pointLookupPrimitives table).phase=0 := by
  simp only [pointLookupPrimitives,lookupWordPrimitives,pointLookupAdderPrimitives,
    PrimitiveResources.add,ge_phase,add_phase,zero_add]
private theorem signed_phase (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (signedPointPrimitives x y hc).phase=0 := by
  simp [signedPointPrimitives,signedCoordinatePrimitives,signedPointLookupPrimitives,
    PrimitiveResources.add,lookup_phase,correction_phase]
private theorem schedule_phase (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) :
    (preparedSchedulePrimitives x y hc n j).phase=0 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp [preparedSchedulePrimitives,preparedCallPrimitives,PrimitiveResources.add,signed_phase,ih]
private theorem scalar_phase (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    (scalarWindowPrimitives P Q hP hQ hrP hrQ).phase=0 := by
  simp only [scalarWindowPrimitives,PrimitiveResources.add,schedule_phase,zero_add]

attribute [local irreducible] primitiveResources
private theorem prepared_resources (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    primitiveResources (preparedScalarProgram P Q hP hQ hrP hrQ)=
      (⟨0,514,0,0,0,0⟩ : PrimitiveResources).add
        (((⟨1,0,0,0,0,0⟩ : PrimitiveResources).add
          ((pointInitializePrimitives (axisWindowOffset P 17+axisWindowOffset Q 17)).add
            (scalarWindowPrimitives P Q hP hQ hrP hrQ))).add ⟨1,0,0,0,0,0⟩) := by
  have hx : primitiveResources (.unitary [.X 836] .done)=⟨1,0,0,0,0,0⟩ := by
    unfold primitiveResources
    rfl
  rw [preparedScalarProgram,primitiveResources_seq,scalarPhasePrepare_primitive,
    scalarComputeProgram,primitiveResources_seq,primitiveResources_seq,hx,
    initializedScalarProgram,primitiveResources_seq,pointInitialize_primitive,scalarWindowsProgram_primitive]

private theorem t_seq (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b

theorem windowTrialProgram_tCount_exact (P Q : ShorECDLP.Secp256k1.Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : ShorECDLP.order • P=0) (hrQ : ShorECDLP.order • Q=0) :
    (windowTrialProgram P Q hP hQ hrP hrQ).tCount=
      7*(scalarWindowPrimitives P Q hP hQ hrP hrQ).toffoli+65792 := by
  have hp : (primitiveResources (preparedScalarProgram P Q hP hQ hrP hrQ)).phase=0 := by
    rw [prepared_resources]
    simp only [PrimitiveResources.add,pointInitializePrimitives,scalar_phase,zero_add,add_zero]
  rw [windowTrialProgram,t_seq,primitiveResources_T_of_no_phase _ hp,
    prepared_resources,scalarFourierProgram_tCount_exact]
  simp only [PrimitiveResources.add,pointInitializePrimitives,zero_add,add_zero]

theorem secpWindowProgram_tCount_exact (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) :
    (secpWindowProgram Q hrQ).tCount=
      7*(secpWindowPrimitives Q hrQ).toffoli+(secpWindowPrimitives Q hrQ).phase := by
  classical
  unfold secpWindowProgram secpWindowPrimitives
  split
  · rfl
  · rw [windowTrialProgram_tCount_exact]
    simp only [windowTrialPrimitives,PrimitiveResources.add,pointInitializePrimitives,
      scalar_phase,zero_add,add_zero]

theorem secpWindowRepeatedProgram_tCount_exact (Q : ShorECDLP.Secp256k1.Point) (hrQ : ShorECDLP.order • Q=0) :
    (secpWindowRepeatedProgram Q hrQ).tCount=
      7*(repeatedWindowPrimitives Q hrQ).toffoli+(repeatedWindowPrimitives Q hrQ).phase := by
  rw [(secpWindowRepeatedProgram_resources Q hrQ).1,secpWindowProgram_tCount_exact]
  simp only [repeatedWindowPrimitives,scalePrimitives,PrimitiveResources.add,add_zero]
  omega
end
end ShorECDLP.Paper2607_13816
