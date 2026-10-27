import ShorECDLP.Submission.«2607_13816».Challenge.WindowNegation
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge

def batchWorkspace : List Wire := List.range' 1024 2565 ++ List.range' 4102 512
def BatchedPointReady (s : BasisState) : Prop := PointLookupValid s ∧ Clean batchWorkspace s

theorem batchWorkspace_outside (w : Wire) (hw : w ∈ batchWorkspace) : w ∉ pointLogicalWires := by
  simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hw
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  dsimp only [Wire] at *
  omega

theorem batchPlacement_aux (w : Wire) (hw : w ∈ 836::pointLookupPath) : batchPlacement w=w := by
  change batchPlacementFn w=w
  simp only [pointLookupPath,List.mem_cons,List.mem_range'_1] at hw
  unfold batchPlacementFn
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem batchedPointReady_batch (s : BasisState) (hs : BatchedPointReady s) :
    BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro w hw
    change s (batchPlacement w)=false
    rw [batchPlacement_aux w (List.mem_cons_of_mem _ hw)]
    apply hs.1.1.1 w
    simp only [pointLookupPath,List.mem_range'_1] at hw
    simp only [List.mem_append,List.mem_range'_1]
    omega
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    change s (batchPlacement (1024+3079+i.val))=false
    rw [batchPlacement_high _ (by dsimp only [Wire]; omega)]
    apply hs.2
    simp only [batchWorkspace,List.mem_append,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · change s (batchPlacement 4102)=false
    rw [batchPlacement_high _ (by decide)]
    exact hs.2 _ (by simp [batchWorkspace])
  · change s (batchPlacement 836)=true
    rw [batchPlacement_aux _ (by simp)]
    exact hs.1.2

theorem batchedPointReady_words (s : BasisState) (hs : BatchedPointReady s) :
    ∀ j : Fin 6, j ≠ 5 → (relabelBasis batchPlacement.symm s) ∘ batchWord 1024 j = fun _ => false := by
  intro j hj
  funext i
  change s (batchPlacement (batchWord 1024 j i))=false
  have hlo : 1024 ≤ batchWord 1024 j i := by dsimp [batchWord,Wire]; omega
  have hhi : batchWord 1024 j i < 3589 := by
    have hjv : j.val ≠ 5 := by intro he; apply hj; exact Fin.ext he
    dsimp [batchWord]
    dsimp only [Wire]
    omega
  rw [batchPlacement_endpoints _ hlo hhi]
  exact hs.2 _ (by simp only [batchWorkspace,List.mem_append,List.mem_range'_1]; dsimp only [Wire] at *; omega)

theorem windowYNegateState_batchedReady (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (windowYNegateState s) := by
  have hf := (windowYNegateState_correct s hs.1.1).2
  refine ⟨⟨windowYNegateState_ready s hs.1.1,?_⟩,?_⟩
  · rw [hf 836 (by decide)]
    exact hs.1.2
  · intro w hw
    rw [hf w (by
      intro hy
      exact batchWorkspace_outside w hw (List.mem_append_right _ (List.mem_append_left _ hy)))]
    exact hs.2 w hw
theorem signedLookupCoordinateState_batchedReady (x y : Nat → Nat) (s : BasisState)
    (hs : BatchedPointReady s) : BatchedPointReady (signedLookupCoordinateState x y s) := by
  refine ⟨signedLookupCoordinateState_ready x y s hs.1,?_⟩
  intro w hw
  have hout := batchWorkspace_outside w hw
  rw [signedLookupCoordinateState_frame x y s hs.1 w
    (fun hx => hout (List.mem_append_left _ hx))
    (fun hy => hout (List.mem_append_right _ (List.mem_append_left _ hy)))]
  exact hs.2 w hw

theorem batchPlacement_address (w : Wire) (hw : w ∈ pointLookupAddress) : batchPlacement w=w := by
  change batchPlacementFn w=w
  simp only [pointLookupAddress,List.mem_range'_1] at hw
  unfold batchPlacementFn
  split_ifs <;> dsimp only [Wire] at * <;> omega

private theorem address_frame (bits : List Wire) (s t : BasisState)
    (h : ∀ w ∈ bits, s w=t w) : tableAddressValue bits s=tableAddressValue bits t := by
  induction bits with
  | nil => rfl
  | cons w ws ih =>
    simp only [tableAddressValue,h w (by simp),ih (fun w hw => h w (by simp [hw]))]

theorem batchWindowTree_route (s : BasisState) :
    batchWindowTree.routeLabel (relabelBasis batchPlacement.symm s) = tableAddressValue pointLookupAddress s := by
  rw [batchWindowTree,tableAddressTree_route,zero_add,one_mul]
  apply address_frame
  intro w hw
  change s (batchPlacement w)=s w
  rw [batchPlacement_address w hw]

theorem windowYNegateState_address (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    tableAddressValue pointLookupAddress (windowYNegateState s)=tableAddressValue pointLookupAddress s := by
  apply address_frame
  intro w hw
  apply (windowYNegateState_correct s hs).2 w
  simp only [pointLookupAddress,List.mem_range'_1] at hw
  simp only [List.mem_range'_1]
  omega

theorem pointWrite_batchedReady (P : Point) (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (pointWrite P s) := by
  refine ⟨⟨pointWrite_valid P s hs.1.1,?_⟩,?_⟩
  · rw [pointWrite_frame P s 836 (by decide +kernel)]
    exact hs.1.2
  · intro w hw
    rw [pointWrite_frame P s w (batchWorkspace_outside w hw)]
    exact hs.2 w hw

end ShorECDLP.Paper2607_13816.ChallengeMigration
