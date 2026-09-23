import ShorECDLP.Submission.«2607_13816».Window.RawRegisters
import ShorECDLP.Submission.«2607_13816».Window.Uniform
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime order) := ⟨order_prime⟩

private theorem scalar_injective (P : Point) (hP : P≠0) (hr : order • P=0)
    (n : Nat) (hn : n≤order) (A : Point) :
    Function.Injective (fun a : Fin n => a.val • P+A) := by
  have ho : addOrderOf P=order := addOrderOf_eq_prime hr hP
  intro a b he
  apply Fin.ext
  apply nsmul_injOn_Iio_addOrderOf (x:=P)
  · change a.val<addOrderOf P
    rw [ho]
    exact lt_of_lt_of_le a.isLt hn
  · change b.val<addOrderOf P
    rw [ho]
    exact lt_of_lt_of_le b.isLt hn
  · exact add_right_cancel he

private theorem one_step_card (P : Point) (hP : P≠0) (hr : order • P=0)
    (n : Nat) (hn : n≤order) (A C : Point) :
    (Finset.univ.filter (fun a : Fin n => a.val • P+A∈fig14ExceptionalPoints C)).card≤4 := by
  let F := Finset.univ.filter (fun a : Fin n => a.val • P+A∈fig14ExceptionalPoints C)
  have hs : F.image (fun a => a.val • P+A) ⊆ fig14ExceptionalPoints C := by
    intro B hB
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hB
    exact (Finset.mem_filter.mp ha).2
  have hc := (Finset.card_le_card hs).trans (fig14ExceptionalPoints_card_le C)
  rw [Finset.card_image_of_injective F (scalar_injective P hP hr n hn A)] at hc
  exact hc

/-- A path with constants fixed independently of the varying scalar excludes
at most four scalars per step, provided that scalar interval is injective. -/
theorem rawAlgebraicExclusions_card (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (js : List Nat)
    (P : Point) (hP : P≠0) (hr : order • P=0) (n : Nat) (hn : n≤order)
    (A : Point) (s : BasisState) :
    (Finset.univ.filter (fun a : Fin n => ¬rawAlgebraicExclusions x y hc js (a.val • P+A) s)).card≤4*js.length := by
  induction js generalizing A with
  | nil => simp [rawAlgebraicExclusions]
  | cons j js ih =>
    let C := preparedWindowDelta x y hc j s
    let F := Finset.univ.filter (fun a : Fin n => a.val • P+A∈fig14ExceptionalPoints C)
    let G := Finset.univ.filter (fun a : Fin n => ¬rawAlgebraicExclusions x y hc js (a.val • P+(A+C)) s)
    have he : (Finset.univ.filter (fun a : Fin n => ¬rawAlgebraicExclusions x y hc (j::js) (a.val • P+A) s))=F∪G := by
      ext a
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,rawAlgebraicExclusions,
        not_and_or,not_not,add_assoc,F,G,C]
    rw [he]
    have hf := one_step_card P hP hr n hn A C
    have hg := ih (A+C)
    have hu := Finset.card_union_le F G
    change F.card≤4 at hf
    change G.card≤4*js.length at hg
    simp only [List.length_cons]
    omega

/-- Vary only the first physical 16-bit P window, preserving every other wire. -/
def rawFirstWordState (a : Fin 65536) (s : BasisState) : BasisState :=
  phaseWordState (List.range' 855 16) (constantBits 16 a.val) s

private theorem first_frame (a : Fin 65536) (s : BasisState) (w : Wire)
    (hw : w∉List.range' 855 16) : rawFirstWordState a s w=s w :=
  phaseWordState_frame _ _ _ _ hw

theorem rawFirstWordState_address (a : Fin 65536) (s : BasisState) :
    tableAddressValue (List.range' 855 16) (rawFirstWordState a s)=a.val := by
  have hw := phaseWordState_word (List.range' 855 16) (List.nodup_range') (constantBits 16 a.val)
    (by simp only [constantBits_length,List.length_range']) s
  have he (bits : List Wire) (t : BasisState) : tableAddressValue bits t=boolWordToNat (wireValues bits t) := by
    induction bits with
    | nil => rfl
    | cons w ws ih => simp only [tableAddressValue,wireValues,List.map_cons,boolWordToNat] at *; rw [ih]
  rw [he]
  change boolWordToNat (wireValues _ (phaseWordState _ _ s))=_
  rw [hw,boolWordToNat_constantBits]
  exact Nat.mod_eq_of_lt a.isLt

/-- No remaining call reads the first scalar window, including during address
reflection. This is the independence needed for the finite counting argument. -/
theorem preparedWindowDelta_firstWord (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (j : Nat) (hj : 1≤j)
    (a : Fin 65536) (s : BasisState) :
    preparedWindowDelta x y hc j (rawFirstWordState a s)=preparedWindowDelta x y hc j s := by
  have hr := first_frame a s 836 (by decide)
  have hz := first_frame a s (windowBankStart j+15) (by
    simp only [List.mem_range'_1,windowBankStart]; dsimp only [Wire] at *; omega)
  have hf (w : Wire) (hw : w∈List.range' (windowBankStart j) 16) :
      windowPrepareState j (rawFirstWordState a s) w=windowPrepareState j s w := by
    have hb := first_frame a s w (by
      simp only [List.mem_range'_1,windowBankStart] at hw ⊢; dsimp only [Wire] at *; omega)
    simp only [windowPrepareState,signedAddressState,tableXorState,hr,hz,hb]
  have hsign := hf (windowBankStart j+15) (by simp only [List.mem_range'_1]; dsimp only [Wire]; omega)
  have ha : tableAddressValue (List.range' (windowBankStart j) 15) (windowPrepareState j (rawFirstWordState a s))=
      tableAddressValue (List.range' (windowBankStart j) 15) (windowPrepareState j s) := by
    apply tableAddressValue_congr
    intro w hw
    apply hf w
    simp only [List.mem_range'_1] at hw ⊢
    omega
  simp only [preparedWindowDelta,windowPointDelta,hsign,ha]

theorem rawAlgebraicExclusions_firstWord (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (js : List Nat)
    (hj : ∀ j∈js,1≤j) (a : Fin 65536) (A : Point) (s : BasisState) :
    rawAlgebraicExclusions x y hc js A (rawFirstWordState a s)=rawAlgebraicExclusions x y hc js A s := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih =>
    simp only [rawAlgebraicExclusions,preparedWindowDelta_firstWord x y hc j (hj j (by simp))]
    rw [ih (fun k hk => hj k (by simp [hk]))]

private theorem initial_affine (P Q : Point) (a : Fin 65536) (s : BasisState) :
    reducedRawInitialPoint P Q (rawFirstWordState a s)=a.val • P+
      (axisWindowOffset P 16+axisWindowOffset Q 13+signedWindowHalfPoint P order-(32768:ℤ) • P) := by
  unfold reducedRawInitialPoint
  rw [rawFirstWordState_address]
  simp only [firstWindowTable,signedWindowDigit,sub_zsmul,natCast_zsmul]
  norm_num
  abel

/-- For every fixed assignment of the other wires, at most 112 of the 65,536
first-window values violate the actual 28-call path exclusions. This is a
conditional counting bound, not yet a quantum sampling-error theorem. -/
theorem reducedRawExclusions_firstWord_card (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    (Finset.univ.filter (fun a : Fin 65536 => ¬reducedRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s))).card≤112 := by
  let hc (j a : Nat) : curve.toAffine.Nonsingular (reducedRawX P Q j a) (reducedRawY P Q j a) := by
    unfold reducedRawX reducedRawY
    split
    · exact oddWindowTable_valid P hP hrP j a
    · exact oddWindowTable_valid Q hQ hrQ (j-17) a
  have hj : ∀ j∈reducedRawIndices,1≤j := by
    intro j hj
    simp only [reducedRawIndices,List.mem_append,List.mem_range'_1] at hj
    omega
  have he (a : Fin 65536) : reducedRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s)=
      rawAlgebraicExclusions (reducedRawX P Q) (reducedRawY P Q) hc reducedRawIndices
        (a.val • P+(axisWindowOffset P 16+axisWindowOffset Q 13+signedWindowHalfPoint P order-(32768:ℤ) • P)) s := by
    change rawAlgebraicExclusions _ _ hc _ _ _=_
    rw [rawAlgebraicExclusions_firstWord _ _ hc _ hj,initial_affine]
  simp only [he]
  have h := rawAlgebraicExclusions_card (reducedRawX P Q) (reducedRawY P Q) hc reducedRawIndices
    P hP hrP 65536 (by norm_num [order])
    (axisWindowOffset P 16+axisWindowOffset Q 13+signedWindowHalfPoint P order-(32768:ℤ) • P) s
  simpa only [reducedRawIndices,List.length_append,List.length_range'] using h


/-- Uniformly varying the first word while holding the other wires fixed gives
an excluded fraction at most 7/4096. Identifying a quantum input's Born weights
with this conditional experiment is a separate obligation. -/
theorem reducedRawExclusions_firstWord_fraction (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    ((Finset.univ.filter (fun a : Fin 65536 =>
      ¬reducedRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s))).card : ℝ)/65536≤7/4096 := by
  have h := reducedRawExclusions_firstWord_card P Q hP hQ hrP hrQ s
  have hr : ((Finset.univ.filter (fun a : Fin 65536 =>
      ¬reducedRawExclusions P Q hP hQ hrP hrQ (rawFirstWordState a s))).card : ℝ)≤112 := by
    exact_mod_cast h
  calc
    _ ≤ (112:ℝ)/65536 := div_le_div_of_nonneg_right hr (by norm_num)
    _ = 7/4096 := by norm_num

end
end ShorECDLP.Paper2607_13816
