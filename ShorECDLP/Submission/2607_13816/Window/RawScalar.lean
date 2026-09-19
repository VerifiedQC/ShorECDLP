import ShorECDLP.Submission.«2607_13816».Window.RawPoint
import ShorECDLP.Submission.«2607_13816».Window.ReducedScalar
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

private theorem signed_y (y : Nat → ShorECDLP.Fp) (s : BasisState) :
    (signedPointTableValue (fun a => (y a).val) s : ShorECDLP.Fp)=
      if s 854 then y (tableAddressValue pointLookupAddress s)
      else -y (tableAddressValue pointLookupAddress s) := by
  have hv : signedPointTableValue (fun a => (y a).val) s=
      (if s 854 then y (tableAddressValue pointLookupAddress s)
      else -y (tableAddressValue pointLookupAddress s)).val := by
    cases h : s 854 <;> simp [signedPointTableValue,h,ZMod.neg_val']
  rw [hv,ZMod.natCast_zmod_val]

private theorem selected_valid (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (j : Nat) (s : BasisState) :
    curve.toAffine.Nonsingular
      ((x j (tableAddressValue pointLookupAddress (preparedRawPointInput j s))).val : ShorECDLP.Fp)
      (signedPointTableValue (fun a => (y j a).val) (preparedRawPointInput j s) : ShorECDLP.Fp) := by
  rw [ZMod.natCast_zmod_val,signed_y]
  split
  · exact hc _ _
  · simpa only [negY_eq_neg] using
      (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr (hc j _)

private theorem selected_point (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (j : Nat) (s : BasisState) :
    WeierstrassCurve.Affine.Point.some (selected_valid x y hc j s)=preparedWindowDelta x y hc j s := by
  have ha := parkedWindow_address (windowBankStart j) (by unfold windowBankStart; omega)
    (windowPrepareState j s)
  have hz : preparedRawPointInput j s 854=windowPrepareState j s (windowBankStart j+15) := by
    simp only [preparedRawPointInput,relabelBasis,Equiv.symm_symm]
    rw [show (854:Wire)=839+15 by rfl,windowAddressPerm_address _ _ 15 (by decide)]
  have he := signed_y (y j) (preparedRawPointInput j s)
  change tableAddressValue pointLookupAddress (preparedRawPointInput j s)=_ at ha
  simp only [hz,ha] at he
  unfold preparedWindowDelta windowPointDelta
  generalize selected_valid x y hc j s = h
  revert h
  rw [ZMod.natCast_zmod_val,ha,he]
  cases windowPrepareState j s (windowBankStart j+15) <;> intro h <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp only [negY_eq_neg]

/-- The raw call has the same complete point output as the repaired call when
its incoming point avoids the four exceptions of the actual selected table entry. -/
theorem preparedRawState_eq_prepared (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (j : Nat)
    (A : Point) (s : BasisState) (hs : PointLookupValid s)
    (he : pointStateCoordinates s=fig14PointEncoding A)
    (hout : A ∉ fig14ExceptionalPoints (preparedWindowDelta x y hc j s)) :
    PreparedRawDomain (fun j a => (x j a).val) (fun j a => (y j a).val) j s ∧
      preparedRawState (fun j a => (x j a).val) (fun j a => (y j a).val) j s=
        preparedWindowCallState x y hc j s := by
  have hp := selected_point x y hc j s
  have h := preparedRawPointState_correct (fun j a => (x j a).val) (fun j a => (y j a).val)
    j A s hs he (ZMod.val_lt _) (signedPointTableValue_lt _ (fun a => ZMod.val_lt _) _)
    (selected_valid x y hc j s) (hp.symm ▸ hout)
  refine ⟨h.1,?_⟩
  rw [h.2,hp,preparedWindowCallState_correct x y hc j A s hs he]
  rfl


/-- A group-law walk over the original input banks. Point writes do not change
these banks, so each subsequent digit is read from the same scalar input. -/
def rawAlgebraicEnd (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) :
    List Nat → Point → BasisState → Point
  | [], A, _ => A
  | j::js, A, s => rawAlgebraicEnd x y hc js (A+preparedWindowDelta x y hc j s) s

/-- Sufficient exclusions along the algebraic walk, without assuming arithmetic
validity or a path certificate. No bound on the measure of this set is asserted. -/
def rawAlgebraicExclusions (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) :
    List Nat → Point → BasisState → Prop
  | [], _, _ => True
  | j::js, A, s => A ∉ fig14ExceptionalPoints (preparedWindowDelta x y hc j s) ∧
      rawAlgebraicExclusions x y hc js (A+preparedWindowDelta x y hc j s) s

private theorem exclusions_write (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (js : List Nat)
    (A B : Point) (s : BasisState) :
    rawAlgebraicExclusions x y hc js A (pointWrite B s)=rawAlgebraicExclusions x y hc js A s := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih => simp only [rawAlgebraicExclusions,preparedWindowDelta_pointWrite,ih]
private theorem end_write (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (js : List Nat)
    (A B : Point) (s : BasisState) :
    rawAlgebraicEnd x y hc js A (pointWrite B s)=rawAlgebraicEnd x y hc js A s := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih => simp only [rawAlgebraicEnd,preparedWindowDelta_pointWrite,ih]

/-- Algebraic exclusions construct the operational certificate used by the raw
circuit theorem; canonical values and nonsingularity follow from the tables. -/
theorem rawAlgebraicExclusions_path (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (js : List Nat)
    (A : Point) (s : BasisState) (good : rawAlgebraicExclusions x y hc js A s) :
    RawPointPath (fun j a => (x j a).val) (fun j a => (y j a).val) js A s
      (rawAlgebraicEnd x y hc js A s) := by
  induction js generalizing A s with
  | nil => exact .nil A s
  | cons j js ih =>
    have hp := selected_point x y hc j s
    refine @RawPointPath.cons (fun j a => (x j a).val) (fun j a => (y j a).val)
      j js A (rawAlgebraicEnd x y hc (j::js) A s) s (ZMod.val_lt _)
      (signedPointTableValue_lt _ (fun a => ZMod.val_lt _) _) (selected_valid x y hc j s)
      (hp.symm ▸ good.1) ?_
    have ht := ih (A+preparedWindowDelta x y hc j s)
      (pointWrite (A+preparedWindowDelta x y hc j s) s)
      (by rw [exclusions_write]; exact good.2)
    simpa only [hp,end_write,rawAlgebraicEnd] using ht

/-- Exactly the remaining 15 P windows followed by the 13 Q windows. -/
def reducedRawIndices : List Nat := List.range' 1 15 ++ List.range' 17 13

def reducedRawX (P Q : Point) (j a : Nat) : ShorECDLP.Fp :=
  if j<17 then oddWindowX P j a else oddWindowX Q (j-17) a

def reducedRawY (P Q : Point) (j a : Nat) : ShorECDLP.Fp :=
  if j<17 then oddWindowY P j a else oddWindowY Q (j-17) a

private theorem reduced_valid (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (j a : Nat) :
    curve.toAffine.Nonsingular (reducedRawX P Q j a) (reducedRawY P Q j a) := by
  unfold reducedRawX reducedRawY
  split
  · exact oddWindowTable_valid P hP hrP j a
  · exact oddWindowTable_valid Q hQ hrQ (j-17) a

/-- The selected point is the signed scalar digit plus the fixed half-point
term, with the Q-axis radix exponent restarting at physical bank 17. -/
theorem reducedRaw_delta (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (j : Nat) (A : Point)
    (s : BasisState) (hs : PointLookupValid s) (he : pointStateCoordinates s=fig14PointEncoding A) :
    preparedWindowDelta (reducedRawX P Q) (reducedRawY P Q) (reduced_valid P Q hP hQ hrP hrQ) j s=
      if j<17 then
        signedWindowDigit 16 (windowRawDigit j s) • ((2^(16*j)) • P)+
          (2^(16*j)) • signedWindowHalfPoint P order
      else signedWindowDigit 16 (windowRawDigit j s) • ((2^(16*(j-17))) • Q)+
          (2^(16*(j-17))) • signedWindowHalfPoint Q order := by
  have hp := preparedWindowCallState_correct (fun k => oddWindowX P (k-0))
    (fun k => oddWindowY P (k-0)) (fun k => oddWindowTable_valid P hP hrP (k-0)) j A s hs he
  have hp' := preparedOddWindowCallAt_correct P hP hrP 0 j A s hs he
  have hq := preparedWindowCallState_correct (fun k => oddWindowX Q (k-17))
    (fun k => oddWindowY Q (k-17)) (fun k => oddWindowTable_valid Q hQ hrQ (k-17)) j A s hs he
  have hq' := preparedOddWindowCallAt_correct Q hQ hrQ 17 j A s hs he
  have ep := add_left_cancel (pointWrite_injective s (hp.symm.trans hp'))
  have eq := add_left_cancel (pointWrite_injective s (hq.symm.trans hq'))
  by_cases hj : j<17
  · simpa only [preparedWindowDelta,windowPointDelta,reducedRawX,reducedRawY,if_pos hj,Nat.sub_zero] using ep
  · simpa only [preparedWindowDelta,windowPointDelta,reducedRawX,reducedRawY,if_neg hj] using eq

def reducedRawProgram (P Q : Point) : AdaptiveCircuit :=
  initializedRawProgram (axisWindowOffset P 16+axisWindowOffset Q 13) P
    (fun j a => (reducedRawX P Q j a).val) (fun j a => (reducedRawY P Q j a).val) reducedRawIndices

def reducedRawInitialPoint (P Q : Point) (s : BasisState) : Point :=
  firstWindowTable (axisWindowOffset P 16+axisWindowOffset Q 13) P
    (tableAddressValue (List.range' 855 16) s)

def reducedRawExclusions (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) : Prop :=
  rawAlgebraicExclusions (reducedRawX P Q) (reducedRawY P Q) (reduced_valid P Q hP hQ hrP hrQ)
    reducedRawIndices (reducedRawInitialPoint P Q s) s

def reducedRawEnd (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) : Point :=
  rawAlgebraicEnd (reducedRawX P Q) (reducedRawY P Q) (reduced_valid P Q hP hQ hrP hrQ)
    reducedRawIndices (reducedRawInitialPoint P Q s) s

/-- Concrete scalar-window exclusions imply the complete 28-call certificate
following the actual first lookup. This does not assert that all scalars qualify. -/
theorem reducedRawExclusions_path (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState)
    (good : reducedRawExclusions P Q hP hQ hrP hrQ s) :
    RawPointPath (fun j a => (reducedRawX P Q j a).val) (fun j a => (reducedRawY P Q j a).val)
      reducedRawIndices (reducedRawInitialPoint P Q s)
      (rawInitialState (axisWindowOffset P 16+axisWindowOffset Q 13) P s)
      (reducedRawEnd P Q hP hQ hrP hrQ s) := by
  have h := rawAlgebraicExclusions_path (reducedRawX P Q) (reducedRawY P Q)
    (reduced_valid P Q hP hQ hrP hrQ) reducedRawIndices (reducedRawInitialPoint P Q s)
    (rawInitialState (axisWindowOffset P 16+axisWindowOffset Q 13) P s)
    (by rw [rawInitialState,exclusions_write]; exact good)
  simpa only [rawInitialState,end_write,reducedRawEnd] using h

/-- The concrete raw schedule coherently computes its algebraic window walk
on clean inputs satisfying the explicit per-step exclusions. -/
theorem reducedRaw_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn (reducedRawProgram P Q)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (reducedRawEnd P Q hP hQ hrP hrQ s) s))
      (fun s => PointInitializeValid s ∧ reducedRawExclusions P Q hP hQ hrP hrQ s) := by
  obtain ⟨cs,ha,hm⟩ := initializedRawPointPath_coherent
    (axisWindowOffset P 16+axisWindowOffset Q 13) P
    (fun j a => (reducedRawX P Q j a).val) (fun j a => (reducedRawY P Q j a).val)
    reducedRawIndices (reducedRawEnd P Q hP hQ hrP hrQ)
  refine ⟨cs,ha.imp ?_,hm⟩
  intro b c hb s hs
  exact hb s ⟨hs.1,reducedRawExclusions_path P Q hP hQ hrP hrQ s hs.2⟩

end
end ShorECDLP.Paper2607_13816
