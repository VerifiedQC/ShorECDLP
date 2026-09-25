import ShorECDLP.Submission.«2607_13816».Window.PreparedLookup

namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

/-- Scalar value of consecutive banks in the physical MSB-first order. -/
def streamScalarValue : Nat → Nat → BasisState → Nat
  | 0, _, _ => 0
  | n+1, j, s => windowRawDigit j s * 65536^n + streamScalarValue n (j+1) s

private theorem value_append (base : Nat) (xs ys : List Nat) :
    windowValue base (xs++ys)=windowValue base xs+base^xs.length*windowValue base ys := by
  induction xs with
  | nil => simp [windowValue]
  | cons x xs ih => simp only [List.cons_append,windowValue,ih,List.length_cons,pow_succ]; ring

private theorem digits_length (n j : Nat) (s : BasisState) :
    (rawWindowDigits n j s).length=n := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp [rawWindowDigits,ih]

/-- The descending-bank convention is the reverse of the existing
little-endian radix digit list, including leading zero windows. -/
theorem streamScalarValue_reverse (n j : Nat) (s : BasisState) :
    streamScalarValue n j s=windowValue 65536 (rawWindowDigits n j s).reverse := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [streamScalarValue,rawWindowDigits,List.reverse_cons,value_append,
      List.length_reverse,digits_length,windowValue,ih]
    ring

/-- All physical words, including the leading word, are 16-bit quantities. -/
theorem streamScalarValue_lt (n j : Nat) (s : BasisState) :
    streamScalarValue n j s<65536^n := by
  induction n generalizing j with
  | zero => simp [streamScalarValue]
  | succ n ih =>
    have hd := windowRawDigit_bound j s
    have ht := ih (j+1)
    have hp : 0<65536^n := by positivity
    simp only [streamScalarValue,pow_succ]
    nlinarith

private theorem geometric_high (n : Nat) :
    radixGeometric (n+1)=65536^n+radixGeometric n := by
  induction n with
  | zero => simp [radixGeometric]
  | succ n ih => simp only [radixGeometric] at ih ⊢; rw [pow_succ]; omega

private theorem digit_half (P : Point) (hr : order • P=0) (n v : Nat) :
    signedWindowDigit 16 v • ((2^(16*n):Nat) • P)+
      (2^(16*n):Nat) • signedWindowHalfPoint P order =
      (v*65536^n) • P - (65535*65536^n) • signedWindowHalfPoint P order := by
  have hd := signedWindowHalfPoint_double P order (by decide +kernel) hr
  have hp : (2^(16*n):Nat)=65536^n := by rw [pow_mul]; norm_num
  rw [hp]
  generalize signedWindowHalfPoint P order = H at hd ⊢
  rw [←hd]
  simp only [signedWindowDigit,sub_zsmul,natCast_zsmul,smul_smul,nsmul_add]
  simp only [←natCast_zsmul,←add_zsmul,←sub_zsmul]
  simp only [sub_eq_add_neg,←neg_zsmul,←add_zsmul]
  apply congrArg (fun z : Int => z • H)
  push_cast
  ring

private theorem indexed_delta (P : Point) (hP : P≠0) (hr : order • P=0)
    (exponent : Nat → Nat) (j : Nat) (s : BasisState) (hs : WindowPointValid s) :
    preparedWindowDelta (fun k => oddWindowX P (exponent k))
      (fun k => oddWindowY P (exponent k))
      (fun k => oddWindowTable_valid P hP hr (exponent k)) j s =
      (windowRawDigit j s*65536^(exponent j)) • P -
        (65535*65536^(exponent j)) • signedWindowHalfPoint P order := by
  obtain ⟨hv,A,hA⟩ := hs
  have h1 := preparedWindowCallState_correct (fun k => oddWindowX P (exponent k))
    (fun k => oddWindowY P (exponent k))
    (fun k => oddWindowTable_valid P hP hr (exponent k)) j A s hv hA
  have h2 := preparedOddWindowCallIndexed_correct P hP hr exponent j A s hv hA
  exact (add_left_cancel (pointWrite_injective s (h1.symm.trans h2))).trans
    (digit_half P hr (exponent j) (windowRawDigit j s))

private theorem descending_sum (P : Point) (hP : P≠0) (hr : order • P=0)
    (n j top : Nat) (ht : top+1=j+n) (s : BasisState) (hs : WindowPointValid s) :
    preparedWindowSum (fun k => oddWindowX P (top-k))
      (fun k => oddWindowY P (top-k))
      (fun k => oddWindowTable_valid P hP hr (top-k)) n j s =
      streamScalarValue n j s • P-axisWindowOffset P n := by
  induction n generalizing j with
  | zero => simp [preparedWindowSum,streamScalarValue,axisWindowOffset,radixGeometric]
  | succ n ih =>
    rw [preparedWindowSum,indexed_delta P hP hr _ j s hs,ih (j+1) (by omega)]
    rw [show top-j=n by omega]
    simp only [streamScalarValue,axisWindowOffset,geometric_high,Nat.mul_add,add_nsmul]
    abel

private theorem end_sum (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (js : List Nat)
    (A : Point) (s : BasisState) :
    rawAlgebraicEnd x y hc js A s = A+(js.map (fun j => preparedWindowDelta x y hc j s)).sum := by
  induction js generalizing A with
  | nil => simp [rawAlgebraicEnd]
  | cons j js ih => simp only [rawAlgebraicEnd,ih,List.map_cons,List.sum_cons,add_assoc]

private theorem sum_range (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (n j : Nat) (s : BasisState) :
    ((List.range' j n).map (fun k => preparedWindowDelta x y hc k s)).sum =
      preparedWindowSum x y hc n j s := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [List.range'_succ,List.map_cons,List.sum_cons,preparedWindowSum,ih]

private theorem two_sums (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) :
    ((List.range' 1 28).map (fun j => preparedWindowDelta (streamRawX P Q) (streamRawY P Q)
      (streamRawTable_valid P Q hP hQ hrP hrQ) j s)).sum =
      preparedWindowSum (fun k => oddWindowX P (15-k)) (fun k => oddWindowY P (15-k))
        (fun k => oddWindowTable_valid P hP hrP (15-k)) 15 1 s +
      preparedWindowSum (fun k => oddWindowX Q (28-k)) (fun k => oddWindowY Q (28-k))
        (fun k => oddWindowTable_valid Q hQ hrQ (28-k)) 13 16 s := by
  rw [show List.range' 1 28=List.range' 1 15++List.range' 16 13 from
    (List.range'_append (s:=1) (m:=15) (n:=13) (step:=1)).symm,List.map_append,List.sum_append]
  rfl

private theorem first_digit (P Q : Point) (s : BasisState) :
    streamRawInitialPoint P Q s = axisWindowOffset P 16+axisWindowOffset Q 13+
      (signedWindowDigit 16 (windowRawDigit 0 s) • ((2^(16*15):Nat) • P)+
        (2^(16*15):Nat) • signedWindowHalfPoint P order) := by
  have ha : tableAddressValue streamAddress s=windowRawDigit 0 s := by
    simp [streamAddress,tableAddressValue,windowRawDigit,windowAddressBits,windowBankStart,
      List.range',wireValues,boolWordToNat]
    omega
  simp only [streamRawInitialPoint,firstWindowTable,ha,signedWindowHalfPoint]
  rw [smul_comm ((order+1)/2) (2^(16*15)) P]

private theorem cancel_offsets (A B D E U V : Point) (h : D+E=U-A) :
    A+B+D+(E+(V-B))=U+V := by
  calc
    _ = A+B+(D+E)+(V-B) := by abel
    _ = U+V := by rw [h]; abel

/-- The MSB-first algebraic walk reconstructs the two input scalars. This
identity alone does not discharge the raw circuit's exceptional-input condition. -/
theorem streamRawEnd_scalars (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) (hs : WindowPointValid s) :
    rawAlgebraicEnd (streamRawX P Q) (streamRawY P Q)
      (streamRawTable_valid P Q hP hQ hrP hrQ) (List.range' 1 28)
      (streamRawInitialPoint P Q s) s =
      streamScalarValue 16 0 s • P+streamScalarValue 13 16 s • Q := by
  have hp := descending_sum P hP hrP 16 0 15 (by decide) s hs
  rw [preparedWindowSum,indexed_delta P hP hrP _ 0 s hs] at hp
  rw [end_sum,two_sums P Q hP hQ hrP hrQ,first_digit,digit_half P hrP,
    descending_sum Q hQ hrQ 13 16 28 (by decide) s hs]
  exact cancel_offsets _ _ _ _ _ _ hp

private theorem digit_write (A : Point) (j : Nat) (s : BasisState) :
    windowRawDigit j (pointWrite A s)=windowRawDigit j s := by
  have h := rawWindowDigits_pointWrite 1 j A s
  simpa only [rawWindowDigits,List.cons.injEq,and_true] using h

private theorem scalar_write (A : Point) (n j : Nat) (s : BasisState) :
    streamScalarValue n j (pointWrite A s)=streamScalarValue n j s := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [streamScalarValue,digit_write,ih]

private theorem end_write (x y : Nat → Nat → ShorECDLP.Fp)
    (hc : ∀ j a, curve.toAffine.Nonsingular (x j a) (y j a)) (js : List Nat)
    (A B : Point) (s : BasisState) :
    rawAlgebraicEnd x y hc js A (pointWrite B s)=rawAlgebraicEnd x y hc js A s := by
  induction js generalizing A with
  | nil => rfl
  | cons j js ih => simp only [rawAlgebraicEnd,preparedWindowDelta_pointWrite,ih]

/-- The same reconstruction applies before loading the initially clean point. -/
theorem streamRawEnd_initialized_scalars (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) (hs : PointInitializeValid s) :
    rawAlgebraicEnd (streamRawX P Q) (streamRawY P Q)
      (streamRawTable_valid P Q hP hQ hrP hrQ) (List.range' 1 28)
      (streamRawInitialPoint P Q s) s =
      streamScalarValue 16 0 s • P+streamScalarValue 13 16 s • Q := by
  have h := streamRawEnd_scalars P Q hP hQ hrP hrQ (pointWrite 0 s)
    (pointInitialize_ready 0 s hs)
  have hi : streamRawInitialPoint P Q (pointWrite 0 s)=streamRawInitialPoint P Q s := by
    rw [first_digit,first_digit,digit_write]
  simpa only [hi,end_write,scalar_write] using h

private theorem prepared_initialize (s : BasisState) (hs : PointInitializeValid s) :
    PointInitializeValid (s ∘ streamPreparedWire) := by
  have hw (w : Wire) (h : w<855) : (s ∘ streamPreparedWire) w=s w := by
    simp only [Function.comp_apply,streamPreparedWire,if_pos h]
  have word (ws : List Wire) (h : ∀ w∈ws,w<855) :
      wireValues ws (s ∘ streamPreparedWire)=wireValues ws s := by
    apply List.map_congr_left
    intro w hmem
    exact hw w (h w hmem)
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩
  · intro w hmem
    rw [hw w (by simp only [List.mem_append,List.mem_range'_1] at hmem; dsimp only [Wire] at *; omega)]
    exact hs.1.1.1 w hmem
  · rw [hw 837 (by decide)]; exact hs.1.1.2.1
  · rw [word _ (by intro w hmem; simp only [List.mem_range'_1] at hmem; dsimp only [Wire] at *; omega)]
    exact hs.1.1.2.2.1
  · rw [word _ (by intro w hmem; simp only [List.mem_range'_1] at hmem; dsimp only [Wire] at *; omega)]
    exact hs.1.1.2.2.2
  · rw [hw 836 (by decide)]; exact hs.1.2
  · rw [word _ (by
      intro w hmem
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
        List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hmem
      dsimp only [Wire] at *
      omega)]
    exact hs.2

/-- Scalar reconstruction in the actual parked-bank layout. -/
theorem streamPreparedRawEnd_scalars (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) (s : BasisState) (hs : PointInitializeValid s) :
    streamPreparedRawEnd P Q hP hQ hrP hrQ s =
      streamScalarValue 16 0 (s ∘ streamPreparedWire) • P+
      streamScalarValue 13 16 (s ∘ streamPreparedWire) • Q :=
  streamRawEnd_initialized_scalars P Q hP hQ hrP hrQ _ (prepared_initialize s hs)

/-- The actual first lookup and all 28 additions coherently produce aP+bQ,
with the original clean-input and path-exclusion premises unchanged. -/
theorem streamPreparedArithmetic_scalars_coherent (P Q : Point) (hP : P≠0) (hQ : Q≠0)
    (hrP : order • P=0) (hrQ : order • Q=0) :
    CoherentlyImplementsOn ((streamPreparedLookup P Q).seq (streamPreparedRawProgram P Q))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite
        (streamScalarValue 16 0 (s ∘ streamPreparedWire) • P+
          streamScalarValue 13 16 (s ∘ streamPreparedWire) • Q) s))
      (fun s => PointInitializeValid s ∧
        streamRawExclusions P Q hP hQ hrP hrQ (s ∘ streamPreparedWire)) := by
  apply (streamPreparedArithmetic_coherent P Q hP hQ hrP hrQ).congrIdeal
  intro s hs
  simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,
    streamPreparedRawEnd_scalars P Q hP hQ hrP hrQ s hs.1]

end
end ShorECDLP.Paper2607_13816
