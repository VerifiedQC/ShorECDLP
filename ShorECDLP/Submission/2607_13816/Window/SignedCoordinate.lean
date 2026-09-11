import ShorECDLP.Submission.«2607_13816».Window.SignedPointY
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointSupport
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

/-- Five sequential field-word queries, each loaded and cleared around its modular addition. -/
def signedLookupCoordinateProgram (x y : Nat → Nat) : AdaptiveCircuit :=
  ((((((((fig14LookupX (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))).seq
    secp256k1ZeroAllowedDivision).seq fig14SquareSubtract).seq
    (fig14LookupX (fun a => (3*x a)%ShorECDLP.p))).seq
    secp256k1ZeroAllowedMultiplication).seq fig14Negate).seq
    (fig14LookupX (fun a => x a%ShorECDLP.p))).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))

def signedLookupCoordinateState (x y : Nat → Nat) (s : BasisState) : BasisState :=
  let s1 := fig14LookupXState (fun a => (ShorECDLP.p-x a)%ShorECDLP.p) s
  let s2 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) s1
  let s3 := zeroAllowedDivisionOutputState s2
  let s4 := fig14SquareSubtractState s3
  let s5 := fig14LookupXState (fun a => (3*x a)%ShorECDLP.p) s4
  let s6 := zeroAllowedMultiplicationOutputState s5
  let s7 := fig14NegateState s6
  let s8 := fig14LookupXState (fun a => x a%ShorECDLP.p) s7
  signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) s8

private theorem lookup_coherent_seq (a b : AdaptiveCircuit) (f g : BasisState → BasisState)
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) PointLookupValid)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) PointLookupValid)
    (hf : ∀ s, PointLookupValid s → PointLookupValid (f s)) :
    CoherentlyImplementsOn (a.seq b) (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) PointLookupValid := by
  have h := ha.seq hb (by
    intro s hs
    simpa [ket] using supportedOn_ket PointLookupValid (f s) (hf s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket]

private theorem lookup_restrict {program : AdaptiveCircuit} {ideal : Quantum.State →ₗ[ℂ] Quantum.State}
    (h : CoherentlyImplementsOn program ideal Secp256k1ZeroAllowedInputValid) :
    CoherentlyImplementsOn program ideal PointLookupValid := by
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s hs.1),hm⟩

private theorem lookup_division_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (zeroAllowedDivisionOutputState s) := by
  refine ⟨fig14Division_ready s hs.1,?_⟩
  rw [zeroAllowedDivisionOutputState_frame s hs.1]
  simpa using hs.2
private theorem lookup_multiplication_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (zeroAllowedMultiplicationOutputState s) := by
  refine ⟨fig14Multiplication_ready s hs.1,?_⟩
  rw [zeroAllowedMultiplicationOutputState_frame s hs.1]
  simpa using hs.2
private theorem lookup_square_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (fig14SquareSubtractState s) :=
  ⟨fig14SquareSubtractState_ready s hs.1,
    ((fig14SquareSubtractState_correct s hs.1).2 836 (by decide +kernel)).trans hs.2⟩
private theorem lookup_negate_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (fig14NegateState s) :=
  ⟨fig14NegateState_ready s hs.1,
    ((fig14NegateState_correct s hs.1).2 836 (by decide +kernel)).trans hs.2⟩

theorem signedLookupCoordinateProgram_coherent (x y : Nat → Nat) :
    CoherentlyImplementsOn (signedLookupCoordinateProgram x y)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState x y)) PointLookupValid := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  let p1 := fig14LookupX (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)
  let f1 := fig14LookupXState (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)
  have h1 : CoherentlyImplementsOn p1 (Finsupp.lmapDomain ℂ ℂ f1) PointLookupValid := fig14LookupX_coherent _ (fun _ => hk _)
  have r1 : ∀ s, PointLookupValid s → PointLookupValid (f1 s) := fig14LookupXState_ready _ (fun _ => hk _)
  let p2 := signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  let f2 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  have h2 : CoherentlyImplementsOn p2 (Finsupp.lmapDomain ℂ ℂ f2) PointLookupValid := signedPointLookupY_coherent _ (fun _ => hk _)
  have r2 : ∀ s, PointLookupValid s → PointLookupValid (f2 s) := signedPointLookupYState_ready _ (fun _ => hk _)
  let p3 := secp256k1ZeroAllowedDivision
  let f3 := zeroAllowedDivisionOutputState
  have h3 : CoherentlyImplementsOn p3 (Finsupp.lmapDomain ℂ ℂ f3) PointLookupValid := lookup_restrict secp256k1ZeroAllowedDivision_coherent
  have r3 : ∀ s, PointLookupValid s → PointLookupValid (f3 s) := lookup_division_ready
  let p4 := fig14SquareSubtract
  let f4 := fig14SquareSubtractState
  have h4 : CoherentlyImplementsOn p4 (Finsupp.lmapDomain ℂ ℂ f4) PointLookupValid := lookup_restrict fig14SquareSubtract_coherent
  have r4 : ∀ s, PointLookupValid s → PointLookupValid (f4 s) := lookup_square_ready
  let p5 := fig14LookupX (fun a => (3*x a)%ShorECDLP.p)
  let f5 := fig14LookupXState (fun a => (3*x a)%ShorECDLP.p)
  have h5 : CoherentlyImplementsOn p5 (Finsupp.lmapDomain ℂ ℂ f5) PointLookupValid := fig14LookupX_coherent _ (fun _ => hk _)
  have r5 : ∀ s, PointLookupValid s → PointLookupValid (f5 s) := fig14LookupXState_ready _ (fun _ => hk _)
  let p6 := secp256k1ZeroAllowedMultiplication
  let f6 := zeroAllowedMultiplicationOutputState
  have h6 : CoherentlyImplementsOn p6 (Finsupp.lmapDomain ℂ ℂ f6) PointLookupValid := lookup_restrict secp256k1ZeroAllowedMultiplication_coherent
  have r6 : ∀ s, PointLookupValid s → PointLookupValid (f6 s) := lookup_multiplication_ready
  let p7 := fig14Negate
  let f7 := fig14NegateState
  have h7 : CoherentlyImplementsOn p7 (Finsupp.lmapDomain ℂ ℂ f7) PointLookupValid := lookup_restrict fig14Negate_coherent
  have r7 : ∀ s, PointLookupValid s → PointLookupValid (f7 s) := lookup_negate_ready
  let p8 := fig14LookupX (fun a => x a%ShorECDLP.p)
  let f8 := fig14LookupXState (fun a => x a%ShorECDLP.p)
  have h8 : CoherentlyImplementsOn p8 (Finsupp.lmapDomain ℂ ℂ f8) PointLookupValid := fig14LookupX_coherent _ (fun _ => hk _)
  have r8 : ∀ s, PointLookupValid s → PointLookupValid (f8 s) := fig14LookupXState_ready _ (fun _ => hk _)
  let p9 := signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  let f9 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  have h9 : CoherentlyImplementsOn p9 (Finsupp.lmapDomain ℂ ℂ f9) PointLookupValid := signedPointLookupY_coherent _ (fun _ => hk _)
  have c2 := lookup_coherent_seq _ _ _ _ h1 h2 r1
  have v2 := fun s hs => r2 _ (r1 s hs)
  have c3 := lookup_coherent_seq _ _ _ _ c2 h3 v2
  have v3 := fun s hs => r3 _ (v2 s hs)
  have c4 := lookup_coherent_seq _ _ _ _ c3 h4 v3
  have v4 := fun s hs => r4 _ (v3 s hs)
  have c5 := lookup_coherent_seq _ _ _ _ c4 h5 v4
  have v5 := fun s hs => r5 _ (v4 s hs)
  have c6 := lookup_coherent_seq _ _ _ _ c5 h6 v5
  have v6 := fun s hs => r6 _ (v5 s hs)
  have c7 := lookup_coherent_seq _ _ _ _ c6 h7 v6
  have v7 := fun s hs => r7 _ (v6 s hs)
  have c8 := lookup_coherent_seq _ _ _ _ c7 h8 v7
  have v8 := fun s hs => r8 _ (v7 s hs)
  have c9 := lookup_coherent_seq _ _ _ _ c8 h9 v8
  exact c9


theorem signedLookupCoordinateState_ready (x y : Nat → Nat) (s : BasisState)
    (hs : PointLookupValid s) : PointLookupValid (signedLookupCoordinateState x y s) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  unfold signedLookupCoordinateState
  apply signedPointLookupYState_ready _ (fun _ => hk _)
  apply fig14LookupXState_ready _ (fun _ => hk _)
  apply lookup_negate_ready
  apply lookup_multiplication_ready
  apply fig14LookupXState_ready _ (fun _ => hk _)
  apply lookup_square_ready
  apply lookup_division_ready
  apply signedPointLookupYState_ready _ (fun _ => hk _)
  exact fig14LookupXState_ready _ (fun _ => hk _) s hs

private theorem lookup_address_frame (s t : BasisState)
    (h : ∀ w, w∉List.range' 263 256 → w∉List.range' 580 256 → t w=s w) :
    tableAddressValue pointLookupAddress t=tableAddressValue pointLookupAddress s := by
  apply tableAddressValue_congr
  intro w hw
  apply h w
  · simp [pointLookupAddress] at hw ⊢; omega
  · simp [pointLookupAddress] at hw ⊢; omega

private theorem lookup_division_address (s : BasisState) (hs : PointLookupValid s) :
    tableAddressValue pointLookupAddress (zeroAllowedDivisionOutputState s)=tableAddressValue pointLookupAddress s := by
  apply lookup_address_frame
  intro w _ hy
  rw [zeroAllowedDivisionOutputState_frame s hs.1]
  simp only [hy,if_false]

private theorem lookup_multiplication_address (s : BasisState) (hs : PointLookupValid s) :
    tableAddressValue pointLookupAddress (zeroAllowedMultiplicationOutputState s)=tableAddressValue pointLookupAddress s := by
  apply lookup_address_frame
  intro w _ hy
  rw [zeroAllowedMultiplicationOutputState_frame s hs.1]
  simp only [hy,if_false]

private theorem lookup_square_address (s : BasisState) (hs : PointLookupValid s) :
    tableAddressValue pointLookupAddress (fig14SquareSubtractState s)=tableAddressValue pointLookupAddress s := by
  apply lookup_address_frame
  intro w hx _
  exact (fig14SquareSubtractState_correct s hs.1).2 w hx

private theorem lookup_negate_address (s : BasisState) (hs : PointLookupValid s) :
    tableAddressValue pointLookupAddress (fig14NegateState s)=tableAddressValue pointLookupAddress s := by
  apply lookup_address_frame
  intro w hx _
  exact (fig14NegateState_correct s hs.1).2 w hx

theorem signedLookupCoordinateState_address (x y : Nat → Nat) (s : BasisState) (hs : PointLookupValid s) :
    tableAddressValue pointLookupAddress (signedLookupCoordinateState x y s)=tableAddressValue pointLookupAddress s := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  let s1 := fig14LookupXState (fun a => (ShorECDLP.p-x a)%ShorECDLP.p) s
  have h1 : PointLookupValid s1 := fig14LookupXState_ready _ (fun _ => hk _) s hs
  have a1 : tableAddressValue pointLookupAddress s1=tableAddressValue pointLookupAddress s := fig14LookupXState_address _ (fun _ => hk _) s hs
  let s2 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) s1
  have h2 : PointLookupValid s2 := signedPointLookupYState_ready _ (fun _ => hk _) s1 h1
  have a2 : tableAddressValue pointLookupAddress s2=tableAddressValue pointLookupAddress s1 := signedPointLookupYState_address _ (fun _ => hk _) s1 h1
  let s3 := zeroAllowedDivisionOutputState s2
  have h3 : PointLookupValid s3 := lookup_division_ready s2 h2
  have a3 : tableAddressValue pointLookupAddress s3=tableAddressValue pointLookupAddress s2 := lookup_division_address s2 h2
  let s4 := fig14SquareSubtractState s3
  have h4 : PointLookupValid s4 := lookup_square_ready s3 h3
  have a4 : tableAddressValue pointLookupAddress s4=tableAddressValue pointLookupAddress s3 := lookup_square_address s3 h3
  let s5 := fig14LookupXState (fun a => (3*x a)%ShorECDLP.p) s4
  have h5 : PointLookupValid s5 := fig14LookupXState_ready _ (fun _ => hk _) s4 h4
  have a5 : tableAddressValue pointLookupAddress s5=tableAddressValue pointLookupAddress s4 := fig14LookupXState_address _ (fun _ => hk _) s4 h4
  let s6 := zeroAllowedMultiplicationOutputState s5
  have h6 : PointLookupValid s6 := lookup_multiplication_ready s5 h5
  have a6 : tableAddressValue pointLookupAddress s6=tableAddressValue pointLookupAddress s5 := lookup_multiplication_address s5 h5
  let s7 := fig14NegateState s6
  have h7 : PointLookupValid s7 := lookup_negate_ready s6 h6
  have a7 : tableAddressValue pointLookupAddress s7=tableAddressValue pointLookupAddress s6 := lookup_negate_address s6 h6
  let s8 := fig14LookupXState (fun a => x a%ShorECDLP.p) s7
  have h8 : PointLookupValid s8 := fig14LookupXState_ready _ (fun _ => hk _) s7 h7
  have a8 : tableAddressValue pointLookupAddress s8=tableAddressValue pointLookupAddress s7 := fig14LookupXState_address _ (fun _ => hk _) s7 h7
  let s9 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) s8
  have a9 : tableAddressValue pointLookupAddress s9=tableAddressValue pointLookupAddress s8 := signedPointLookupYState_address _ (fun _ => hk _) s8 h8
  exact a9.trans (a8.trans (a7.trans (a6.trans (a5.trans (a4.trans (a3.trans (a2.trans a1)))))))

private theorem lookup_X_sign (table : Nat → Nat) (hv : ∀ a, table a<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) : fig14LookupXState table s 854=s 854 := by
  rw [fig14LookupXState_eq table hv s hs.1 hs.2]
  exact (fig14ConstantXState_correct _ (hv _) s hs.1).2 854 (by decide +kernel)

private theorem signed_table_minus (y : Nat → Nat) (s : BasisState) :
    signedPointTableValue (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) s =
      (ShorECDLP.p-signedPointTableValue y s)%ShorECDLP.p := by
  unfold signedPointTableValue
  cases h : s 854 <;> simp

private theorem lookup_division_sign (s : BasisState) (hs : PointLookupValid s) :
    zeroAllowedDivisionOutputState s 854=s 854 := by
  rw [zeroAllowedDivisionOutputState_frame s hs.1]
  simp
private theorem lookup_multiplication_sign (s : BasisState) (hs : PointLookupValid s) :
    zeroAllowedMultiplicationOutputState s 854=s 854 := by
  rw [zeroAllowedMultiplicationOutputState_frame s hs.1]
  simp

private theorem lookupXState_eq_controlled (table : Nat → Nat) (hv : ∀ a, table a<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) :
    fig14LookupXState table s=fig14ControlledConstantXState (table (tableAddressValue pointLookupAddress s)) s := by
  rw [fig14LookupXState_eq table hv s hs.1 hs.2]
  have hl := fig14ConstantXState_correct (table (tableAddressValue pointLookupAddress s)) (hv _) s hs.1
  have hr := fig14ControlledConstantXState_correct (table (tableAddressValue pointLookupAddress s)) (hv _) s hs.1
  have he : boolWordToNat (wireValues (List.range' 263 256) (fig14ConstantXState (table (tableAddressValue pointLookupAddress s)) s))=
      boolWordToNat (wireValues (List.range' 263 256) (fig14ControlledConstantXState (table (tableAddressValue pointLookupAddress s)) s)) := by
    simp [hl.1,hr.1,hs.2]
  have he' := boolWordToNat_injective_of_length (by simp [wireValues]) he
  funext w
  by_cases hw : w∈List.range' 263 256
  · exact List.map_inj_left.mp he' w hw
  · exact (hl.2 w hw).trans (hr.2 w hw).symm

theorem signedLookupCoordinateState_eq (x y : Nat → Nat) (s : BasisState) (hs : PointLookupValid s) :
    signedLookupCoordinateState x y s=fig14CoordinateState
      (x (tableAddressValue pointLookupAddress s)) (signedPointTableValue y s) s := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  let s1 := fig14LookupXState (fun a => (ShorECDLP.p-x a)%ShorECDLP.p) s
  have h1 : PointLookupValid s1 := fig14LookupXState_ready _ (fun _ => hk _) s hs
  have a1 : tableAddressValue pointLookupAddress s1=tableAddressValue pointLookupAddress s := fig14LookupXState_address _ (fun _ => hk _) s hs
  have z1 : s1 854=s 854 := lookup_X_sign (fun a => (ShorECDLP.p-x a)%ShorECDLP.p) (fun _ => hk _) s hs
  have e1 := fig14LookupXState_eq (fun a => (ShorECDLP.p-x a)%ShorECDLP.p) (fun _ => hk _) s hs.1 hs.2
  let s2 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) s1
  have h2 : PointLookupValid s2 := signedPointLookupYState_ready _ (fun _ => hk _) s1 h1
  have a2 : tableAddressValue pointLookupAddress s2=tableAddressValue pointLookupAddress s := (signedPointLookupYState_address _ (fun _ => hk _) s1 h1).trans a1
  have z2 : s2 854=s 854 := (signedPointLookupYState_sign _ (fun _ => hk _) s1 h1).trans z1
  have e2 := signedPointLookupYState_eq (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) (fun _ => hk _) s1 h1
  rw [signed_table_minus y s1, signedPointTableValue, a1, z1] at e2
  let s3 := zeroAllowedDivisionOutputState s2
  have h3 : PointLookupValid s3 := lookup_division_ready s2 h2
  have a3 : tableAddressValue pointLookupAddress s3=tableAddressValue pointLookupAddress s := (lookup_division_address s2 h2).trans a2
  have z3 : s3 854=s 854 := (lookup_division_sign s2 h2).trans z2
  let s4 := fig14SquareSubtractState s3
  have h4 : PointLookupValid s4 := lookup_square_ready s3 h3
  have a4 : tableAddressValue pointLookupAddress s4=tableAddressValue pointLookupAddress s := (lookup_square_address s3 h3).trans a3
  have z4 : s4 854=s 854 := ((fig14SquareSubtractState_correct s3 h3.1).2 854 (by decide +kernel)).trans z3
  let s5 := fig14LookupXState (fun a => (3*x a)%ShorECDLP.p) s4
  have h5 : PointLookupValid s5 := fig14LookupXState_ready _ (fun _ => hk _) s4 h4
  have a5 : tableAddressValue pointLookupAddress s5=tableAddressValue pointLookupAddress s := (fig14LookupXState_address _ (fun _ => hk _) s4 h4).trans a4
  have z5 : s5 854=s 854 := (lookup_X_sign (fun a => (3*x a)%ShorECDLP.p) (fun _ => hk _) s4 h4).trans z4
  have e5 := lookupXState_eq_controlled (fun a => (3*x a)%ShorECDLP.p) (fun _ => hk _) s4 h4
  rw [a4] at e5
  let s6 := zeroAllowedMultiplicationOutputState s5
  have h6 : PointLookupValid s6 := lookup_multiplication_ready s5 h5
  have a6 : tableAddressValue pointLookupAddress s6=tableAddressValue pointLookupAddress s := (lookup_multiplication_address s5 h5).trans a5
  have z6 : s6 854=s 854 := (lookup_multiplication_sign s5 h5).trans z5
  let s7 := fig14NegateState s6
  have h7 : PointLookupValid s7 := lookup_negate_ready s6 h6
  have a7 : tableAddressValue pointLookupAddress s7=tableAddressValue pointLookupAddress s := (lookup_negate_address s6 h6).trans a6
  have z7 : s7 854=s 854 := ((fig14NegateState_correct s6 h6.1).2 854 (by decide +kernel)).trans z6
  let s8 := fig14LookupXState (fun a => x a%ShorECDLP.p) s7
  have h8 : PointLookupValid s8 := fig14LookupXState_ready _ (fun _ => hk _) s7 h7
  have a8 : tableAddressValue pointLookupAddress s8=tableAddressValue pointLookupAddress s := (fig14LookupXState_address _ (fun _ => hk _) s7 h7).trans a7
  have z8 : s8 854=s 854 := (lookup_X_sign (fun a => x a%ShorECDLP.p) (fun _ => hk _) s7 h7).trans z7
  have e8 := fig14LookupXState_eq (fun a => x a%ShorECDLP.p) (fun _ => hk _) s7 h7.1 h7.2
  rw [a7] at e8
  let s9 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) s8
  have e9 := signedPointLookupYState_eq (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) (fun _ => hk _) s8 h8
  rw [signed_table_minus y s8, signedPointTableValue, a8, z8] at e9
  change s9=_
  dsimp only [s9]
  rw [e9]
  dsimp only [s8]
  rw [e8]
  dsimp only [s7,s6,s5]
  rw [e5]
  dsimp only [s4,s3,s2]
  rw [e2]
  dsimp only [s1]
  rw [e1]
  rfl

theorem signedLookupCoordinateState_frame (x y : Nat → Nat) (s : BasisState) (hs : PointLookupValid s)
    (w : Wire) (hx : w∉List.range' 263 256) (hy : w∉List.range' 580 256) :
    signedLookupCoordinateState x y s w=s w := by
  rw [signedLookupCoordinateState_eq x y s hs]
  exact fig14CoordinateState_frame _ _ s hs.1 w hx hy

theorem signedLookupCoordinateState_sign (x y : Nat → Nat) (s : BasisState) (hs : PointLookupValid s) :
    signedLookupCoordinateState x y s 854=s 854 :=
  signedLookupCoordinateState_frame x y s hs 854 (by decide +kernel) (by decide +kernel)

private theorem lookup_core_support (a : AdaptiveCircuit)
    (ha : a.wires ⊆ List.range 839) : a.wires ⊆ List.range 855 := by
  intro w hw
  have h := ha hw
  simp only [List.mem_range] at h ⊢
  omega

private theorem lookup_square_support : fig14SquareSubtract.wires ⊆ List.range 855 := by
  apply lookup_core_support
  intro w hw
  apply fig14CoordinateProgram_wires_subset 0 0
  simp only [fig14CoordinateProgram,modularWires_seq]
  aesop

private theorem lookup_negate_support : fig14Negate.wires ⊆ List.range 855 := by
  apply lookup_core_support
  intro w hw
  apply fig14CoordinateProgram_wires_subset 0 0
  simp only [fig14CoordinateProgram,modularWires_seq]
  aesop

private theorem lookup_field_support (a : AdaptiveCircuit) (ha : a.wires ⊆ zeroAllowedLayout) :
    a.wires ⊆ List.range 855 := by
  intro w hw
  have h := ha hw
  simp [zeroAllowedLayout] at h ⊢
  dsimp only [Wire] at *
  omega

private theorem lookup_seq_support (a b : AdaptiveCircuit) (ha : a.wires ⊆ List.range 855)
    (hb : b.wires ⊆ List.range 855) : (a.seq b).wires ⊆ List.range 855 := by
  intro w hw
  rw [modularWires_seq] at hw
  exact hw.elim (fun h => ha h) (fun h => hb h)

theorem signedLookupCoordinateProgram_wires (x y : Nat → Nat) :
    (signedLookupCoordinateProgram x y).wires ⊆ List.range 855 := by
  unfold signedLookupCoordinateProgram
  apply lookup_seq_support
  · apply lookup_seq_support
    · apply lookup_seq_support
      · apply lookup_seq_support
        · apply lookup_seq_support
          · apply lookup_seq_support
            · apply lookup_seq_support
              · apply lookup_seq_support
                · exact fig14LookupX_wires _
                · exact signedPointLookupY_wires _
              · exact lookup_field_support _ secp256k1ZeroAllowedDivision_wires_subset
            · exact lookup_square_support
          · exact fig14LookupX_wires _
        · exact lookup_field_support _ secp256k1ZeroAllowedMultiplication_wires_subset
      · exact lookup_negate_support
    · exact fig14LookupX_wires _
  · exact signedPointLookupY_wires _

private theorem lookup_count855 (p : AdaptiveCircuit) (h : p.wires ⊆ List.range 855) : p.qubitCount ≤ 855 := by
  have hs : p.wires.dedup.toFinset ⊆ (List.range 855).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h (by simpa using hw))
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range (n := 855))] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hc

theorem signedLookupCoordinateProgram_qubitCount (x y : Nat → Nat) :
    (signedLookupCoordinateProgram x y).qubitCount ≤ 855 :=
  lookup_count855 _ (signedLookupCoordinateProgram_wires x y)

end
end ShorECDLP.Paper2607_13816
