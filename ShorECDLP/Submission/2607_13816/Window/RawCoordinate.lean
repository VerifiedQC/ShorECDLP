import ShorECDLP.Submission.«2607_13816».Arithmetic.PointExceptions
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointRawDomain
import ShorECDLP.Submission.«2607_13816».Window.SignedCoordinate

/-! Five actual signed coordinate queries with raw nonzero field operations.
The query layout retains its explicit enabled-root contract (`PointLookupValid`).
This is conditional coherent correctness, not full-window domain coverage or a
new success/resource certificate. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

/-- Complete query state immediately before the unconditional division. -/
def signedRawBeforeDivision (x y : Nat → Nat) (s : BasisState) : BasisState :=
  signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
    (fig14LookupXState (fun a => (ShorECDLP.p-x a)%ShorECDLP.p) s)
/-- Complete state before multiplication. The nonzero division agreement theorem
identifies the extended state map here with the raw operation's output. -/
def signedRawBeforeMultiplication (x y : Nat → Nat) (s : BasisState) : BasisState :=
  fig14LookupXState (fun a => (3*x a)%ShorECDLP.p)
    (fig14SquareSubtractState (zeroAllowedDivisionOutputState (signedRawBeforeDivision x y s)))
/-- Explicit query readiness (including root control 836=true) and both executed
nonzero interfaces. Neither field operation's precondition is optional. -/
def SignedRawDomain (x y : Nat → Nat) (s : BasisState) : Prop :=
  PointLookupValid s ∧
  boolWordToNat (wireValues (List.range' 263 256) (signedRawBeforeDivision x y s)) ≠ 0 ∧
  boolWordToNat (wireValues (List.range' 263 256) (signedRawBeforeMultiplication x y s)) ≠ 0

/-- The two raw domain conditions are exactly those of the selected signed
constant core. Query readiness, including the enabled root, remains required. -/
theorem signedRawDomain_iff_selected (x y : Nat → Nat) (s : BasisState) (hs : PointLookupValid s) :
    SignedRawDomain x y s ↔
      Fig14RawDomain (x (tableAddressValue pointLookupAddress s)) (signedPointTableValue y s) s := by
  have he := signedLookup_interfaces_eq x y s hs
  change signedRawBeforeDivision x y s = _ ∧ signedRawBeforeMultiplication x y s = _ at he
  simp only [SignedRawDomain,Fig14RawDomain,he.1,he.2,and_iff_right hs,and_iff_right hs.1]

/-- Excluding the four affine exceptional points supplies the actual signed
query domain, for the constant selected by the entry address and sign. -/
theorem signedRawDomain_of_nonexceptional (x y : Nat → Nat) (s : BasisState)
    (hs : PointLookupValid s)
    (hx : x (tableAddressValue pointLookupAddress s)<ShorECDLP.p)
    (hy : signedPointTableValue y s<ShorECDLP.p)
    (h₁ : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular
      (boolWordToNat (wireValues (List.range' 263 256) s))
      (boolWordToNat (wireValues (List.range' 580 256) s)))
    (h₂ : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular
      (x (tableAddressValue pointLookupAddress s) : ShorECDLP.Fp)
      (signedPointTableValue y s : ShorECDLP.Fp))
    (hout : (.some h₁ : ShorECDLP.Secp256k1.Point) ∉ fig14ExceptionalPoints (.some h₂)) :
    SignedRawDomain x y s := by
  have hf := fig14_nonexceptional_factors h₁ h₂ hout
  exact (signedRawDomain_iff_selected x y s hs).mpr
    (fig14RawDomain_of_factors _ _ hx hy s hs.1 hs.2 hf.1 hf.2)

/-- Five load/add/unload queries around the raw arithmetic core; no repair. -/
def signedRawProgram (x y : Nat → Nat) : AdaptiveCircuit :=
  ((((((((fig14LookupX (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))).seq
    secp256k1InPlaceDivision).seq fig14SquareSubtract).seq
    (fig14LookupX (fun a => (3*x a)%ShorECDLP.p))).seq
    secp256k1InPlaceMultiplication).seq fig14Negate).seq
    (fig14LookupX (fun a => x a%ShorECDLP.p))).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))

private theorem strengthen {program : AdaptiveCircuit}
    {ideal : State →ₗ[ℂ] State} {Valid Stronger : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid) (hsub : ∀ s, Stronger s → Valid s) :
    CoherentlyImplementsOn program ideal Stronger := by
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (hsub s hs)),hm⟩
private theorem rawDivision_coherent :
    CoherentlyImplementsOn secp256k1InPlaceDivision
      (Finsupp.lmapDomain ℂ ℂ zeroAllowedDivisionOutputState)
      (fun s => Secp256k1ZeroAllowedInputValid s ∧
        boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) := by
  have h := strengthen secp256k1InPlaceDivision_coherent
    (fun s (hs : Secp256k1ZeroAllowedInputValid s ∧ boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) => ⟨⟨hs.1.1, Nat.pos_of_ne_zero hs.2, hs.1.2.2.1⟩, hs.1.2.2.2⟩)
  apply h.congrIdeal
  intro s hs
  simp [ket, rawDivision_agrees s hs.1 hs.2]
private theorem rawMultiplication_coherent :
    CoherentlyImplementsOn secp256k1InPlaceMultiplication
      (Finsupp.lmapDomain ℂ ℂ zeroAllowedMultiplicationOutputState)
      (fun s => Secp256k1ZeroAllowedInputValid s ∧
        boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) := by
  have h := strengthen secp256k1InPlaceMultiplication_coherent
    (fun s (hs : Secp256k1ZeroAllowedInputValid s ∧ boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) => ⟨⟨hs.1.1, Nat.pos_of_ne_zero hs.2, hs.1.2.2.1⟩, hs.1.2.2.2⟩)
  apply h.congrIdeal
  intro s hs
  simp [ket, rawMultiplication_agrees s hs.1 hs.2]

private theorem coherent_coordinate_seq (a b : AdaptiveCircuit)
    (f g : BasisState → BasisState) (Valid Next : BasisState → Prop)
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) Valid)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) Next)
    (hf : ∀ s, Valid s → Next (f s)) :
    CoherentlyImplementsOn (a.seq b) (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) Valid := by
  have h := ha.seq hb (by
    intro s hs
    have he : (Finsupp.lmapDomain ℂ ℂ f) (ket s)=ket (f s) := by simp [ket]
    rw [he]
    exact supportedOn_ket _ _ (hf s hs))
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

/-- The actual five-query raw circuit coherently implements the complete signed
coordinate state on supported superpositions, including address/sign superpositions. -/
theorem signedRawProgram_coherent (x y : Nat → Nat) :
    CoherentlyImplementsOn (signedRawProgram x y)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState x y)) (SignedRawDomain x y) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  let p1 := fig14LookupX (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)
  let f1 := fig14LookupXState (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)
  have h1 : CoherentlyImplementsOn p1 (Finsupp.lmapDomain ℂ ℂ f1) (SignedRawDomain x y) := strengthen (fig14LookupX_coherent _ (fun _ => hk _)) (fun _ hs => hs.1)
  have r1 : ∀ s, PointLookupValid s → PointLookupValid (f1 s) := fig14LookupXState_ready _ (fun _ => hk _)
  let p2 := signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  let f2 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  have h2 : CoherentlyImplementsOn p2 (Finsupp.lmapDomain ℂ ℂ f2) PointLookupValid := signedPointLookupY_coherent _ (fun _ => hk _)
  have r2 : ∀ s, PointLookupValid s → PointLookupValid (f2 s) := signedPointLookupYState_ready _ (fun _ => hk _)
  let p3 := secp256k1InPlaceDivision
  let f3 := zeroAllowedDivisionOutputState
  have h3 : CoherentlyImplementsOn p3 (Finsupp.lmapDomain ℂ ℂ f3) (fun s => Secp256k1ZeroAllowedInputValid s ∧ boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) := rawDivision_coherent
  have r3 : ∀ s, PointLookupValid s → PointLookupValid (f3 s) := lookup_division_ready
  let p4 := fig14SquareSubtract
  let f4 := fig14SquareSubtractState
  have h4 : CoherentlyImplementsOn p4 (Finsupp.lmapDomain ℂ ℂ f4) PointLookupValid := lookup_restrict fig14SquareSubtract_coherent
  have r4 : ∀ s, PointLookupValid s → PointLookupValid (f4 s) := lookup_square_ready
  let p5 := fig14LookupX (fun a => (3*x a)%ShorECDLP.p)
  let f5 := fig14LookupXState (fun a => (3*x a)%ShorECDLP.p)
  have h5 : CoherentlyImplementsOn p5 (Finsupp.lmapDomain ℂ ℂ f5) PointLookupValid := fig14LookupX_coherent _ (fun _ => hk _)
  have r5 : ∀ s, PointLookupValid s → PointLookupValid (f5 s) := fig14LookupXState_ready _ (fun _ => hk _)
  let p6 := secp256k1InPlaceMultiplication
  let f6 := zeroAllowedMultiplicationOutputState
  have h6 : CoherentlyImplementsOn p6 (Finsupp.lmapDomain ℂ ℂ f6) (fun s => Secp256k1ZeroAllowedInputValid s ∧ boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) := rawMultiplication_coherent
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
  have c2 := coherent_coordinate_seq _ _ _ _ _ _ h1 h2 (fun s hs => r1 s hs.1)
  have v2 := fun s (hs : SignedRawDomain x y s) => r2 _ (r1 s hs.1)
  have c3 := coherent_coordinate_seq _ _ _ _ _ _ c2 h3 (fun s hs => ⟨(v2 s hs).1, hs.2.1⟩)
  have v3 := fun s hs => r3 _ (v2 s hs)
  have c4 := coherent_coordinate_seq _ _ _ _ _ _ c3 h4 v3
  have v4 := fun s hs => r4 _ (v3 s hs)
  have c5 := coherent_coordinate_seq _ _ _ _ _ _ c4 h5 v4
  have v5 := fun s hs => r5 _ (v4 s hs)
  have c6 := coherent_coordinate_seq _ _ _ _ _ _ c5 h6 (fun s hs => ⟨(v5 s hs).1, hs.2.2⟩)
  have v6 := fun s hs => r6 _ (v5 s hs)
  have c7 := coherent_coordinate_seq _ _ _ _ _ _ c6 h7 v6
  have v7 := fun s hs => r7 _ (v6 s hs)
  have c8 := coherent_coordinate_seq _ _ _ _ _ _ c7 h8 v7
  have v8 := fun s hs => r8 _ (v7 s hs)
  have c9 := coherent_coordinate_seq _ _ _ _ _ _ c8 h9 v8
  exact c9

private theorem division_snapshot_ready (x y : Nat → Nat) (s : BasisState)
    (hs : SignedRawDomain x y s) : PointLookupValid (signedRawBeforeDivision x y s) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  exact signedPointLookupYState_ready _ (fun _ => hk _) _
    (fig14LookupXState_ready _ (fun _ => hk _) s hs.1)
private theorem multiplication_snapshot_ready (x y : Nat → Nat) (s : BasisState)
    (hs : SignedRawDomain x y s) : PointLookupValid (signedRawBeforeMultiplication x y s) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  exact fig14LookupXState_ready _ (fun _ => hk _) _
    (lookup_square_ready _ (lookup_division_ready _ (division_snapshot_ready x y s hs)))

/-- Both actual query-core arithmetic inputs satisfy the original nonzero contract. -/
theorem signedRawDomain_interfaces (x y : Nat → Nat) (s : BasisState)
    (hs : SignedRawDomain x y s) :
    Secp256k1InPlaceInputValid (signedRawBeforeDivision x y s) ∧
    Secp256k1InPlaceInputValid (signedRawBeforeMultiplication x y s) := by
  have hd := (division_snapshot_ready x y s hs).1
  have hm := (multiplication_snapshot_ready x y s hs).1
  exact ⟨⟨⟨hd.1, Nat.pos_of_ne_zero hs.2.1, hd.2.2.1⟩, hd.2.2.2⟩,
    ⟨⟨hm.1, Nat.pos_of_ne_zero hs.2.2, hm.2.2.1⟩, hm.2.2.2⟩⟩

/-- The second domain snapshot is precisely the full state after raw division,
square subtraction and the third real coordinate query. -/
theorem signedRawBeforeMultiplication_eq (x y : Nat → Nat) (s : BasisState)
    (hs : SignedRawDomain x y s) :
    signedRawBeforeMultiplication x y s =
      fig14LookupXState (fun a => (3*x a)%ShorECDLP.p)
        (fig14SquareSubtractState (fig15DivisionOutputState (signedRawBeforeDivision x y s))) := by
  rw [rawDivision_agrees _ (division_snapshot_ready x y s hs).1 hs.2.1]
  rfl

/-- All query/work wires and the enabled root are restored, and the output
is ready for another query core (whose nonzero conditions still need proof). -/
theorem signedRawProgram_output (x y : Nat → Nat) (s : BasisState)
    (hs : SignedRawDomain x y s) :
    PointLookupValid (signedLookupCoordinateState x y s) ∧
    ∀ w, w ∉ List.range' 263 256 → w ∉ List.range' 580 256 →
      signedLookupCoordinateState x y s w = s w :=
  ⟨signedLookupCoordinateState_ready x y s hs.1,
    signedLookupCoordinateState_frame x y s hs.1⟩
end
end ShorECDLP.Paper2607_13816
