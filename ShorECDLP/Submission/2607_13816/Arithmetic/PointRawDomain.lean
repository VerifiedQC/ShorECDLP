import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCircuit
/-! Figure 14 coordinate core with direct nonzero Figure 15 arithmetic.
This module removes the zero-as-one wrappers only in a separately named circuit.
The domain checks both executed field interfaces for both control values. It does
not establish that the full window algorithm stays in this domain, an exceptional
input probability bound, or a paper resource/success certificate. Existing repaired
circuits and their certificates are unchanged. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem prepare_nonzero (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hn : boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) :
    fig15ZeroPrepareState s = s := by
  have hr : 263 :: List.range' 264 255 = List.range' 263 256 := by decide +kernel
  funext w
  by_cases h1 : w = 263
  · subst w; simp [fig15ZeroPrepareState, nonzeroInputPrepareState, hr, hn]
  · by_cases h2 : w = 837
    · subst w; simp [fig15ZeroPrepareState, nonzeroInputPrepareState, hr, hn, upd, hs.2.1]
    · simp [fig15ZeroPrepareState, nonzeroInputPrepareState, hr, hn, upd, h1, h2]
private theorem nonzero_ready (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hn : boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) :
    Secp256k1InPlaceInputValid s := by
  simpa only [prepare_nonzero s hs hn] using fig15ZeroPrepareState_ready s hs

theorem rawDivision_agrees (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hn : boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) :
    fig15DivisionOutputState s = zeroAllowedDivisionOutputState s := by
  rw [zeroAllowedDivisionOutputState_frame s hs, prepare_nonzero s hs hn]
  funext w
  by_cases hw : w ∈ List.range' 580 256
  · simp only [if_pos hw]
  · simp only [if_neg hw, fig15DivisionOutputState_eq s (nonzero_ready s hs hn)]
theorem rawMultiplication_agrees (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hn : boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) :
    fig15MultiplicationOutputState s = zeroAllowedMultiplicationOutputState s := by
  rw [zeroAllowedMultiplicationOutputState_frame s hs, prepare_nonzero s hs hn]
  funext w
  by_cases hw : w ∈ List.range' 580 256
  · simp only [if_pos hw]
  · simp only [if_neg hw, fig15MultiplicationOutputState_eq s (nonzero_ready s hs hn)]


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
    (fun s (hs : Secp256k1ZeroAllowedInputValid s ∧ boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) => nonzero_ready s hs.1 hs.2)
  apply h.congrIdeal
  intro s hs
  simp [ket, rawDivision_agrees s hs.1 hs.2]
private theorem rawMultiplication_coherent :
    CoherentlyImplementsOn secp256k1InPlaceMultiplication
      (Finsupp.lmapDomain ℂ ℂ zeroAllowedMultiplicationOutputState)
      (fun s => Secp256k1ZeroAllowedInputValid s ∧
        boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) := by
  have h := strengthen secp256k1InPlaceMultiplication_coherent
    (fun s (hs : Secp256k1ZeroAllowedInputValid s ∧ boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) => nonzero_ready s hs.1 hs.2)
  apply h.congrIdeal
  intro s hs
  simp [ket, rawMultiplication_agrees s hs.1 hs.2]

/-- The state at the actually executed division interface, for either control. -/
def fig14BeforeDivision (x₂ y₂ : Nat) (s : BasisState) : BasisState :=
  fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)
    (fig14ConstantXState ((ShorECDLP.p-x₂)%ShorECDLP.p) s)
/-- State at the multiplication interface. Under the division nonzero condition,
`rawDivision_agrees` identifies this with the raw division's actual ideal output. -/
def fig14BeforeMultiplication (x₂ y₂ : Nat) (s : BasisState) : BasisState :=
  fig14ControlledConstantXState ((3*x₂)%ShorECDLP.p)
    (fig14SquareSubtractState (zeroAllowedDivisionOutputState (fig14BeforeDivision x₂ y₂ s)))
/-- Both field operations execute even when control 836 is false. Neither
nonzero condition is guarded by that control. Algorithmic coverage is not asserted. -/
def Fig14RawDomain (x₂ y₂ : Nat) (s : BasisState) : Prop :=
  Secp256k1ZeroAllowedInputValid s ∧
  boolWordToNat (wireValues (List.range' 263 256) (fig14BeforeDivision x₂ y₂ s)) ≠ 0 ∧
  boolWordToNat (wireValues (List.range' 263 256) (fig14BeforeMultiplication x₂ y₂ s)) ≠ 0

/-- Nine coordinate stages with the nonzero Figure 15 operations directly;
no zero-as-one wrappers and no exceptional-point repair. -/
def fig14RawProgram (x₂ y₂ : Nat) : AdaptiveCircuit :=
  (((((((((fig14ConstantX ((ShorECDLP.p-x₂)%ShorECDLP.p)).seq (fig14ControlledConstantY ((ShorECDLP.p-y₂)%ShorECDLP.p))).seq (secp256k1InPlaceDivision)).seq (fig14SquareSubtract)).seq (fig14ControlledConstantX ((3*x₂)%ShorECDLP.p))).seq (secp256k1InPlaceMultiplication)).seq (fig14Negate)).seq (fig14ConstantX (x₂%ShorECDLP.p))).seq (fig14ControlledConstantY ((ShorECDLP.p-y₂)%ShorECDLP.p)))


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


/-- Raw physical circuit coherently implements the complete coordinate state
on the executed domain, with normalized input-independent branch coefficients. -/
theorem fig14RawProgram_coherent (x₂ y₂ : Nat) :
    CoherentlyImplementsOn (fig14RawProgram x₂ y₂)
      (Finsupp.lmapDomain ℂ ℂ (fig14CoordinateState x₂ y₂)) (Fig14RawDomain x₂ y₂) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  let p1 := fig14ConstantX ((ShorECDLP.p-x₂)%ShorECDLP.p)
  let f1 := fig14ConstantXState ((ShorECDLP.p-x₂)%ShorECDLP.p)
  have h1 : CoherentlyImplementsOn p1 (Finsupp.lmapDomain ℂ ℂ f1) (Fig14RawDomain x₂ y₂) := strengthen (fig14ConstantX_coherent _) (fun _ hs => hs.1)
  have r1 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f1 s) := fig14ConstantXState_ready _ (hk _)
  let p2 := fig14ControlledConstantY ((ShorECDLP.p-y₂)%ShorECDLP.p)
  let f2 := fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)
  have h2 : CoherentlyImplementsOn p2 (Finsupp.lmapDomain ℂ ℂ f2) Secp256k1ZeroAllowedInputValid := fig14ControlledConstantY_coherent _
  have r2 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f2 s) := fig14ControlledConstantYState_ready _ (hk _)
  let p3 := secp256k1InPlaceDivision
  let f3 := zeroAllowedDivisionOutputState
  have h3 : CoherentlyImplementsOn p3 (Finsupp.lmapDomain ℂ ℂ f3) (fun s => Secp256k1ZeroAllowedInputValid s ∧ boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) := rawDivision_coherent
  have r3 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f3 s) := fig14Division_ready
  let p4 := fig14SquareSubtract
  let f4 := fig14SquareSubtractState
  have h4 : CoherentlyImplementsOn p4 (Finsupp.lmapDomain ℂ ℂ f4) Secp256k1ZeroAllowedInputValid := fig14SquareSubtract_coherent
  have r4 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f4 s) := fig14SquareSubtractState_ready
  let p5 := fig14ControlledConstantX ((3*x₂)%ShorECDLP.p)
  let f5 := fig14ControlledConstantXState ((3*x₂)%ShorECDLP.p)
  have h5 : CoherentlyImplementsOn p5 (Finsupp.lmapDomain ℂ ℂ f5) Secp256k1ZeroAllowedInputValid := fig14ControlledConstantX_coherent _
  have r5 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f5 s) := fig14ControlledConstantXState_ready _ (hk _)
  let p6 := secp256k1InPlaceMultiplication
  let f6 := zeroAllowedMultiplicationOutputState
  have h6 : CoherentlyImplementsOn p6 (Finsupp.lmapDomain ℂ ℂ f6) (fun s => Secp256k1ZeroAllowedInputValid s ∧ boolWordToNat (wireValues (List.range' 263 256) s) ≠ 0) := rawMultiplication_coherent
  have r6 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f6 s) := fig14Multiplication_ready
  let p7 := fig14Negate
  let f7 := fig14NegateState
  have h7 : CoherentlyImplementsOn p7 (Finsupp.lmapDomain ℂ ℂ f7) Secp256k1ZeroAllowedInputValid := fig14Negate_coherent
  have r7 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f7 s) := fig14NegateState_ready
  let p8 := fig14ConstantX (x₂%ShorECDLP.p)
  let f8 := fig14ConstantXState (x₂%ShorECDLP.p)
  have h8 : CoherentlyImplementsOn p8 (Finsupp.lmapDomain ℂ ℂ f8) Secp256k1ZeroAllowedInputValid := fig14ConstantX_coherent _
  have r8 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f8 s) := fig14ConstantXState_ready _ (hk _)
  let p9 := fig14ControlledConstantY ((ShorECDLP.p-y₂)%ShorECDLP.p)
  let f9 := fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)
  have h9 : CoherentlyImplementsOn p9 (Finsupp.lmapDomain ℂ ℂ f9) Secp256k1ZeroAllowedInputValid := fig14ControlledConstantY_coherent _
  have c2 := coherent_coordinate_seq _ _ _ _ _ _ h1 h2 (fun s hs => r1 s hs.1)
  have v2 := fun s (hs : Fig14RawDomain x₂ y₂ s) => r2 _ (r1 s hs.1)
  have c3 := coherent_coordinate_seq _ _ _ _ _ _ c2 h3 (fun s hs => ⟨v2 s hs, hs.2.1⟩)
  have v3 := fun s hs => r3 _ (v2 s hs)
  have c4 := coherent_coordinate_seq _ _ _ _ _ _ c3 h4 v3
  have v4 := fun s hs => r4 _ (v3 s hs)
  have c5 := coherent_coordinate_seq _ _ _ _ _ _ c4 h5 v4
  have v5 := fun s hs => r5 _ (v4 s hs)
  have c6 := coherent_coordinate_seq _ _ _ _ _ _ c5 h6 (fun s hs => ⟨v5 s hs, hs.2.2⟩)
  have v6 := fun s hs => r6 _ (v5 s hs)
  have c7 := coherent_coordinate_seq _ _ _ _ _ _ c6 h7 v6
  have v7 := fun s hs => r7 _ (v6 s hs)
  have c8 := coherent_coordinate_seq _ _ _ _ _ _ c7 h8 v7
  have v8 := fun s hs => r8 _ (v7 s hs)
  have c9 := coherent_coordinate_seq _ _ _ _ _ _ c8 h9 v8
  exact c9

/-- The two executed interfaces satisfy the original nonzero arithmetic contract.
This includes false controls; there is no control hypothesis. -/
theorem fig14RawDomain_interfaces (x₂ y₂ : Nat) (s : BasisState)
    (hs : Fig14RawDomain x₂ y₂ s) :
    Secp256k1InPlaceInputValid (fig14BeforeDivision x₂ y₂ s) ∧
    Secp256k1InPlaceInputValid (fig14BeforeMultiplication x₂ y₂ s) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  have hd : Secp256k1ZeroAllowedInputValid (fig14BeforeDivision x₂ y₂ s) :=
    fig14ControlledConstantYState_ready _ (hk _) _ (fig14ConstantXState_ready _ (hk _) s hs.1)
  have hm : Secp256k1ZeroAllowedInputValid (fig14BeforeMultiplication x₂ y₂ s) :=
    fig14ControlledConstantXState_ready _ (hk _) _ (fig14SquareSubtractState_ready _ (fig14Division_ready _ hd))
  exact ⟨nonzero_ready _ hd hs.2.1, nonzero_ready _ hm hs.2.2⟩

/-- Complete frame and canonical clean-work readiness of the coherent raw output. -/
theorem fig14RawProgram_output (x₂ y₂ : Nat) (s : BasisState)
    (hs : Fig14RawDomain x₂ y₂ s) :
    Secp256k1ZeroAllowedInputValid (fig14CoordinateState x₂ y₂ s) ∧
    ∀ w, w ∉ List.range' 263 256 → w ∉ List.range' 580 256 →
      fig14CoordinateState x₂ y₂ s w = s w :=
  ⟨fig14CoordinateState_ready x₂ y₂ s hs.1,
    fig14CoordinateState_frame x₂ y₂ s hs.1⟩
end ShorECDLP.Paper2607_13816
