import ShorECDLP.Submission.«2607_13816».Arithmetic.PointStages
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

/-- The nine Figure 14 coordinate stages on the shared physical layout.
The two field operations use the explicit zero-as-one extension. This
coordinate permutation is not yet certified as total elliptic-curve addition. -/
def fig14CoordinateProgram (x₂ y₂ : Nat) : AdaptiveCircuit :=
  (((((((((fig14ConstantX ((ShorECDLP.p-x₂)%ShorECDLP.p)).seq (fig14ControlledConstantY ((ShorECDLP.p-y₂)%ShorECDLP.p))).seq (secp256k1ZeroAllowedDivision)).seq (fig14SquareSubtract)).seq (fig14ControlledConstantX ((3*x₂)%ShorECDLP.p))).seq (secp256k1ZeroAllowedMultiplication)).seq (fig14Negate)).seq (fig14ConstantX (x₂%ShorECDLP.p))).seq (fig14ControlledConstantY ((ShorECDLP.p-y₂)%ShorECDLP.p)))

/-- Complete-state specification, including restoration of all working wires. -/
def fig14CoordinateState (x₂ y₂ : Nat) (s : BasisState) : BasisState :=
  (fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)) ((fig14ConstantXState (x₂%ShorECDLP.p)) ((fig14NegateState) ((zeroAllowedMultiplicationOutputState) ((fig14ControlledConstantXState ((3*x₂)%ShorECDLP.p)) ((fig14SquareSubtractState) ((zeroAllowedDivisionOutputState) ((fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)) ((fig14ConstantXState ((ShorECDLP.p-x₂)%ShorECDLP.p)) (s)))))))))

private theorem coherent_coordinate_seq (a b : AdaptiveCircuit)
    (f g : BasisState → BasisState) (Valid : BasisState → Prop)
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) Valid)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) Valid)
    (hf : ∀ s, Valid s → Valid (f s)) :
    CoherentlyImplementsOn (a.seq b) (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) Valid := by
  have h := ha.seq hb (by
    intro s hs
    have he : (Finsupp.lmapDomain ℂ ℂ f) (ket s)=ket (f s) := by simp [ket]
    rw [he]
    exact supportedOn_ket _ _ (hf s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket]

/-- Every stage leaves the next stage's complete input contract ready,
even when either coordinate is zero and the control is arbitrary. -/
theorem fig14CoordinateState_ready (x₂ y₂ : Nat) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1ZeroAllowedInputValid (fig14CoordinateState x₂ y₂ s) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  unfold fig14CoordinateState
  apply fig14ControlledConstantYState_ready _ (hk _)
  apply fig14ConstantXState_ready _ (hk _)
  apply fig14NegateState_ready
  apply fig14Multiplication_ready
  apply fig14ControlledConstantXState_ready _ (hk _)
  apply fig14SquareSubtractState_ready
  apply fig14Division_ready
  apply fig14ControlledConstantYState_ready _ (hk _)
  apply fig14ConstantXState_ready _ (hk _)
  exact hs

/-- One normalized, input-independent branch expansion implements the actual
nine-stage coordinate program on arbitrary supported superpositions. -/
theorem fig14CoordinateProgram_coherent (x₂ y₂ : Nat) :
    CoherentlyImplementsOn (fig14CoordinateProgram x₂ y₂)
      (Finsupp.lmapDomain ℂ ℂ (fig14CoordinateState x₂ y₂)) Secp256k1ZeroAllowedInputValid := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  let p1 := fig14ConstantX ((ShorECDLP.p-x₂)%ShorECDLP.p)
  let f1 := fig14ConstantXState ((ShorECDLP.p-x₂)%ShorECDLP.p)
  have h1 : CoherentlyImplementsOn p1 (Finsupp.lmapDomain ℂ ℂ f1) Secp256k1ZeroAllowedInputValid := fig14ConstantX_coherent _
  have r1 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f1 s) := fig14ConstantXState_ready _ (hk _)
  let p2 := fig14ControlledConstantY ((ShorECDLP.p-y₂)%ShorECDLP.p)
  let f2 := fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)
  have h2 : CoherentlyImplementsOn p2 (Finsupp.lmapDomain ℂ ℂ f2) Secp256k1ZeroAllowedInputValid := fig14ControlledConstantY_coherent _
  have r2 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f2 s) := fig14ControlledConstantYState_ready _ (hk _)
  let p3 := secp256k1ZeroAllowedDivision
  let f3 := zeroAllowedDivisionOutputState
  have h3 : CoherentlyImplementsOn p3 (Finsupp.lmapDomain ℂ ℂ f3) Secp256k1ZeroAllowedInputValid := secp256k1ZeroAllowedDivision_coherent
  have r3 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f3 s) := fig14Division_ready
  let p4 := fig14SquareSubtract
  let f4 := fig14SquareSubtractState
  have h4 : CoherentlyImplementsOn p4 (Finsupp.lmapDomain ℂ ℂ f4) Secp256k1ZeroAllowedInputValid := fig14SquareSubtract_coherent
  have r4 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f4 s) := fig14SquareSubtractState_ready
  let p5 := fig14ControlledConstantX ((3*x₂)%ShorECDLP.p)
  let f5 := fig14ControlledConstantXState ((3*x₂)%ShorECDLP.p)
  have h5 : CoherentlyImplementsOn p5 (Finsupp.lmapDomain ℂ ℂ f5) Secp256k1ZeroAllowedInputValid := fig14ControlledConstantX_coherent _
  have r5 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f5 s) := fig14ControlledConstantXState_ready _ (hk _)
  let p6 := secp256k1ZeroAllowedMultiplication
  let f6 := zeroAllowedMultiplicationOutputState
  have h6 : CoherentlyImplementsOn p6 (Finsupp.lmapDomain ℂ ℂ f6) Secp256k1ZeroAllowedInputValid := secp256k1ZeroAllowedMultiplication_coherent
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
  have c2 := coherent_coordinate_seq _ _ _ _ _ h1 h2 r1
  have v2 := fun s hs => r2 _ (r1 s hs)
  have c3 := coherent_coordinate_seq _ _ _ _ _ c2 h3 v2
  have v3 := fun s hs => r3 _ (v2 s hs)
  have c4 := coherent_coordinate_seq _ _ _ _ _ c3 h4 v3
  have v4 := fun s hs => r4 _ (v3 s hs)
  have c5 := coherent_coordinate_seq _ _ _ _ _ c4 h5 v4
  have v5 := fun s hs => r5 _ (v4 s hs)
  have c6 := coherent_coordinate_seq _ _ _ _ _ c5 h6 v5
  have v6 := fun s hs => r6 _ (v5 s hs)
  have c7 := coherent_coordinate_seq _ _ _ _ _ c6 h7 v6
  have v7 := fun s hs => r7 _ (v6 s hs)
  have c8 := coherent_coordinate_seq _ _ _ _ _ c7 h8 v7
  have v8 := fun s hs => r8 _ (v7 s hs)
  have c9 := coherent_coordinate_seq _ _ _ _ _ c8 h9 v8
  exact c9

private theorem coordinate_frame_seq (f g : BasisState → BasisState)
    (hfready : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f s))
    (hf : ∀ s, Secp256k1ZeroAllowedInputValid s → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f s w=s w)
    (hg : ∀ s, Secp256k1ZeroAllowedInputValid s → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → g s w=s w) :
    ∀ s, Secp256k1ZeroAllowedInputValid s → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → g (f s) w=s w := by
  intro s hs w hx hy
  rw [hg _ (hfready s hs) w hx hy,hf s hs w hx hy]

/-- The complete coordinate circuit restores every wire outside X and Y,
including the arbitrary point control, zero flag, and all working wires. -/
theorem fig14CoordinateState_frame (x₂ y₂ : Nat) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (w : Wire)
    (hx : w ∉ List.range' 263 256) (hy : w ∉ List.range' 580 256) :
    fig14CoordinateState x₂ y₂ s w=s w := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  let f1 := fig14ConstantXState ((ShorECDLP.p-x₂)%ShorECDLP.p)
  have r1 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f1 s) := fig14ConstantXState_ready _ (hk _)
  let f2 := fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)
  have r2 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f2 s) := fig14ControlledConstantYState_ready _ (hk _)
  let f3 := zeroAllowedDivisionOutputState
  have r3 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f3 s) := fig14Division_ready
  let f4 := fig14SquareSubtractState
  have r4 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f4 s) := fig14SquareSubtractState_ready
  let f5 := fig14ControlledConstantXState ((3*x₂)%ShorECDLP.p)
  have r5 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f5 s) := fig14ControlledConstantXState_ready _ (hk _)
  let f6 := zeroAllowedMultiplicationOutputState
  have r6 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f6 s) := fig14Multiplication_ready
  let f7 := fig14NegateState
  have r7 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f7 s) := fig14NegateState_ready
  let f8 := fig14ConstantXState (x₂%ShorECDLP.p)
  have r8 : ∀ s, Secp256k1ZeroAllowedInputValid s → Secp256k1ZeroAllowedInputValid (f8 s) := fig14ConstantXState_ready _ (hk _)
  let f9 := fig14ControlledConstantYState ((ShorECDLP.p-y₂)%ShorECDLP.p)
  have h1 : ∀ u, Secp256k1ZeroAllowedInputValid u → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f1 u w=u w := by
    intro u hu w hx _hy
    exact (fig14ConstantXState_correct _ (hk _) u hu).2 w hx
  have h2 : ∀ u, Secp256k1ZeroAllowedInputValid u → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f2 u w=u w := by
    intro u hu w _hx hy
    exact (fig14ControlledConstantYState_correct _ (hk _) u hu).2 w hy
  have h3 : ∀ u, Secp256k1ZeroAllowedInputValid u → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f3 u w=u w := by
    intro u hu w _hx hy
    change zeroAllowedDivisionOutputState u w=u w
    simp only [zeroAllowedDivisionOutputState_frame u hu,if_neg hy]
  have h4 : ∀ u, Secp256k1ZeroAllowedInputValid u → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f4 u w=u w := by
    intro u hu w hx _hy
    exact (fig14SquareSubtractState_correct u hu).2 w hx
  have h5 : ∀ u, Secp256k1ZeroAllowedInputValid u → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f5 u w=u w := by
    intro u hu w hx _hy
    exact (fig14ControlledConstantXState_correct _ (hk _) u hu).2 w hx
  have h6 : ∀ u, Secp256k1ZeroAllowedInputValid u → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f6 u w=u w := by
    intro u hu w _hx hy
    change zeroAllowedMultiplicationOutputState u w=u w
    simp only [zeroAllowedMultiplicationOutputState_frame u hu,if_neg hy]
  have h7 : ∀ u, Secp256k1ZeroAllowedInputValid u → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f7 u w=u w := by
    intro u hu w hx _hy
    exact (fig14NegateState_correct u hu).2 w hx
  have h8 : ∀ u, Secp256k1ZeroAllowedInputValid u → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f8 u w=u w := by
    intro u hu w hx _hy
    exact (fig14ConstantXState_correct _ (hk _) u hu).2 w hx
  have h9 : ∀ u, Secp256k1ZeroAllowedInputValid u → ∀ w,
      w ∉ List.range' 263 256 → w ∉ List.range' 580 256 → f9 u w=u w := by
    intro u hu w _hx hy
    exact (fig14ControlledConstantYState_correct _ (hk _) u hu).2 w hy
  have c2 := coordinate_frame_seq _ _ r1 h1 h2
  have v2 := fun u hu => r2 _ (r1 u hu)
  have c3 := coordinate_frame_seq _ _ v2 c2 h3
  have v3 := fun u hu => r3 _ (v2 u hu)
  have c4 := coordinate_frame_seq _ _ v3 c3 h4
  have v4 := fun u hu => r4 _ (v3 u hu)
  have c5 := coordinate_frame_seq _ _ v4 c4 h5
  have v5 := fun u hu => r5 _ (v4 u hu)
  have c6 := coordinate_frame_seq _ _ v5 c5 h6
  have v6 := fun u hu => r6 _ (v5 u hu)
  have c7 := coordinate_frame_seq _ _ v6 c6 h7
  have v7 := fun u hu => r7 _ (v6 u hu)
  have c8 := coordinate_frame_seq _ _ v7 c7 h8
  have v8 := fun u hu => r8 _ (v7 u hu)
  have c9 := coordinate_frame_seq _ _ v8 c8 h9
  exact c9 s hs w hx hy
end ShorECDLP.Paper2607_13816
