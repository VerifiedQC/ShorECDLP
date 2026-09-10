import ShorECDLP.Submission.«2607_13816».Arithmetic.WordGray
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointCorrection
namespace ShorECDLP.Paper2607_13816
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩
/-- Fixed 513-bit encoding in physical X, Y, infinity order. -/
def pointCoordinateWord (v : Bool × (ShorECDLP.Fp × ShorECDLP.Fp)) : List Bool :=
  (constantBits 256 v.2.1.val++constantBits 256 v.2.2.val)++[v.1]
@[simp] theorem pointCoordinateWord_length (v : Bool × (ShorECDLP.Fp × ShorECDLP.Fp)) :
    (pointCoordinateWord v).length=513 := by simp [pointCoordinateWord]
private theorem fieldBits_injective : Function.Injective (fun x : ShorECDLP.Fp => constantBits 256 x.val) := by
  intro x y h
  have hh := congrArg boolWordToNat h
  have hx : x.val<2^256 := (ZMod.val_lt x).trans (by decide +kernel)
  have hy : y.val<2^256 := (ZMod.val_lt y).trans (by decide +kernel)
  simp only [boolWordToNat_constantBits,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] at hh
  exact ZMod.val_injective _ hh
theorem pointCoordinateWord_injective : Function.Injective pointCoordinateWord := by
  intro x y h
  have hs := List.append_inj h (by simp)
  have hxy := List.append_inj hs.1 (by simp)
  have hx := fieldBits_injective hxy.1
  have hy := fieldBits_injective hxy.2
  have hb : x.1=y.1 := by simpa using hs.2
  exact Prod.ext hb (Prod.ext hx hy)
private theorem run_mapped_swaps {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (pairs : List (α × α)) :
    ∀ x, runFiniteSwaps (pairs.map (fun p => (f p.1,f p.2))) (f x)=f (runFiniteSwaps pairs x) := by
  induction pairs with
  | nil => intro x; rfl
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    intro x
    simp only [List.map_cons,runFiniteSwaps,List.foldl_cons,hf.swap_apply]
    exact ih (Equiv.swap a b x)
private theorem run_expanded_swaps (pairs : List (List Bool × List Bool))
    (h : ∀ p ∈ pairs, p.1.length=p.2.length) :
    ∀ x, runFiniteSwaps (pairs.flatMap (fun p => wordGraySwaps p.1 p.2)) x=runFiniteSwaps pairs x := by
  induction pairs with
  | nil => intro x; rfl
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    intro x
    have he := wordGraySwaps_correct a b (h (a,b) (by simp)) x
    have ht := ih (fun p hp => h p (by simp [hp])) (Equiv.swap a b x)
    simp only [List.flatMap_cons,runFiniteSwaps,List.foldl_append,List.foldl_cons]
    rw [show List.foldl (fun y p => Equiv.swap p.1 p.2 y) x (wordGraySwaps a b)=Equiv.swap a b x from he]
    exact ht
/-- Explicit adjacent-word swaps for the finite exceptional-point correction. -/
noncomputable def pointCorrectionWordEdges {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) : List (List Bool × List Bool) :=
  ((fig14CorrectionSwaps hC).map (fun p => (pointCoordinateWord p.1,pointCoordinateWord p.2))).flatMap
    (fun p => wordGraySwaps p.1 p.2)
theorem pointCorrectionWordEdges_correct {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) (P : ShorECDLP.Secp256k1.Point) :
    runFiniteSwaps (pointCorrectionWordEdges hC)
      (pointCoordinateWord (fig14EncodedEquiv x₂ y₂ (fig14PointEncoding P)))=
        pointCoordinateWord (fig14PointEncoding (P+(.some hC))) := by
  rw [pointCorrectionWordEdges,run_expanded_swaps _ (by
    intro p hp
    obtain ⟨q,hmem,rfl⟩ := List.mem_map.mp hp
    simp)]
  rw [run_mapped_swaps pointCoordinateWord pointCoordinateWord_injective,
    fig14CorrectionSwaps_correct hC P]
private theorem expanded_length (pairs : List (List Bool × List Bool)) (n : Nat)
    (h : ∀ p ∈ pairs, p.1.length=n) :
    (pairs.flatMap (fun p => wordGraySwaps p.1 p.2)).length≤pairs.length*(2*n) := by
  induction pairs with
  | nil => simp
  | cons p ps ih =>
    have hp := wordGraySwaps_length p.1 p.2
    rw [h p (by simp)] at hp
    have ht := ih (fun q hq => h q (by simp [hq]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith
/-- The four exceptional swaps expand to at most 4,104 single-bit edges. -/
theorem pointCorrectionWordEdges_length {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    (pointCorrectionWordEdges hC).length≤4104 := by
  have hh := expanded_length
    ((fig14CorrectionSwaps hC).map (fun p => (pointCoordinateWord p.1,pointCoordinateWord p.2))) 513 (by
      intro p hp
      obtain ⟨q,hmem,rfl⟩ := List.mem_map.mp hp
      simp)
  have hs := fig14CorrectionSwaps_length hC
  simp only [List.length_map] at hh
  exact hh.trans (by omega)
theorem pointCorrectionWordEdges_adjacent {x₂ y₂ : ShorECDLP.Fp}
    (hC : ShorECDLP.Secp256k1.curve.toAffine.Nonsingular x₂ y₂) :
    ∀ p ∈ pointCorrectionWordEdges hC, WordsAdjacent p.1 p.2 ∧ p.1.length=513 := by
  intro p hp
  obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  have hh := wordGraySwaps_edges (pointCoordinateWord v.1) (pointCoordinateWord v.2) (by simp) p hp
  simpa using hh
end ShorECDLP.Paper2607_13816
