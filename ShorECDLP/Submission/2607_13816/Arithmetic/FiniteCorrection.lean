import ShorECDLP.Submission.«2607_13816».Arithmetic.PointPermutation
namespace ShorECDLP.Paper2607_13816

/-- Extend a finite injective matching by one transposition per pair.
The tail is matched first; the head's current image is then swapped to its target. -/
def finiteMatchingPermutation {α : Type*} [DecidableEq α] : List (α × α) → Equiv.Perm α
  | [] => Equiv.refl α
  | (a,b)::rest =>
    let e := finiteMatchingPermutation rest
    e.trans (Equiv.swap (e a) b)

theorem finiteMatchingPermutation_correct {α : Type*} [DecidableEq α]
    (pairs : List (α × α)) (ha : (pairs.map Prod.fst).Nodup) (hb : (pairs.map Prod.snd).Nodup) :
    ∀ a b, (a,b) ∈ pairs → finiteMatchingPermutation pairs a=b := by
  induction pairs with
  | nil => simp
  | cons pair rest ih =>
    rcases pair with ⟨a,b⟩
    have hA := List.nodup_cons.mp ha
    have hB := List.nodup_cons.mp hb
    have htail := ih hA.2 hB.2
    intro x y hxy
    rcases List.mem_cons.mp hxy with hxy | hxy
    · cases hxy
      simp [finiteMatchingPermutation]
    · have hex : x≠a := by
        intro he
        apply hA.1
        exact List.mem_map.mpr ⟨(x,y),hxy,by simp [he]⟩
      have hey : y≠b := by
        intro he
        apply hB.1
        exact List.mem_map.mpr ⟨(x,y),hxy,by simp [he]⟩
      have hyimage : y≠finiteMatchingPermutation rest a := by
        intro he
        exact hex ((finiteMatchingPermutation rest).injective ((htail x y hxy).trans he))
      simp only [finiteMatchingPermutation,Equiv.trans_apply,htail x y hxy]
      exact Equiv.swap_apply_of_ne_of_ne hyimage hey

/-- The matching extension fixes every point outside all listed sources and targets. -/
theorem finiteMatchingPermutation_frame {α : Type*} [DecidableEq α]
    (pairs : List (α × α)) (x : α)
    (hxA : x ∉ pairs.map Prod.fst) (hxB : x ∉ pairs.map Prod.snd) :
    finiteMatchingPermutation pairs x=x := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨a,b⟩
    have hA : x≠a ∧ x ∉ rest.map Prod.fst := by simpa only [List.map_cons,List.mem_cons,not_or] using hxA
    have hB : x≠b ∧ x ∉ rest.map Prod.snd := by simpa only [List.map_cons,List.mem_cons,not_or] using hxB
    have he := ih hA.2 hB.2
    have hxa : x≠finiteMatchingPermutation rest a := by
      intro h
      exact hA.1 ((finiteMatchingPermutation rest).injective (he.trans h))
    simp only [finiteMatchingPermutation,Equiv.trans_apply,he]
    exact Equiv.swap_apply_of_ne_of_ne hxa hB.1

/-- Explicit ordered swaps for the matching extension. -/
def finiteMatchingSwaps {α : Type*} [DecidableEq α] : List (α × α) → List (α × α)
  | [] => []
  | (a,b)::rest => finiteMatchingSwaps rest++[(finiteMatchingPermutation rest a,b)]
def runFiniteSwaps {α : Type*} [DecidableEq α] (swaps : List (α × α)) (x : α) : α :=
  swaps.foldl (fun y pair => Equiv.swap pair.1 pair.2 y) x
private theorem runFiniteSwaps_append {α : Type*} [DecidableEq α]
    (a b : List (α × α)) (x : α) : runFiniteSwaps (a++b) x=runFiniteSwaps b (runFiniteSwaps a x) := by
  simp only [runFiniteSwaps,List.foldl_append]
theorem finiteMatchingSwaps_length {α : Type*} [DecidableEq α] (pairs : List (α × α)) :
    (finiteMatchingSwaps pairs).length=pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => rcases pair with ⟨a,b⟩; simp [finiteMatchingSwaps,ih]
theorem finiteMatchingSwaps_apply {α : Type*} [DecidableEq α] (pairs : List (α × α)) :
    ∀ x, runFiniteSwaps (finiteMatchingSwaps pairs) x=finiteMatchingPermutation pairs x := by
  induction pairs with
  | nil => intro x; rfl
  | cons pair rest ih =>
    rcases pair with ⟨a,b⟩
    intro x
    dsimp only [finiteMatchingSwaps]
    rw [runFiniteSwaps_append,ih]
    rfl

/-- If two injective embeddings agree outside a finite list, the constructed
matching corrects the first to the second everywhere. -/
theorem finiteMatchingPermutation_comp {α β : Type*} [DecidableEq α]
    (F T : β → α) (exceptions : List β) (hnd : exceptions.Nodup)
    (hF : Function.Injective F) (hT : Function.Injective T)
    (hgood : ∀ x, x ∉ exceptions → F x=T x) :
    ∀ x, finiteMatchingPermutation (exceptions.map (fun y => (F y,T y))) (F x)=T x := by
  have ha : ((exceptions.map (fun y => (F y,T y))).map Prod.fst).Nodup := by
    simpa only [List.map_map,Function.comp_def] using hnd.map hF
  have hb : ((exceptions.map (fun y => (F y,T y))).map Prod.snd).Nodup := by
    simpa only [List.map_map,Function.comp_def] using hnd.map hT
  intro x
  by_cases hx : x ∈ exceptions
  · exact finiteMatchingPermutation_correct _ ha hb _ _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
  · rw [finiteMatchingPermutation_frame _ (F x) ?_ ?_,hgood x hx]
    · simp only [List.map_map,Function.comp_def,List.mem_map]
      rintro ⟨y,hy,he⟩
      exact hx ((hF he) ▸ hy)
    · simp only [List.map_map,Function.comp_def,List.mem_map]
      rintro ⟨y,hy,he⟩
      exact hx ((hT (he.trans (hgood x hx))) ▸ hy)
end ShorECDLP.Paper2607_13816
