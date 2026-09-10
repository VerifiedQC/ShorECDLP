import ShorECDLP.Submission.«2607_13816».Arithmetic.FiniteCorrection
namespace ShorECDLP.Paper2607_13816
private def liftWordPairs (bit : Bool) (pairs : List (List Bool × List Bool)) :=
  pairs.map (fun p => (bit::p.1,bit::p.2))
/-- Recursive Gray-path transpositions: each pair differs at just one bit. -/
def wordGraySwaps : List Bool → List Bool → List (List Bool × List Bool)
  | a::as,b::bs =>
    if a=b then liftWordPairs a (wordGraySwaps as bs)
    else if as=bs then [(a::as,b::bs)]
    else [(a::as,b::as)]++liftWordPairs b (wordGraySwaps as bs)++[(a::as,b::as)]
  | _,_ => []
private theorem swap_cons (bit head : Bool) (a b x : List Bool) :
    Equiv.swap (bit::a) (bit::b) (head::x)=
      if head=bit then head::Equiv.swap a b x else head::x := by
  by_cases hh : head=bit
  · subst head
    by_cases hxa : x=a <;> by_cases hxb : x=b <;> simp [Equiv.swap_apply_def,hxa,hxb]
  · simp [Equiv.swap_apply_def,hh]
private theorem run_lift_cons (bit head : Bool) (pairs : List (List Bool × List Bool))
    (x : List Bool) :
    runFiniteSwaps (liftWordPairs bit pairs) (head::x)=
      if head=bit then head::runFiniteSwaps pairs x else head::x := by
  induction pairs generalizing x with
  | nil => simp [liftWordPairs,runFiniteSwaps]
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    simp only [liftWordPairs,List.map_cons,runFiniteSwaps,List.foldl_cons]
    rw [swap_cons]
    by_cases hh : head=bit
    · simp only [if_pos hh]
      exact (ih (Equiv.swap a b x)).trans (by simp only [if_pos hh,runFiniteSwaps])
    · simp only [if_neg hh]
      exact (ih x).trans (by simp only [if_neg hh])
private theorem run_lift_nil (bit : Bool) (pairs : List (List Bool × List Bool)) :
    runFiniteSwaps (liftWordPairs bit pairs) ([] : List Bool) = [] := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    simpa [liftWordPairs,runFiniteSwaps,Equiv.swap_apply_def] using ih
private theorem run_lift_swap (bit : Bool) (pairs : List (List Bool × List Bool))
    (a b : List Bool) (h : ∀ x, runFiniteSwaps pairs x=Equiv.swap a b x) :
    ∀ x, runFiniteSwaps (liftWordPairs bit pairs) x=Equiv.swap (bit::a) (bit::b) x := by
  intro x
  cases x with
  | nil => simp [run_lift_nil,Equiv.swap_apply_def]
  | cons head x => rw [run_lift_cons,h,swap_cons]
private theorem conjugate_swap {α : Type*} [DecidableEq α] (a b c x : α)
    (hba : b≠a) (hbc : b≠c) :
    Equiv.swap a c (Equiv.swap c b (Equiv.swap a c x))=Equiv.swap a b x := by
  by_cases hac : a=c
  · subst c; simp
  · by_cases hxa : x=a <;> by_cases hxb : x=b <;> by_cases hxc : x=c <;>
      simp_all [Equiv.swap_apply_def,Ne.symm hba,Ne.symm hbc,Ne.symm hac]

theorem wordGraySwaps_correct (a b : List Bool) (hlen : a.length=b.length) :
    ∀ x, runFiniteSwaps (wordGraySwaps a b) x=Equiv.swap a b x := by
  induction a generalizing b with
  | nil =>
    have hb : b=[] := by simpa using hlen.symm
    subst b
    simp [wordGraySwaps,runFiniteSwaps]
  | cons ah ats ih =>
    cases b with
    | nil => simp at hlen
    | cons bh bt =>
      have ht : ats.length=bt.length := by simpa using hlen
      have hr := ih bt ht
      by_cases hh : ah=bh
      · subst bh
        simpa only [wordGraySwaps,if_pos rfl] using run_lift_swap ah _ ats bt hr
      · by_cases htail : ats=bt
        · subst bt
          intro x
          simp [wordGraySwaps,hh,runFiniteSwaps]
        · intro x
          rw [wordGraySwaps,if_neg hh,if_neg htail]
          have hm := run_lift_swap bh _ ats bt hr
          simp only [runFiniteSwaps,List.foldl_append,List.foldl_cons,List.foldl_nil]
          rw [show List.foldl (fun y pair => Equiv.swap pair.1 pair.2 y)
            (Equiv.swap (ah::ats) (bh::ats) x) (liftWordPairs bh (wordGraySwaps ats bt))=
            Equiv.swap (bh::ats) (bh::bt) (Equiv.swap (ah::ats) (bh::ats) x) from hm _]
          exact conjugate_swap (ah::ats) (bh::bt) (bh::ats) x
            (by simp [Ne.symm hh]) (by simp [Ne.symm htail])
/-- Two words differ at exactly one position. -/
def WordsAdjacent (a b : List Bool) : Prop :=
  ∃ pre suffix x y, x≠y ∧ a=pre++x::suffix ∧ b=pre++y::suffix
private theorem adjacent_cons (bit : Bool) {a b : List Bool} (h : WordsAdjacent a b) :
    WordsAdjacent (bit::a) (bit::b) := by
  obtain ⟨pre,suffix,x,y,hxy,ha,hb⟩ := h
  exact ⟨bit::pre,suffix,x,y,hxy,by simp [ha],by simp [hb]⟩

private theorem lift_edges (bit : Bool) (pairs : List (List Bool × List Bool)) (n : Nat)
    (h : ∀ pair ∈ pairs, WordsAdjacent pair.1 pair.2 ∧ pair.1.length=n) :
    ∀ pair ∈ liftWordPairs bit pairs, WordsAdjacent pair.1 pair.2 ∧ pair.1.length=n+1 := by
  intro pair hp
  change pair ∈ pairs.map (fun p => (bit::p.1,bit::p.2)) at hp
  obtain ⟨p,hmem,he⟩ := List.mem_map.mp hp
  subst pair
  have hh := h p hmem
  exact ⟨adjacent_cons bit hh.1,by simpa using hh.2⟩
theorem wordGraySwaps_edges (a b : List Bool) (hlen : a.length=b.length) :
    ∀ pair ∈ wordGraySwaps a b, WordsAdjacent pair.1 pair.2 ∧ pair.1.length=a.length := by
  induction a generalizing b with
  | nil => simp [wordGraySwaps]
  | cons ah ats ih =>
    cases b with
    | nil => simp at hlen
    | cons bh bt =>
      have ht : ats.length=bt.length := by simpa using hlen
      have hr := ih bt ht
      by_cases hh : ah=bh
      · rw [wordGraySwaps,if_pos hh]
        exact lift_edges ah _ _ hr
      · by_cases htail : ats=bt
        · rw [wordGraySwaps,if_neg hh,if_pos htail]
          intro pair hp
          have he := List.mem_singleton.mp hp
          subst pair
          exact ⟨⟨[],ats,ah,bh,hh,rfl,by simp [htail]⟩,rfl⟩
        · rw [wordGraySwaps,if_neg hh,if_neg htail]
          intro pair hp
          simp only [List.mem_append,List.mem_singleton,or_assoc] at hp
          rcases hp with hp | hp | hp
          · subst pair
            exact ⟨⟨[],ats,ah,bh,hh,rfl,rfl⟩,rfl⟩
          · exact lift_edges bh _ _ hr pair hp
          · subst pair
            exact ⟨⟨[],ats,ah,bh,hh,rfl,rfl⟩,rfl⟩
/-- A width-n transposition uses at most 2n adjacent edges. -/
theorem wordGraySwaps_length (a b : List Bool) : (wordGraySwaps a b).length≤2*a.length := by
  induction a generalizing b with
  | nil => simp [wordGraySwaps]
  | cons ah ats ih =>
    cases b with
    | nil => simp [wordGraySwaps]
    | cons bh bt =>
      have hr := ih bt
      by_cases hh : ah=bh
      · simp only [wordGraySwaps,if_pos hh,liftWordPairs,List.length_map,List.length_cons]
        omega
      · by_cases htail : ats=bt
        · simp only [wordGraySwaps,if_neg hh,if_pos htail,List.length_cons,List.length_nil]
          omega
        · simp only [wordGraySwaps,if_neg hh,if_neg htail,liftWordPairs,List.length_append,
            List.length_map,List.length_cons,List.length_nil]
          omega
end ShorECDLP.Paper2607_13816
