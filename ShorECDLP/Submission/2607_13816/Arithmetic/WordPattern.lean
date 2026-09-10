import ShorECDLP.Submission.«2607_13816».Arithmetic.WordGray
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Compile-time state used to read compressed equality constants. -/
def wordPattern (R : List Wire) (bits : List Bool) : BasisState :=
  fun w => bits.getD (R.idxOf w) false
theorem wordPattern_read (R : List Wire) (bits : List Bool) (hn : R.Nodup)
    (hl : bits.length=R.length) : wireValues R (wordPattern R bits)=bits := by
  apply List.ext_getElem
  · simpa [wireValues] using hl.symm
  · intro i hi hj
    simp only [wireValues,List.getElem_map,wordPattern,hn.idxOf_getElem]
    exact List.getD_eq_getElem _ _ hj
/-- First position where two words differ; callers prove adjacency and equal width. -/
def firstDifferentBit : List Bool → List Bool → Nat
  | a::as,b::bs => if a=b then firstDifferentBit as bs+1 else 0
  | _,_ => 0
private theorem firstDifferentBit_prefix (pre tail : List Bool) (a b : Bool) (hab : a≠b) :
    firstDifferentBit (pre++a::tail) (pre++b::tail)=pre.length := by
  induction pre with
  | nil => simp [firstDifferentBit,hab]
  | cons h hs ih => simp [firstDifferentBit,ih]
private theorem getD_at_middle (pre tail : List Bool) (a : Bool) :
    (pre++a::tail).getD pre.length false=a := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp
private theorem getD_off_middle (pre tail : List Bool) (a b : Bool) (i : Nat) (hi : i≠pre.length) :
    (pre++a::tail).getD i false=(pre++b::tail).getD i false := by
  by_cases hl : i<pre.length
  · rw [List.getD_append _ _ _ _ hl,List.getD_append _ _ _ _ hl]
  · have hle : pre.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hle,List.getD_append_right _ _ _ _ hle]
    have hs : ∃ j, i-pre.length=j+1 := ⟨i-pre.length-1,by omega⟩
    obtain ⟨j,hj⟩ := hs
    rw [hj,List.getD_cons_succ,List.getD_cons_succ]
/-- The first differing position of adjacent words selects a real register wire,
and their compile-time patterns differ only there. -/
theorem adjacent_word_patterns (R : List Wire) (a b : List Bool) (hn : R.Nodup)
    (hl : a.length=R.length) (ha : WordsAdjacent a b) :
    let i := firstDifferentBit a b
    i<R.length ∧
    wordPattern R a (R.getD i 0)≠wordPattern R b (R.getD i 0) ∧
    ∀ w ∈ R, w≠R.getD i 0 → wordPattern R a w=wordPattern R b w := by
  obtain ⟨pre,tail,x,y,hxy,rfl,rfl⟩ := ha
  rw [firstDifferentBit_prefix pre tail x y hxy]
  dsimp only
  have hi : pre.length<R.length := by simp only [List.length_append,List.length_cons] at hl; omega
  have ht : R.getD pre.length 0=R[pre.length] := List.getD_eq_getElem _ _ hi
  have hidx : R.idxOf (R.getD pre.length 0)=pre.length := by rw [ht,hn.idxOf_getElem]
  refine ⟨hi,?_,?_⟩
  · simp only [wordPattern,hidx,getD_at_middle]
    exact hxy
  · intro w hw hwt
    have hj : R.idxOf w≠pre.length := by
      intro he
      apply hwt
      rw [← he,List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hw)]
      exact (List.getElem_idxOf (List.idxOf_lt_length_of_mem hw)).symm
    exact getD_off_middle pre tail x y (R.idxOf w) hj
end ShorECDLP.Paper2607_13816
