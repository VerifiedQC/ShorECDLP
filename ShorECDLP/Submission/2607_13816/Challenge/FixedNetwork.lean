import ShorECDLP.Submission.«2607_13816».Challenge.EndpointTransposition
import ShorECDLP.Submission.«2607_13816».Challenge.FixedMatching
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
/-- Slots 0–3 hold source endpoints, 4–7 targets, and 8 the data word. -/
abbrev MatchingSlot := Fin 9
abbrev MatchingMove := MatchingSlot × MatchingSlot × MatchingSlot
/-- Six tail adjustments, four data swaps, then the exact reverse adjustments. -/
def matchingPrepare : List MatchingMove :=
  [(3,7,2),(3,7,1),(2,6,1),(3,7,0),(2,6,0),(1,5,0)]
def matchingData : List MatchingMove := [(3,7,8),(2,6,8),(1,5,8),(0,4,8)]
def matchingNetwork : List MatchingMove :=
  matchingPrepare ++ matchingData ++ matchingPrepare.reverse

def matchingMoveRun {α : Type*} [DecidableEq α] (m : MatchingMove)
    (s : MatchingSlot → α) : MatchingSlot → α :=
  Function.update s m.2.2 (Equiv.swap (s m.1) (s m.2.1) (s m.2.2))
def matchingNetworkRun {α : Type*} [DecidableEq α]
    (s : MatchingSlot → α) : MatchingSlot → α :=
  matchingNetwork.foldl (fun s m => matchingMoveRun m s) s

theorem matchingNetwork_length : matchingNetwork.length = 16 := rfl

theorem matchingNetworkRun_data {α : Type*} [DecidableEq α] (s : MatchingSlot → α) :
    matchingNetworkRun s 8 =
      runFiniteSwaps (finiteMatchingSwaps [(s 0,s 4),(s 1,s 5),(s 2,s 6),(s 3,s 7)]) (s 8) := by
  simp [matchingNetworkRun, matchingNetwork, matchingPrepare, matchingData,
    matchingMoveRun, Function.update, runFiniteSwaps, finiteMatchingSwaps,
    finiteMatchingPermutation]

theorem matchingNetworkRun_frame {α : Type*} [DecidableEq α]
    (s : MatchingSlot → α) (i : MatchingSlot) (hi : i ≠ 8) :
    matchingNetworkRun s i = s i := by
  fin_cases i <;> simp_all [matchingNetworkRun, matchingNetwork, matchingPrepare,
    matchingData, matchingMoveRun, Function.update]

open ShorECDLP Quantum

/-- This lowering uses only fixed wire addresses, never endpoint values. -/
def matchingMovesCircuit {n : Nat} (rows : MatchingSlot → Fin n → Wire)
    (flag : Wire) (scratch : List Wire) (moves : List MatchingMove) : Circuit :=
  moves.flatMap fun m => endpointTranspositionCircuit
    (rows m.1) (rows m.2.1) (rows m.2.2) flag scratch

theorem matchingMoveCircuit_correct {n : Nat}
    (rows : MatchingSlot → Fin n → Wire) (flag : Wire) (scratch : List Wire)
    (m : MatchingMove)
    (g : EndpointGeometry (rows m.1) (rows m.2.1) (rows m.2.2) flag scratch)
    (apart : ∀ i j, i ≠ j → ∀ k l, rows i k ≠ rows j l)
    (st : BasisState) (hc : Clean scratch st) (hz : st flag = false) :
    let out := Classical.run (endpointTranspositionCircuit
      (rows m.1) (rows m.2.1) (rows m.2.2) flag scratch) st
    (∀ i, out ∘ rows i = matchingMoveRun m (fun j => st ∘ rows j) i) ∧
      Clean scratch out ∧ out flag = false ∧
      (∀ w, (∀ i k, w ≠ rows i k) → out w = st w) := by
  have h := endpointTransposition_correct _ _ _ flag scratch g st hc hz
  refine ⟨?_, ?_, h.2.1, ?_⟩
  · intro i
    by_cases hi : i = m.2.2
    · subst i
      simpa [matchingMoveRun] using h.1
    · simp only [matchingMoveRun, Function.update_of_ne hi]
      funext k
      exact h.2.2 (rows i k) (fun l => apart i m.2.2 hi k l)
  · intro w hw
    rw [h.2.2 w (fun k => (g.scratchApart w hw k).2.2)]
    exact hc w hw
  · intro w hw
    exact h.2.2 w (hw m.2.2)

theorem matchingMovesCircuit_correct {n : Nat}
    (rows : MatchingSlot → Fin n → Wire) (flag : Wire) (scratch : List Wire)
    (moves : List MatchingMove)
    (geometries : ∀ m ∈ moves,
      EndpointGeometry (rows m.1) (rows m.2.1) (rows m.2.2) flag scratch)
    (apart : ∀ i j, i ≠ j → ∀ k l, rows i k ≠ rows j l)
    (st : BasisState) (hc : Clean scratch st) (hz : st flag = false) :
    let out := Classical.run (matchingMovesCircuit rows flag scratch moves) st
    (∀ i, out ∘ rows i = moves.foldl (fun s m => matchingMoveRun m s)
      (fun j => st ∘ rows j) i) ∧ Clean scratch out ∧ out flag = false ∧
      (∀ w, (∀ i k, w ≠ rows i k) → out w = st w) := by
  induction moves generalizing st with
  | nil => exact ⟨fun _ => rfl, hc, hz, fun _ _ => rfl⟩
  | cons m ms ih =>
    have hm := matchingMoveCircuit_correct rows flag scratch m
      (geometries m (by simp)) apart st hc hz
    have ht := ih (fun x hx => geometries x (by simp [hx])) _ hm.2.1 hm.2.2.1
    simp only [matchingMovesCircuit, List.flatMap_cons, Classical.run_append, List.foldl_cons]
    refine ⟨?_, ht.2.1, ht.2.2.1, ?_⟩
    · intro i
      exact (ht.1 i).trans (congrArg (fun s => ms.foldl (fun s m => matchingMoveRun m s) s i) (funext hm.1))
    · intro w hw
      exact (ht.2.2.2 w hw).trans (hm.2.2.2 w hw)

def matchingCircuit {n : Nat} (rows : MatchingSlot → Fin n → Wire)
    (flag : Wire) (scratch : List Wire) : Circuit :=
  matchingMovesCircuit rows flag scratch matchingNetwork

theorem matchingCircuit_correct {n : Nat}
    (rows : MatchingSlot → Fin n → Wire) (flag : Wire) (scratch : List Wire)
    (geometries : ∀ m ∈ matchingNetwork,
      EndpointGeometry (rows m.1) (rows m.2.1) (rows m.2.2) flag scratch)
    (apart : ∀ i j, i ≠ j → ∀ k l, rows i k ≠ rows j l)
    (st : BasisState) (hc : Clean scratch st) (hz : st flag = false) :
    let out := Classical.run (matchingCircuit rows flag scratch) st
    out ∘ rows 8 = runFiniteSwaps (finiteMatchingSwaps
      [(st ∘ rows 0,st ∘ rows 4),(st ∘ rows 1,st ∘ rows 5),
       (st ∘ rows 2,st ∘ rows 6),(st ∘ rows 3,st ∘ rows 7)]) (st ∘ rows 8) ∧
    (∀ i, i ≠ 8 → out ∘ rows i = st ∘ rows i) ∧
    Clean scratch out ∧ out flag = false ∧
    (∀ w, (∀ i k, w ≠ rows i k) → out w = st w) := by
  have h := matchingMovesCircuit_correct rows flag scratch matchingNetwork
    geometries apart st hc hz
  refine ⟨(h.1 8).trans (matchingNetworkRun_data _), ?_, h.2⟩
  intro i hi
  exact (h.1 i).trans (matchingNetworkRun_frame _ i hi)

theorem matchingMovesCircuit_HPFree {n : Nat}
    (rows : MatchingSlot → Fin n → Wire) (flag : Wire) (scratch : List Wire)
    (moves : List MatchingMove) :
    Classical.HPFree (matchingMovesCircuit rows flag scratch moves) := by
  induction moves with
  | nil => exact Classical.hpFree_nil
  | cons m ms ih =>
    simp only [matchingMovesCircuit, List.flatMap_cons, Classical.hpFree_append]
    refine ⟨?_, ih⟩
    simp only [endpointTranspositionCircuit, Classical.hpFree_append]
    exact ⟨⟨endpointTests_HPFree _ _ _ _ _, endpointWordCircuit_HPFree _ _⟩,
      endpointTests_HPFree _ _ _ _ _⟩

/-- The fixed circuit introduces no basis-state phase. -/
theorem matchingCircuit_quantum {n : Nat}
    (rows : MatchingSlot → Fin n → Wire) (flag : Wire) (scratch : List Wire)
    (st : BasisState) :
    Quantum.run (matchingCircuit rows flag scratch) (ket st) =
      ket (Classical.run (matchingCircuit rows flag scratch) st) := by
  exact Quantum.run_ket_agrees_classical _ _
    (matchingMovesCircuit_HPFree rows flag scratch matchingNetwork)

/-- A concrete contiguous layout: nine 513-bit words, one flag, 511 scratch wires. -/
def matchingRows (base : Wire) (j : MatchingSlot) (i : Fin 513) : Wire :=
  base + 513*j.val + i.val
def matchingFlag (base : Wire) : Wire := base + 4617
def matchingScratch (base : Wire) : List Wire :=
  List.ofFn (fun i : Fin 511 => base + 4618 + i.val)

theorem matchingRows_injective (base : Wire) (j : MatchingSlot) :
    Function.Injective (matchingRows base j) := by
  intro i k h
  apply Fin.ext
  exact Nat.add_left_cancel h

theorem matchingRows_apart (base : Wire) (i j : MatchingSlot) (h : i ≠ j)
    (k l : Fin 513) : matchingRows base i k ≠ matchingRows base j l := by
  have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
  dsimp [matchingRows]
  change (base + 513*i.val + k.val : Nat) ≠ base + 513*j.val + l.val
  simp only [Wire] at *
  omega

theorem matchingRows_bound (base : Wire) (j : MatchingSlot) (i : Fin 513) :
    matchingRows base j i < matchingFlag base := by
  dsimp [matchingRows, matchingFlag]
  change (base + 513*j.val + i.val : Nat) < base + 4617
  simp only [Wire] at *
  omega

theorem matchingScratch_above (base : Wire) (w : Wire) (hw : w ∈ matchingScratch base) :
    matchingFlag base < w := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  dsimp [matchingFlag]
  change (base + 4617 : Nat) < base + 4618 + i.val
  simp only [Wire] at *
  omega

theorem matchingRows_layout (base : Wire) (j : MatchingSlot) :
    EqConstLayout (List.ofFn (matchingRows base j)) (matchingFlag base) (matchingScratch base) := by
  refine ⟨?_, ?_⟩
  · simp only [List.length_ofFn, matchingScratch]
    decide
  · apply List.nodup_append.mpr
    refine ⟨List.nodup_ofFn.mpr (matchingRows_injective base j), ?_, ?_⟩
    · apply List.nodup_cons.mpr
      refine ⟨?_, List.nodup_ofFn.mpr ?_⟩
      · intro h
        exact (Nat.lt_irrefl _) (matchingScratch_above base _ h)
      · intro i k h
        apply Fin.ext
        exact Nat.add_left_cancel h
    · intro w hw v ht he
      subst v
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      rcases List.mem_cons.mp ht with he | hs
      · exact (Nat.ne_of_lt (matchingRows_bound base j i)) he
      · exact (Nat.lt_asymm (matchingScratch_above base _ hs)) (matchingRows_bound base j i)

theorem matchingNetwork_distinct (m : MatchingMove) (hm : m ∈ matchingNetwork) :
    m.1 ≠ m.2.2 ∧ m.2.1 ≠ m.2.2 := by
  simp [matchingNetwork, matchingPrepare, matchingData] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem matchingNetwork_geometry (base : Wire) (m : MatchingMove) (hm : m ∈ matchingNetwork) :
    EndpointGeometry (matchingRows base m.1) (matchingRows base m.2.1)
      (matchingRows base m.2.2) (matchingFlag base) (matchingScratch base) := by
  have hd := matchingNetwork_distinct m hm
  refine ⟨matchingRows_injective base _, ?_, ?_, matchingRows_layout base _, ?_⟩
  · intro i j
    exact ⟨matchingRows_apart base _ _ hd.1 i j, matchingRows_apart base _ _ hd.2 i j⟩
  · intro i
    exact ⟨(Nat.ne_of_lt (matchingRows_bound base _ i)).symm,
      (Nat.ne_of_lt (matchingRows_bound base _ i)).symm,
      (Nat.ne_of_lt (matchingRows_bound base _ i)).symm⟩
  · intro w hw i
    have hs := matchingScratch_above base w hw
    exact ⟨(Nat.ne_of_lt ((matchingRows_bound base _ i).trans hs)).symm,
      (Nat.ne_of_lt ((matchingRows_bound base _ i).trans hs)).symm,
      (Nat.ne_of_lt ((matchingRows_bound base _ i).trans hs)).symm⟩
end ShorECDLP.Paper2607_13816.ChallengeMigration
