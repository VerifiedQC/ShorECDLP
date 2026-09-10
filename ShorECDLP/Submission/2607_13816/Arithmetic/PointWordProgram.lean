import ShorECDLP.Submission.«2607_13816».Arithmetic.PointWordEdge
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Compile an ordered sequence of adjacent point-word transpositions. -/
def pointWordProgram : List (List Bool × List Bool) → Circuit
  | [] => []
  | (a,b)::ps => pointWordEdge a b ++ pointWordProgram ps

theorem pointWordProgram_clean (ps : List (List Bool × List Bool))
    (hv : ∀ p ∈ ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) :
    Clean (558::559::pointCorrectionScratch) (run (pointWordProgram ps) s) := by
  induction ps generalizing s with
  | nil => exact hc
  | cons p ps ih =>
    have hp := hv p (by simp)
    rw [pointWordProgram,run_append]
    exact ih (fun q hq => hv q (by simp [hq])) _ (pointWordEdge_clean _ _ hp.1 hp.2 s hc)

theorem pointWordProgram_frame (ps : List (List Bool × List Bool))
    (hv : ∀ p ∈ ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) :
    ∀ w, w ∉ pointLogicalWires → run (pointWordProgram ps) s w=s w := by
  induction ps generalizing s with
  | nil => intros; rfl
  | cons p ps ih =>
    have hp := hv p (by simp)
    intro w hw
    rw [pointWordProgram,run_append]
    rw [ih (fun q hq => hv q (by simp [hq])) _ (pointWordEdge_clean _ _ hp.1 hp.2 s hc) w hw]
    exact pointWordEdge_frame _ _ hp.1 hp.2 s hc w hw

theorem pointWordProgram_correct (ps : List (List Bool × List Bool))
    (hv : ∀ p ∈ ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) (hq : s 836=true) :
    wireValues pointLogicalWires (run (pointWordProgram ps) s)=
      runFiniteSwaps ps (wireValues pointLogicalWires s) := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have hp := hv p (by simp)
    rw [pointWordProgram,run_append]
    have hq' : run (pointWordEdge p.1 p.2) s 836=true :=
      (pointWordEdge_control _ _ hp.1 hp.2 s hc).trans hq
    rw [ih (fun q hq => hv q (by simp [hq])) _ (pointWordEdge_clean _ _ hp.1 hp.2 s hc) hq',
      pointWordEdge_correct _ _ hp.1 hp.2 s hc hq]
    rfl

theorem pointWordProgram_disabled (ps : List (List Bool × List Bool))
    (hv : ∀ p ∈ ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513)
    (s : BasisState) (hc : Clean (558::559::pointCorrectionScratch) s) (hq : s 836=false) :
    run (pointWordProgram ps) s=s := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hv p (by simp)
    rw [pointWordProgram,run_append,pointWordEdge_disabled _ _ hp.1 hp.2 s hc hq]
    exact ih (fun q hq => hv q (by simp [hq]))

theorem pointWordProgram_tCount (ps : List (List Bool × List Bool)) :
    ShorECDLP.tCount (pointWordProgram ps) ≤ 21553*ps.length := by
  induction ps with
  | nil => simp [pointWordProgram,ShorECDLP.tCount]
  | cons p ps ih =>
    have hp := pointWordEdge_tCount p.1 p.2
    rw [pointWordProgram,tCount_append]
    simp only [List.length_cons]
    omega

theorem pointWordProgram_HPFree (ps : List (List Bool × List Bool)) :
    HPFree (pointWordProgram ps) := by
  induction ps with
  | nil => simp [pointWordProgram,HPFree]
  | cons p ps ih =>
    exact List.forall_mem_append.mpr ⟨pointWordEdge_HPFree _ _,ih⟩

theorem pointWordProgram_wellFormed (ps : List (List Bool × List Bool))
    (hv : ∀ p ∈ ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513) :
    CircuitWellFormed (pointWordProgram ps) := by
  induction ps with
  | nil => simp [pointWordProgram,CircuitWellFormed]
  | cons p ps ih =>
    have hp := hv p (by simp)
    exact List.forall_mem_append.mpr ⟨pointWordEdge_wellFormed _ _ hp.1 hp.2,
      ih (fun q hq => hv q (by simp [hq]))⟩

theorem pointWordProgram_usesOnly (ps : List (List Bool × List Bool))
    (hv : ∀ p ∈ ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513) :
    PaperCircuitUsesOnly (List.range 839) (pointWordProgram ps) := by
  induction ps with
  | nil => simp [pointWordProgram,PaperCircuitUsesOnly]
  | cons p ps ih =>
    have hp := hv p (by simp)
    exact List.forall_mem_append.mpr ⟨pointWordEdge_usesOnly _ _ hp.1 hp.2,
      ih (fun q hq => hv q (by simp [hq]))⟩
theorem pointWordProgram_qubitCount (ps : List (List Bool × List Bool))
    (hv : ∀ p ∈ ps, WordsAdjacent p.1 p.2 ∧ p.1.length=513) :
    ShorECDLP.qubitCount (pointWordProgram ps) ≤ 839 := by
  have hs : (circuitWires (pointWordProgram ps)).dedup.toFinset ⊆ (List.range 839).toFinset := by
    intro w hw
    have hh : w ∈ circuitWires (pointWordProgram ps) := by simpa using hw
    obtain ⟨gate,hgate,hwgate⟩ := List.mem_flatMap.mp hh
    exact List.mem_toFinset.mpr (pointWordProgram_usesOnly ps hv gate hgate w hwgate)
  have hh := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range)] at hh
  simpa only [ShorECDLP.qubitCount,List.length_range] using hh

end ShorECDLP.Paper2607_13816
