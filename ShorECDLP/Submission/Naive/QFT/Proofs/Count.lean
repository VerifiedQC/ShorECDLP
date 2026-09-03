import ShorECDLP.Submission.Naive.QFT.Proofs.Step
import ShorECDLP.Submission.Naive.QFT.Proofs.Swap

/-
# Q4 — QFT and inverse-QFT structural obligations

This file discharges the structural half of the QFT submission: exact T-count,
well-formedness, and output normalization for `qft r anc` and its adjoint-defined
inverse `iqft r anc`. None of it touches the Fourier semantics. The forward results
are tallies over the `++`/`flatMap` circuit shape; the inverse results follow from
the generic adjoint contracts.

- **T-count** (`tCount_qft`): `qft r anc = qftCore r anc ++ bitReverse r`. The bit
  reversal is all SWAPs (T-count `0`); the core contributes one `qftPhaseLayer` of
  `15` T per remaining wire, so the whole circuit costs `15 * (n(n-1)/2)` where
  `n = r.length` — one controlled phase per unordered pair of register qubits.
- **Well-formedness** (`qft_wellFormed`): every atom's wires are distinct because the
  register is `Nodup` and the shared ancilla lies outside it.
- **Normalization** (`normSq_run_qft_ket`): well-formedness feeds the framework's
  `normSq_run_ket`, so a basis input stays a unit vector.
- **Inverse QFT** (`tCount_iqft`, `iqft_wellFormed`, `normSq_run_iqft_ket`): circuit
  adjoint preserves the forward circuit's cost, well-formedness, and normalization.
-/

namespace ShorECDLP.Quantum

open scoped Classical

/-! ============================================================
    T-count
============================================================ -/

/-- A phase layer onto one target costs `15` T per control. -/
theorem tCount_qftPhaseLayer
    (target anc : Wire) :
    ∀ (cs : List Wire) (k : Nat),
      tCount (qftPhaseLayer target anc cs k) = 15 * cs.length := by
  intro cs
  induction cs with
  | nil =>
      intro k
      rfl
  | cons c cs ih =>
      intro k
      rw [qftPhaseLayer, tCount_append, tCount_cPhase, ih (k + 1),
        List.length_cons]
      ring

/-- The T-count of the (unreversed) QFT core on an MSB-first list of `m` wires is
`15 * (0 + 1 + ⋯ + (m-1))`: processing the head qubit lays `m-1` controlled phases,
and the tail recurses. -/
theorem tCount_qftCoreMSB
    (anc : Wire) (ws : List Wire) :
    tCount (qftCoreMSB anc ws)
      = 15 * (∑ i ∈ Finset.range ws.length, i) := by
  induction ws with
  | nil =>
      simp [qftCoreMSB]
  | cons target rest ih =>
      have hH : tCount [Gate.H target] = 0 := rfl
      rw [qftCoreMSB, tCount_append, tCount_append, hH,
        tCount_qftPhaseLayer target anc rest 2, ih,
        List.length_cons, Finset.sum_range_succ]
      ring

/-- Every gate in `bitReverse` is a SWAP, so its T-count is `0`. -/
theorem tCount_bitReverse
    (r : List Wire) :
    tCount (bitReverse r) = 0 := by
  rw [bitReverse]
  induction (r.zip r.reverse).take (r.length / 2) with
  | nil => rfl
  | cons p ps ih =>
      rw [List.flatMap_cons, tCount_append, tCount_swap, ih]

/-- **Q4, T-count.** The exact QFT on an `n`-wire register costs

    15 * (n * (n - 1) / 2)

T gates: `15` per controlled phase (`tCount_cPhase`), one controlled phase per
unordered pair of register qubits, and the final bit-reversal SWAPs are free. -/
theorem tCount_qft
    (r : List Wire) (anc : Wire) :
    tCount (qft r anc)
      = 15 * (r.length * (r.length - 1) / 2) := by
  rw [qft, tCount_append, tCount_bitReverse, qftCore, tCount_qftCoreMSB,
    List.length_reverse, Finset.sum_range_id, Nat.add_zero]

/-- The inverse QFT has exactly the same T-count as the QFT: taking a
circuit adjoint changes phase direction but not primitive cost. -/
theorem tCount_iqft
    (r : List Wire) (anc : Wire) :
    tCount (iqft r anc)
      = 15 * (r.length * (r.length - 1) / 2) := by
  rw [iqft, tCount_adjoint, tCount_qft]

/-! ============================================================
    Well-formedness
============================================================ -/

/-- The paired-SWAP wires produced by `bitReverse` are distinct: the pair at index
`i < n/2` is `(r[i], r[n-1-i])`, and `Nodup` forbids `i = n-1-i` below the midpoint. -/
theorem bitReverse_pairs_distinct
    (r : List Wire) (hnd : r.Nodup) :
    ∀ p ∈ (r.zip r.reverse).take (r.length / 2), p.1 ≠ p.2 := by
  refine List.forall_mem_iff_getElem.mpr ?_
  intro i hi
  rw [List.length_take, lt_min_iff] at hi
  obtain ⟨hihalf, hizip⟩ := hi
  have hlen : (r.zip r.reverse).length = r.length := by simp
  rw [hlen] at hizip
  intro heq
  simp only [List.getElem_take, List.getElem_zip, List.getElem_reverse] at heq
  rw [hnd.getElem_inj_iff] at heq
  omega

/-- Each SWAP in a pair list is well-formed when its two wires differ. -/
theorem swapPairs_wellFormed
    (ps : List (Wire × Wire))
    (h : ∀ p ∈ ps, p.1 ≠ p.2) :
    CircuitWellFormed (ps.flatMap fun p => swap p.1 p.2) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.flatMap_cons, circuitWellFormed_append]
      exact ⟨
        swap_wellFormed p.1 p.2 (h p (by simp)),
        ih (fun q hq => h q (by simp [hq]))⟩

/-- The bit-reversal stage is well-formed on any `Nodup` register. -/
theorem bitReverse_wellFormed
    (r : List Wire) (hnd : r.Nodup) :
    CircuitWellFormed (bitReverse r) := by
  rw [bitReverse]
  exact swapPairs_wellFormed _ (bitReverse_pairs_distinct r hnd)

/-- The QFT core is well-formed: each qubit's Hadamard-plus-phase step lands on distinct
wires, all disjoint from the shared clean ancilla. -/
theorem qftCoreMSB_wellFormed
    (anc : Wire) (ws : List Wire)
    (hanc : anc ∉ ws) (hnd : ws.Nodup) :
    CircuitWellFormed (qftCoreMSB anc ws) := by
  induction ws with
  | nil => simp [qftCoreMSB]
  | cons target rest ih =>
      simp only [List.mem_cons, not_or] at hanc
      obtain ⟨hat, harest⟩ := hanc
      obtain ⟨htrest, hndrest⟩ := List.nodup_cons.mp hnd
      rw [qftCoreMSB, circuitWellFormed_append]
      exact ⟨
        qftStep_wellFormed target anc rest 2 (Ne.symm hat) htrest harest,
        ih harest hndrest⟩

/-- The QFT core on an LSB-first register is well-formed. -/
theorem qftCore_wellFormed
    (r : List Wire) (anc : Wire)
    (hanc : anc ∉ r) (hnd : r.Nodup) :
    CircuitWellFormed (qftCore r anc) := by
  rw [qftCore]
  exact qftCoreMSB_wellFormed anc r.reverse (by simpa using hanc) (by simpa using hnd)

/-- **Q4, well-formedness.** The full exact QFT is a well-formed physical circuit
whenever the register is duplicate-free and the shared ancilla lies outside it. -/
theorem qft_wellFormed
    (r : List Wire) (anc : Wire)
    (hanc : anc ∉ r) (hnd : r.Nodup) :
    CircuitWellFormed (qft r anc) := by
  rw [qft, circuitWellFormed_append]
  exact ⟨qftCore_wellFormed r anc hanc hnd, bitReverse_wellFormed r hnd⟩

/-- The inverse QFT is well-formed under exactly the QFT's wire-layout
hypotheses. -/
theorem iqft_wellFormed
    (r : List Wire) (anc : Wire)
    (hanc : anc ∉ r) (hnd : r.Nodup) :
    CircuitWellFormed (iqft r anc) := by
  rw [iqft]
  exact (circuitWellFormed_adjoint (qft r anc)).2
    (qft_wellFormed r anc hanc hnd)

/-! ============================================================
    Output normalization
============================================================ -/

/-- **Q4, normalization.** Running the QFT on a computational-basis ket yields a unit
vector: the circuit is well-formed (`qft_wellFormed`), and every well-formed circuit
preserves squared norm (`normSq_run_ket`). -/
theorem normSq_run_qft_ket
    (r : List Wire) (anc : Wire) (s : BasisState)
    (hanc : anc ∉ r) (hnd : r.Nodup) :
    normSq (run (qft r anc) (ket s)) = 1 :=
  normSq_run_ket (qft r anc) (qft_wellFormed r anc hanc hnd) s

/-- Running the inverse QFT on a computational-basis ket also yields a
unit vector. -/
theorem normSq_run_iqft_ket
    (r : List Wire) (anc : Wire) (s : BasisState)
    (hanc : anc ∉ r) (hnd : r.Nodup) :
    normSq (run (iqft r anc) (ket s)) = 1 :=
  normSq_run_ket (iqft r anc) (iqft_wellFormed r anc hanc hnd) s

end ShorECDLP.Quantum
