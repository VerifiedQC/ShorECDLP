import ShorECDLP.Framework.Quantum.InnerProduct

namespace ShorECDLP.Quantum

/--
Controlled phase using one clean ancilla.

The ancilla is required to start in `|0⟩`:

    .CCX c t anc
    .P .forward k anc
    .CCX c t anc

The first Toffoli computes `c ∧ t` into `anc`, `.P .forward k anc` applies the phase
exactly when both controls are set, and the final Toffoli uncomputes the
ancilla.
-/
def cPhase
    (k : Nat)
    (c t anc : Wire) : Circuit :=
  [
    .CCX c t anc,
    .P .forward k anc,
    .CCX c t anc
  ]

/--
Swap two wires using the standard three-CNOT construction.
-/
def swap
    (a b : Wire) : Circuit :=
  [
    .CX a b,
    .CX b a,
    .CX a b
  ]

/-!
Apply all controlled phases into one QFT target qubit.

`controls` is ordered from nearest to farthest:

    [q_{j-1}, q_{j-2}, ..., q_0]

so the first control uses `P(.forward,2)`, the next `P(.forward,3)`, etc.
-/
def qftPhaseLayer
    (target anc : Wire) :
    List Wire → Nat → Circuit
  | [], _ =>
      []
  | c :: cs, k =>
      cPhase k c target anc ++
        qftPhaseLayer target anc cs (k + 1)

/--
QFT without final bit reversal.

The input list is ordered MSB-first.
-/
def qftCoreMSB
    (anc : Wire) :
    List Wire → Circuit
  | [] => []

  | target :: rest =>
      [.H target] ++
      qftPhaseLayer target anc rest 2 ++
      qftCoreMSB anc rest

def qftCore
    (r : List Wire)
    (anc : Wire) : Circuit :=
  qftCoreMSB anc r.reverse

/--
Reverse the logical order of a register using pairwise SWAPs.
-/
def bitReverse
    (r : List Wire) : Circuit :=
  ((r.zip r.reverse).take (r.length / 2)).flatMap
    fun p => swap p.1 p.2

/--
Textbook exact QFT on an LSB-first register.
`anc` is one clean ancilla reused by every controlled phase.
-/
def qft
    (r : List Wire)
    (anc : Wire) : Circuit :=
  qftCore r anc ++
  bitReverse r

/-- Textbook exact inverse QFT. Reversing gate order alone would be
incorrect because phase gates are not self-adjoint; `Circuit.adjoint`
also reverses every phase direction. -/
def iqft
    (r : List Wire)
    (anc : Wire) : Circuit :=
  Circuit.adjoint (qft r anc)
