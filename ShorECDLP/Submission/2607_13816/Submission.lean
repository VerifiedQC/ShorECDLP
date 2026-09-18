import ShorECDLP.Submission.«2607_13816».Window.ReducedNumericBounds

/-!
# Current verified submission — secp256k1 (256 bits)

Target reference: arXiv:2607.13816v2. These are bounds for OUR CURRENT
physical circuit, not the paper's resource claim.

                         One trial             26 trials, with reset
Logical wires            ≤ 1,303               ≤ 1,303 (reused)
T-model cost             ≤ 161,379,629,708,789  ≤ 4,195,870,372,428,514
Success probability      ≥ 16.3%               ≥ 99%

One trial uses 256 + 208 Fourier input bits, one direct point-table load,
and 28 point additions. There are 54,168 phase-rotation cost units.
The Toffoli bound is 23,054,232,807,803. Exact counts depend on the public
point's exceptional-correction tables; this numeric upper bound includes
all correction leaves, with up to 4,104 edges per leaf, and is conservative.

COST CONVENTION: `tCount` charges 7 per CCX and 1 per P rotation.
It is NOT a synthesized Clifford+T count: rotation approximation accuracy,
synthesis cost, and accumulated error have not been supplied.

The success theorem uses a noncomputable public-point-checked decoder
specification (candidate set bound 2^49 + 2), not an efficient executable
classical implementation. Inputs start in the all-zero quantum state.

The 855-wire streaming constructor has an allocation proof, but its full
sampling/success connection remains open. The paper's 835-wire target
is also open. Neither is the circuit certified below.
-/

namespace ShorECDLP.Paper2607_13816.Submission
open Quantum ShorECDLP.Secp256k1
noncomputable section

/-- One actual measured trial; the public identity point has a trivial branch. -/
def trial (Q : Point) (hQ : ShorECDLP.order • Q = 0) : AdaptiveCircuit :=
  reducedSecpWindowProgram Q hQ

/-- Twenty-six actual trials, resetting and reusing the same wires. -/
def algorithm (Q : Point) (hQ : ShorECDLP.order • Q = 0) : AdaptiveCircuit :=
  reducedSecpWindowRepeatedProgram Q hQ

/-- The numeric resource bounds apply to the same trial as the success theorem. -/
theorem trial_resources (Q : Point) (hQ : ShorECDLP.order • Q = 0) :
    (trial Q hQ).qubitCount ≤ 1303 ∧
    (trial Q hQ).tCount ≤ 161379629708789 :=
  ⟨reducedSecpWindowProgram_qubitCount Q hQ, reducedSecpWindow_tCount_bound Q hQ⟩

/-- Exact model count, retaining the public-point-dependent correction cost. -/
theorem trial_t_model_exact (Q : Point) (hQ : ShorECDLP.order • Q = 0) :
    (trial Q hQ).tCount =
      7 * (reducedSecpWindowPrimitives Q hQ).toffoli +
        (reducedSecpWindowPrimitives Q hQ).phase :=
  reducedSecpWindowProgram_tCount_exact Q hQ

/-- Single-run probability for the verified decoder specification. -/
theorem trial_success (Q : Point) (hQ : ShorECDLP.order • Q = 0)
    (d : Nat) (hd : Q = d • G) :
    (163 : ℝ) / 1000 ≤ reducedSecpWindowSuccessMass Q hQ d :=
  reducedSecpWindowSuccessMass_numeric Q hQ d hd

/-- End-to-end certificate: same physical circuit, numeric resources and Born mass.
The filtered branches are exactly those accepted by the verified decoder. -/
theorem certificate (Q : Point) (hQ : ShorECDLP.order • Q = 0)
    (d : Nat) (hd : Q = d • G) :
    (algorithm Q hQ).qubitCount ≤ 1303 ∧
    (algorithm Q hQ).tCount ≤ 4195870372428514 ∧
    (99 : ℝ) / 100 ≤ Instrument.bornMass
      ((algorithm Q hQ).run.filter
        (fun b => (reducedSecpWindowRepeatedCandidate Q hQ b.history).isSome))
      (ket zeroBasisState) :=
  ⟨reducedSecpWindowRepeatedProgram_qubitCount Q hQ,
   reducedSecpWindowRepeated_tCount_bound Q hQ,
   reducedSecpWindowRepeatedCandidate_success Q hQ d hd⟩

/-- Any returned scalar is the correct discrete logarithm modulo the group order. -/
theorem decoder_sound (Q : Point) (hQ : ShorECDLP.order • Q = 0)
    (d : Nat) (hd : Q = d • G) (history : List Bool) (c : ZMod ShorECDLP.order)
    (hc : reducedSecpWindowRepeatedCandidate Q hQ history = some c) :
    c = (d : ZMod ShorECDLP.order) :=
  reducedSecpWindowRepeatedCandidate_sound Q hQ d hd history c hc

end
end ShorECDLP.Paper2607_13816.Submission
