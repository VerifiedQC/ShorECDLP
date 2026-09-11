#!/usr/bin/env python3
"""Check emitted coherent controls, low-bit masks, and nonterminal R controls."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.StepControl
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
private def zeros (v n : Nat) : Nat := ((List.range n).filter (fun k => !v.testBit k)).length
private def ccx (n : Nat) : Nat := if n<2 then 0 else 2*n-3
private def cx (n : Nat) : Nat := if n=1 then 1 else 0
private def xx (n : Nat) : Nat := if n=0 then 1 else 0
def main : IO Unit := do
  let mut checked := 0
  for n in List.range 11 do
    for v in [0,1,2,2^n-1,2^n,2^n+3] do
      let r := List.range n
      let c := computeControl r v 20 (List.range' 30 10)
      let expect : PrimitiveResources := ⟨2*zeros v n+xx n,0,cx n,ccx n,0,0⟩
      unless primitiveResources (.unitary c .done) == expect do
        throw (IO.userError "coherent control primitive mismatch")
      checked := checked+1
  for n in [0,1,2,9] do
    for k in List.range 4 do
      for v in [0,1,2,2^k-1,2^k,2^k+3] do
        let c := rControlNonterminal (List.range' 12 k) v 20 (List.range n) 21 (List.range' 30 10)
        let expect : PrimitiveResources := ⟨2*xx n+2*zeros (v%2^k) (k+1),0,
          2*cx n+cx (k+1),2*ccx n+ccx (k+1),0,0⟩
        unless primitiveResources (.unitary c .done) == expect do
          throw (IO.userError "nonterminal control primitive mismatch")
        checked := checked+1
  IO.println s!"{checked} emitted coherent control circuits passed"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="control-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
