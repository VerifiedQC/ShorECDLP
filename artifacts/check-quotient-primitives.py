#!/usr/bin/env python3
"""Check actual coherent quotient blocks, including the full 256-lane traversal."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.QuotientSwap
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def main : IO Unit := do
  let mut checked := 0
  for offset in [0,1000] do
    for (k,K) in [(0,0),(1,1),(1,2),(1,4),(2,5),(7,9),(1,128),(1,256),(127,256)] do
      let r : QuotientSwapRegisters := ⟨offset,offset+1,List.range' (offset+2) (K-k+1),
        List.range' (offset+300) 9,List.range' (offset+309) 9,List.range' (offset+318) 10⟩
      let leaves := K-k+1
      let nodes := leaves-1
      let expect : PrimitiveResources := ⟨8+4*nodes,0,144+2*leaves+2*nodes,72+leaves+2*nodes,0,0⟩
      unless primitiveResources (.unitary (quotientSwapUnitary r k K) .done) == expect do
        throw (IO.userError "quotient block primitive mismatch")
      checked := checked+1
  IO.println s!"{checked} actual coherent quotient blocks passed"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="quotient-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
