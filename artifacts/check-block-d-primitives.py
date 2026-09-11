#!/usr/bin/env python3
"""Check actual production EEA quotient-length/selector block."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def main : IO Unit := do
  let mut checked := 0
  for offset in [0,1000] do
    let r : IndexedStepRegisters := ⟨offset,offset+1,offset+2,offset+3,
      List.range' (offset+4) 259,List.range' (offset+263) 259,
      List.range' (offset+522) 9,List.range' (offset+531) 9,
      List.range' (offset+540) 9,List.range' (offset+549) 9,List.range' (offset+558) 22⟩
    for (k,K) in [(1,1),(1,2),(1,4),(2,5),(7,9),(1,128),(1,256),(127,256)] do
      let w : ActiveWindow := ⟨k,K⟩
      let leaves := K-k+1
      let nodes := leaves-1
      let v : PrimitiveResources := ⟨48+4*nodes,0,170+2*leaves+2*nodes,108+leaves+2*nodes,0,0⟩
      unless primitiveResources (.unitary (blockDForward r w) .done) == v do
        throw (IO.userError "indexed quotient block primitive mismatch")
      unless primitiveResources (.unitary (blockDInverse r w) .done) == v do
        throw (IO.userError "inverse quotient block primitive mismatch")
      checked := checked+2
  IO.println s!"{checked} actual production D blocks passed"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="block-d-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
