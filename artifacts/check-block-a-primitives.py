#!/usr/bin/env python3
"""Check actual production EEA terminal/shift blocks."""
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
    for (c,v) in [(blockAForward r,(⟨108,0,1599,906,0,0⟩ : PrimitiveResources)),
        (blockCForward r,⟨4,0,3,35,0,0⟩),
        (blockAInverse r,⟨140,0,1599,906,0,0⟩),(blockCInverse r,⟨4,0,3,35,0,0⟩)] do
      unless primitiveResources (.unitary c .done) == v do
        throw (IO.userError "indexed block primitive mismatch")
      checked := checked+1
  IO.println s!"{checked} actual production A/C blocks passed"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="block-a-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
