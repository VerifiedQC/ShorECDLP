#!/usr/bin/env python3
"""Replay exact primitive counts for 9-bit endpoint transforms."""
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r"""
import ShorECDLP.Submission.«2607_13816».EEA.EndpointPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def main : IO Unit := do
  let mut checked := 0
  for n in [0,1,255,256,511,512,1024] do
    for k in [0,1,4,128,255,511,512] do
      for restore in [false,true] do
        let program := if restore then restoreIntervalEndpoints else prepareIntervalEndpoints
        let v := primitiveResources (.unitary (program (List.range 9) (List.range' 9 9)
          (List.range' 18 9) (List.range' 27 9) 36 n k) .done)
        let expected : PrimitiveResources :=
          ⟨10+2*(constantBits 9 4).count true+2*(constantBits 9 (n+2)).count true+
            4*(constantBits 9 k).count true,0,190,104,0,0⟩
        unless v == expected do throw (IO.userError "endpoint primitive mismatch")
        checked := checked+1
  IO.println s!"{checked} actual endpoint transforms passed primitive formulas"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="endpoint-primitives-") as directory:
        source = Path(directory) / "Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
