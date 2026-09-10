#!/usr/bin/env python3
"""Run the executable point-constructor check with the repository's pinned Lean."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointTotal
open ShorECDLP ShorECDLP.Paper2607_13816

/-- Reproducible executable-constructor check; no evaluation is used as a proof. -/
def main : IO Unit := do
  let C := Secp256k1.G
  let hC := Secp256k1.generator_nonsingular
  let pairs := fig14CorrectionSwaps hC
  let edges := pointCorrectionWordEdges hC
  unless (fig14ExceptionalList C).length == 4 && pairs.length == 4 && edges.length == 1786 do
    throw (IO.userError "unexpected generator correction shape")
  for P in [0,C,-C,-(C+C),C+C,C+C+C] do
    let actual := runFiniteSwaps edges (pointCoordinateWord (fig14EncodedEquiv Secp256k1.generatorX Secp256k1.generatorY (fig14PointEncoding P)))
    let expected := pointCoordinateWord (fig14PointEncoding (P+C))
    unless actual == expected do
      throw (IO.userError "generator correction replay failed")
  unless (pointAddProgram (0 : Secp256k1.Point)).tCount == 0 do
    throw (IO.userError "infinity addition is not empty")
  IO.println s!"generator: {(fig14ExceptionalList C).length} exceptions, {pairs.length} swaps, {edges.length} adjacent edges; six group cases passed"
  for i in [0,edges.length/2,edges.length-1] do
    let (a,b) := edges[i]!
    let circuit := pointWordEdge a b
    IO.println s!"edge {i}: bit {firstDifferentBit a b}, gates {circuit.length}, T {tCount circuit}, wires {qubitCount circuit}"
"""

if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="point-correction-") as directory:
        source = Path(directory) / "Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake", "env", "lean", "--run", str(source)], cwd=ROOT, check=True)
