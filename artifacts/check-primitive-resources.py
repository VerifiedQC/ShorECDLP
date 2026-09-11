#!/usr/bin/env python3
"""Run the primitive resource check with the repository's pinned Lean."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyAdd
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def main : IO Unit := do
  let mut checked := 0
  for n in [2:7] do
    for k in [0:2^n] do
      let bits := (List.range n).map (fun i => k.testBit i)
      let program := controlledGidneyAddConst (List.range' 4 n) (List.range' (4+n) (n-1)) bits 0 1 2 3
      let v := primitiveResources program
      unless v.phase == 0 && v.x ≤ 4*n-2 && v.h ≤ 4*(n-1) do
        throw (IO.userError s!"primitive bound failed at width {n}, constant {k}: {repr v}")
      unless v.toffoli == (if k == 0 then 0 else 3*n-4) && program.tCount == 7*v.toffoli do
        throw (IO.userError "Toffoli/T conversion failed")
      unless primitiveResources (program.seq program) == v.add v do
        throw (IO.userError "sequence resource composition failed")
      checked := checked+1
  -- Independent component maxima can occur on different branches.
  let left := AdaptiveCircuit.unitary [.CCX 0 1 2] .done
  let right := AdaptiveCircuit.unitary [.P .forward 1 0] .done
  let branch := AdaptiveCircuit.xMeasureReset 3 left right
  let v := primitiveResources branch
  unless branch.tCount == 7 && 7*v.toffoli+v.phase == 8 && v.measurements == 1 do
    throw (IO.userError "mixed-branch T conversion must be a strict upper bound")
  IO.println s!"{checked} actual constant-adder circuits and mixed-branch conversion passed"
"""

if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="primitive-resources-") as directory:
        source = Path(directory) / "Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake", "env", "lean", "--run", str(source)], cwd=ROOT, check=True)
