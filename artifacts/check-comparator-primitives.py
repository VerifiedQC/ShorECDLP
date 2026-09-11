#!/usr/bin/env python3
"""Check actual comparator gate trees and fixed-control resource transfers."""
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.ComparatorPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
deriving instance BEq for AdaptiveCircuit

def main : IO Unit := do
  let mut checked := 0
  for n in [1:7] do
    for threshold in [0:2^n+2] do
      let input := List.range' 5 n
      let dirty := List.range' (5+n) n
      let ge := controlledGidneyCompareGE input dirty threshold 0 1 2 3 4
      let lt := controlledGidneyCompareLT input dirty threshold 0 1 2 3 4
      let v := primitiveResources ge
      let l := primitiveResources lt
      unless v.x ≤ 2*n && v.h ≤ 4*n && v.cnot ≤ 15*n-1 && v.toffoli ≤ 3*n-1 &&
          v.phase == 0 && v.measurements ≤ n do
        throw (IO.userError s!"GE budget failed at {n}/{threshold}")
      unless l.x ≤ 2*n && l.h ≤ 4*n && l.cnot ≤ 15*n && l.toffoli ≤ 3*n-1 &&
          l.phase == 0 && l.measurements ≤ n do
        throw (IO.userError s!"LT budget failed at {n}/{threshold}")
      let lowered := constantControlProgram 0 ge
      unless lowered == gidneyCompareGE input dirty threshold 1 2 3 4 do
        throw (IO.userError "uncontrolled GE constructor differs from explicit lowering")
      let u := primitiveResources lowered
      unless u.x ≤ v.x+v.cnot && u.h == v.h && u.cnot ≤ v.cnot &&
          u.toffoli == v.toffoli && u.phase == v.phase && u.measurements == v.measurements do
        throw (IO.userError "comparator lowering resource transfer failed")
      let ul := primitiveResources (gidneyCompareLT input dirty threshold 1 2 3 4)
      unless ul.x ≤ 17*n && ul.h ≤ 4*n && ul.cnot ≤ 15*n-1 && ul.toffoli ≤ 3*n-1 &&
          ul.phase == 0 && ul.measurements ≤ n do
        throw (IO.userError "uncontrolled LT budget failed")
      unless constantControlProgram 0 lt == gidneyCompareLT input dirty threshold 1 2 3 4 do
        throw (IO.userError "uncontrolled LT differs from lowered controlled LT")
      checked := checked+1
  IO.println s!"{checked} threshold cases: GE, LT and uncontrolled primitive budgets passed"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="comparator-primitives-") as directory:
        source = Path(directory) / "Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake", "env", "lean", "--run", str(source)], cwd=ROOT, check=True)
