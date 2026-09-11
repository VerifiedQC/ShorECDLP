#!/usr/bin/env python3
"""Check primitive budgets of the emitted variable modular circuits."""
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.LoopPrimitiveCounts

open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def main : IO Unit := do
  let mut checked := 0
  for n in [2:4] do
    let input := List.range' 6 n
    let acc := List.range' (6+n) n
    let bits := fun k => (List.range n).map (Nat.testBit k)
    let p := 2^n-1
    for m in [0:3] do
      let controls := List.range' (6+2*n) m
      for circuit in [hornerMul controls input acc (bits 1) p 1 2 3 4,
          hornerMulInverse controls input acc (bits p) p 1 2 3 4,
          squareLoop controls input acc (bits 1) p 0 1 2 3 4,
          squareLoopInverse controls input acc (bits p) p 0 1 2 3 4] do
        let v := primitiveResources circuit
        unless v.x≤(23*n+1)*m+(21*n-3)*(m-1) &&
            v.h≤(8*n-4)*m+(8*n-4)*(m-1) &&
            v.cnot≤(38*n-14)*m+(33*n-16)*(m-1) &&
            v.toffoli≤(11*n-3)*m+(6*n-5)*(m-1) &&
            v.phase==0 && v.measurements≤(2*n-1)*m+(2*n-1)*(m-1) do
          throw (IO.userError s!"loop primitive bound failed {n}/{m}: {repr v}")
        checked := checked+1
  IO.println s!"{checked} actual forward/inverse Horner and square loops passed primitive bounds"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="loop-primitives-") as directory:
        source = Path(directory) / "Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake", "env", "lean", "--run", str(source)], cwd=ROOT, check=True)
