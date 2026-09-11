#!/usr/bin/env python3
"""Check primitive budgets of the emitted modular constant circuits."""
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def within (v : PrimitiveResources) (x h cx ccx m : Nat) : Bool :=
  v.x≤x && v.h≤h && v.cnot≤cx && v.toffoli≤ccx && v.phase==0 && v.measurements≤m

def main : IO Unit := do
  let mut checked := 0
  for n in [2:4] do
    let target := List.range' 5 n
    let dirty := List.range' (5+n) n
    for p in [3:2^n] do
      if p%2 == 1 then
        let bits := fun k => (List.range n).map (Nat.testBit k)
        for k in [0:p] do
          let a := controlledConstantModularAdd target dirty (bits k) (bits (2^n-p)) p 0 1 2 3 4
          let u := uncontrolledConstantModularAdd target dirty (bits k) (bits (2^n-p)) p 1 2 3 4
          unless within (primitiveResources a) (29*n-5) (20*n-8) (75*n-31) (15*n-11) (5*n-2) do
            throw (IO.userError s!"controlled modular budget failed {n}/{p}/{k}")
          unless within (primitiveResources u) (74*n-20) (20*n-8) (75*n-33) (15*n-11) (5*n-2) do
            throw (IO.userError s!"uncontrolled modular budget failed {n}/{p}/{k}")
          unless a.tCount == 7*(primitiveResources a).toffoli && u.tCount == 7*(primitiveResources u).toffoli do
            throw (IO.userError "zero-phase modular T conversion failed")
          checked := checked+2
        let neg := controlledModularNegate target dirty (bits p) 0 1 2 3 4
        unless within (primitiveResources neg) (12*n-4) (16*n-8) (61*n-32) (12*n-10) (4*n-2) do
          throw (IO.userError s!"negation budget failed {n}/{p}")
        checked := checked+1
  IO.println s!"{checked} actual modular constant circuits passed all primitive budgets"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="constant-primitives-") as directory:
        source = Path(directory) / "Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake", "env", "lean", "--run", str(source)], cwd=ROOT, check=True)
