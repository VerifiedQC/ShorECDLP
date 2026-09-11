#!/usr/bin/env python3
"""Check actual production EEA end-of-iteration block."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def gateVector : Gate → PrimitiveResources
  | .X _ => ⟨1,0,0,0,0,0⟩
  | .H _ => ⟨0,1,0,0,0,0⟩
  | .CX _ _ => ⟨0,0,1,0,0,0⟩
  | .CCX _ _ _ => ⟨0,0,0,1,0,0⟩
  | .P _ _ _ => ⟨0,0,0,0,1,0⟩
def main : IO Unit := do
  let mut checked := 0
  for offset in [0,1000] do
    let r : IndexedStepRegisters := ⟨offset,offset+1,offset+2,offset+3,
      List.range' (offset+4) 259,List.range' (offset+263) 259,
      List.range' (offset+522) 9,List.range' (offset+531) 9,
      List.range' (offset+540) 9,List.range' (offset+549) 9,List.range' (offset+558) 22⟩
    for t in [0,1,4,64,512,1024,1616,1619] do
      let windows := endIterationWindowsAt 256 t
      let v : PrimitiveResources := if t%4=0 then
        ⟨4+endIterationXFormula 9 256 windows,0,1+endIterationCnotFormula 259 9 256 windows,
          66+endIterationToffoliFormula 259 9 256 windows,0,0⟩ else ⟨0,0,0,0,0,0⟩
      unless ((blockHForward r 256 t).foldl (fun (v : PrimitiveResources) g => v.add (gateVector g)) ⟨0,0,0,0,0,0⟩) == v do
        throw (IO.userError s!"indexed end-of-iteration primitive mismatch at {t}")
      checked := checked+1
  IO.println s!"{checked} actual production H blocks passed"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="block-h-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
