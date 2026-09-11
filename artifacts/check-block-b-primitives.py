#!/usr/bin/env python3
"""Check complete production B blocks on singleton windows."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».EEA.BlockBPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def gateVector : Gate → PrimitiveResources
  | .X _ => ⟨1,0,0,0,0,0⟩
  | .H _ => ⟨0,1,0,0,0,0⟩
  | .CX _ _ => ⟨0,0,1,0,0,0⟩
  | .CCX _ _ _ => ⟨0,0,0,1,0,0⟩
  | .P _ _ _ => ⟨0,0,0,0,1,0⟩
def pathVector (outcome : Bool) : AdaptiveCircuit → PrimitiveResources
  | .done => ⟨0,0,0,0,0,0⟩
  | .unitary g next => (g.foldl (fun (v : PrimitiveResources) gate => v.add (gateVector gate)) ⟨0,0,0,0,0,0⟩).add (pathVector outcome next)
  | .xMeasureReset _ l r => (⟨0,0,0,0,0,1⟩ : PrimitiveResources).add
      (if outcome then pathVector outcome r else pathVector outcome l)
def main : IO Unit := do
  let mut checked := 0
  for offset in [0,1000] do
    let r : IndexedStepRegisters := ⟨offset,offset+1,offset+2,offset+3,
      List.range' (offset+4) 259,List.range' (offset+263) 259,
      List.range' (offset+522) 9,List.range' (offset+531) 9,
      List.range' (offset+540) 9,List.range' (offset+549) 9,List.range' (offset+558) 22⟩
    for k in [4,128] do
      let w : ActiveWindow := ⟨k,k⟩
      let rr := r.remainder w
      let expected := (⟨28,0,1,198,0,0⟩ : PrimitiveResources).add
        ((intervalPrimitiveFormula9 rr 256 k k .sub true).add
          (intervalPrimitiveFormula9 rr 256 k k .add false))
      let c := blockBAdaptive r 256 w
      unless pathVector true c == expected do throw (IO.userError "B all-one path mismatch")
      let lower : PrimitiveResources := ⟨expected.x,0,expected.cnot-expected.measurements,
        expected.toffoli,0,expected.measurements⟩
      unless pathVector false c == lower do throw (IO.userError "B all-zero path mismatch")
      checked := checked+1
  IO.println s!"{checked} actual singleton B blocks passed both extremal measurement paths"

"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="block-b-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
