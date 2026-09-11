#!/usr/bin/env python3
"""Check complete production E blocks on singleton windows."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».EEA.BlockEPrimitiveCounts
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
      let tree := coefficientPrefixTree (r.coefficient w) k k
      let leaves := tree.leaves
      let nodes := tree.internalNodes
      let expected : PrimitiveResources := ⟨44+16*nodes,8*(leaves+nodes),
        280+16*leaves+12*nodes,160+10*leaves+4*nodes,0,4*(leaves+nodes)⟩
      let c := blockEAdaptive r 256 w
      unless pathVector true c == expected do throw (IO.userError "E all-one path mismatch")
      let lower : PrimitiveResources := ⟨expected.x,0,expected.cnot-expected.measurements,
        expected.toffoli,0,expected.measurements⟩
      unless pathVector false c == lower do throw (IO.userError "E all-zero path mismatch")
      checked := checked+1
  IO.println s!"{checked} actual singleton E blocks passed both extremal measurement paths"

"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="block-e-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
