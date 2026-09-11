#!/usr/bin/env python3
"""Check actual production shift and terminal-padding primitive vectors."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».EEA.ShiftPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def main : IO Unit := do
  let mut checked := 0
  for offset in [0,1000] do
    let shift : ShiftRegisters := ⟨offset,offset+1,List.range' (offset+2) 259,
      List.range' (offset+261) 9,offset+270,offset+271,List.range' (offset+272) 8,[]⟩
    let padding : TerminalPaddingRegisters := ⟨offset,offset+1,List.range' (offset+2) 259,
      List.range' (offset+261) 9,offset+270,List.range' (offset+271) 7,offset+278⟩
    let circuits := [(preShiftUnitary shift,(⟨68,0,1067,566,0,0⟩ : PrimitiveResources)),
      (postShiftUnitary shift,⟨64,0,1065,566,0,0⟩),
      (terminalPaddingForward padding,⟨36,0,527,305,0,0⟩),
      (terminalPaddingInverse padding,⟨68,0,527,305,0,0⟩)]
    for (c,v) in circuits do
      unless primitiveResources (.unitary c .done) == v do
        throw (IO.userError "production shift primitive mismatch")
      checked := checked+1
  IO.println s!"{checked} actual production-width shift and padding circuits passed"

"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="shift-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
