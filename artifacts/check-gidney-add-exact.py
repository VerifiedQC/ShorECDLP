#!/usr/bin/env python3
"""Replay actual small constant-adder measurement trees for exact X/H counts."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r'''
import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyAdd
open ShorECDLP ShorECDLP.Paper2607_13816
def main : IO Unit := do
  for offset in [0,100] do
    for n in List.range 7 do
      for k in List.range (2^n) do
        let input := List.range' (offset+10) n
        let dirty := List.range' (offset+20) (n-1)
        let bs := (List.range n).map (Nat.testBit k)
        let v := primitiveResources (controlledGidneyAddConst input dirty bs offset (offset+1) (offset+2) (offset+3))
        IO.println s!"{n} {k} {v.x} {v.h} {v.phase} {v.measurements}"
'''
def main():
    with tempfile.TemporaryDirectory(prefix='gidney-add-exact-') as tmp:
        p=Path(tmp)/'Main.lean';p.write_text(LEAN_CHECK)
        result=subprocess.run(['lake','env','lean','--run',str(p)],cwd=ROOT,text=True,capture_output=True,check=True)
    checks=0
    for line in result.stdout.splitlines():
        n,k,x,h,p,m=map(int,line.split())
        expected=(4*n-2,4*(n-1),0,n-1) if n>=2 and k else (0,0,0,0)
        assert (x,h,p,m)==expected,(n,k,(x,h,p,m),expected)
        checks+=1
    assert checks==254,checks
    print('PASS: 254 actual constant-adder trees, including zero patterns and widths 0–6')
if __name__=='__main__': main()
