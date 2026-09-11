#!/usr/bin/env python3
"""Replay actual small carry-comparator measurement trees for exact primitive vectors."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r'''
import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyCompare
open ShorECDLP ShorECDLP.Paper2607_13816
def main : IO Unit := do
  for offset in [0,100] do
    for n in List.range 7 do
      for k in List.range (2^n) do
        let input := List.range' (offset+10) n
        let dirty := List.range' (offset+20) n
        let bs := (List.range n).map (Nat.testBit k)
        let actual := controlledGidneyCompareCarry input dirty bs offset (offset+1) (offset+2) (offset+3) (offset+4)
        let v := primitiveResources actual
        IO.println s!"carry {n} {k} {v.x} {v.h} {v.cnot} {v.toffoli} {v.phase} {v.measurements}"
  for offset in [0,100] do
    for n in List.range 7 do
      for p in List.range (2^n+2) do
        let input := List.range' (offset+10) n
        let dirty := List.range' (offset+20) n
        let v := primitiveResources (controlledGidneyCompareGE input dirty p offset (offset+1) (offset+2) (offset+3) (offset+4))
        IO.println s!"ge {n} {p} {v.x} {v.h} {v.cnot} {v.toffoli} {v.phase} {v.measurements}"
'''
def main():
    with tempfile.TemporaryDirectory(prefix='gidney-add-exact-') as tmp:
        p=Path(tmp)/'Main.lean';p.write_text(LEAN_CHECK)
        result=subprocess.run(['lake','env','lean','--run',str(p)],cwd=ROOT,text=True,capture_output=True,check=True)
    checks=0
    for line in result.stdout.splitlines():
        mode,*numbers=line.split()
        n,k,x,h,cx,ccx,p,m=map(int,numbers)
        bits=k if mode=='carry' else (1<<n)-k
        first=bits&1
        weight=bin(bits>>1).count('1')
        expected=(2*n,4*n,6*n+1+7*first+9*weight,3*n-1,0,n) if n else (0,0,0,0,0,0)
        if mode=='ge':
            if k==0: expected=(0,0,1,0,0,0)
            elif k>=(1<<n): expected=(0,0,0,0,0,0)
        assert (x,h,cx,ccx,p,m)==expected,(n,k,(x,h,cx,ccx,p,m),expected)
        checks+=1
    assert checks==536,checks
    print('PASS: 536 complete actual carry/controlled-threshold comparator vectors, including all shortcut cases at widths 0–6')
if __name__=='__main__': main()
