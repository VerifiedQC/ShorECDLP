#!/usr/bin/env python3
"""Exhaustively replay the exported signed-address CNOT network at width 16."""
from pathlib import Path
import json
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
LEAN = r'''
import ShorECDLP.Submission.«2607_13816».Window.SignedAddress
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def gateRow : Gate → List Nat
 | .CX a b => [a,b]
 | _ => []
def main : IO Unit := do
 for n in [0,1,2,3,4,15] do
  IO.println s!"{n}:{(Lean.toJson ((signedAddressCircuit 0 1 (List.range' 2 n)).map gateRow)).compress}"
'''
def replay(gates, state):
    for c,t in gates:
        state ^= ((state >> c) & 1) << t
    return state

def main():
    with tempfile.TemporaryDirectory(prefix='signed-address-') as directory:
        source=Path(directory)/'Check.lean'
        source.write_text(LEAN)
        out=subprocess.run(['lake','env','lean','--run',str(source)],cwd=ROOT,
                           check=True,text=True,capture_output=True).stdout
    checked=0
    for line in out.splitlines():
        width,raw=line.split(':',1)
        n=int(width); gates=json.loads(raw); half=1<<n; mask=half-1
        assert len(gates)==2*n
        assert all(len(g)==2 and g[0] in (0,1) and 2<=g[1]<n+2 for g in gates)
        for low in range(half):
            for q in range(2):
                for sign in range(2):
                    for spectator in range(2):
                        state=q | sign<<1 | low<<2 | spectator<<20
                        expected=state ^ ((mask<<2) if q^sign else 0)
                        actual=replay(gates,state)
                        assert actual==expected,(n,low,q,sign,spectator)
                        assert replay(gates,actual)==state
                        if q:
                            value=low+half*sign
                            address=(actual>>2)&mask
                            assert address==(half-1-value if value<half else value-half)
                            odd=(2*address+1)*(1 if sign else -1)
                            assert odd==2*value-2*half+1
                            # A concrete odd-order additive group; 2*halfpoint=1.
                            order=65537; halfpoint=(order+1)//2
                            assert (odd*halfpoint-halfpoint)%order==(value-half)%order
                        checked+=1
    print(f'{checked} actual Lean gate-stream cases passed complete frame, involution, signed endpoints and half-point identity')
if __name__=='__main__':
    main()
