#!/usr/bin/env python3
"""Run the unchanged explicit axiom disclosures in two bounded Lean processes."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess
import sys


def main():
    lines = [line.strip() for line in sys.stdin if line.strip()]
    if not lines or lines[0] != 'import ShorECDLP':
        raise SystemExit('expected the ShorECDLP import before axiom disclosures')
    commands = lines[1:]
    if not commands or any(not re.fullmatch(r'#print axioms [^\s]+', line) for line in commands):
        raise SystemExit('expected only explicit #print axioms commands')
    # Every original command appears once, in one contiguous half. No cached
    # audit result is trusted, and each process imports the current full project.
    midpoint = (len(commands) + 1) // 2
    chunks = [commands[:midpoint], commands[midpoint:]]

    def run(chunk):
        return subprocess.run(
            ['lake', 'env', 'lean', '/dev/stdin'],
            input='import ShorECDLP\n' + '\n'.join(chunk) + '\n',
            cwd=Path(__file__).resolve().parents[1],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(run, (chunk for chunk in chunks if chunk)))
    for result in results:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
    if any(result.returncode != 0 for result in results):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
