#!/usr/bin/env python3
"""Load explicit per-module disclosures and check Lean's exact output coverage."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
NAME = re.compile(r"ShorECDLP\.[^\s]+")
RESULT = re.compile(r"^'(.+)' (?:depends on axioms:|does not depend on any axioms)", re.M)


def declarations(root=ROOT):
    directory = root / "scripts" / "axioms"
    files = sorted(directory.glob("*.txt"))
    if not files:
        raise ValueError("no axiom manifests")
    names, seen = [], set()
    for path in files:
        module = path.stem
        if not NAME.fullmatch(module) or not (root / (module.replace('«', '').replace('»', '').replace('.', '/') + '.lean')).is_file():
            raise ValueError(f"manifest has no source module: {path.name}")
        entries = [line.strip() for line in path.read_text().splitlines()
                   if line.strip() and not line.lstrip().startswith('#')]
        if not entries:
            raise ValueError(f"empty manifest: {path.name}")
        for name in entries:
            if not NAME.fullmatch(name):
                raise ValueError(f"invalid declaration in {path.name}: {name}")
            if name in seen:
                raise ValueError(f"duplicate axiom disclosure: {name}")
            seen.add(name)
            names.append(name)
    return names


def check_output(names, output):
    actual = RESULT.findall(output)
    if len(actual) != len(names) or len(set(actual)) != len(actual) or set(actual) != set(names):
        missing = sorted(set(names) - set(actual))
        extra = sorted(set(actual) - set(names))
        raise ValueError(f"axiom output mismatch: expected {len(names)}, got {len(actual)}; "
                         f"missing={missing}; extra={extra}; duplicates={len(actual)-len(set(actual))}")
    return len(names)


def main():
    try:
        names = declarations()
        if sys.argv[1:] == ["commands"]:
            print("import ShorECDLP")
            for name in names:
                print(f"#print axioms {name}")
        elif sys.argv[1:] == ["check-output"]:
            count = check_output(names, sys.stdin.read())
            print(f"axiom manifests: exactly {count} disclosures checked")
        else:
            raise ValueError("usage: axiom-manifests.py commands|check-output")
    except (ValueError, OSError) as error:
        raise SystemExit(str(error))


if __name__ == "__main__":
    main()
