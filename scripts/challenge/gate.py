#!/usr/bin/env python3
"""Protected local checks. Run only inside the organizer's isolated build worker."""
from __future__ import annotations
from pathlib import Path
import os
import re
import subprocess
import sys

ROOT = Path(os.environ.get("SHORECDLP_ROOT", Path(__file__).resolve().parents[2])).resolve()

def reject_disabled_kernel(source: str) -> None:
    # Conservative explicit policy, including comments and escaped identifiers.
    # This is NOT a parser or a defense against arbitrary elaborator metaprograms.
    # Independent replay remains mandatory even when this check succeeds.
    if "skipKernelTC" in source:
        raise ValueError("debug.skipKernelTC is forbidden in submitted/project source")

def environment():
    env = os.environ.copy()
    env["LEAN_PATH"] = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    lean = Path(subprocess.check_output(
        ["lake", "env", "which", "lean"], cwd=ROOT, text=True).strip())
    return lean, env

def replay(module: str, *, extra_path: Path | None = None,
           timeout: int = 600) -> subprocess.CompletedProcess:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", module):
        raise ValueError("invalid replay module")
    lean, env = environment()
    if extra_path is not None:
        env["LEAN_PATH"] = str(extra_path) + os.pathsep + env["LEAN_PATH"]
    # A separate process replays stored declarations with Lean's kernel.
    # It does not evaluate the submitted source's commands/options.
    return subprocess.run([str(lean.with_name("leanchecker")), "--verbose", module],
                          cwd=ROOT, env=env, text=True, capture_output=True,
                          timeout=timeout)

def check_project_sources() -> int:
    paths = [ROOT / "ShorECDLP.lean", *sorted((ROOT / "ShorECDLP").rglob("*.lean"))]
    for path in paths:
        reject_disabled_kernel(path.read_text())
    return len(paths)

def main() -> int:
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--source-only", action="store_true")
    group.add_argument("--replay",
                        help="Organizer-selected module prefix; all matching oleans are replayed")
    parser.add_argument("--root", type=Path, help="evaluator-selected candidate root")
    parser.add_argument("--artifact-path", type=Path, help="evaluator-sealed Entrant-only overlay")
    args = parser.parse_args()
    global ROOT
    if args.root is not None:
        ROOT = args.root.resolve()
    count = check_project_sources()
    if args.source_only:
        print(f"explicit kernel-disable policy passed ({count} sources)")
        return 0
    result = replay(args.replay, extra_path=args.artifact_path)
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    if result.returncode:
        return result.returncode
    modules = [line[len("replaying "):] for line in result.stdout.splitlines()
               if line.startswith("replaying ")]
    if not modules:
        raise ValueError("leanchecker reported no replayed modules")
    print(f"explicit kernel-disable policy passed ({count} sources); "
          f"replay passed: {len(modules)} modules under {args.replay}")
    return 0

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, subprocess.TimeoutExpired) as exc:
        print(f"challenge gate rejected: {exc}", file=sys.stderr)
        raise SystemExit(1)
