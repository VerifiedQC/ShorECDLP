#!/usr/bin/env python3
"""Enforce the sanctioned Lean source tree and compiler-derived aggregator closure."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(os.environ.get("SHORECDLP_ROOT", Path(__file__).resolve().parents[1])).resolve()
ENTRY = ROOT / "ShorECDLP.lean"
SOURCE_ROOT = ROOT / "ShorECDLP"


def source_files() -> list[Path]:
    return [ENTRY, *sorted(SOURCE_ROOT.rglob("*.lean"))]


def tracked_lean_files() -> set[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    )
    return {
        ROOT / path.decode("utf-8")
        for path in result.stdout.split(b"\0")
        if path
    }


def direct_source_dependencies(source: Path) -> set[Path]:
    """Ask Lean itself to parse one module header and resolve its direct imports."""
    result = subprocess.run(
        ["lake", "env", "lean", "--src-deps", str(source.relative_to(ROOT))],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return {
        Path(line).resolve()
        for line in result.stdout.splitlines()
        if line.strip()
    }


def compiler_source_closure(files: list[Path]) -> set[Path]:
    """Follow compiler-parsed import edges from the root aggregator."""
    with ThreadPoolExecutor(max_workers=min(8, len(files))) as executor:
        dependency_map = dict(zip(files, executor.map(direct_source_dependencies, files)))

    sanctioned = set(files)
    unexpected_local: set[Path] = set()
    for dependencies in dependency_map.values():
        for dependency in dependencies:
            try:
                relative = dependency.relative_to(ROOT)
            except ValueError:
                continue
            if relative.parts and relative.parts[0] != ".lake" and dependency not in sanctioned:
                unexpected_local.add(dependency)
    if unexpected_local:
        names = ", ".join(str(path.relative_to(ROOT)) for path in sorted(unexpected_local))
        raise ValueError(f"compiler resolved local Lean source outside sanctioned tree: {names}")

    reachable: set[Path] = set()
    pending = [ENTRY]
    while pending:
        source = pending.pop()
        if source in reachable:
            continue
        reachable.add(source)
        for dependency in dependency_map[source]:
            if dependency == ENTRY or SOURCE_ROOT in dependency.parents:
                if dependency not in reachable:
                    pending.append(dependency)
    return reachable


def main() -> int:
    files = source_files()
    failures: list[str] = []

    symlinked = [path for path in files if path.is_symlink()]
    if symlinked:
        failures.append(
            "Lean sources must be regular in-tree files, not symlinks: "
            + ", ".join(str(path.relative_to(ROOT)) for path in symlinked)
        )

    try:
        tracked = tracked_lean_files()
    except (OSError, subprocess.CalledProcessError) as error:
        failures.append(f"could not enumerate tracked Lean sources: {error}")
    else:
        source_set = set(files)
        sanctioned = source_set | {ROOT / "lakefile.lean"}
        unexpected_tracked = sorted(tracked - sanctioned)
        if unexpected_tracked:
            failures.append(
                "tracked Lean files outside ShorECDLP tree: "
                + ", ".join(str(path.relative_to(ROOT)) for path in unexpected_tracked)
            )
        untracked_sources = sorted(source_set - tracked)
        if untracked_sources:
            failures.append(
                "untracked Lean sources in the build tree: "
                + ", ".join(str(path.relative_to(ROOT)) for path in untracked_sources)
            )

    try:
        reachable = compiler_source_closure(files)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        failures.append(f"could not obtain Lean source dependencies: {error}")
    else:
        orphaned = sorted(
            str(path.relative_to(ROOT)) for path in files if path.resolve() not in reachable
        )
        if orphaned:
            failures.append(
                "source files not reachable from ShorECDLP.lean: " + ", ".join(orphaned)
            )

    if failures:
        print("source gate failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(f"source gate passed: {len(files)} Lean files; all aggregator-reachable")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
