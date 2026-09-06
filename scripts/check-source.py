#!/usr/bin/env python3
"""Enforce the sanctioned Lean source tree and compiler-derived aggregator closure."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import os
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(os.environ.get("SHORECDLP_ROOT", Path(__file__).resolve().parents[1])).resolve()
ENTRY = ROOT / "ShorECDLP.lean"
SOURCE_ROOT = ROOT / "ShorECDLP"
MATH_ROOT = SOURCE_ROOT / "Math"
FRAMEWORK_ROOT = SOURCE_ROOT / "Framework"
NAIVE_ROOT = SOURCE_ROOT / "Submission" / "Naive"
PAPER_ROOT = SOURCE_ROOT / "Submission" / "2607_13816"

LAYER_ROOTS = {
    "Math": MATH_ROOT,
    "Framework": FRAMEWORK_ROOT,
    "Naive": NAIVE_ROOT,
    "2607_13816": PAPER_ROOT,
}

ALLOWED_PROJECT_IMPORTS = {
    "Math": {"Math"},
    "Framework": {"Math", "Framework"},
    "Naive": {"Math", "Framework", "Naive"},
    "2607_13816": {"Math", "Framework", "2607_13816"},
    "Root": {"Math", "Framework", "Naive", "2607_13816"},
}

TEXTUAL_LAYER_PREFIXES = {
    "ShorECDLP.Math": "Math",
    "ShorECDLP.Framework": "Framework",
    "ShorECDLP.Submission.Naive": "Naive",
    "ShorECDLP.Submission.«2607_13816»": "2607_13816",
}

IMPORT_RE = re.compile(r"^\s*import\s+(.+?)(?:\s+--.*)?$")


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


def source_tree_symlinks() -> list[Path]:
    """Find file and directory symlinks without following directory symlinks."""
    symlinks = [
        path
        for path in (ENTRY, ROOT / "lakefile.lean", SOURCE_ROOT)
        if path.is_symlink()
    ]
    if not SOURCE_ROOT.is_symlink() and SOURCE_ROOT.is_dir():
        for directory, dirnames, filenames in os.walk(SOURCE_ROOT, followlinks=False):
            for name in [*dirnames, *filenames]:
                path = Path(directory) / name
                if path.is_symlink():
                    symlinks.append(path)
    return sorted(set(symlinks))


def lean_prefix() -> Path:
    """Return the resolved root of the active, workflow-pinned Lean toolchain."""
    result = subprocess.run(
        ["lake", "env", "lean", "--print-prefix"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return Path(result.stdout.strip()).resolve()


def is_within(path: Path, directory: Path) -> bool:
    try:
        path.relative_to(directory)
        return True
    except ValueError:
        return False


def source_layer(path: Path) -> str:
    """Classify an in-repository Lean source into the approved architecture."""
    resolved = path.resolve()
    if resolved == ENTRY.resolve():
        return "Root"
    for layer, directory in LAYER_ROOTS.items():
        if is_within(resolved, directory.resolve()):
            return layer
    raise ValueError(
        "Lean source is outside the approved Math/Framework/submission layers: "
        f"{path.relative_to(ROOT)}"
    )


def textual_module_layer(module: str) -> str | None:
    """Classify a textual project import; return None for external modules."""
    if module == "ShorECDLP":
        return "Root"
    for prefix, layer in TEXTUAL_LAYER_PREFIXES.items():
        if module == prefix or module.startswith(prefix + "."):
            return layer
    if module.startswith("ShorECDLP."):
        raise ValueError(f"project import is outside the approved layers: {module}")
    return None


def textual_project_imports(source: Path) -> list[tuple[str, str]]:
    imports: list[tuple[str, str]] = []
    for line in source.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match is None:
            continue
        for module in match.group(1).split():
            layer = textual_module_layer(module)
            if layer is not None:
                imports.append((module, layer))
    return imports


def check_textual_layering(files: list[Path]) -> None:
    """Reject forbidden project imports using the source text itself."""
    violations: list[str] = []
    root_import_layers: set[str] = set()
    for source in files:
        layer = source_layer(source)
        for module, imported_layer in textual_project_imports(source):
            if layer == "Root":
                root_import_layers.add(imported_layer)
            if imported_layer not in ALLOWED_PROJECT_IMPORTS[layer]:
                violations.append(
                    f"{source.relative_to(ROOT)} ({layer}) -> {module} ({imported_layer})"
                )
    if violations:
        raise ValueError("forbidden textual import edge(s): " + ", ".join(violations))
    missing = {"Naive", "2607_13816"} - root_import_layers
    if missing:
        raise ValueError(
            "ShorECDLP.lean must directly import both submission aggregators; missing layer(s): "
            + ", ".join(sorted(missing))
        )


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


def compiler_source_closure(files: list[Path], toolchain_root: Path) -> set[Path]:
    """Follow compiler-parsed import edges from the root aggregator."""
    with ThreadPoolExecutor(max_workers=min(8, len(files))) as executor:
        dependency_map = dict(zip(files, executor.map(direct_source_dependencies, files)))

    sanctioned = {path.resolve() for path in files}
    layering_violations: list[tuple[Path, str, Path, str]] = []
    root_dependency_layers: set[str] = set()
    for source, dependencies in dependency_map.items():
        layer = source_layer(source)
        for dependency in dependencies:
            if dependency not in sanctioned:
                continue
            imported_layer = source_layer(dependency)
            if layer == "Root":
                root_dependency_layers.add(imported_layer)
            if imported_layer not in ALLOWED_PROJECT_IMPORTS[layer]:
                layering_violations.append(
                    (source.resolve(), layer, dependency, imported_layer)
                )
    if layering_violations:
        edges = ", ".join(
            f"{source.relative_to(ROOT)} ({layer}) -> "
            f"{dependency.relative_to(ROOT)} ({imported_layer})"
            for source, layer, dependency, imported_layer in sorted(layering_violations)
        )
        raise ValueError(f"forbidden compiler-resolved import edge(s): {edges}")
    missing = {"Naive", "2607_13816"} - root_dependency_layers
    if missing:
        raise ValueError(
            "compiler did not resolve both submission aggregators directly from ShorECDLP.lean; "
            "missing layer(s): " + ", ".join(sorted(missing))
        )

    dependency_path = ROOT / ".lake" / "packages"
    if dependency_path.is_symlink():
        raise ValueError(f"Lake package root must not be a symlink: {dependency_path}")
    if not dependency_path.is_dir():
        raise ValueError(f"Lake package root is missing: {dependency_path}")
    dependency_root = dependency_path.resolve()
    unexpected: set[Path] = set()
    for dependencies in dependency_map.values():
        for dependency in dependencies:
            if dependency in sanctioned:
                continue
            if is_within(dependency, dependency_root) or is_within(dependency, toolchain_root):
                continue
            unexpected.add(dependency)
    if unexpected:
        names = ", ".join(str(path) for path in sorted(unexpected))
        raise ValueError(f"compiler resolved Lean source outside allowed roots: {names}")

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
    symlinked = source_tree_symlinks()
    if symlinked:
        print("source gate failed:", file=sys.stderr)
        print(
            "  Lean sources must be regular in-tree files, not symlinks: "
            + ", ".join(str(path.relative_to(ROOT)) for path in symlinked),
            file=sys.stderr,
        )
        return 1

    files = source_files()
    failures: list[str] = []

    try:
        for source in files:
            source_layer(source)
        check_textual_layering(files)
    except (OSError, ValueError) as error:
        failures.append(f"source layering check failed: {error}")

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
        toolchain_root = lean_prefix()
        reachable = compiler_source_closure(files, toolchain_root)
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

    print(
        f"source gate passed: {len(files)} Lean files; all aggregator-reachable; "
        "Math/Framework/Naive/2607_13816 import directions enforced"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
