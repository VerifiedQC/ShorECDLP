#!/usr/bin/env python3
"""Build a sealed combined root from trusted dependencies and stopped worker outputs."""
from pathlib import Path
import shutil
import stat

PREFIX = Path('ShorECDLP/Submission/Entrant')


def regular_path(root, path, directory=False):
    for parent in [path, *path.parents]:
        if parent == root.parent:
            break
        mode = parent.lstat().st_mode
        if stat.S_ISLNK(mode):
            raise ValueError(f'symlink in artifact path: {parent}')
    mode = path.stat().st_mode
    if not (stat.S_ISDIR(mode) if directory else stat.S_ISREG(mode)):
        raise ValueError(f'non-regular artifact path: {path}')


def stage(candidate, overlay, trusted_lib):
    candidate = candidate.resolve(strict=True)
    overlay = overlay.resolve(strict=True)
    if overlay == candidate or candidate in overlay.parents or any(overlay.iterdir()):
        raise ValueError('overlay must be an empty runner-owned directory outside candidate')
    trusted_lib = trusted_lib.resolve(strict=True)
    # Lean resolves a package prefix to one root. Populate that root from trusted
    # artifacts first, then replace ONLY the entrant subtree with worker output.
    if trusted_lib == candidate or candidate in trusted_lib.parents:
        raise ValueError('trusted artifacts must be outside the candidate')
    shutil.copytree(trusted_lib, overlay, dirs_exist_ok=True)
    if (overlay / PREFIX).exists():
        shutil.rmtree(overlay / PREFIX)
    source = candidate / PREFIX
    regular_path(candidate, source, directory=True)
    modules = sorted(source.rglob('*.lean'))
    if source / 'Main.lean' not in modules:
        raise ValueError('missing Entrant/Main.lean')
    count = 0
    for path in modules:
        regular_path(candidate, path)
        relative = path.relative_to(candidate).with_suffix('')
        base = candidate / '.lake/build/lib/lean' / relative
        for suffix in ('.olean', '.olean.private', '.olean.server'):
            artifact = Path(str(base) + suffix)
            if not artifact.exists() and not artifact.is_symlink():
                if suffix == '.olean':
                    raise ValueError(f'missing compiled entrant: {relative}')
                continue
            regular_path(candidate, artifact)
            target = overlay / (str(relative) + suffix)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(artifact, target, follow_symlinks=False)
            target.chmod(0o444)
            count += 1
    return count


