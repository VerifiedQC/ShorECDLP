#!/usr/bin/env python3
"""Check a frozen source snapshot against an evaluator-owned Git tree.

Run this protected script before installing build caches. Neither candidate Git
metadata nor filters are consulted. This is not a process sandbox; see
 docs/CHALLENGE_EDITABLE_BOUNDARY.md for the runner contract.
"""
import argparse
import hashlib
import os
from pathlib import Path
import re
import stat
import subprocess
import sys

ALLOWED = 'ShorECDLP/Submission/Entrant'


def git(repo, *args):
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
               GIT_CONFIG_SYSTEM=os.devnull, GIT_NO_REPLACE_OBJECTS='1',
               GIT_TERMINAL_PROMPT='0', GIT_OPTIONAL_LOCKS='0')
    return subprocess.check_output(
        ['git', '--no-replace-objects', '-c', 'core.fsmonitor=false',
         '-C', str(repo), *args], env=env, stderr=subprocess.PIPE)


def canonical(path):
    return (bool(path) and not path.startswith('/') and
            all(p not in ('', '.', '..', '.git') for p in path.split('/')) and
            not any(ord(c) < 32 or ord(c) == 127 for c in path))


def editable(path):
    return path.startswith(ALLOWED + '/')


def check(args):
    root = Path(args.repo).resolve(strict=True)
    trusted = Path(args.trusted_repo).resolve(strict=True)
    if not root.is_dir() or not trusted.is_dir():
        raise ValueError('source and trusted repository must be directories')
    if trusted == root or root in trusted.parents:
        raise ValueError('trusted repository must be outside the candidate snapshot')
    if args.allow.rstrip('/') != ALLOWED:
        raise ValueError('only ' + ALLOWED + ' may be editable')
    tree = args.trusted_tree
    if not re.fullmatch(r'(?:[0-9a-f]{40}|[0-9a-f]{64})', tree):
        raise ValueError('trusted tree must be a full lowercase object hash')
    if git(trusted, 'cat-file', '-t', tree).strip() != b'tree':
        raise ValueError('trusted pin must identify a tree, not a commit or ref')
    expected = {}
    directories = set()
    for row in git(trusted, 'ls-tree', '-r', '-z', '--full-tree', tree).split(b'\0'):
        if not row:
            continue
        metadata, rawpath = row.split(b'\t', 1)
        mode, kind, oid = metadata.decode('ascii').split()
        path = os.fsdecode(rawpath)
        if not canonical(path) or kind != 'blob' or mode not in ('100644', '100755'):
            raise ValueError('unsupported trusted entry: ' + repr(path))
        expected[path] = (mode, oid)
        parts = path.split('/')
        directories.update('/'.join(parts[:i]) for i in range(1, len(parts)))
    parts = ALLOWED.split('/')
    directories.update('/'.join(parts[:i]) for i in range(1, len(parts) + 1))
    seen = set()
    errors = []

    def walk(folder, prefix=''):
        for entry in sorted(os.scandir(folder), key=lambda e: e.name):
            path = prefix + entry.name
            info = entry.stat(follow_symlinks=False)
            # Only runner-owned root Git administration is excluded. Never read it.
            if path == '.git':
                if not (stat.S_ISDIR(info.st_mode) or stat.S_ISREG(info.st_mode)):
                    errors.append('invalid Git administration: ' + repr(path))
                continue
            if not canonical(path):
                errors.append('invalid path: ' + repr(path))
                continue
            if stat.S_ISDIR(info.st_mode):
                if path not in directories and not editable(path):
                    errors.append('unexpected directory: ' + repr(path))
                walk(entry.path, path + '/')
                continue
            if not stat.S_ISREG(info.st_mode) or info.st_mode & 0o7000:
                errors.append('non-regular or special-mode file: ' + repr(path))
                continue
            if path == ALLOWED:
                errors.append('editable root must be a directory')
                continue
            if editable(path):
                continue
            seen.add(path)
            if path not in expected:
                errors.append('unexpected file: ' + repr(path))
                continue
            mode, oid = expected[path]
            if bool(info.st_mode & 0o111) != (mode == '100755'):
                errors.append('executable mode changed: ' + repr(path))
            digest = hashlib.new('sha1' if len(oid) == 40 else 'sha256')
            digest.update(b'blob ' + str(info.st_size).encode() + b'\0')
            fd = os.open(entry.path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
            with os.fdopen(fd, 'rb') as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b''):
                    digest.update(block)
            if digest.hexdigest() != oid:
                errors.append('content changed: ' + repr(path))
    walk(root)
    errors.extend('missing file: ' + repr(p) for p in sorted(expected)
                  if not editable(p) and p not in seen)
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', default='.', help='frozen candidate source directory')
    parser.add_argument('--trusted-repo', required=True, help='evaluator-owned Git object store')
    parser.add_argument('--trusted-tree', required=True, help='fixed evaluator-owned tree hash')
    parser.add_argument('--allow', default=ALLOWED)
    args = parser.parse_args()
    try:
        errors = check(args)
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print('ERROR: invalid boundary check configuration or unreadable input: ' + str(exc), file=sys.stderr)
        return 2
    if errors:
        print('REJECT: source differs outside editable boundary', file=sys.stderr)
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print('ACCEPT: protected source matches trusted tree')
    return 0


if __name__ == '__main__':
    sys.exit(main())
