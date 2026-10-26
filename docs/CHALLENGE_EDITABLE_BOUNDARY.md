# Protected source boundary

The evaluator runs `scripts/challenge/check-editable.py` from its protected
installation. It compares a frozen candidate source snapshot with a fixed Git
**tree object** in a separate, evaluator-owned repository. Only files below
`ShorECDLP/Submission/Entrant/` may differ. The entrant cannot choose the pin,
the checker, its arguments, or the subsequent build commands.

Example (the runner supplies both absolute paths and the full tree hash):

```sh
python3 /trusted/scripts/challenge/check-editable.py \
  --repo /worker/source \
  --trusted-repo /trusted/repository \
  --trusted-tree "$TRUSTED_TREE" \
  --allow ShorECDLP/Submission/Entrant
```

There is deliberately no default trusted repository or tree. `HEAD`, branch
names, abbreviated hashes and commit hashes are not accepted as tree pins.
Missing arguments fail closed. Exit status 0 accepts, 1 rejects a source
boundary violation, and 2 reports invalid configuration or unreadable input.

The checker enumerates the actual filesystem, including ignored and untracked
files. It checks protected file contents and Git's executable-bit distinction
against tree blobs. It does not use candidate indexes, status caches, Git
filters or configuration. Added, missing and renamed protected files are
rejected. An empty unexpected directory outside the editable subtree is also
rejected. Symlinks, special files, special file mode bits, control characters
in paths and nested `.git` entries are rejected, including within the editable
subtree. Trusted trees with symlinks or submodules are unsupported and rejected.
Ordinary read/write permission bits are not part of Git's tree format and are
not compared.

The exact root `.git` administration entry is excluded. The runner must own
that metadata or omit it altogether; it must not execute contestant-supplied
Git hooks or configuration. The trusted repository must be outside the
candidate snapshot. Git environment overrides are removed when reading it.

Run this check on a clean source snapshot **before** restoring trusted build
dependencies and caches. In particular, a contestant-provided `.lake` directory
is not exempt. After acceptance, the runner must prevent concurrent changes,
restore only trusted dependencies, and build in an isolated worker without
credentials. This checker neither freezes files itself nor provides process
isolation. A mutable snapshot or an editable evaluator invalidates the boundary.

Run regression tests with:

```sh
python3 scripts/challenge/test-editable.py
```

The tests exercise editable changes, protected mutations and deletion,
executable-bit changes, ignored and untracked additions, injected build caches,
prefix confusion, symlinks, special files, nested Git metadata, invalid pins,
Git index hiding flags and poisoned Git environment variables. These checks
establish the source-edit boundary; they do not establish an Eigen-hosted
service's sandbox or deployment configuration.
