# Building and checking

Use the repository root as the working directory. Keep `lean-toolchain` and all
three `lake-manifest.json` files unchanged to reproduce the pinned configuration.

## Lean

Optionally obtain the precompiled Mathlib dependencies for the committed revision:

```sh
lake exe cache get
```

This is the Mathlib project's [documented cache command](https://leanprover-community.github.io/install/project.html).
Keep the lockfiles pinned; do not run `lake update` to reproduce this package.
Downloading this cache does not compile the local project or run its audits.
On Windows, use a short checkout path; if Git reports long-path errors, enable
Windows long-path support and Git's `core.longpaths` before retrying the checkout.

Build the application and run the configured audits:

```sh
lake build
python -B scripts/run_lean_audits.py
```

The first command builds `ManuscriptIBAW.lean` and its import closure. It does
not reproduce the historical compilation of all 1,999 project modules.
The second command first builds the direct imports of the four library audits
listed in `packages/ModularRep/audit-targets.json` and
`ManuscriptIBAW/MainAudit.lean`, including `ModularRep.AxiomGate`, then invokes
each audit with `--trust=0`. Lake builds their transitive dependencies as needed.
Any dependency-build or audit failure stops the script with an error.
A normal application build alone is not a claim that these audit commands ran.
The separate exhaustive application declaration audit described in the historical
compilation record cannot be regenerated using the distributed tools.

The launcher's `lake env lean` invocations supply `--trust=0 --threads=1`.
They do not automatically apply the packages' `leanOptions`, and do not replay
the historical `-M8192` memory limit or per-package `-D` settings, including
`-DrelaxedAutoImplicit=false`, recorded in
[verification/compilation.json](verification/compilation.json).
The dependency build uses Lake's pinned package configuration; the subsequent
audit invocations are not an exact reproduction of those historical commands.

## Documents

Install LuaLaTeX (with the packages used by `docs/manuals/preamble.tex`), Poppler
(`pdftoppm`), and the Python requirements in `scripts/documentation-requirements.txt`.
Then run:

```sh
python -m pip install -r scripts/documentation-requirements.txt
python -B scripts/build_manual_pdfs.py
```

The builder writes only `output/pdf/formalisation-report.pdf` and
`output/pdf/library-manual.pdf`. Intermediate files and rendered pages go under
ignored `tmp/pdfs`. Inspect changed pages after editing. Shared bibliography
definitions are in `docs/manuals/bibliography-entries.tex`; the two bibliography
selector files preserve each document's reference order.

After intentional source or PDF changes, refresh current documentary records
only after completing the stated checks. Do not relabel historical compiler or
resource records as a new compilation. The source checker deliberately rejects
documents whose recorded identities no longer match their sources.

The HTML module catalogue and manuscript correspondence tables are supplied
as recorded documentation. Their complete generation inputs are not included;
the retained catalogue script explains this limitation and does not regenerate
them from the public package.

## Source and release checks

```sh
python -B scripts/check_repository.py
python -B -m unittest discover -s scripts/tests
python -B -m unittest discover -s scripts -p test_current_package.py
python -B scripts/export_release.py --ref HEAD --output ../source-package.zip
```

The repository check tolerates Git and build directories. The exported package
has an exact manifest and a stricter check:

```sh
python -B scripts/verify_release.py /path/to/extracted/ModularRep
```

Do this pristine-package check before running `lake build` inside the export.
Its result verifies consistency with the recorded source inventory; it does not establish the
external mathematical assumptions. Checksums can be compared with a trusted
release record; an internally consistent manifest alone is not a signature.

The regular GitHub workflow runs portable source checks and verifies an export
of its checked-out commit. The separate application-build-and-audits workflow
runs only in a private repository and uses a dedicated self-hosted runner
labelled `lean`, with Git, Python 3.11 or later and `elan` installed.

Do not attach a persistent self-hosted runner to a public repository. A manual
trigger on this workflow does not prevent a pull request from adding another
workflow targeting that runner. Use a controlled private mirror with isolated
runner access, and review any code before running it. That mirror must start
from the released source snapshot and retain its pinned configuration.
The private-repository job condition here is not an access control for other
workflows. See
[GitHub's self-hosted runner guidance](https://docs.github.com/en/actions/reference/security/secure-use#hardening-for-self-hosted-runners).
