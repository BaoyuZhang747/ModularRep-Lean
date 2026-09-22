# ModularRep and the manuscript application

This repository contains the Lean sources accompanying Baoyu Zhang's manuscript
on the inductive blockwise Alperin weight condition for groups of types B and C
and sporadic groups. `packages/ModularRep` contains the reusable representation
theory library; `ManuscriptIBAW` contains the manuscript application.

This release is a checked Lean companion under its stated external assumptions.
Its mathematical scope is set out in [SCOPE.md](SCOPE.md); verification records
and file identities are listed in [STATUS.json](STATUS.json).

- [Formalisation report](output/pdf/formalisation-report.pdf): manuscript deductions and their assumptions.
- [Library manual](output/pdf/library-manual.pdf): reusable mathematics and Lean declarations.
- [Reference manuscript](manuscript/manuscript.pdf) and [source](manuscript/current/main.tex).
- [Library module index](packages/ModularRep/docs/catalogue/index.html).
- [Manuscript statement index](docs/current-manuscript-index.md).

The report and manual have one maintained source tree in [docs/manuals](docs/manuals).
They share the reference definitions in `bibliography-entries.tex`.

## Build and use

Install Lean's `elan` toolchain manager, open a terminal in this directory, and run:

```sh
lake build
```

`lean-toolchain` selects Lean 4.33.1. The three Lake manifests retain the checked
dependency revisions. `lake build` may download dependencies and perform a
substantial compilation; do not use `lake update` when reproducing this revision.
Build products and downloaded dependencies stay in ignored `.lake` directories.
This builds the application root and its import closure, not every distributed
module. See [BUILDING.md](BUILDING.md) for the optional pinned Mathlib cache.

For library use, import the module named in the manual. `ModularRep.Library`
imports a selection of general constructions. The library has its own Lake
project under `packages/ModularRep`; its required local `formalisation` package
and computation inputs are included. The application endpoints are
`ManuscriptIBAW.Main.theorem_1_1` and `ManuscriptIBAW.Main.corollary_1_2`.

## Verification and mathematical scope

With Python 3.11 or later, check the current source and documentation records:

```sh
python -B scripts/check_repository.py
```

This source check permits Git metadata and build caches. It does not invoke Lean
or prove the external mathematical assumptions. To rerun the configured Lean
audits, run `python -B scripts/run_lean_audits.py`. The script first builds every
direct import of the five audit targets, including modules outside the default
application build, and then elaborates those audits with `--trust=0`.

The recorded compilation covered all 1,999 project modules and four library
audits with `--trust=0`; the configured assertions and an additional exhaustive
application declaration audit passed. Pinned precompiled external dependencies
were reused. See the [compilation summary](verification/compilation.json),
[source identities](verification/source-identity.json),
[assertion results](verification/assertions.json), and
[resource measurements](verification/resources.json). The recorded compilation
used approximately 38.1 CPU hours and a peak sampled sum of resident working sets
of 10.40 GiB. These are historical measurements, not measurements of this
repository reorganisation.

The [relocation check](verification/relocation.json) separately records the
pinned toolchain/environment check and a fresh successful `ReusableProviders`
audit using authenticated existing objects. That r31 relocation check did not
repeat the remaining configured audits or the full compilation.

The application theorems are conditional on explicit external assumptions.
The complete classical and sporadic input collections have not been constructed,
and their joint satisfiability has not been established by this companion.
These assumptions define the scope of the released theorems.
Imported external proofs were not replayed. Original logs and compiled objects
are not distributed. The helper and generator for the additional exhaustive
application declaration audit are not included; the supplied commands rerun the
configured library and main application audits, not that additional audit.

## Documentation and releases

See [BUILDING.md](BUILDING.md) for documentation dependencies and checks.
The PDFs and their current source bindings are tracked with the sources.
GitHub Actions checks the source package and release export. The separately
dispatched application build and configured audits are restricted to a private
repository with a dedicated runner; see the runner guidance in BUILDING.

Report Appendix C describes auxiliary constructions in the source library.
Their relationship to the application endpoints is specified in
[SCOPE.md](SCOPE.md). [CHANGELOG.md](CHANGELOG.md) records the source and
documentation changes.

Create a versioned source ZIP from a Git tag or commit:

```sh
python -B scripts/export_release.py --ref HEAD --output ../lean-package.zip
```

The ZIP has one enclosing `ModularRep` directory. After extraction, run
`python -B scripts/verify_release.py` from that directory to verify its exact
contents before creating build files there. The release manifest identifies the
source commit; uncommitted changes are excluded. Private working records,
superseded supporting documentation, previous ZIPs,
Git metadata and build caches are excluded.

The [Apache licence supplied with ModularRep](packages/ModularRep/LICENSE)
remains in the library directory, alongside its original notices. The library
licence does not grant additional rights over the manuscript or application.
[Third-party terms](THIRD_PARTY_NOTICES.md) are retained.
