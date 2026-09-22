# Verification records

The scope and limitations are stated in [STATUS.json](../../../STATUS.json).
The records give [source identities](../../../verification/source-identity.json),
[assertion results](../../../verification/assertions.json),
[compilation results](../../../verification/compilation.json) and
[resource measurements](../../../verification/resources.json).

From the repository root, run `python -B scripts/check_repository.py` to check
the specified source identities, dependency pins and declaration associations.
For a freshly extracted release, run `python -B scripts/verify_release.py`.
These commands do not run Lean or prove the external mathematical assumptions.
See [build instructions](../../../BUILDING.md) for compilation and the configured audits.
