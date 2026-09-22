# Computation assets

This directory contains eleven generating GAP programs in `code/` and their
eleven exact recorded outputs in `outputs/`. [assets.json](assets.json) records
file hashes, versions printed by each output, and the direct Lean consumers of
each embedded transcript constant.

For an independent rerun, use the recorded GAP and package versions, run from
the package root, and direct the output to a new file. For example:

```text
gap -q --quitonbreak data/computations/code/baby.g > baby.rerun.out
```

Replace `baby` with the corresponding stem in `assets.json`. Each program names
its required GAP packages via `LoadPackage`. Some AtlasRep computations may need
its representation data. A version absent from an output is recorded as
unknown; it is not inferred. Successful execution on another version is not a
claim of byte-for-byte reproduction of the archived transcript.

The package build embeds the preserved files through
`ModularRep.ComputationTranscriptSnapshots`. Lake tracks both each output and
its generating program. No GAP execution is needed to build Lean sources.

The trust boundary has three parts: the external computation and its table
identification; file ingestion by `include_str`; and the Lean-checked parser,
arithmetic, and mathematical deductions on the resulting strings. The latter
does not authenticate the first two. Keep the preserved outputs unchanged when
checking the archived certificates.
