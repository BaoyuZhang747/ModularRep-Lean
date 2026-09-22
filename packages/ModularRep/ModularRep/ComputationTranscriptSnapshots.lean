/-!
# Shared snapshots of the current root output transcripts

Each output file is embedded exactly once in this module.  Every parser in the
verification project imports these public constants, so two downstream
certificates cannot accidentally elaborate against different snapshots of the
same file.

`include_str` is a build tool operation: Lake tracks the eleven files through the
`input_file` targets in `lakefile.toml`, and Lean embeds their contents as
string literals while elaborating this module.  The Lean kernel can check pure
computations on the resulting strings, but it does not verify the operation
that read a file and produced an embedded string literal.
-/

namespace ModularRep.ComputationTranscriptSnapshots

def babyTranscript : String := include_str
  "../data/computations/outputs/baby.out"

def fi24BlocksTranscript : String := include_str
  "../data/computations/outputs/fi24blocks.out"

def fi24P3Transcript : String := include_str
  "../data/computations/outputs/fi24p3.out"

def fi24WeightsTranscript : String := include_str
  "../data/computations/outputs/fi24weights.out"

def monsterTranscript : String := include_str
  "../data/computations/outputs/monster.out"

def o7BlockTwoTranscript : String := include_str
  "../data/computations/outputs/o7block2.out"

def o7BlocksTranscript : String := include_str
  "../data/computations/outputs/o7blocks.out"

def o7BrauerTranscript : String := include_str
  "../data/computations/outputs/o7brauer.out"

def o7RadicalTranscript : String := include_str
  "../data/computations/outputs/o7radical.out"

def o7WeightsTranscript : String := include_str
  "../data/computations/outputs/o7weights.out"

def sp6Transcript : String := include_str
  "../data/computations/outputs/sp6.out"

end ModularRep.ComputationTranscriptSnapshots


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
