import Formalisation.IBAWAssembly
import Formalisation.IBAWBlockWitness
import Formalisation.IBAWCollapse
import Formalisation.IBAWOrbitTransport

/-!
# Manuscript-specific iBAW formalisation

This import collects the abstract formalisation of the manuscript's iBAW
proof architecture.

The formalised layer contains:

* automorphism actions on blocks, radical classes, central character sectors,
  Brauer objects, local weight objects, and defect-zero objects;
* a radical partition derived from a global bijection, together with its
  blockwise and local fibre restrictions;
* a strict separation between a combinatorial candidate preserving induced
  blocks and the additional certification of intermediate-group block
  equalities, extensions, modular character triples, and the `Q = 1`
  normalisation;
* an exact description of the `Q = 1` part by reductions of defect-zero
  objects;
* restriction to block witnesses and aggregation of a coherent witness for
  every block;
* construction of coherent blockwise or sectorwise equivalences;
* transport from one block or sector across a transitive automorphism orbit,
  including independence of transporters, propagation of equivariant labels
  and compatibility predicates, and propagation of `Q = 1` normalisation
  from a base block;
* the finite-cardinality and trivial-action core of the complete-collapse
  argument.

The following mathematical bridges are deliberately not encoded as
definitions or silently assumed consequences:

* construction of the concrete character, block, radical-subgroup, and weight
  sets for a finite group;
* the quotient by the kernel of a central character in the blockwise
  inductive condition;
* Späth's descent from the inductive condition to blockwise witnesses on the
  simple group;
* proofs that `weightBlock` is the actual induced block and `blockSector` is
  the unique central character sector of that block;
* the facts that the actual central characters of Brauer characters and
  weights agree with the sectors assigned through their block labels;
* proofs that a concrete matched pair satisfies the required equalities of
  blocks over intermediate groups, extension, and modular character-triple
  requirements;
* classification results, Lie-theoretic correspondences, and GAP or CHEVIE
  calculations used to construct the input witnesses.

Consequently this layer verifies the construction and transport deductions in the
manuscript without claiming an end-to-end formal proof of its main theorems.
-/


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
