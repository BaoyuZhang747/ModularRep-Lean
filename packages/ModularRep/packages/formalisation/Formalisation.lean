import Formalisation.C2Cancellation
import Formalisation.BlockCancellation
import Formalisation.ComputationArithmetic
import Formalisation.ComponentReturn
import Formalisation.ComponentReturnAssembly
import Formalisation.CyclicQuotient
import Formalisation.DependencyCases
import Formalisation.DependencyGraph
import Formalisation.EquivariantActions
import Formalisation.EvenFieldTransport
import Formalisation.ExactStabilizer
import Formalisation.FibreTransport
import Formalisation.GGGRFiniteCore
import Formalisation.InnerTwistedConjugacy
import Formalisation.MainDependencies
import Formalisation.ManuscriptSpecific
import Formalisation.PCore
import Formalisation.PairedLeviOrbit
import Formalisation.PreliminaryDependencies
import Formalisation.RestrictionRank
import Formalisation.ReductionLogic
import Formalisation.SemidirectStabilizer
import Formalisation.SporadicPrimeArithmetic
import Formalisation.SylowObstruction
import Formalisation.SymplecticCaseSplit

/-!
# Scope of the formalisation

This project checks self-contained mathematical mechanisms, a
manuscript-specific iBAW construction layer, and an explicit conditional
dependency certificate for the manuscript:

* the full abstract cancellation lemma, including block-preserving transport,
  for finite sets with an involution;
* construction of the `p`-core and inheritance of cyclic quotients by
  subgroups;
* fixed-point and stabiliser facts together with the complete dependent-fibre
  transport theorem;
* cycle propagation, its connection to an actual semidirect-product
  stabiliser factorisation, and construction of the resulting coherent component
  tuple;
* the Cartesian-product description of paired-Levi orbits once the regular
  overgroup supplies the full product of factor diagonal actions, together
  with the finite return correction used in the type-B induction;
* the exact-stabiliser deduction that every subgroup has cyclic quotient by
  its `2`-core once the manuscript's normal subgroup of order at most two and
  cyclic quotient have been supplied;
* the matrix-level linear algebra used in the restriction-rank calculation;
* the finite arithmetic used in the computation transcripts;
* the final Sylow obstruction in the symplectic principal-block argument;
* the Lang-cocycle identities, quotient-kernel transport, and preservation of
  irreducibility on intermediate subgroups used in the even-field symplectic
  argument;
* the finite core of the generalised Gelfand--Graev argument;
* the group identities used to untwist inner-twisted conjugacy;
* the exact prime supports of the standard factored orders of the four
  boundary sporadic groups;
* the quantifier-level passage from the three verified families and the
  defect-zero case to the hypothesis of Späth's finite group reduction;
* exhaustiveness of the eight type-C cases, four type-B cases, and the
  partition of the 26 sporadic groups into the 22 CTBlocks cases and four
  boundary cases.

The manuscript-specific layer provides typed block, radical, sector, Brauer,
weight, and defect-zero data.  It derives local partitions, restricts and
combines block or sector witnesses, transports witnesses along automorphism
orbits from a stabiliser-equivariant representative, identifies the whole
trivial-radical part with reductions of defect-zero objects, and proves the
finite set core of the complete-collapse argument.  It treats preservation of
the induced block as part of a candidate bijection.  The interpretation of
that block label, intermediate-group block equalities, extensions, modular
character triples, cited descent theorems, and concrete
representation theoretic constructions remain explicit external inputs.

The dependency layer has granular nodes for cited inputs, computation
transcripts, semantic bridges, and every named derived result used in
Sections 2--5.  Lean checks that the graphs are ranked and acyclic, that the
manuscript's case splits are exhaustive, and that the three section
headlines and the finite group corollary follow conditionally from the
declared inputs and semantic realisation maps.

The project does not formalise modular character theory, the truth of cited
classification and character-theoretic results, or the semantic correctness
of GAP computations.  It therefore does not constitute an unconditional
Lean proof of the manuscript's main theorems.  Its strongest global result is
a checked dependency-level proof conditional on those explicit inputs and on
the stated interpretations of the semantic bridge nodes.
-/


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
