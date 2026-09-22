import ModularRep.PaperProofs.OddTwoBroughButterflyGroups
import ModularRep.PaperProofs.OddTwoActualLocalBlockSupport

/-!
# The exact MRR 3.11 source on the two actual PSp triples

MRR (2026), Lemma 3.11, printed p.344, is the modular butterfly theorem;
Spath (2017), Theorem 3.5(b), pp.669--670, gives its block refinement.
It replaces the ambient group while keeping the normal group and both
characters, provided the natural conjugation images agree and the new
local subgroup is the indicated inverse image.

This module records only that named E2 theorem specialized to the TWO
ALREADY COMPUTED tuples: the actual PSp base in PCSp semidirect Aut(F),
and the actual PSp base in its full holomorph. The same actual iota, psi,
raw weight W, own normalizer reduction R, and coefficient fields are used
on both sides. Their normal bases and local intersections are identified
with the same PSp and own normalizer by the checked computed equivalences.

`BlockTripleSourceSemantics` must have the authenticated standard modular
block-isomorphism meaning, including character-triple invariance. An
arbitrary predicate is not a licensed interpretation of this source law.
No representation foundations are rebuilt, and no source instance is
constructed. The K consumer supplies the natural-image and exact-local-
preimage hypotheses from OddTwoBroughButterflyGroups. The prior actual
Brough relation and the shared normalizer root convention remain explicit.
No final FLZ condition, principal orbit witness, or Type C endpoint occurs.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoBroughButterflySource

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple (OwnNormalizerReduction)
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoBroughButterflyGroups

universe u

variable {n : ℕ} {F k K : Type u}
variable [Field F] [Finite F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]

local instance groupAutFinite (G : Type u) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun a : MulAut G => (a : G → G)) DFunLike.coe_injective

local instance groupFintype (G : Type u) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)

/-- Exact published E2 on the fixed actual tuples. The group hypotheses
are the literal natural-conjugation range and local-image preimage from
MRR 3.11. No alternate group, map, root, local character, or target predicate
is supplied by this record. Transport along the computed base/normalizer
identifications is part of specializing the standard theorem to these
subgroup presentations; it is not a free equivalence hypothesis.

The compatibility premise retains a common modular root convention along
the ACTUAL own normalizer inclusion. It does not equate whole root lifts
for groups with different exponents. -/
structure MRRLemma311Source (semantics : BlockTripleSourceSemantics 2 k K) : Prop where
  butterfly : ∀ (iota : PrimeRegularRootEmbedding 2 k K (PSp n F))
      (psi : IBr iota) (W : CharacterWeight 2 K (PSp n F))
      (R : OwnNormalizerReduction (k := k) W),
    RootCompatibleAlong iota R.root
      (Subgroup.normalizer (W.subgroup : Set (PSp n F))).subtype →
    (holConjugation iota psi).range = (broughConjugation S iota psi).range →
    ((OddTwoBroughActualTriple.localSubgroup S iota psi W).map
      (broughConjugation S iota psi)).comap (holConjugation iota psi) =
        OddTwoActualStabilizerTriple.localSubgroup iota
          (MonoidHom.id (MulAut (PSp n F))) psi W →
    semantics.blockIsomorphic (OddTwoBroughActualTriple.arguments S iota psi W R) →
    semantics.blockIsomorphic (OddTwoActualStabilizerTriple.arguments iota
      (MonoidHom.id (MulAut (PSp n F))) psi W R)

variable {semantics : BlockTripleSourceSemantics 2 k K}
variable (source : MRRLemma311Source S semantics)
variable (iota : PrimeRegularRootEmbedding 2 k K (PSp n F))
variable (psi : IBr iota) (W : CharacterWeight 2 K (PSp n F))
variable (R : OwnNormalizerReduction (k := k) W)

include source in
/-- K supplies precisely the two group hypotheses of the licensed source.
The Brough relation is an earlier relation on the SAME psi, W and R, not
an orbit witness or a final Definition 3.5 conclusion. -/
theorem blockIsomorphic_of_brough
    (roots : RootCompatibleAlong iota R.root
      (Subgroup.normalizer (W.subgroup : Set (PSp n F))).subtype)
    (relation : semantics.blockIsomorphic
      (OddTwoBroughActualTriple.arguments S iota psi W R)) :
    semantics.blockIsomorphic (OddTwoActualStabilizerTriple.arguments iota
      (MonoidHom.id (MulAut (PSp n F))) psi W R) :=
  source.butterfly iota psi W R roots
    (conjugation_ranges S iota psi)
    (local_conjugation_image_preimage S iota psi W) relation

end ModularRep.PaperProofs.OddTwoBroughButterflySource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
