import ModularRep.PaperProofs.TypeBCriterionEmbeddedPairBinding
import ModularRep.PaperProofs.TypeBCentralKernelPairRepresentativeSplitting

/-!
# The literal pair relation on the original criterion carriers

The fixed base is embedded into the full finite semidirect ambient. The
relation is the existing splitting ClassWitness after the actual Brauer
and weight-class equivalences. Normality, ordinary roots on the embedded
base, and residue calibration are constructed from the original data.

The two transport consequences use the existing one-way Butterfly
certificate. The relation and introduction from an existing raw witness
do not depend on that certificate. No new source record is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBEmbeddedPairClassWitness

open ModularRep TypeBCriterionHypotheses
open TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelTripleCarriers TypeBCentralKernelTripleRootFamily
open TypeBLocalReductionInstantiation

variable {p : ℕ} {K O k M E : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group M] [Finite M] [Group E] [Finite E]
  (Msys : ModularSystem p K O k)
  (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
  (action : NaturalAction G field)
  (root : PrimeRegularRootEmbedding p k K G)
  (calibration : RootResidueCompatible Msys root)

/-- The prescribed specified catalogue family on all actual embedded pairs.
This is a type abbreviation in substance, with no witness or source field. -/
def CatalogueFamily : Type :=
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  ∀ (theta : IBr (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root))
    (W : CharacterWeight p K (embeddedG G field))
    (hUT : U (embeddedG G field) W ≤
      T (embeddedG G field)
        (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root) theta),
    PhysicalBlockFamily (k := k)
      (inside (embeddedG G field)
        (T (embeddedG G field)
          (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root) theta))
      (inside (U (embeddedG G field) W)
        (T (embeddedG G field)
          (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root) theta))

variable (catalogues : CatalogueFamily G field action root)
  [HasEnoughRootsOfUnity K (Nat.card G)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding p k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- The existing literal class-witness relation, pulled back to the original
Brauer and ordinary weight-class carriers through the same embedding. -/
def Relation (phi : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) : Prop := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) G field
  exact TypeBCentralKernelPairRepresentativeSplitting.ClassWitness
    Msys (embeddedG G field)
    (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root)
    (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue G field Msys root calibration)
    catalogues navarro
    (TypeBCriterionEmbeddedPairBinding.brauerEquiv G field root phi)
    (TypeBCriterionEmbeddedPairBinding.weightClassEquiv G field w)

/-- An existing witness on the transported original raw representative
introduces the relation; no Butterfly certificate is needed. -/
theorem of_rawWitness (phi : IBr root) (W : CharacterWeight p K G)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G))
    (representative : classOf W = w) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
    letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) G field
    ∀ (hUT : U (embeddedG G field)
        (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv G field W) ≤
      T (embeddedG G field)
        (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root)
        (TypeBCriterionEmbeddedPairBinding.brauerEquiv G field root phi)),
      Nonempty (TypeBCentralKernelPairSplittingBinding.PairWitness
        Msys (embeddedG G field)
        (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root)
        (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue G field Msys root calibration)
        (TypeBCriterionEmbeddedPairBinding.brauerEquiv G field root phi)
        (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv G field W) hUT navarro
        (catalogues (TypeBCriterionEmbeddedPairBinding.brauerEquiv G field root phi)
          (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv G field W) hUT)) →
      Relation Msys G field action root calibration catalogues navarro phi w := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) G field
  intro hUT witness
  unfold Relation
  refine ⟨TypeBCriterionEmbeddedPairBinding.rawWeightEquiv G field W, ?_, hUT, witness⟩
  exact (TypeBCriterionEmbeddedPairBinding.weightClassEquiv_classOf G field W).symm.trans
    (congrArg (TypeBCriterionEmbeddedPairBinding.weightClassEquiv G field) representative)

/-- Simultaneous twisting uses the inverse of the same full ambient actor
on the original character and the original weight class. -/
theorem simultaneous_iff
    (certificate : TypeBCentralKernelButterflyCertificate.ButterflyCertificate p k K)
    (phi : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G))
    (a : Ambient field) :
    Relation Msys G field action root calibration catalogues navarro
        (IrreducibleBrauerCharacter.twist root phi (action.hom a⁻¹))
        (CharacterWeight.rightTwistConjugacyClass (action.hom a⁻¹) w) ↔
      Relation Msys G field action root calibration catalogues navarro phi w := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) G field
  unfold Relation
  rw [TypeBCriterionEmbeddedPairBinding.brauerEquiv_twist G field action root a phi,
    TypeBCriterionEmbeddedPairBinding.weightClassEquiv_rightTwist G field action a w]
  exact TypeBCentralKernelPairRepresentativeSplitting.classWitness_conjugate_iff
    Msys (embeddedG G field)
    (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root)
    (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue G field Msys root calibration)
    catalogues navarro certificate
    (TypeBCriterionEmbeddedPairBinding.brauerEquiv G field root phi)
    (TypeBCriterionEmbeddedPairBinding.weightClassEquiv G field w) a

/-- The related original character has the complete embedded witness for
every original raw representative of the prescribed class. -/
theorem all_representatives
    (certificate : TypeBCentralKernelButterflyCertificate.ButterflyCertificate p k K)
    (phi : IBr root)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G))
    (related : Relation Msys G field action root calibration catalogues navarro phi w)
    (W : CharacterWeight p K G) (representative : classOf W = w) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
    letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) G field
    TypeBCentralKernelPairRepresentativeSplitting.WitnessAt
      Msys (embeddedG G field)
      (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root)
      (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue G field Msys root calibration)
      catalogues navarro
      (TypeBCriterionEmbeddedPairBinding.brauerEquiv G field root phi)
      (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv G field W) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) G field
  apply TypeBCentralKernelPairRepresentativeSplitting.all_representatives
    Msys (embeddedG G field)
    (TypeBCriterionEmbeddedPairBinding.embeddedRoot G field root)
    (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue G field Msys root calibration)
    catalogues navarro certificate
    (TypeBCriterionEmbeddedPairBinding.brauerEquiv G field root phi)
    (TypeBCriterionEmbeddedPairBinding.weightClassEquiv G field w) related
    (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv G field W)
  exact (TypeBCriterionEmbeddedPairBinding.weightClassEquiv_classOf G field W).symm.trans
    (congrArg (TypeBCriterionEmbeddedPairBinding.weightClassEquiv G field) representative)

end ModularRep.PaperProofs.TypeBEmbeddedPairClassWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
