import Formalisation.IBAWAssembly
import Mathlib.Tactic

/-!
# Paper proof: construction over central character sectors

This file combines correspondences on central character sectors. A coherent
automorphism-equivariant equivalence is supplied on each central character
sector.  Lean combines these equivalences, proves that the result preserves
blocks and sectors, and derives the block and radical-subgroup restrictions.
If the intermediate-block, extension, character-triple, and `Q = 1`
normalisation clauses hold on every sector fibre, Lean proves the full abstract
iBAW datum.

The distinction between `SectorwiseCandidate` and
`SectorwiseCertification` is essential.  An iBAW-bijection in the sense of
Feng--Li--Zhang Definition 3.5 supplies only the candidate and its modular
character-triple relation.  It does not, without an additional theorem, supply
all of Spath Definition 4.1(iii)--(iv).  The final section gives a small logical
model in which the weak data exist but a full `IBAW.Data` object cannot exist.

Routine representation theoretic facts identifying blocks, characters, and
weights with their unique central sectors are external inputs.  They are not
reproved here.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicCentralSectorAssemblyLemma56Relative

open Formalisation
open Formalisation.IBAW

universe u

variable {A Block Radical Sector Brauer Weight DZ : Type u}
variable [Group A]
variable [MulAction A Block] [MulAction A Radical] [MulAction A Sector]
variable [MulAction A Brauer] [MulAction A Weight] [MulAction A DZ]

variable {C : Context A Block Radical Sector Brauer Weight DZ}

/-- The set-theoretic and equivariance inputs supplied sector by sector.

The field `family` is stronger and more precise than merely choosing an
equivalence on each sector: `map_actFibre` in `EquivariantFibreEquiv` says that
the choices commute with every automorphism carrying one sector to another.
Block preservation remains explicit because one sector may contain several
blocks. -/
structure SectorwiseCandidate
    (C : Context A Block Radical Sector Brauer Weight DZ) where
  family : EquivariantFibreEquiv (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C))
  blockPreserving : forall (sector : Sector)
      (x : Fibre (brauerSector C) sector),
    C.weightBlock (family.fibreEquiv sector x) = C.brauerBlock x

namespace SectorwiseCandidate

/-- The disjoint union of the sectorwise maps, before the remaining
representation theoretic clauses are attached. -/
def assemble (D : SectorwiseCandidate C) : Candidate C :=
  candidateOfIndexedFibres (brauerSector C) (weightSector C)
    (brauerSector_equivariant (C := C))
    (weightSector_equivariant (C := C)) D.family D.blockPreserving

@[simp]
theorem assemble_apply (D : SectorwiseCandidate C) (x : Brauer) :
    D.assemble.equiv x =
      (D.family.fibreEquiv (brauerSector C x) ⟨x, rfl⟩).1 := by
  rfl

/-- Transport compatibility of the sector maps gives equivariance of their
disjoint union under the full automorphism action. -/
theorem assemble_equivariant (D : SectorwiseCandidate C)
    (a : A) (x : Brauer) :
    D.assemble.equiv (a • x) = a • D.assemble.equiv x :=
  D.assemble.equiv_equivariant a x

/-- Block preservation on every sector fibre gives block preservation of the
disjoint union. -/
theorem assemble_preserves_block (D : SectorwiseCandidate C) (x : Brauer) :
    C.weightBlock (D.assemble.equiv x) = C.brauerBlock x :=
  D.assemble.block_preserving x

/-- In the concrete manuscript instance, `weightBlock` is the block induced
from the inflated local defect zero character.  Thus this is exactly the
block induction clause, with its representation theoretic interpretation
kept outside the abstract construction. -/
theorem assemble_preserves_blockInduction
    (D : SectorwiseCandidate C) (x : Brauer) :
    C.weightBlock (D.assemble.equiv x) = C.brauerBlock x :=
  D.assemble_preserves_block x

/-- The resulting map sends every Brauer object to a weight in the sector
determined by the same block. -/
theorem assemble_preserves_sector (D : SectorwiseCandidate C) (x : Brauer) :
    weightSector C (D.assemble.equiv x) = brauerSector C x :=
  D.assemble.sector_preserving x

/-- The resulting map restricts to a bijection on every block. -/
def assembledBlockEquiv (D : SectorwiseCandidate C) (block : Block) :
    {x : Brauer // C.brauerBlock x = block} ≃
      {y : Weight // C.weightBlock y = block} :=
  D.assemble.blockEquiv block

/-- The radical subgroup attached to a Brauer object is determined by the
weight to which the resulting map sends it. -/
def part (D : SectorwiseCandidate C) (x : Brauer) : Radical :=
  D.assemble.part x

/-- The derived radical decomposition is equivariant. -/
theorem part_equivariant (D : SectorwiseCandidate C) (a : A) (x : Brauer) :
    D.part (a • x) = a • D.part x :=
  D.assemble.part_equivariant a x

/-- The derived parts really form a partition of the Brauer objects. -/
def partitionEquiv (D : SectorwiseCandidate C) :
    Brauer ≃ Sigma fun radical : Radical => {x : Brauer // D.part x = radical} :=
  D.assemble.partitionEquiv

/-- Restricting the resulting map simultaneously by block and radical class
gives the local bijection required in the construction argument. -/
def assembledLocalEquiv (D : SectorwiseCandidate C)
    (block : Block) (radical : Radical) :
    {x : Brauer // C.brauerBlock x = block ∧ D.part x = radical} ≃
      {y : Weight // C.weightBlock y = block ∧
        C.weightRadical y = radical} :=
  D.assemble.localEquiv block radical

end SectorwiseCandidate

/-- Every clause exposed by the sector construction.

The fields involving only the resulting equivalence are deductions from a
coherent sectorwise family.  The four representation theoretic predicates
are not such deductions: they must be certified on every sector fibre.  The
last field makes explicit that `extensionsOK` includes the coincidence of the
global and local extensions at `Q = 1`, as required by Spath's normalisation
clause. -/
structure AssembledClauses (D : SectorwiseCandidate C) where
  partition :
    Brauer ≃ Sigma fun radical : Radical => {x : Brauer // D.part x = radical}
  blockBijection : forall block : Block,
    {x : Brauer // C.brauerBlock x = block} ≃
      {y : Weight // C.weightBlock y = block}
  localBijection : forall (block : Block) (radical : Radical),
    {x : Brauer // C.brauerBlock x = block ∧ D.part x = radical} ≃
      {y : Weight // C.weightBlock y = block ∧
        C.weightRadical y = radical}
  partitionEquivariance : forall (a : A) (x : Brauer),
    D.part (a • x) = a • D.part x
  equivariance : forall (a : A) (x : Brauer),
    D.assemble.equiv (a • x) = a • D.assemble.equiv x
  blockInduction : forall x : Brauer,
    C.weightBlock (D.assemble.equiv x) = C.brauerBlock x
  centralCharacters : forall x : Brauer,
    weightSector C (D.assemble.equiv x) = brauerSector C x
  intermediateBlockEqualities : forall x : Brauer,
    C.intermediateBlockEqualitiesOK x (D.assemble.equiv x)
  extensions : forall x : Brauer,
    C.extensionsOK x (D.assemble.equiv x)
  characterTriples : forall x : Brauer,
    C.characterTripleOK x (D.assemble.equiv x)
  qOneNormalisation : forall d : DZ,
    D.assemble.equiv (C.reduce d) = C.atOne d
  qOneExtensionCompatibility : forall d : DZ,
    C.extensionsOK (C.reduce d) (C.atOne d)

/-- The representation theoretic clauses needed to upgrade the sectorwise
candidate to Spath's full inductive condition.

All hypotheses are fibrewise.  In particular, `normalisation` states the
`Q = 1` identity on the relevant sector map, rather than assuming that the
resulting equivalence is already normalised. -/
structure SectorwiseCertification (D : SectorwiseCandidate C) where
  intermediateBlockEqualities : forall (sector : Sector)
      (x : Fibre (brauerSector C) sector),
    C.intermediateBlockEqualitiesOK x (D.family.fibreEquiv sector x)
  extensions : forall (sector : Sector)
      (x : Fibre (brauerSector C) sector),
    C.extensionsOK x (D.family.fibreEquiv sector x)
  characterTriples : forall (sector : Sector)
      (x : Fibre (brauerSector C) sector),
    C.characterTripleOK x (D.family.fibreEquiv sector x)
  normalisation : forall d : DZ,
    (D.family.fibreEquiv (brauerSector C (C.reduce d))
      ⟨C.reduce d, rfl⟩).1 = C.atOne d

namespace SectorwiseCertification

/-- Combine the sectorwise maps and all four fibrewise certifications into
one full abstract iBAW datum. -/
def assemble (D : SectorwiseCandidate C)
    (H : SectorwiseCertification D) : Data C :=
  dataOfSectorFibres D.family D.blockPreserving
    H.intermediateBlockEqualities H.extensions H.characterTriples
    (fun d => by
      rw [EquivariantFibreEquiv.assemble_apply]
      exact H.normalisation d)

theorem assembled_intermediateBlockEqualities
    (D : SectorwiseCandidate C) (H : SectorwiseCertification D)
    (x : Brauer) :
    C.intermediateBlockEqualitiesOK x ((H.assemble D).equiv x) :=
  (H.assemble D).intermediateBlockEqualities x

theorem assembled_extensions
    (D : SectorwiseCandidate C) (H : SectorwiseCertification D)
    (x : Brauer) : C.extensionsOK x ((H.assemble D).equiv x) :=
  (H.assemble D).extensions x

theorem assembled_characterTriple
    (D : SectorwiseCandidate C) (H : SectorwiseCertification D)
    (x : Brauer) : C.characterTripleOK x ((H.assemble D).equiv x) :=
  (H.assemble D).characterTriple x

theorem assembled_normalisation
    (D : SectorwiseCandidate C) (H : SectorwiseCertification D)
    (d : DZ) : (H.assemble D).equiv (C.reduce d) = C.atOne d :=
  (H.assemble D).normalisation d

/-- At `Q = 1`, normalisation identifies the matched local object with the
ordinary defect zero character, so the fibrewise extension clause becomes
the required equality of the global and local extensions. -/
theorem assembled_qOneExtensionCompatibility
    (D : SectorwiseCandidate C) (H : SectorwiseCertification D)
    (d : DZ) : C.extensionsOK (C.reduce d) (C.atOne d) := by
  rw [← H.assembled_normalisation D d]
  exact H.assembled_extensions D (C.reduce d)

/-- The full conclusion of combining the sector correspondences. Its inputs
are specified on each sector and do not contain a global
equivalence or an already combined iBAW datum. -/
def allAssembledClauses
    (D : SectorwiseCandidate C) (H : SectorwiseCertification D) :
    AssembledClauses D where
  partition := D.partitionEquiv
  blockBijection := D.assembledBlockEquiv
  localBijection := D.assembledLocalEquiv
  partitionEquivariance := D.part_equivariant
  equivariance := D.assemble_equivariant
  blockInduction := D.assemble_preserves_blockInduction
  centralCharacters := D.assemble_preserves_sector
  intermediateBlockEqualities := H.assembled_intermediateBlockEqualities D
  extensions := H.assembled_extensions D
  characterTriples := H.assembled_characterTriple D
  qOneNormalisation := H.assembled_normalisation D
  qOneExtensionCompatibility := H.assembled_qOneExtensionCompatibility D

/-- The combined conclusion assumes the sectorwise maps and
the four missing clauses separately, and proves the full combined datum. -/
theorem lemma_5_6_relative
    (D : SectorwiseCandidate C) (H : SectorwiseCertification D) :
    Nonempty (Data C) :=
  ⟨H.assemble D⟩

end SectorwiseCertification

/-! ## Why a weak iBAW-bijection is not enough

The following one-point model is not a representation theoretic
counterexample.  It is a logical audit of the interface: equivariant,
block-preserving sectorwise bijections and a true character-triple predicate
do not determine an extension predicate.  Therefore that implication must be
supplied by the strong quotient character-triple theorem used in the
application, rather than inferred from the word "iBAW-bijection" alone.
-/

namespace WeakDataSeparation

abbrev One := PUnit

instance : Group One where
  mul _ _ := PUnit.unit
  one := PUnit.unit
  inv _ := PUnit.unit
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel _ := rfl

instance : MulAction One One where
  smul _ _ := PUnit.unit
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- A context in which all set-theoretic and character-triple data are
trivial, but the required extension predicate is false. -/
def weakContext : Context One One One One One One One where
  brauerBlock _ := PUnit.unit
  weightBlock _ := PUnit.unit
  weightRadical _ := PUnit.unit
  blockSector _ := PUnit.unit
  oneRadical := PUnit.unit
  reduce _ := PUnit.unit
  atOne _ := PUnit.unit
  oneRadical_fixed _ := rfl
  brauerBlock_equivariant _ _ := rfl
  weightBlock_equivariant _ _ := rfl
  weightRadical_equivariant _ _ := rfl
  blockSector_equivariant _ _ := rfl
  reduce_equivariant _ _ := rfl
  atOne_equivariant _ _ := rfl
  reduce_injective _ _ _ := Subsingleton.elim _ _
  atOne_radical _ := rfl
  atOne_block _ := rfl
  atOne_complete _ _ := ⟨PUnit.unit, rfl⟩
  intermediateBlockEqualitiesOK _ _ := True
  extensionsOK _ _ := False
  characterTripleOK _ _ := True
  intermediateBlockEqualities_equivariant _ _ _ := Iff.rfl
  extensions_equivariant _ _ _ := Iff.rfl
  characterTriple_equivariant _ _ _ := Iff.rfl

def weakFamily : SectorwiseCandidate weakContext where
  family :=
    { fibreEquiv := fun _ => Equiv.refl _
      map_actFibre := by
        intro a sector x
        apply Subtype.ext
        exact Subsingleton.elim _ _ }
  blockPreserving _ _ := rfl

theorem weak_family_has_characterTriples :
    forall x : One,
      weakContext.characterTripleOK x (weakFamily.assemble.equiv x) := by
  simp [weakContext]

theorem weak_family_has_normalisation :
    forall d : One,
      weakFamily.assemble.equiv (weakContext.reduce d) = weakContext.atOne d := by
  intro d
  exact Subsingleton.elim _ _

/-- The weak family cannot be upgraded to full iBAW data because no matched
pair satisfies the deliberately false extension predicate. -/
theorem no_full_data_from_weak_family :
    ¬ Nonempty (Data weakContext) := by
  rintro ⟨W⟩
  exact W.extensions PUnit.unit

end WeakDataSeparation

end ModularRep.PaperProofs.SporadicCentralSectorAssemblyLemma56Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
