import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# Combining Fischer central sectors on the actual carriers

This file adds the An--Dietrich sector maps, their block-induction and
character-triple clauses, and the extension input from Spath, Lemma 6.1, to
the neutral literal carriers in `SporadicFi24LiteralCarrierBase`.  Lean
combines the sector maps and derives their global, block, radical, and local
restrictions.  The separate carrier module contains none of these
character-weight equivalences, so a cancellation argument can depend on the
literal carriers without importing the blockwise conclusion proved here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

open Formalisation

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

noncomputable local instance centerFintypeAssembly :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable {BlockIndex : Type u} [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

variable (IntermediateBlockEqualities CompatibleExtensions ModularCharacterTriple :
  IBr iota → WeightClass (p := p) (K := K) (X := X) → Prop)

/-- An--Dietrich sector correspondences and their transport laws, used to
combine the Fischer sectors. The input specifies a map on each sector. -/
structure AnDietrichSectorInput where
  family : EquivariantFibreEquiv
    (brauerSector iota hinj blocks)
    (weightSector (R := R))
    (brauerSector_equivariant iota hinj blocks E1)
    (weightSector_equivariant_actual (iota := iota) (hinj := hinj)
      (blocks := blocks) (R := R) E1)
  blockInduction : ∀ (sector : CentralSector (k := k) (X := X))
      (phi : Fibre (brauerSector iota hinj blocks) sector),
    R.1.weightBlock (family.fibreEquiv sector phi) =
      brauerBlock iota hinj blocks phi
  characterTriple : ∀ (sector : CentralSector (k := k) (X := X))
      (phi : Fibre (brauerSector iota hinj blocks) sector),
    ModularCharacterTriple phi (family.fibreEquiv sector phi)

/-- Exact Spath Lemma 6.1 clauses cited in the Fischer application.  The
cyclic outer-stabiliser and AWC-goodness hypotheses belong to the source
instantiation of this record; no iBAW conclusion is a field. -/
structure SpathLemma61Input
    (AD : AnDietrichSectorInput iota hinj blocks E1
      ModularCharacterTriple) where
  intermediateBlockEqualities :
    ∀ (sector : CentralSector (k := k) (X := X))
      (phi : Fibre (brauerSector iota hinj blocks) sector),
      IntermediateBlockEqualities phi (AD.family.fibreEquiv sector phi)
  compatibleExtensions :
    ∀ (sector : CentralSector (k := k) (X := X))
      (phi : Fibre (brauerSector iota hinj blocks) sector),
      CompatibleExtensions phi (AD.family.fibreEquiv sector phi)

namespace AnDietrichSectorInput

variable {IntermediateBlockEqualities CompatibleExtensions ModularCharacterTriple}
variable (AD : AnDietrichSectorInput iota hinj blocks E1
  ModularCharacterTriple)

/-- Disjoint union of the corrected An--Dietrich maps on the literal sector
fibres. -/
def assemble : IBr iota ≃ WeightClass (p := p) (K := K) (X := X) :=
  AD.family.assemble

@[simp]
theorem assemble_apply (phi : IBr iota) :
    assemble iota hinj blocks E1 AD phi =
      (AD.family.fibreEquiv (brauerSector iota hinj blocks phi)
        ⟨phi, rfl⟩).1 :=
  rfl

/-- Transport compatibility of the sector maps proves equivariance of their
disjoint union under every automorphism of the literal cover. -/
theorem assemble_equivariant (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    assemble iota hinj blocks E1 AD (a • phi) =
      a • assemble iota hinj blocks E1 AD phi :=
  EquivariantFibreEquiv.assemble_equivariant AD.family a phi

/-- The sectorwise block-induction clause proves global preservation of the
literal induced block. -/
theorem assemble_preserves_blockInduction (phi : IBr iota) :
    R.1.weightBlock (assemble iota hinj blocks E1 AD phi) =
      brauerBlock iota hinj blocks phi := by
  rw [assemble_apply iota hinj blocks E1 AD]
  exact AD.blockInduction (brauerSector iota hinj blocks phi) ⟨phi, rfl⟩

/-- Global block preservation implies preservation of the literal central
character sector. -/
theorem assemble_preserves_sector (phi : IBr iota) :
    weightSector (R := R) (assemble iota hinj blocks E1 AD phi) =
      brauerSector iota hinj blocks phi := by
  unfold weightSector brauerSector
  rw [assemble_preserves_blockInduction iota hinj blocks E1 AD]

/-- Restriction of the resulting equivalence to one literal block. -/
def assembledBlockEquiv (b : ActualBlock (k := k) (X := X)) :
    {phi : IBr iota // brauerBlock iota hinj blocks phi = b} ≃
      {w : WeightClass (p := p) (K := K) (X := X) // R.1.weightBlock w = b} where
  toFun phi := ⟨assemble iota hinj blocks E1 AD phi, by
    rw [assemble_preserves_blockInduction iota hinj blocks E1 AD,
      phi.property]⟩
  invFun w := ⟨(assemble iota hinj blocks E1 AD).symm w, by
    calc
      brauerBlock iota hinj blocks
          ((assemble iota hinj blocks E1 AD).symm w) =
          R.1.weightBlock (assemble iota hinj blocks E1 AD
            ((assemble iota hinj blocks E1 AD).symm w)) :=
        (assemble_preserves_blockInduction iota hinj blocks E1 AD
          ((assemble iota hinj blocks E1 AD).symm w)).symm
      _ = R.1.weightBlock w :=
        congrArg R.1.weightBlock
          ((assemble iota hinj blocks E1 AD).apply_symm_apply w)
      _ = b := w.property⟩
  left_inv phi := by
    apply Subtype.ext
    exact (assemble iota hinj blocks E1 AD).symm_apply_apply phi
  right_inv w := by
    apply Subtype.ext
    exact (assemble iota hinj blocks E1 AD).apply_symm_apply w

/-- Radical class of the weight matched with a literal Brauer character. -/
def part (phi : IBr iota) : RadicalClass (p := p) (X := X) :=
  weightRadical (assemble iota hinj blocks E1 AD phi)

/-- The radical decomposition transported from the actual set of weights is
equivariant. -/
theorem part_equivariant (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    part iota hinj blocks E1 AD (a • phi) =
      a • part iota hinj blocks E1 AD phi := by
  unfold part
  rw [assemble_equivariant iota hinj blocks E1 AD,
    weightRadical_equivariant]

/-- The derived radical parts are a genuine disjoint-union partition. -/
def partitionEquiv :
    IBr iota ≃ Sigma fun radical : RadicalClass (p := p) (X := X) =>
      {phi : IBr iota // part iota hinj blocks E1 AD phi = radical} :=
  (Equiv.sigmaFiberEquiv (part iota hinj blocks E1 AD)).symm

/-- Simultaneous restriction by a literal block and a radical class. -/
def assembledLocalEquiv (b : ActualBlock (k := k) (X := X))
    (radical : RadicalClass (p := p) (X := X)) :
    {phi : IBr iota //
      brauerBlock iota hinj blocks phi = b ∧
        part iota hinj blocks E1 AD phi = radical} ≃
      {w : WeightClass (p := p) (K := K) (X := X) //
        R.1.weightBlock w = b ∧ weightRadical w = radical} where
  toFun phi := ⟨assemble iota hinj blocks E1 AD phi, by
    exact ⟨by rw [assemble_preserves_blockInduction iota hinj blocks E1 AD,
        phi.property.1],
      phi.property.2⟩⟩
  invFun w := ⟨(assemble iota hinj blocks E1 AD).symm w, by
    constructor
    · calc
        brauerBlock iota hinj blocks
            ((assemble iota hinj blocks E1 AD).symm w) =
            R.1.weightBlock (assemble iota hinj blocks E1 AD
              ((assemble iota hinj blocks E1 AD).symm w)) :=
          (assemble_preserves_blockInduction iota hinj blocks E1 AD
            ((assemble iota hinj blocks E1 AD).symm w)).symm
        _ = R.1.weightBlock w :=
          congrArg R.1.weightBlock
            ((assemble iota hinj blocks E1 AD).apply_symm_apply w)
        _ = b := w.property.1
    · change weightRadical (assemble iota hinj blocks E1 AD
          ((assemble iota hinj blocks E1 AD).symm w)) = radical
      rw [(assemble iota hinj blocks E1 AD).apply_symm_apply]
      exact w.property.2⟩
  left_inv phi := by
    apply Subtype.ext
    exact (assemble iota hinj blocks E1 AD).symm_apply_apply phi
  right_inv w := by
    apply Subtype.ext
    exact (assemble iota hinj blocks E1 AD).apply_symm_apply w

/-- An--Dietrich's supplied fibrewise modular character-triple clause holds
for the combined pair.  This is L packaging over E2. -/
theorem assembled_characterTriple (phi : IBr iota) :
    ModularCharacterTriple phi (assemble iota hinj blocks E1 AD phi) := by
  rw [assemble_apply iota hinj blocks E1 AD]
  exact AD.characterTriple (brauerSector iota hinj blocks phi) ⟨phi, rfl⟩

/-- Spath's supplied intermediate block equalities hold for the combined
pair.  This is L packaging over E2. -/
theorem assembled_intermediateBlockEqualities
    (S : SpathLemma61Input iota hinj blocks E1
      IntermediateBlockEqualities CompatibleExtensions
      ModularCharacterTriple AD)
    (phi : IBr iota) :
    IntermediateBlockEqualities phi
      (assemble iota hinj blocks E1 AD phi) := by
  rw [assemble_apply iota hinj blocks E1 AD]
  exact S.intermediateBlockEqualities
    (brauerSector iota hinj blocks phi) ⟨phi, rfl⟩

/-- Spath's supplied compatible extensions hold for the combined pair.
This is L packaging over E2. -/
theorem assembled_compatibleExtensions
    (S : SpathLemma61Input iota hinj blocks E1
      IntermediateBlockEqualities CompatibleExtensions
      ModularCharacterTriple AD)
    (phi : IBr iota) :
    CompatibleExtensions phi (assemble iota hinj blocks E1 AD phi) := by
  rw [assemble_apply iota hinj blocks E1 AD]
  exact S.compatibleExtensions
    (brauerSector iota hinj blocks phi) ⟨phi, rfl⟩

end AnDietrichSectorInput

/-- Conclusions obtained by combining the Fischer sector correspondences.  It has no
field asserting BAW-goodness, iBAW, or existence of an `IBAW.Data` object. -/
structure Fi24AssembledClauses
    (AD : AnDietrichSectorInput iota hinj blocks E1
      ModularCharacterTriple) where
  partition :
    IBr iota ≃ Sigma fun radical : RadicalClass (p := p) (X := X) =>
      {phi : IBr iota //
        AnDietrichSectorInput.part iota hinj blocks E1 AD phi = radical}
  blockRestriction : ∀ b : ActualBlock (k := k) (X := X), Nonempty
    ({phi : IBr iota // brauerBlock iota hinj blocks phi = b} ≃
      {w : WeightClass (p := p) (K := K) (X := X) // R.1.weightBlock w = b})
  localRestriction : ∀ (b : ActualBlock (k := k) (X := X))
      (radical : RadicalClass (p := p) (X := X)), Nonempty
    ({phi : IBr iota //
        brauerBlock iota hinj blocks phi = b ∧
          AnDietrichSectorInput.part iota hinj blocks E1 AD phi = radical} ≃
      {w : WeightClass (p := p) (K := K) (X := X) //
        R.1.weightBlock w = b ∧ weightRadical w = radical})
  automorphismTransport : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
    AnDietrichSectorInput.assemble iota hinj blocks E1 AD (a • phi) =
      a • AnDietrichSectorInput.assemble iota hinj blocks E1 AD phi
  blockInduction : ∀ phi : IBr iota,
    R.1.weightBlock
        (AnDietrichSectorInput.assemble iota hinj blocks E1 AD phi) =
      brauerBlock iota hinj blocks phi
  centralSector : ∀ phi : IBr iota,
    weightSector (R := R)
        (AnDietrichSectorInput.assemble iota hinj blocks E1 AD phi) =
      brauerSector iota hinj blocks phi
  radicalTransport : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
    AnDietrichSectorInput.part iota hinj blocks E1 AD (a • phi) =
      a • AnDietrichSectorInput.part iota hinj blocks E1 AD phi
  intermediateBlockEqualities : ∀ phi : IBr iota,
    IntermediateBlockEqualities phi
      (AnDietrichSectorInput.assemble iota hinj blocks E1 AD phi)
  compatibleExtensions : ∀ phi : IBr iota,
    CompatibleExtensions phi
      (AnDietrichSectorInput.assemble iota hinj blocks E1 AD phi)
  modularCharacterTriple : ∀ phi : IBr iota,
    ModularCharacterTriple phi
      (AnDietrichSectorInput.assemble iota hinj blocks E1 AD phi)

/-- Strongest honest concrete Fischer bridge presently available.  Lean
combines the literal carrier maps; the three representation theoretic
predicate fields remain projections of the exact An--Dietrich and Spath E2
inputs. -/
def fi24_source_shaped_assembly
    (AD : AnDietrichSectorInput iota hinj blocks E1
      ModularCharacterTriple)
    (S : SpathLemma61Input iota hinj blocks E1
      IntermediateBlockEqualities CompatibleExtensions
      ModularCharacterTriple AD) :
    Fi24AssembledClauses iota hinj blocks E1
      IntermediateBlockEqualities CompatibleExtensions
      ModularCharacterTriple AD where
  partition := AnDietrichSectorInput.partitionEquiv iota hinj blocks E1 AD
  blockRestriction b :=
    ⟨AnDietrichSectorInput.assembledBlockEquiv iota hinj blocks E1 AD b⟩
  localRestriction b radical :=
    ⟨AnDietrichSectorInput.assembledLocalEquiv iota hinj blocks E1 AD
      b radical⟩
  automorphismTransport :=
    AnDietrichSectorInput.assemble_equivariant iota hinj blocks E1 AD
  blockInduction :=
    AnDietrichSectorInput.assemble_preserves_blockInduction
      iota hinj blocks E1 AD
  centralSector :=
    AnDietrichSectorInput.assemble_preserves_sector iota hinj blocks E1 AD
  radicalTransport :=
    AnDietrichSectorInput.part_equivariant iota hinj blocks E1 AD
  intermediateBlockEqualities :=
    AnDietrichSectorInput.assembled_intermediateBlockEqualities
      iota hinj blocks E1 AD S
  compatibleExtensions :=
    AnDietrichSectorInput.assembled_compatibleExtensions
      iota hinj blocks E1 AD S
  modularCharacterTriple :=
    AnDietrichSectorInput.assembled_characterTriple iota hinj blocks E1 AD

end ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
