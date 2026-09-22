import ModularRep.PaperProofs.TypeBQ3B2DihedralDefect

/-!
# The defect group of the exceptional block B2

The block, ordinary and Brauer characters, and defect subgroup are those in
the exceptional application. Kessar--Malle's Theorem 1.1 supplies the
abelian-defect implication already expressed by `AbelianHeightZeroSource`.
Sambale's online Theorem 8.1(1), (3) gives one or three Brauer characters
for quaternion defect of order eight, and therefore excludes two. These published
results remain explicit assumptions.

The proof below excludes the abelian and quaternion possibilities directly.
It does not use a count of six ordinary characters. A separate implication
allows this exclusion to be used by the existing block constructions.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.DefectEight

open ModularRep ModularRep.PaperProofs
open TypeBExceptionalQ3Proposition416Actual
open TypeBExceptionalQ3Proposition416Relative
open TypeBLocalReductionInstantiation TypeBQ3B2DihedralDefect

open scoped MonoidAlgebra

variable {k K O X : Type}
variable [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
variable [CharZero K] [CharP k 2] [IsAlgClosed k]
variable [Group X] [Fintype X]
variable {blockIdempotent : Formalisation.ComputationArithmetic.Q3Block → k[X]}

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The quaternion exclusion on the specified block and its defect subgroup.
The cardinality is that of its actual irreducible Brauer characters. -/
structure QuaternionExclusionSource
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity root)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D) : Prop where
  not_two : Nonempty (D ≃* QuaternionGroup 2) →
    Nat.card (ActualBrauerFibre root hinj blocks .B2) ≠ 2

/-- The direct exclusion implies the conditional numerical statement used
by the existing construction. It does not assert that such a block exists. -/
theorem QuaternionExclusionSource.toNumerical
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity root)
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (ordinary : PhysicalOrdinarySource blocks Msys root hinj)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D)
    (source : QuaternionExclusionSource blocks Msys root calibration hinj D defect) :
    QuaternionTwoBrauerSource blocks Msys root calibration hinj ordinary D defect where
  ordinary_card_six quaternion two := (source.not_two quaternion two).elim

/-- Positive height and two Brauer characters leave only dihedral defect
among the groups of order eight. -/
theorem defect_is_dihedral
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity root)
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (ordinary : PhysicalOrdinarySource blocks Msys root hinj)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D)
    (table : PhysicalTableSource blocks Msys root hinj ordinary D)
    (classification : OrderEightClassificationSource D)
    (heightZero : AbelianHeightZeroSource blocks Msys root calibration hinj ordinary D defect)
    (quaternion : QuaternionExclusionSource blocks Msys root calibration hinj D defect)
    (two : Nat.card (ActualBrauerFibre root hinj blocks .B2) = 2) :
    Nonempty (D ≃* DihedralGroup 4) := by
  rcases classification.classified table.defect_order with abelian | dihedral | quaternionGroup
  · obtain ⟨chi, degree, positive, value, height⟩ := table.positive_height
    have zero := heightZero.height_zero abelian chi degree positive value
    omega
  · exact dihedral
  · exact (quaternion.not_two quaternionGroup two).elim

end ManuscriptIBAW.TypeB.DefectEight

/-
This file accompanies Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It formalises selected arguments under the explicit assumptions described
in this package's formalisation report.
-/
