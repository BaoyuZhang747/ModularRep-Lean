import ModularRep.PaperProofs.TypeBExceptionalQ3CanonicalInnerRangeActual
import ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting
import ModularRep.PaperProofs.TypeBLiteralBlockReindex
import ModularRep.PaperProofs.TypeBLocalReductionInstantiation
import ModularRep.OrdinaryBlockFibre
import ModularRep.Navarro417DefectSource
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
The B2 defect elimination on its actual subgroup and character fibres.

The elementary order-eight classification uses literal group isomorphisms.
The height-zero source is only the abelian-defect implication of the
Malle--Navarro--Schaeffer Fry--Tiep corollary, with height expressed through
the degree and group-order valuations. Its Theorem A concerns odd primes;
the corollary and the previously established abelian implication apply here.
Macgregor's quaternion decomposition matrices, Section 2, give six ordinary
characters when the defect group is Q8 and there are two Brauer characters.
These are separate E1/E2 statements on the same specified block.

The E3/U table binding supplies the actual ordinary-fibre count, the order of
the nominated Navarro defect subgroup, and a supported ordinary character
whose degree has positive height. It supplies no abstract height predicate.
The ordinary selector is fixed to actual stable-reduction multiplicities in
the displayed modular system; its literal decomposition is derived from the
same named block decomposition. Ordinary roots and residue calibration remain
explicit, and no ordinary algebraic closure is imposed.

The existing three-case elimination is reused internally. This file adds the
specified bindings and returns an isomorphism type for the actual subgroup.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B2DihedralDefect

open Formalisation.ComputationArithmetic
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative
open ModularRep.PaperProofs.TypeBLocalReductionInstantiation

variable {k K O X : Type}
variable [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
variable [CharZero K] [CharP k 2] [IsAlgClosed k]
variable [Group X] [Fintype X]
variable {blockIdempotent : Q3Block → k[X]}

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The specified ordinary selector on the literal reindexing of the SAME
complete decomposition. The finite block enumeration is constructed. -/
abbrev PhysicalOrdinarySource
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity root)
    [HasEnoughRootsOfUnity K (Nat.card X)] : Type :=
  letI := TypeBLiteralBlockReindex.literalBlockFintype blocks
  TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys root hinj
    (TypeBLiteralBlockReindex.literalBlocks blocks)

/-- The complete specified ordinary-character fibre of the named B2. -/
abbrev OrdinaryFibre
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity root)
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (ordinary : PhysicalOrdinarySource blocks Msys root hinj) : Type :=
  letI := TypeBLiteralBlockReindex.literalBlockFintype blocks
  OrdinaryBlockFibre.OrdinaryBlockFibre ordinary.physical.ordinaryBlock
    (primitiveBlockOfLabel blocks .B2)

/-- The elementary classification, restricted to the displayed finite group.
All three alternatives have their actual group-theoretic meanings. -/
structure OrderEightClassificationSource (T : Type) [Group T] [Finite T] : Prop where
  classified : Nat.card T = 8 →
    IsMulCommutative T ∨ Nonempty (T ≃* DihedralGroup 4) ∨
      Nonempty (T ≃* QuaternionGroup 2)

/-- The table claim is about an actual character in the complete specified
fibre and its actual degree. The strict inequality is the positive-height
condition, written without introducing a height function or predicate. -/
structure PhysicalTableSource
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity root)
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (ordinary : PhysicalOrdinarySource blocks Msys root hinj)
    (D : Subgroup X) : Prop where
  defect_order : Nat.card D = 8
  ordinary_card : Nat.card (OrdinaryFibre blocks Msys root hinj ordinary) = 5
  positive_height : ∃ chi : OrdinaryFibre blocks Msys root hinj ordinary,
    ∃ degree : Nat, 0 < degree ∧ chi.val 1 = (degree : K) ∧
      (Nat.card X).factorization 2 <
        degree.factorization 2 + (Nat.card D).factorization 2

/-- The needed direction of height zero on this specified block and defect.
The degree equality is in the same ordinary field as its actual character. -/
structure AbelianHeightZeroSource
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity root)
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (ordinary : PhysicalOrdinarySource blocks Msys root hinj)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D) : Prop where
  height_zero : IsMulCommutative D →
    ∀ chi : OrdinaryFibre blocks Msys root hinj ordinary, ∀ degree : Nat,
      0 < degree → chi.val 1 = (degree : K) →
      degree.factorization 2 + (Nat.card D).factorization 2 =
        (Nat.card X).factorization 2

/-- Macgregor's Q8, two-Brauer-character numerical consequence. Both counts
refer to the same primitive idempotent and displayed modular system. -/
structure QuaternionTwoBrauerSource
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity root)
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (ordinary : PhysicalOrdinarySource blocks Msys root hinj)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D) : Prop where
  ordinary_card_six : Nonempty (D ≃* QuaternionGroup 2) →
    Nat.card (ActualBrauerFibre root hinj blocks .B2) = 2 →
    Nat.card (OrdinaryFibre blocks Msys root hinj ordinary) = 6

/-- The named Brauer table supplies l(B2)=2, and the existing elimination
then gives D8 for the actual Navarro defect subgroup. -/
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
    (heightZero : AbelianHeightZeroSource blocks Msys root calibration hinj
      ordinary D defect)
    (quaternion : QuaternionTwoBrauerSource blocks Msys root calibration hinj
      ordinary D defect)
    (brauerMap : LiteralBrauerOutputMap root)
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible :
      BrauerBlockFibreCompatible root hinj blocks brauerMap) :
    Nonempty (D ≃* DihedralGroup 4) := by
  have brauer_card : Nat.card (ActualBrauerFibre root hinj blocks .B2) = 2 := by
    calc
      Nat.card (ActualBrauerFibre root hinj blocks .B2) =
          Nat.card (BrauerOutputFibre .B2) :=
        Nat.card_congr (brauerBlockFibreEquiv root hinj blocks brauerMap
          brauerMap_injective brauerMap_surjective brauerBlock_compatible .B2).symm
      _ = Fintype.card (BrauerOutputFibre .B2) := Nat.card_eq_fintype_card
      _ = q3BrauerCount .B2 := brauerOutputFibre_card .B2
      _ = 2 := rfl
  let input : BlockTwoDefectInput (Subgroup X) :=
    { defect := D
      IsAbelian := fun Q => IsMulCommutative Q
      IsDihedral := fun Q => Nonempty (Q ≃* DihedralGroup 4)
      IsQuaternion := fun Q => Nonempty (Q ≃* QuaternionGroup 2)
      classified := classification.classified table.defect_order
      positiveHeight_excludes_abelian := by
        intro abelian
        obtain ⟨chi, degree, positive, value, height⟩ := table.positive_height
        have zero := heightZero.height_zero abelian chi degree positive value
        omega
      ordinaryCharacterCount := Nat.card (OrdinaryFibre blocks Msys root hinj ordinary)
      ordinaryCharacterCount_eq_five := table.ordinary_card
      quaternion_forces_six_characters := fun h =>
        quaternion.ordinary_card_six h brauer_card }
  exact BlockTwoDefectInput.defect_is_dihedral input

end ModularRep.PaperProofs.TypeBQ3B2DihedralDefect


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
