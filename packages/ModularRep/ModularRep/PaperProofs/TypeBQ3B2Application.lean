import ModularRep.PaperProofs.TypeBQ3B2DihedralDefect
import ModularRep.PaperProofs.TypeBQ3B2WeightFixedness
import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier

/-!
The actual B2 deduction on the retained triple-cover carrier: its nominated
specified defect is D8, and the complete actual weight fibre consists of two
classes with different canonical radical orders, both fixed by every block
automorphism. The actual Brauer count is derived from its complete table
dictionary. No matching or fixed-block criterion is an input or conclusion.

The carrier is the same quotient of the free-presentation cover of the
matrix Omega group over ZMod 3 used by the accepted q3 applications. The
source identifications in that construction and in the specified table and
published statements remain conditional. No new carrier is substituted.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B2Application

open ModularRep CharacterWeight
open Formalisation.ComputationArithmetic
open TypeBQ3TripleCoverCarrier
open TypeBExceptionalQ3Proposition416Actual
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction
open TypeBQ3B2DihedralDefect TypeBQ3B2WeightFixedness
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open FDRepSimpleClassKZero

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The manuscript's D8 and order-distinguished weight-fixedness deductions,
with every carrier on the same retained actual triple cover. -/
theorem actualTripleCover_B2_defect_and_weights (matrixSource : MatrixExceptionalSource) :
  letI : Finite X := finite_X matrixSource
  ∀ (root : PrimeRegularRootEmbedding 2 k K X)
    (Msys : ModularSystem 2 K O k)
    (calibration : RootResidueCompatible Msys root)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
    (navarro : ∀ W : CharacterWeight 2 K X,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys (localQuotientRoot root W.subgroup)
        (localRoot_residueCanonical Msys root calibration W.subgroup))
    (d : Q3Block → k[X]) (blocks : BlockIdempotentDecomposition d)
    (ordinary : PhysicalOrdinarySource blocks Msys root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root))
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D)
    (table : PhysicalTableSource blocks Msys root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) ordinary D)
    (classification : OrderEightClassificationSource D)
    (heightZero : AbelianHeightZeroSource blocks Msys root calibration
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) ordinary D defect)
    (quaternion : QuaternionTwoBrauerSource blocks Msys root calibration
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) ordinary D defect)
    (R : LocalBlockInductionSource (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (physical : GuardedBlockCompatibility root R.operations)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent
      (primitiveBlockOfLabel blocks .B2) = d .B2)
    (sambale : SambaleKessarB2OrderSource Msys root calibration navarro
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks R physical ambientAt)
    (brauerMap : LiteralBrauerOutputMap root)
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible : BrauerBlockFibreCompatible root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks brauerMap),
    Nonempty (D ≃* DihedralGroup 4) ∧
    ∃ weightEight weightFour : R.Fibre (primitiveBlockOfLabel blocks .B2),
      radicalOrder weightEight.val = 8 ∧
      radicalOrder weightFour.val = 4 ∧
      (∀ weight : R.Fibre (primitiveBlockOfLabel blocks .B2),
        weight = weightEight ∨ weight = weightFour) ∧
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B2)) = 2 ∧
      ∀ (alpha : actualBlockStabilizer blocks .B2)
        (weight : R.Fibre (primitiveBlockOfLabel blocks .B2)),
        alpha • weight = weight := by
  letI : Finite X := finite_X matrixSource
  intro root Msys calibration ordinaryRoots navarro d blocks ordinary D defect table
    classification heightZero quaternion R physical ambientAt sambale brauerMap
    brauerMap_injective brauerMap_surjective brauerBlock_compatible
  let hinj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding root
  have dihedral := TypeBQ3B2DihedralDefect.defect_is_dihedral blocks Msys root
    calibration hinj ordinary D defect table classification heightZero quaternion
    brauerMap brauerMap_injective brauerMap_surjective brauerBlock_compatible
  have brauerCard : Nat.card (ActualBrauerFibre root hinj blocks .B2) = 2 := by
    calc
      Nat.card (ActualBrauerFibre root hinj blocks .B2) =
          Nat.card (BrauerOutputFibre .B2) :=
        Nat.card_congr (brauerBlockFibreEquiv root hinj blocks brauerMap
          brauerMap_injective brauerMap_surjective brauerBlock_compatible .B2).symm
      _ = Fintype.card (BrauerOutputFibre .B2) := Nat.card_eq_fintype_card
      _ = q3BrauerCount .B2 := brauerOutputFibre_card .B2
      _ = 2 := rfl
  exact ⟨dihedral, weight_orders_card_and_fixed Msys root calibration navarro hinj
    blocks R physical ambientAt sambale D defect dihedral brauerCard⟩

end ModularRep.PaperProofs.TypeBQ3B2Application


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
