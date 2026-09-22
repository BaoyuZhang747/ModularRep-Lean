import ModularRep.PaperProofs.TypeBExceptionalQ3CanonicalInnerRangeActual
import ModularRep.PaperProofs.TypeBQ3FaithfulLocalReduction
import ModularRep.Navarro417DefectSource
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
The two small faithful blocks have dihedral defect of order eight in
Macgregor's exceptional-cover classification. Identifying those blocks with
the displayed B8/B9 idempotents is the explicit group and table binding below.

Sambale, Blocks with defect group D_{2^n} x C_{2^m}, Theorem 4.1 and its
proof, specialized to n=3 and m=0, give the one-way consequence that a D8
block with two Brauer characters has two weight classes. The source here
retains the same complete modular system, its actual root residue equation,
and enough ordinary roots for the group order.

The source interpretation includes Navarro (3.18), (4.8), and the weight
convention on p. 90: a defect-zero quotient block determines its unique
ordinary character and irreducible Brauer reduction, with the same quotient,
inflation, and conjugacy relation. Navarro (4.11) authenticates the nominated
defect subgroup through the literal central Brauer map. These are E1 inputs
in the E2 dihedral numerical specialization; identifying the published groups,
blocks, roots, and sets of weights with the displayed objects is U.

The all-raw GuardedBlockCompatibility index is essential. It identifies the
inflated local selector for every raw weight through its specified irreducible
reduction. The fixed-X family of scoped Navarro sources is a separate index,
so every required reduction exists in the displayed root convention.
Together with the complete normalizer and ambient catalogues already stored
by R, and the displayed ambient idempotent equality at the fixed block, it
identifies the complete specified fibre. It is not merely soundness for weights
already assigned to that fibre. No ordinary algebraic closure is required.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3FaithfulDihedralCounts

open Formalisation.ComputationArithmetic
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual
open ModularRep.PaperProofs.TypeBLocalReductionInstantiation
open ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily
open ModularRep.PaperProofs.TypeBQ3FaithfulLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

variable {k K O X : Type}
variable [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
variable [CharZero K] [CharP k 2] [IsAlgClosed k]
variable [Group X] [Fintype X]
variable {blockIdempotent : Q3Block → k[X]}

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Macgregor's two D8 blocks, bound to precisely the displayed idempotents.
The Navarro support witness includes independent evidence that D is a
2-group and the exact central-Brauer-support characterization. -/
structure MacgregorD8DefectSource
    (blocks : BlockIdempotentDecomposition blockIdempotent) : Prop where
  blockEight : ∃ D : Subgroup X,
    Navarro411DefectRepresentative (p := 2) blocks .B8 D ∧
      Nonempty (D ≃* DihedralGroup 4)
  blockNine : ∃ D : Subgroup X,
    Navarro411DefectRepresentative (p := 2) blocks .B9 D ∧
      Nonempty (D ≃* DihedralGroup 4)

/-- The authenticated defect witness implies maximality in the literal
nonzero central Brauer support, with no freely supplied defect predicate. -/
theorem defect_isMaximal
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : Q3Block) (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks block D) :
    IsMaximalCentralBrauerDefect (p := 2) blocks block D :=
  IsMaximalNonzeroPSubgroup.of_nonzero_iff_isSubconjugate
    defect.isPGroup defect.support411.nonzero_iff_isSubconjugate

/-- The fixed-block Sambale numerical consequence on the actual carriers.
The complete specified weight interpretation is indexed before the numerical
field; the source supplies no matching, action, extension, or criterion. -/
structure SambaleD8CountSource
    (Msys : ModularSystem 2 K O k)
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys iota)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
    (navarro : ∀ W : CharacterWeight 2 K X,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys
        (localQuotientRoot iota W.subgroup)
        (localRoot_residueCanonical Msys iota calibration W.subgroup))
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (physicalCompatibility : GuardedBlockCompatibility iota R.operations)
    (block : Q3Block)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent
      (primitiveBlockOfLabel blocks block) = blockIdempotent block) : Prop where
  weight_card_two : ∀ D : Subgroup X,
    Navarro411DefectRepresentative (p := 2) blocks block D →
    Nonempty (D ≃* DihedralGroup 4) →
    Nat.card (ActualBrauerFibre iota hinj blocks block) = 2 →
    Nat.card (R.Fibre (primitiveBlockOfLabel blocks block)) = 2

/-- The literal Brauer output table supplies both numerical premises before
the two fixed-block dihedral statements are applied. -/
theorem weight_fibre_cards
    (Msys : ModularSystem 2 K O k)
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys iota)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
    (navarro : ∀ W : CharacterWeight 2 K X,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys
        (localQuotientRoot iota W.subgroup)
        (localRoot_residueCanonical Msys iota calibration W.subgroup))
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (physicalCompatibility : GuardedBlockCompatibility iota R.operations)
    (ambientAtEight : R.operations.ambientBlockData.blockIdempotent
      (primitiveBlockOfLabel blocks .B8) = blockIdempotent .B8)
    (ambientAtNine : R.operations.ambientBlockData.blockIdempotent
      (primitiveBlockOfLabel blocks .B9) = blockIdempotent .B9)
    (brauerMap : LiteralBrauerOutputMap iota)
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible :
      BrauerBlockFibreCompatible iota hinj blocks brauerMap)
    (macgregor : MacgregorD8DefectSource blocks)
    (sambaleEight : SambaleD8CountSource Msys iota calibration navarro hinj blocks R
      physicalCompatibility .B8 ambientAtEight)
    (sambaleNine : SambaleD8CountSource Msys iota calibration navarro hinj blocks R
      physicalCompatibility .B9 ambientAtNine) :
    Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B8)) = 2 ∧
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B9)) = 2 := by
  have brauer_card : ∀ block : Q3Block,
      (block = .B8 ∨ block = .B9) →
      Nat.card (ActualBrauerFibre iota hinj blocks block) = 2 := by
    intro block hblock
    calc
      Nat.card (ActualBrauerFibre iota hinj blocks block) =
          Nat.card (BrauerOutputFibre block) :=
        Nat.card_congr (brauerBlockFibreEquiv iota hinj blocks brauerMap
          brauerMap_injective brauerMap_surjective brauerBlock_compatible block).symm
      _ = Fintype.card (BrauerOutputFibre block) := Nat.card_eq_fintype_card
      _ = q3BrauerCount block := brauerOutputFibre_card block
      _ = 2 := by rcases hblock with rfl | rfl <;> rfl
  obtain ⟨D8, defectEight, dihedralEight⟩ := macgregor.blockEight
  obtain ⟨D9, defectNine, dihedralNine⟩ := macgregor.blockNine
  exact ⟨sambaleEight.weight_card_two D8 defectEight dihedralEight
      (brauer_card .B8 (Or.inl rfl)),
    sambaleNine.weight_card_two D9 defectNine dihedralNine
      (brauer_card .B9 (Or.inr rfl))⟩

end ModularRep.PaperProofs.TypeBQ3FaithfulDihedralCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
