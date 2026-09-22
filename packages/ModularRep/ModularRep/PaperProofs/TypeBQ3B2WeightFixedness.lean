import ModularRep.PaperProofs.TypeBQ3FaithfulDihedralCounts
import ModularRep.CharacterWeightRadicalOrderFixedness

/-!
The refined weight census for the literal B2 block follows the D8 defect
deduction. Sambale, Theorem 4.1 and its proof (the retained source text at
lines 90--114, 214--220 and 274), together with the support-preserving
weight correspondence in Kessar, Introduction to block theory (2007),
Proposition 5.5 and its proof at lines 1038--1057 and Propositions 5.6--5.7
through line 1083, supplies two weight classes supported at orders eight
and four. The line references refer to the retained source extraction.

The one-way source below is indexed by the same modular system, ambient
root, all-raw scoped reductions, specified local selectors and literal B2
idempotent as the actual fibre. Identifying the published block and weight
correspondence with these objects remains an explicit source interpretation.
The Navarro (4.11) witness and the equivalence to DihedralGroup 4 are inputs
to its sole field; the field supplies neither a free order function nor an
automorphism action. Cardinality and fixedness under the complete actual
block stabilizer are deductions from the two different canonical orders.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B2WeightFixedness

open Formalisation.ComputationArithmetic
open ModularRep CharacterWeight
open TypeBExceptionalQ3Proposition416Actual
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

variable {k K O X : Type}
variable [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
variable [CharZero K] [CharP k 2] [IsAlgClosed k]
variable [Group X] [Fintype X]
variable {blockIdempotent : Q3Block → k[X]}

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The refined D8 census, scoped to the complete specified B2 weight fibre. -/
structure SambaleKessarB2OrderSource
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
    (R : LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (physicalCompatibility : GuardedBlockCompatibility iota R.operations)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent
      (primitiveBlockOfLabel blocks .B2) = blockIdempotent .B2) : Prop where
  weight_orders : ∀ D : Subgroup X,
    Navarro411DefectRepresentative (p := 2) blocks .B2 D →
    Nonempty (D ≃* DihedralGroup 4) →
    Nat.card (ActualBrauerFibre iota hinj blocks .B2) = 2 →
    ∃ weightEight weightFour : R.Fibre (primitiveBlockOfLabel blocks .B2),
      radicalOrder weightEight.val = 8 ∧
      radicalOrder weightFour.val = 4 ∧
      ∀ weight : R.Fibre (primitiveBlockOfLabel blocks .B2),
        weight = weightEight ∨ weight = weightFour

variable (Msys : ModularSystem 2 K O k)
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
  (R : LocalBlockInductionSource
    (p := 2) (k := k) (K := K) (G := X)
    (Block := PrimitiveBlock k X))
  (physicalCompatibility : GuardedBlockCompatibility iota R.operations)
  (ambientAt : R.operations.ambientBlockData.blockIdempotent
    (primitiveBlockOfLabel blocks .B2) = blockIdempotent .B2)
  (source : SambaleKessarB2OrderSource Msys iota calibration navarro hinj blocks R
    physicalCompatibility ambientAt)

include source in
/-- The same two witnesses give cardinality two and full stabilizer fixedness. -/
theorem weight_orders_card_and_fixed
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D)
    (dihedral : Nonempty (D ≃* DihedralGroup 4))
    (brauerCard : Nat.card (ActualBrauerFibre iota hinj blocks .B2) = 2) :
    ∃ weightEight weightFour : R.Fibre (primitiveBlockOfLabel blocks .B2),
      radicalOrder weightEight.val = 8 ∧
      radicalOrder weightFour.val = 4 ∧
      (∀ weight : R.Fibre (primitiveBlockOfLabel blocks .B2),
        weight = weightEight ∨ weight = weightFour) ∧
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B2)) = 2 ∧
      ∀ (alpha : actualBlockStabilizer blocks .B2)
        (weight : R.Fibre (primitiveBlockOfLabel blocks .B2)),
        alpha • weight = weight := by
  obtain ⟨weightEight, weightFour, orderEight, orderFour, exhaustive⟩ :=
    source.weight_orders D defect dihedral brauerCard
  have distinct : weightEight ≠ weightFour := by
    intro same
    have orders := congrArg
      (fun weight : R.Fibre (primitiveBlockOfLabel blocks .B2) => radicalOrder weight.val)
      same
    omega
  have card : Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B2)) = 2 := by
    apply Nat.card_eq_two_iff.mpr
    refine ⟨weightEight, weightFour, distinct, ?_⟩
    apply Set.eq_univ_of_forall
    intro weight
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using exhaustive weight
  have fixed : ∀ (alpha : actualBlockStabilizer blocks .B2)
      (weight : R.Fibre (primitiveBlockOfLabel blocks .B2)),
      alpha • weight = weight :=
    EquivariantBlockAssignment.fibre_smul_eq_self_of_orders_eight_four
      R.equivariantBlockAssignment (primitiveBlockOfLabel blocks .B2)
      weightEight weightFour exhaustive orderEight orderFour
  exact ⟨weightEight, weightFour, orderEight, orderFour, exhaustive, card, fixed⟩

include source in
/-- The actual B2 fibre has two points and its full block stabilizer fixes both. -/
theorem weight_fibre_card_and_fixed
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D)
    (dihedral : Nonempty (D ≃* DihedralGroup 4))
    (brauerCard : Nat.card (ActualBrauerFibre iota hinj blocks .B2) = 2) :
    Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B2)) = 2 ∧
      ∀ (alpha : actualBlockStabilizer blocks .B2)
        (weight : R.Fibre (primitiveBlockOfLabel blocks .B2)),
        alpha • weight = weight := by
  obtain ⟨_, _, _, _, _, card, fixed⟩ :=
    weight_orders_card_and_fixed Msys iota calibration navarro hinj blocks R
      physicalCompatibility ambientAt source D defect dihedral brauerCard
  exact ⟨card, fixed⟩

end ModularRep.PaperProofs.TypeBQ3B2WeightFixedness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
