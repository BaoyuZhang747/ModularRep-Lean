import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBQ3FaithfulLocalReduction
import ModularRep.CharacterWeightRadicalOrderFixedness
import ModularRep.Navarro417DefectSource
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
The fixed D8 census is stated on the literal dominated block of matrix G3.
Its complete Brauer fibre is defined by actual representation support. The
ambient block decomposition and all local catalogues are those of the same
weight operations; only the selected ambient idempotent is identified here.

The one-way numerical statement is the same specialization of Sambale,
Theorem 4.1 and its proof, and Kessar, Proposition 5.5 and Propositions 5.6--5.7,
as the accepted B2 order census. This instance concerns the actual downstairs
block and remains E2/U independently of the instance on X. Its fixed modular
system, residue calibration, sufficient ordinary roots, all-raw scoped Navarro
reductions, and all-raw specified selector guard identify the complete fibre.
The field supplies two exhaustive weight classes with their canonical radical
orders. Cardinality and full block-stabilizer fixedness are derived below.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B2DownstairsWeights

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The fixed-block numerical statement on the complete specified G3 fibre. -/
structure SambaleKessarOrderSource
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K G3)
    (calibration : RootResidueCompatible Msys root)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card G3)]
    (navarro : ∀ W : CharacterWeight 2 K G3,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys
        (localQuotientRoot root W.subgroup)
        (localRoot_residueCanonical Msys root calibration W.subgroup))
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (physical : GuardedBlockCompatibility root R.operations)
    (b : LiteralPrimitiveBlock k G3)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val) : Prop where
  weight_orders :
    letI := R.operations.ambientBlockData.fintypeBlock
    ∀ D : Subgroup G3,
      Navarro411DefectRepresentative (p := 2) R.operations.ambientBlockData.blocks b D →
      Nonempty (D ≃* DihedralGroup 4) →
      Nat.card (BrauerFibre root b) = 2 →
      ∃ weightEight weightFour : R.Fibre b,
        radicalOrder weightEight.val = 8 ∧
        radicalOrder weightFour.val = 4 ∧
        ∀ weight : R.Fibre b, weight = weightEight ∨ weight = weightFour

variable (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K G3)
  (calibration : RootResidueCompatible Msys root)
  [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card G3)]
  (navarro : ∀ W : CharacterWeight 2 K G3,
    letI := localOrdinaryRoots (K := K) W.subgroup
    ScopedDefectZeroReductionSource Msys
      (localQuotientRoot root W.subgroup)
      (localRoot_residueCanonical Msys root calibration W.subgroup))
  (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (physical : GuardedBlockCompatibility root R.operations)
  (b : LiteralPrimitiveBlock k G3)
  (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
  (source : SambaleKessarOrderSource Msys root calibration navarro R physical b ambientAt)

include source in
/-- Keep both census witnesses and derive cardinality and actual action fixedness. -/
theorem weight_orders_card_and_fixed
    (D : Subgroup G3)
    (defect :
      letI := R.operations.ambientBlockData.fintypeBlock
      Navarro411DefectRepresentative (p := 2) R.operations.ambientBlockData.blocks b D)
    (dihedral : Nonempty (D ≃* DihedralGroup 4))
    (brauerCard : Nat.card (BrauerFibre root b) = 2) :
    ∃ weightEight weightFour : R.Fibre b,
      radicalOrder weightEight.val = 8 ∧
      radicalOrder weightFour.val = 4 ∧
      (∀ weight : R.Fibre b, weight = weightEight ∨ weight = weightFour) ∧
      Nat.card (R.Fibre b) = 2 ∧
      ∀ (alpha : MulAction.stabilizer (MulAut G3)ᵐᵒᵖ b)
        (weight : R.Fibre b), alpha • weight = weight := by
  letI := R.operations.ambientBlockData.fintypeBlock
  obtain ⟨weightEight, weightFour, orderEight, orderFour, exhaustive⟩ :=
    source.weight_orders D defect dihedral brauerCard
  have distinct : weightEight ≠ weightFour := by
    intro same
    have orders := congrArg (fun weight : R.Fibre b => radicalOrder weight.val) same
    omega
  have card : Nat.card (R.Fibre b) = 2 := by
    apply Nat.card_eq_two_iff.mpr
    refine ⟨weightEight, weightFour, distinct, ?_⟩
    apply Set.eq_univ_of_forall
    intro weight
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using exhaustive weight
  have fixed : ∀ (alpha : MulAction.stabilizer (MulAut G3)ᵐᵒᵖ b)
      (weight : R.Fibre b), alpha • weight = weight :=
    EquivariantBlockAssignment.fibre_smul_eq_self_of_orders_eight_four
      R.equivariantBlockAssignment b weightEight weightFour exhaustive orderEight orderFour
  exact ⟨weightEight, weightFour, orderEight, orderFour, exhaustive, card, fixed⟩

end ModularRep.PaperProofs.TypeBQ3B2DownstairsWeights


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
