import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterTrivialAD3Assembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction

/-! Actual block induction on the SAME completed AD3 family. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterTrivialBlockAssembly

open ModularRep ModularRep.CharacterWeight Formalisation
open TypeBCentralKernelNormalizerInertia (localAut rightTwist_eq_iff_local_fixed)
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryTransport

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "A" => (MulAut G)ᵐᵒᵖ
local notation "S" => FaithfulSector (k := k) (X := G)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "pX" => faithfulBrauerSector iota hinj blocks R E1
local notation "pY" => faithfulWeightSector iota hinj blocks R E1

local notation "hpX" => brauerProjection_equivariant iota hinj blocks R E1
local notation "hpY" => weightProjection_equivariant iota hinj blocks R E1

open CyclicOuterLemma37Concrete
open TypeBCentralKernelWeightTransport (localMk)
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
open SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings
open SporadicFi24P3Definition44NamedCarrierOriginalPairComparison
open SporadicFi24P3Definition44NamedCarrierFaithfulFamilyComparison

open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryAssembly
open SporadicFi24P3Definition44NamedCarrierFaithfulAD3Assembly
open SporadicFi24P3Definition44NamedCarrierOuterTrivialNormalizerAction

open SporadicFi24P3Definition44NamedCarrierOuterTrivialAD3Assembly
open SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction

/-- Preserve the completed AD3 witness and add block induction for every matched row. -/
theorem outer_trivial_manuscript_block_assembly
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1)
    (hcard : Nat.card (Subgroup.center G) = 1 ∨ Nat.card (Subgroup.center G) = 2)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (nu0 : FaithfulSector (k := k) (X := G)) :
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let inj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    let bP := faithfulBrauerSector iota inj bs R routine
    let wP := faithfulWeightSector iota inj bs R routine
    ∀ (e0 : Fibre bP nu0 ≃ Fibre wP nu0),
      BaseBlockPreserving iota inj R bs routine nu0 e0 →
      ∃ (e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine)
        (hFamily : FamilyProperties iota inj bs R routine e),
        (∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0) ∧
        StableMatchedOrdinaryFixed iota inj bs R routine e ∧
        FaithfulAD3Output iota inj bs R routine e hFamily.1 ∧
        MatchedBlockOutput iota inj R bs routine e := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro e0 hblock
  obtain ⟨e, hFamily, hIndependent, hFixed, hAD3⟩ :=
    SporadicFi24P3Definition44NamedCarrierOuterTrivialAD3Assembly.outer_trivial_manuscript_ad3_assembly iota R hOuter hcard compatibility availability nu0 e0
  exact ⟨e, hFamily, hIndependent, hFixed, hAD3,
    matched_block_output_of_base iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R R.1.operations.ambientBlockData.blocks ⟨⟩ nu0
      (hcard.elim Or.inl (fun h => Or.inr (Or.inl h))) e0 hblock e hIndependent compatibility⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterTrivialBlockAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
