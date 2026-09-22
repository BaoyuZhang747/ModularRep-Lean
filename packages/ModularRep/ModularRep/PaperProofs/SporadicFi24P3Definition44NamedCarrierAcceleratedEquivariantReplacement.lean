import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSpathPartition
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFamilyComparison

/-! Lemma5.5: choose the translated family once, and attach the actual ordinary
partition and actual character-triple comparisons to that same family.
Structural and canonical realization inputs retain their published/binding scope.
No comparison, partition, or caller-selected predicate is supplied as an input. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedEquivariantReplacement
open ModularRep Formalisation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulSpathPartition
open SporadicFi24P3Definition44NamedCarrierFaithfulFamilyComparison
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison
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
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (availability : LocalCanonicalAvailability iota)
include compatibility availability

theorem centerless_partition_and_comparison
    (nu0 : S) (hcenter : Subgroup.center G = ⊥)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      OrdinaryPartitionOutput iota hinj blocks R E1 e hFamily.1 ∧
      CenterlessMatchedComparisons iota hinj blocks R E1 hcenter e hFamily.1 := by
  obtain ⟨e, hFamily, hIndependent, hComparison⟩ :=
    centerless_family_with_comparisons iota hinj blocks R E1 nu0 hcenter hOuter principle e0 he0
  exact ⟨e, hFamily, hIndependent,
    partition_output_of_ordinary_output iota hinj blocks R E1 e hFamily
      (ordinary_output_of_availability iota hinj blocks R E1 e hFamily compatibility availability),
    hComparison⟩

theorem central_two_partition_and_comparison
    {T C : Type u} [Group T] [Group C]
    (E : GroupExtension G T C) (hC : Nat.card C = 2)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (hAut : Function.Surjective E.conjAct) (hZ : Nat.card (Subgroup.center G) = 2)
    (nu0 : S) (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      OrdinaryPartitionOutput iota hinj blocks R E1 e hFamily.1 ∧
      CentralTwoMatchedComparisons iota hinj blocks R E1 E hC hOuter hAut hZ e hFamily.1 := by
  obtain ⟨e, hFamily, hIndependent, hComparison⟩ :=
    central_two_family_with_comparisons iota hinj blocks R E1 E hC hOuter hAut hZ
      compatibility nu0 principle e0 he0
  exact ⟨e, hFamily, hIndependent,
    partition_output_of_ordinary_output iota hinj blocks R E1 e hFamily
      (ordinary_output_of_availability iota hinj blocks R E1 e hFamily compatibility availability),
    hComparison⟩

theorem faithful_partition_and_comparison
    (nu0 : S) (hOuter : Nat.card (LiteralOuterQuotient G) = 2) (tau : MulAut G)
    (hcard : Nat.card (Subgroup.center G) = 3 ∨
      Nat.card (Subgroup.center G) = 4 ∨ Nat.card (Subgroup.center G) = 6)
    (hinverts : ∀ z : Subgroup.center G, tau (z : G) = (z : G)⁻¹)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      OrdinaryPartitionOutput iota hinj blocks R E1 e hFamily.1 ∧
      MatchedComparisons iota hinj blocks R E1 e := by
  obtain ⟨e, hFamily, hIndependent, hComparison⟩ :=
    family_with_comparisons iota hinj blocks R E1 compatibility
      nu0 hOuter tau hcard hinverts e0 he0
  exact ⟨e, hFamily, hIndependent,
    partition_output_of_ordinary_output iota hinj blocks R E1 e hFamily
      (ordinary_output_of_availability iota hinj blocks R E1 e hFamily compatibility availability),
    hComparison⟩

theorem outer_trivial_partition_and_comparison
    (nu0 : S) (hcase : FaithfulSectorOrbitCases (G := G))
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      OrdinaryPartitionOutput iota hinj blocks R E1 e hFamily.1 ∧
      MatchedComparisons iota hinj blocks R E1 e := by
  obtain ⟨e, hFamily, hIndependent⟩ :=
    family_from_sector_orbit iota hinj blocks R E1 nu0 (faithfulSector_orbit nu0 hcase) e0 he0
  have hComparison : ∀ (phi : FB) (V : CharacterWeight p K G),
      (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) = (e phi).val →
      ∀ source : CanonicalRawReduction iota V,
        PhysicalPairComparison iota hinj blocks phi.val V source := by
    intro phi V hmatch source
    have hsector : weightSector (R := R)
        (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
          brauerSector iota hinj blocks phi.val := by
      rw [hmatch]
      exact congrArg Subtype.val (hFamily.2.1 phi)
    exact outer_trivial_physical_pair iota hinj blocks R compatibility phi.val V source hOuter hsector
  refine ⟨e, hFamily, hIndependent,
    partition_output_of_ordinary_output iota hinj blocks R E1 e hFamily
      (ordinary_output_of_availability iota hinj blocks R E1 e hFamily compatibility availability),
    hComparison, ?_⟩
  intro rawAvailability phi V hmatch
  obtain ⟨source⟩ := rawAvailability phi V hmatch
  exact ⟨source, hComparison phi V hmatch source⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedEquivariantReplacement


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
