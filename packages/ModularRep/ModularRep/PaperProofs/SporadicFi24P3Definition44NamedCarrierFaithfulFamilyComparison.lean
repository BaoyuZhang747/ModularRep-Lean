import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPairComparison

/-! One transported faithful-sector family with the actual original-pair
comparisons. Both central scalar equations are derived from the specified
sectors. Correctness holds for every retained canonical reduction; the
existence consequence uses only availability of reductions at actual matches. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFamilyComparison

open ModularRep Formalisation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings
open SporadicFi24P3Definition44NamedCarrierOriginalPairComparison

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

/-- The concrete comparison at the scalar character computed from the
original specified Brauer block. Only an output abbreviation. -/
def PhysicalPairComparison (phi : IBr iota) (V : CharacterWeight p K G)
    (source : CanonicalRawReduction iota V) : Prop :=
  OriginalPairComparison iota (brauerSector iota hinj blocks phi)
    (scalarBrauer iota hinj blocks phi) V source

/-- Universal comparison and its nonvacuous existence consequence. The
availability premise gives only canonical reductions of actual matches. -/
def MatchedComparisons (e : FB ≃ FW) : Prop :=
  (∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) = (e phi).val →
    ∀ source : CanonicalRawReduction iota V,
      PhysicalPairComparison iota hinj blocks phi.val V source) ∧
  ((∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) = (e phi).val →
    Nonempty (CanonicalRawReduction iota V)) →
    ∀ (phi : FB) (V : CharacterWeight p K G),
      (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) = (e phi).val →
      ∃ source : CanonicalRawReduction iota V,
        PhysicalPairComparison iota hinj blocks phi.val V source)

theorem outer_trivial_physical_pair
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (phi : IBr iota) (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1)
    (hsector : weightSector (R := R)
      (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
        brauerSector iota hinj blocks phi) :
    PhysicalPairComparison iota hinj blocks phi V source :=
  outer_trivial_pair_comparison iota _ (scalarBrauer iota hinj blocks phi) V source hOuter
    (rawWeightSector_scalar iota R V source compatibility _ hsector)

theorem family_with_comparisons
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (nu0 : S) (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (tau : MulAut G)
    (hcard : Nat.card (Subgroup.center G) = 3 ∨
      Nat.card (Subgroup.center G) = 4 ∨ Nat.card (Subgroup.center G) = 6)
    (hinverts : ∀ z : Subgroup.center G, tau (z : G) = (z : G)⁻¹)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ e : FB ≃ FW, FamilyProperties iota hinj blocks R E1 e ∧
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      MatchedComparisons iota hinj blocks R E1 e := by
  have hcase : FaithfulSectorOrbitCases (G := G) :=
    Or.inr (Or.inr ⟨hcard, tau, hinverts⟩)
  obtain ⟨e, hFamily, hIndependent⟩ := family_from_sector_orbit iota hinj blocks R E1 nu0
    (faithfulSector_orbit nu0 hcase) e0 he0
  have hcomp : ∀ (phi : FB) (V : CharacterWeight p K G),
      (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) = (e phi).val →
      ∀ source : CanonicalRawReduction iota V,
        PhysicalPairComparison iota hinj blocks phi.val V source := by
    intro phi V hmatch source
    have hsector : weightSector (R := R)
        (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
          brauerSector iota hinj blocks phi.val := by
      rw [hmatch]
      exact congrArg Subtype.val (hFamily.2.1 phi)
    exact faithful_pair_comparison iota _ (scalarBrauer iota hinj blocks phi.val) V source
      phi.faithful hOuter tau hcard hinverts
      (rawWeightSector_scalar iota R V source compatibility _ hsector)
  refine ⟨e, hFamily, hIndependent, hcomp, ?_⟩
  intro availability phi V hmatch
  obtain ⟨source⟩ := availability phi V hmatch
  exact ⟨source, hcomp phi V hmatch source⟩

/-- The manuscript's same-family faithful-centres3/4/6 comparison. Only
the original specified operations and canonical block compatibility are
added to the base-sector bijection and actual group facts. The family is
chosen before reductions; every available reduction receives the concrete
original-pair comparison with both scalar bindings derived. -/
theorem faithful_family_equivariant_comparison
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (nu0 : FaithfulSector (k := k) (X := G))
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (tau : MulAut G)
    (hcard : Nat.card (Subgroup.center G) = 3 ∨
      Nat.card (Subgroup.center G) = 4 ∨ Nat.card (Subgroup.center G) = 6)
    (hinverts : ∀ z : Subgroup.center G, tau (z : G) = (z : G)⁻¹) :
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let inj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    let bP := faithfulBrauerSector iota inj bs R routine
    let wP := faithfulWeightSector iota inj bs R routine
    ∀ (e0 : Fibre bP nu0 ≃ Fibre wP nu0),
      (∀ (a : (MulAut G)ᵐᵒᵖ) (ha : a • nu0 = nu0) (x : Fibre bP nu0),
        e0 (stabilizerFibreEquiv bP
          (brauerProjection_equivariant iota inj bs R routine) nu0 a ha x) =
          stabilizerFibreEquiv wP
            (weightProjection_equivariant iota inj bs R routine) nu0 a ha (e0 x)) →
      ∃ e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine,
        FamilyProperties iota inj bs R routine e ∧
        (∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0) ∧
        MatchedComparisons iota inj bs R routine e := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact family_with_comparisons iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ compatibility nu0 hOuter tau hcard hinverts

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFamilyComparison


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
