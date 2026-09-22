import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulAD3Assembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterTrivialNormalizerAction

/-! Outer-trivial full AD(3) on original G with identity embedding,
constructed on the same ordinary family with the original comparison models. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterTrivialAD3Assembly

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

/-- Equivariance of the reference bijection follows from the actual outer order. -/
theorem baseEquiv_equivariant_of_outer_card_one
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1)
    (nu0 : S) (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0) :
    e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
      stabilizerFibreEquiv pY hpY nu0 a ha (e0 x) := by
  have hb : a • x.val.val = x.val.val := by
    obtain ⟨g, rfl⟩ := innerInverseOpHom_surjective_of_outer_card_one hOuter a
    change MulOpposite.op (MulAut.conj g⁻¹) • x.val.val = x.val.val
    exact inner_fixes_ibr iota g x.val.val
  have hw : a • (e0 x).val.val = (e0 x).val.val := by
    obtain ⟨g, rfl⟩ := innerInverseOpHom_surjective_of_outer_card_one hOuter a
    change MulOpposite.op (MulAut.conj g⁻¹) • (e0 x).val.val = (e0 x).val.val
    exact inner_fixes_weightClass (p := p) (K := K) g (e0 x).val.val
  have hx : stabilizerFibreEquiv pX hpX nu0 a ha x = x := by
    apply Subtype.ext
    change a • x.val = x.val
    exact (faithfulIBr_smul_eq_iff iota hinj blocks R E1 a x.val).mpr hb
  have hy : stabilizerFibreEquiv pY hpY nu0 a ha (e0 x) = e0 x := by
    apply Subtype.ext
    change a • (e0 x).val = (e0 x).val
    exact (faithfulWeight_smul_eq_iff iota hinj blocks R E1 a (e0 x).val).mpr hw
  rw [hx, hy]

omit [Invertible (Fintype.card (Subgroup.center G) : k)] in
/-- Full original-group action data under trivial actual outer quotient. -/
theorem outer_trivial_action_output (chi : IBr iota)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1) (V : CharacterWeight p K G) :
    FaithfulActionOutput iota chi V := by
  refine ⟨(fun _ _ h => h), inferInstance, ?_, inner_brauer_fixed iota chi,
    normalizerAction_mem_range_iff_of_outer_card_one iota chi hOuter V.subgroup,
    ?_, rawIsoClass_stabilizer_comap_eq V, ordinary_fixed V, localAut_conj V.subgroup⟩
  · rw [Subgroup.map_id]
  · intro g
    exact ⟨g, 1, by simp⟩

/-- Enrich one already constructed ordinary family, preserving every row. -/
theorem outer_trivial_ad3_output_of_ordinary
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1)
    (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (hOrdinary : OrdinaryLocalOutput iota hinj blocks R E1 e hFamily.1) :
    FaithfulAD3Output iota hinj blocks R E1 e hFamily.1 := by
  have hOld : FaithfulOrdinaryOutput iota hinj blocks R E1 e hFamily.1 := by
    obtain ⟨Omega, hclass, hcovariance, hfixed⟩ := hOrdinary
    refine ⟨Omega, hclass, hcovariance, hfixed, ?_⟩
    intro nu Q phi
    let V := characterWeightAt iota.prime Q (Omega nu Q phi).val
    let source : CanonicalRawReduction iota V :=
      Classical.choice (availability Q (Omega nu Q phi).val)
    have hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) =
        (e phi.val).val := hclass nu Q phi
    have hsector : weightSector (R := R)
        (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) =
          brauerSector iota hinj blocks phi.val.val := by
      rw [hmatch]
      exact congrArg Subtype.val (hFamily.2.1 phi.val)
    exact ⟨source, outer_trivial_action_output iota phi.val.val hOuter V,
      outer_trivial_physical_pair iota hinj blocks R compatibility
        phi.val.val V source hOuter hsector⟩
  exact faithful_ad3_output_of_ordinary iota hinj blocks R E1 e hFamily.1 hOld

/-- One family and one ordinary realization suffice for the full outer-trivial branch. -/
theorem outer_trivial_family_ad3_assembly
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1)
    (hcard : Nat.card (Subgroup.center G) = 1 ∨ Nat.card (Subgroup.center G) = 2)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota) (nu0 : S)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      StableMatchedOrdinaryFixed iota hinj blocks R E1 e ∧
      FaithfulAD3Output iota hinj blocks R E1 e hFamily.1 := by
  have hcase : FaithfulSectorOrbitCases (G := G) := by
    rcases hcard with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨e, hFamily, hIndependent, hFixed, hOrdinary⟩ :=
    family_ordinary_deduction iota hinj blocks R E1 nu0 hcase e0
      (baseEquiv_equivariant_of_outer_card_one iota hinj blocks R E1 hOuter nu0 e0)
  exact ⟨e, hFamily, hIndependent, hFixed,
    outer_trivial_ad3_output_of_ordinary iota hinj blocks R E1 hOuter e hFamily
      compatibility availability (hOrdinary compatibility availability)⟩

/-- Full manuscript AD(3a-d) on original G; reference equivariance is derived. -/
theorem outer_trivial_manuscript_ad3_assembly
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
      ∃ (e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine)
        (hFamily : FamilyProperties iota inj bs R routine e),
        (∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0) ∧
        StableMatchedOrdinaryFixed iota inj bs R routine e ∧
        FaithfulAD3Output iota inj bs R routine e hFamily.1 := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro e0
  exact outer_trivial_family_ad3_assembly iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ hOuter hcard
    compatibility availability nu0 e0

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterTrivialAD3Assembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
