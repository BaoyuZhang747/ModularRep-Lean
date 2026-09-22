import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison

/-! The same transported family carries the centreless and centre-two
comparisons for every matched original raw weight and canonical reduction.
Branch inputs stay separate; lower reduction availability only supplies
existence after the family and its comparisons have been constructed. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison

open ModularRep Formalisation
open EvenFieldFLZBAWGoodFamily
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps
open SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison

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

omit [Fintype G] [Invertible (Fintype.card (Subgroup.center G) : k)] in
theorem centerless_card_one (hcenter : Subgroup.center G = ⊥) :
    Nat.card (Subgroup.center G) = 1 := by
  have : Subsingleton (Subgroup.center G) := by rw [hcenter]; infer_instance
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩

omit [Invertible (Fintype.card (Subgroup.center G) : k)] in
abbrev centerlessCardInvertible (hcenter : Subgroup.center G = ⊥) :
    Invertible (Fintype.card (Subgroup.center G) : k) :=
  invertibleOfNonzero (by
    have hc : Fintype.card (Subgroup.center G) = 1 := by
      simpa only [Nat.card_eq_fintype_card] using centerless_card_one hcenter
    rw [hc, Nat.cast_one]
    exact one_ne_zero)

/-- The exact centreless output at the map and match derived from e. -/
def CenterlessMatchedPair (hcenter : Subgroup.center G = ⊥)
    (e : FB ≃ FW) (he : ∀ (a : A) (x : FB), e (a • x) = a • e x)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
      (e phi).val) (source : CanonicalRawReduction iota V) : Prop :=
  CenterlessPairComparison iota phi.val V
    (centerlessOmega iota hinj blocks R E1 hcenter e)
    (centerlessOmega_equivariant iota hinj blocks R E1 hcenter e he)
    (hmatch.trans (centerlessOmega_at_original iota hinj blocks R E1 hcenter e phi).symm) source hcenter

theorem centerless_same_family_pair (hcenter : Subgroup.center G = ⊥)
    (e : FB ≃ FW) (he : ∀ (a : A) (x : FB), e (a • x) = a • e x)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
      (e phi).val) (source : CanonicalRawReduction iota V)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    CenterlessMatchedPair iota hinj blocks R E1 hcenter e he phi V hmatch source :=
  centerless_pair_comparison iota phi.val V
    (centerlessOmega iota hinj blocks R E1 hcenter e)
    (centerlessOmega_equivariant iota hinj blocks R E1 hcenter e he)
    (hmatch.trans (centerlessOmega_at_original iota hinj blocks R E1 hcenter e phi).symm)
    source hcenter hOuter principle

/-- Output correctness for every reduction, with a separate existence consequence. -/
def CenterlessMatchedComparisons (hcenter : Subgroup.center G = ⊥)
    (e : FB ≃ FW) (he : ∀ (a : A) (x : FB), e (a • x) = a • e x) : Prop :=
  (∀ (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
      (e phi).val) (source : CanonicalRawReduction iota V),
    CenterlessMatchedPair iota hinj blocks R E1 hcenter e he phi V hmatch source) ∧
  ((∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) = (e phi).val →
      Nonempty (CanonicalRawReduction iota V)) →
    ∀ (phi : FB) (V : CharacterWeight p K G)
      (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
        (e phi).val), ∃ source : CanonicalRawReduction iota V,
      CenterlessMatchedPair iota hinj blocks R E1 hcenter e he phi V hmatch source)

theorem centerless_family_with_comparisons (nu0 : S)
    (hcenter : Subgroup.center G = ⊥)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      CenterlessMatchedComparisons iota hinj blocks R E1 hcenter e hFamily.1 := by
  obtain ⟨e, hFamily, hIndependent⟩ := family_from_sector_orbit iota hinj blocks R E1 nu0
    (faithfulSector_orbit nu0 (Or.inl (centerless_card_one hcenter))) e0 he0
  have hcomp : ∀ (phi : FB) (V : CharacterWeight p K G)
      (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
        (e phi).val) (source : CanonicalRawReduction iota V),
      CenterlessMatchedPair iota hinj blocks R E1 hcenter e hFamily.1 phi V hmatch source := by
    intro phi V hmatch source
    exact centerless_same_family_pair iota hinj blocks R E1 hcenter e hFamily.1
      phi V hmatch source hOuter principle
  refine ⟨e, hFamily, hIndependent, hcomp, ?_⟩
  intro availability phi V hmatch
  obtain ⟨source⟩ := availability phi V hmatch
  exact ⟨source, hcomp phi V hmatch source⟩

variable {T C : Type u} [Group T] [Group C]
variable (E : GroupExtension G T C) (hC : Nat.card C = 2)
variable (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
variable (hAut : Function.Surjective E.conjAct)
variable (hZ : Nat.card (Subgroup.center G) = 2)

/-- The exact centre-two output at the scalar restriction of the SAME e. -/
def CentralTwoMatchedPair
    (e : FB ≃ FW) (he : ∀ (a : A) (x : FB), e (a • x) = a • e x)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
      (e phi).val) (source : CanonicalRawReduction iota V) : Prop :=
  CentralTwoPairComparison iota (brauerSector iota hinj blocks phi.val)
    (scalarBrauer iota hinj blocks phi.val) E hC hOuter hAut hZ V source
    (scalarOmega iota hinj blocks R E1 _ phi.faithful e)
    (scalarOmega_equivariant iota hinj blocks R E1 _ phi.faithful e he)
    (hmatch.trans (scalarOmega_at_original iota hinj blocks R E1 e phi).symm)

theorem central_two_same_family_pair
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
      (e phi).val) (source : CanonicalRawReduction iota V)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    CentralTwoMatchedPair iota hinj blocks R E1 E hC hOuter hAut hZ e hFamily.1
      phi V hmatch source := by
  have hsector : weightSector (R := R)
      (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
        brauerSector iota hinj blocks phi.val := by
    rw [hmatch]
    exact congrArg Subtype.val (hFamily.2.1 phi)
  exact central_two_pair_comparison iota _ (scalarBrauer iota hinj blocks phi.val)
    E hC hOuter hAut hZ V source
    (scalarOmega iota hinj blocks R E1 _ phi.faithful e)
    (scalarOmega_equivariant iota hinj blocks R E1 _ phi.faithful e hFamily.1)
    (hmatch.trans (scalarOmega_at_original iota hinj blocks R E1 e phi).symm)
    (rawWeightSector_scalar iota R V source compatibility _ hsector) principle

/-- Every canonical reduction receives comparison; lower availability gives existence. -/
def CentralTwoMatchedComparisons
    (e : FB ≃ FW) (he : ∀ (a : A) (x : FB), e (a • x) = a • e x) : Prop :=
  (∀ (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
      (e phi).val) (source : CanonicalRawReduction iota V),
    CentralTwoMatchedPair iota hinj blocks R E1 E hC hOuter hAut hZ e he
      phi V hmatch source) ∧
  ((∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) = (e phi).val →
      Nonempty (CanonicalRawReduction iota V)) →
    ∀ (phi : FB) (V : CharacterWeight p K G)
      (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
        (e phi).val), ∃ source : CanonicalRawReduction iota V,
      CentralTwoMatchedPair iota hinj blocks R E1 E hC hOuter hAut hZ e he
        phi V hmatch source)

theorem central_two_family_with_comparisons
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (nu0 : S) (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      CentralTwoMatchedComparisons iota hinj blocks R E1 E hC hOuter hAut hZ e hFamily.1 := by
  obtain ⟨e, hFamily, hIndependent⟩ := family_from_sector_orbit iota hinj blocks R E1 nu0
    (faithfulSector_orbit nu0 (Or.inr (Or.inl hZ))) e0 he0
  have hcomp : ∀ (phi : FB) (V : CharacterWeight p K G)
      (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
        (e phi).val) (source : CanonicalRawReduction iota V),
      CentralTwoMatchedPair iota hinj blocks R E1 E hC hOuter hAut hZ e hFamily.1
        phi V hmatch source := by
    intro phi V hmatch source
    exact central_two_same_family_pair iota hinj blocks R E1 E hC hOuter hAut hZ
      compatibility e hFamily phi V hmatch source principle
  refine ⟨e, hFamily, hIndependent, hcomp, ?_⟩
  intro availability phi V hmatch
  obtain ⟨source⟩ := availability phi V hmatch
  exact ⟨source, hcomp phi V hmatch source⟩

omit [Invertible (Fintype.card (Subgroup.center G) : k)] in
/-- The centreless manuscript family comparison. Centre invertibility,
root injectivity, the actual catalogue and empty routine are internal;
no canonical block compatibility or scalar equation is supplied. -/
theorem centerless_family_equivariant_comparison
    (nu0 : FaithfulSector (k := k) (X := G))
    (hcenter : Subgroup.center G = ⊥)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    letI : Invertible (Fintype.card (Subgroup.center G) : k) :=
      centerlessCardInvertible hcenter
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
      ∃ (e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine)
        (hFamily : FamilyProperties iota inj bs R routine e),
        (∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0) ∧
        CenterlessMatchedComparisons iota inj bs R routine hcenter e hFamily.1 := by
  let : Invertible (Fintype.card (Subgroup.center G) : k) := centerlessCardInvertible hcenter
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact centerless_family_with_comparisons iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ nu0 hcenter hOuter principle

/-- The centre-two manuscript family comparison on the original extension.
Both Omega laws and scalar bindings are derived for the same family. -/
theorem central_two_family_equivariant_comparison
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (nu0 : FaithfulSector (k := k) (X := G))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
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
      ∃ (e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine)
        (hFamily : FamilyProperties iota inj bs R routine e),
        (∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0) ∧
        CentralTwoMatchedComparisons iota inj bs R routine E hC hOuter hAut hZ e hFamily.1 := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact central_two_family_with_comparisons iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ E hC hOuter hAut hZ compatibility nu0 principle

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
