import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessNormalizerAction

/-! Centreless AD(3a) on the same realized ordinary family, with the
complete accepted same-pair character comparison. Actual action range,
factorization and inertia are derived before reduction/extension inputs. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOrdinaryAssembly

open ModularRep ModularRep.CharacterWeight Formalisation
open TypeBCentralKernelNormalizerInertia (localAut)
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
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
open SporadicFi24P3Definition44NamedCarrierCenterlessNormalizerAction

theorem rawIsoClass_stabilizer_comap_eq (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (hcenter : Subgroup.center G = ⊥) :
    (MulAction.stabilizer A (Quotient.mk'' V : CharacterWeight.IsoClass)).comap
        (inverseOpHom (actualConjugation iota phi.val)) =
      embeddedNormalizer (innerEmbedding iota phi.val) V.subgroup := by
  rw [rawIsoClass_stabilizer_eq iota hinj blocks R E1 e hFamily phi V hmatch]
  apply Subgroup.ext
  intro a
  change inverseOpHom (actualConjugation iota phi.val) a ∈
      (MulAction.stabilizer A phi.val ⊓
        MulAction.stabilizer A
          (⟨V.subgroup, V.radical⟩ : RadicalSubgroup (p := p) (G := G))) ↔
    a ∈ embeddedNormalizer (innerEmbedding iota phi.val) V.subgroup
  have hop : inverseOpHom (actualConjugation iota phi.val) a =
      (MulOpposite.op (actualConjugation iota phi.val a))⁻¹ := by
    change MulOpposite.op (actualConjugation iota phi.val a⁻¹) =
      MulOpposite.op ((actualConjugation iota phi.val a)⁻¹)
    exact congrArg MulOpposite.op (map_inv (actualConjugation iota phi.val) a)
  rw [hop, Subgroup.inv_mem_iff]
  change (MulOpposite.op (actualConjugation iota phi.val a) • phi.val = phi.val ∧
    MulOpposite.op (actualConjugation iota phi.val a) •
      (⟨V.subgroup, V.radical⟩ : RadicalSubgroup (p := p) (G := G)) =
        (⟨V.subgroup, V.radical⟩ : RadicalSubgroup (p := p) (G := G))) ↔ _
  rw [radical_fixed_iff]
  constructor
  · rintro ⟨_, stable⟩
    exact (mem_normalizer_iff_stable iota phi.val hcenter V.subgroup a).mpr stable
  · intro ha
    exact ⟨actualConjugation_brauer_fixed iota phi.val a,
      (mem_normalizer_iff_stable iota phi.val hcenter V.subgroup a).mp ha⟩

theorem ordinary_fixed (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (hcenter : Subgroup.center G = ⊥)
    (d : embeddedNormalizer (innerEmbedding iota phi.val) V.subgroup) :
    OrdinaryIrreducibleCharacter.twist K _ V.localCharacter
        (localAut V.subgroup (actualConjugation iota phi.val d.val)
          (embedded_radical_stable iota phi.val hcenter V.subgroup d)) = V.localCharacter :=
  (original_local_fixed_iff iota hinj blocks R E1 e hFamily phi V hmatch
    (actualConjugation iota phi.val d.val)
    (embedded_radical_stable iota phi.val hcenter V.subgroup d)).mp
      (actualConjugation_brauer_fixed iota phi.val d.val)

theorem base_first_factorization (e : FB ≃ FW)
    (he : ∀ (a : A) (x : FB), e (a • x) = a • e x)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (hcenter : Subgroup.center G = ⊥) (a : ActualAutAmbient iota phi.val) :
    ∃ x : G, ∃ d : embeddedNormalizer (innerEmbedding iota phi.val) V.subgroup,
      a = innerEmbedding iota phi.val x * d.val := by
  obtain ⟨d, x, ha⟩ := matchedAmbient_factorization iota phi.val V
    (centerlessOmega iota hinj blocks R E1 hcenter e)
    (centerlessOmega_equivariant iota hinj blocks R E1 hcenter e he)
    (hmatch.trans (centerlessOmega_at_original iota hinj blocks R E1 hcenter e phi).symm) a
  refine ⟨actualConjugation iota phi.val d.val x, d, ?_⟩
  calc
    a = d.val * innerEmbedding iota phi.val x := ha
    _ = innerEmbedding iota phi.val (actualConjugation iota phi.val d.val x) * d.val := by
      rw [innerEmbedding_conjugation iota phi.val d.val x]
      simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Concrete constructed action clauses for the original centreless pair. -/
def CenterlessActionOutput (chi : IBr iota) (V : CharacterWeight p K G)
    (hcenter : Subgroup.center G = ⊥) : Prop :=
  Function.Injective (innerEmbedding iota chi) ∧
  (actualBase iota chi).Normal ∧
  (Subgroup.center G).map (innerEmbedding iota chi) ≤
    Subgroup.center (ActualAutAmbient iota chi) ∧
  (∀ a : ActualAutAmbient iota chi,
    MulOpposite.op (actualConjugation iota chi a) • chi = chi) ∧
  (∀ alpha : MulAut G, alpha ∈ (normalizerAction iota chi V.subgroup).range ↔
    (∀ z : Subgroup.center G, alpha z.val = z.val) ∧
    V.subgroup.comap alpha.toMonoidHom = V.subgroup ∧ MulOpposite.op alpha • chi = chi) ∧
  (∀ a : ActualAutAmbient iota chi,
    ∃ x : G, ∃ d : embeddedNormalizer (innerEmbedding iota chi) V.subgroup,
      a = innerEmbedding iota chi x * d.val) ∧
  (MulAction.stabilizer A (Quotient.mk'' V : CharacterWeight.IsoClass)).comap
      (inverseOpHom (actualConjugation iota chi)) =
    embeddedNormalizer (innerEmbedding iota chi) V.subgroup ∧
  (∀ d : embeddedNormalizer (innerEmbedding iota chi) V.subgroup,
    OrdinaryIrreducibleCharacter.twist K _ V.localCharacter
      (localAut V.subgroup (actualConjugation iota chi d.val)
        (embedded_radical_stable iota chi hcenter V.subgroup d)) = V.localCharacter) ∧
  ∀ (d : embeddedNormalizer (innerEmbedding iota chi) V.subgroup)
    (n : Subgroup.normalizer (V.subgroup : Set G)),
    localAut V.subgroup (actualConjugation iota chi d.val)
      (embedded_radical_stable iota chi hcenter V.subgroup d) (localMk V.subgroup n) =
    localMk V.subgroup ((normalizerBaseEquiv (innerEmbedding iota chi)
      (innerEmbedding_injective iota chi hcenter) V.subgroup).symm
        (MulAut.conjNormal d (normalizerBaseEquiv (innerEmbedding iota chi)
          (innerEmbedding_injective iota chi hcenter) V.subgroup n)))

theorem centerless_action_output (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (hcenter : Subgroup.center G = ⊥) :
    CenterlessActionOutput iota phi.val V hcenter := by
  refine ⟨innerEmbedding_injective iota phi.val hcenter, inferInstance,
    embedded_center_central iota phi.val hcenter,
    actualConjugation_brauer_fixed iota phi.val,
    normalizerAction_mem_range_iff iota phi.val hcenter V.subgroup,
    base_first_factorization iota hinj blocks R E1 e hFamily.1 phi V hmatch hcenter,
    rawIsoClass_stabilizer_comap_eq iota hinj blocks R E1 e hFamily phi V hmatch hcenter,
    ordinary_fixed iota hinj blocks R E1 e hFamily phi V hmatch hcenter,
    ordinary_quotient_conjugation iota phi.val hcenter V.subgroup⟩

/-- One ordinary family, with action and full comparison at each actual row. -/
def CenterlessOrdinaryOutput (hcenter : Subgroup.center G = ⊥)
    (e : FB ≃ FW) (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi) : Prop :=
  ∃ (Omega : ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q)
    (hclass : ∀ nu Q phi, classAt iota.prime Q (Omega nu Q phi).val = (e phi.val).val),
    (∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) (a : A)
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q),
      (Omega (a • nu) (Q.rightTwist a.unop)
        (brauerTransport iota hinj blocks R E1 e he nu Q a phi)).val =
        SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localCharacterTwist
          iota.prime Q a (Omega nu Q phi).val) ∧
    (∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q)
      (alpha : MulAut G) (stable : Q.val.comap alpha.toMonoidHom = Q.val),
      MulOpposite.op alpha • phi.val.val = phi.val.val ↔
        OrdinaryIrreducibleCharacter.twist K _ (Omega nu Q phi).val.val
          (localAut Q.val alpha stable) = (Omega nu Q phi).val.val) ∧
    ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q),
      ∃ source : CanonicalRawReduction iota
          (characterWeightAt iota.prime Q (Omega nu Q phi).val),
        CenterlessActionOutput iota phi.val.val
          (characterWeightAt iota.prime Q (Omega nu Q phi).val) hcenter ∧
        CenterlessMatchedPair iota hinj blocks R E1 hcenter e he phi.val
          (characterWeightAt iota.prime Q (Omega nu Q phi).val) (hclass nu Q phi) source

theorem centerless_ordinary_output_of_availability (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (hcenter : Subgroup.center G = ⊥)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    CenterlessOrdinaryOutput iota hinj blocks R E1 hcenter e hFamily.1 := by
  obtain ⟨Omega, hclass, hcovariance, hfixed⟩ :=
    ordinary_output_of_availability iota hinj blocks R E1 e hFamily compatibility availability
  refine ⟨Omega, hclass, hcovariance, hfixed, ?_⟩
  intro nu Q phi
  let V := characterWeightAt iota.prime Q (Omega nu Q phi).val
  let source : CanonicalRawReduction iota V :=
    Classical.choice (availability Q (Omega nu Q phi).val)
  refine ⟨source, ?_, ?_⟩
  · exact centerless_action_output iota hinj blocks R E1 e hFamily phi.val V
      (hclass nu Q phi) hcenter
  · exact centerless_same_family_pair iota hinj blocks R E1 hcenter e hFamily.1 phi.val V
      (hclass nu Q phi) source hOuter principle

theorem centerless_family_ordinary_assembly
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
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
      StableMatchedOrdinaryFixed iota hinj blocks R E1 e ∧
      CenterlessOrdinaryOutput iota hinj blocks R E1 hcenter e hFamily.1 := by
  obtain ⟨e, hFamily, hIndependent, hfixed, _⟩ :=
    family_ordinary_deduction iota hinj blocks R E1 nu0
      (Or.inl (centerless_card_one hcenter)) e0 he0
  exact ⟨e, hFamily, hIndependent, hfixed,
    centerless_ordinary_output_of_availability iota hinj blocks R E1 e hFamily
      compatibility availability hcenter hOuter principle⟩

omit [Invertible (Fintype.card (Subgroup.center G) : k)] in
/-- Specified centreless AD(3a) and same ordinary-pair comparison.
Root injectivity, centre invertibility, actual blocks and routine are internal. -/
theorem centerless_manuscript_ordinary_assembly
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
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
        StableMatchedOrdinaryFixed iota inj bs R routine e ∧
        CenterlessOrdinaryOutput iota inj bs R routine hcenter e hFamily.1 := by
  let : Invertible (Fintype.card (Subgroup.center G) : k) := centerlessCardInvertible hcenter
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact centerless_family_ordinary_assembly iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ compatibility availability nu0 hcenter hOuter principle


end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOrdinaryAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
