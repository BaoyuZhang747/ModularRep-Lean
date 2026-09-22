import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoNormalizerAction

/-! Centre-two AD(3a) on the original extension and SAME ordinary family.
The complete gamma/model comparison is retained on every actual row. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoOrdinaryAssembly

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
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
open SporadicFi24P3Definition44NamedCarrierCentralTwoNormalizerAction

open SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings

variable {T C : Type u} [Group T] [Group C]
variable (E : GroupExtension G T C)

theorem rawIsoClass_stabilizer_comap_eq (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    :
    (MulAction.stabilizer A (Quotient.mk'' V : CharacterWeight.IsoClass)).comap
        (inverseOpHom (ambientAction E iota phi.val)) =
      embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup := by
  rw [rawIsoClass_stabilizer_eq iota hinj blocks R E1 e hFamily phi V hmatch]
  apply Subgroup.ext
  intro a
  change inverseOpHom (ambientAction E iota phi.val) a ∈
      (MulAction.stabilizer A phi.val ⊓
        MulAction.stabilizer A
          (⟨V.subgroup, V.radical⟩ : RadicalSubgroup (p := p) (G := G))) ↔
    a ∈ embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup
  have hop : inverseOpHom (ambientAction E iota phi.val) a =
      (MulOpposite.op (ambientAction E iota phi.val a))⁻¹ := by
    change MulOpposite.op (ambientAction E iota phi.val a⁻¹) =
      MulOpposite.op ((ambientAction E iota phi.val a)⁻¹)
    exact congrArg MulOpposite.op (map_inv (ambientAction E iota phi.val) a)
  rw [hop, Subgroup.inv_mem_iff]
  change (MulOpposite.op (ambientAction E iota phi.val a) • phi.val = phi.val ∧
    MulOpposite.op (ambientAction E iota phi.val a) •
      (⟨V.subgroup, V.radical⟩ : RadicalSubgroup (p := p) (G := G)) =
        (⟨V.subgroup, V.radical⟩ : RadicalSubgroup (p := p) (G := G))) ↔ _
  rw [radical_fixed_iff]
  constructor
  · rintro ⟨_, stable⟩
    exact (mem_normalizer_iff_stable E iota phi.val V.subgroup a).mpr stable
  · intro ha
    exact ⟨ambient_brauer_fixed E iota phi.val a,
      (mem_normalizer_iff_stable E iota phi.val V.subgroup a).mp ha⟩

theorem ordinary_fixed (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (d : embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup) :
    OrdinaryIrreducibleCharacter.twist K _ V.localCharacter
        (localAut V.subgroup (ambientAction E iota phi.val d.val)
          (normalizer_stable E iota phi.val V.subgroup d)) = V.localCharacter :=
  (original_local_fixed_iff iota hinj blocks R E1 e hFamily phi V hmatch
    (ambientAction E iota phi.val d.val)
    (normalizer_stable E iota phi.val V.subgroup d)).mp
      (ambient_brauer_fixed E iota phi.val d.val)

theorem base_first_factorization (e : FB ≃ FW)
    (he : ∀ (a : A) (x : FB), e (a • x) = a • e x)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (a : brauerAmbient E iota phi.val) :
    ∃ x : G, ∃ d : embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup,
      a = brauerEmbedding E iota phi.val x * d.val := by
  let nu := brauerSector iota hinj blocks phi.val
  let sphi := scalarBrauer iota hinj blocks phi.val
  have hfactor : ∃ d : embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup,
      ∃ x : G, a = d.val * brauerEmbedding E iota phi.val x :=
    matchedAmbient_factorization iota nu sphi V
    (scalarOmega iota hinj blocks R E1 nu phi.faithful e)
    (scalarOmega_equivariant iota hinj blocks R E1 nu phi.faithful e he)
    (hmatch.trans (scalarOmega_at_original iota hinj blocks R E1 e phi).symm) E a
  obtain ⟨d, x, ha⟩ := hfactor
  refine ⟨ambientAction E iota phi.val d.val x, d, ?_⟩
  calc
    a = d.val * brauerEmbedding E iota phi.val x := ha
    _ = brauerEmbedding E iota phi.val (ambientAction E iota phi.val d.val x) * d.val := by
      change d.val * brauerEmbedding E iota phi.val x =
        brauerEmbedding E iota phi.val
          (actualConjugation iota phi.val (brauerAction E iota phi.val d.val) x) * d.val
      rw [brauerEmbedding_conjugation E iota phi.val d.val x]
      simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Concrete constructed action clauses for the original extension pair. -/
def CentralTwoActionOutput (chi : IBr iota) (V : CharacterWeight p K G) : Prop :=
  Function.Injective (brauerEmbedding E iota chi) ∧
  ((brauerEmbedding E iota chi).range).Normal ∧
  (Subgroup.center G).map (brauerEmbedding E iota chi) ≤
    Subgroup.center (brauerAmbient E iota chi) ∧
  (∀ a : brauerAmbient E iota chi,
    MulOpposite.op (ambientAction E iota chi a) • chi = chi) ∧
  (∀ alpha : MulAut G, alpha ∈ (normalizerAction E iota chi V.subgroup).range ↔
    (∀ z : Subgroup.center G, alpha z.val = z.val) ∧
    V.subgroup.comap alpha.toMonoidHom = V.subgroup ∧ MulOpposite.op alpha • chi = chi) ∧
  (∀ a : brauerAmbient E iota chi,
    ∃ x : G, ∃ d : embeddedNormalizer (brauerEmbedding E iota chi) V.subgroup,
      a = brauerEmbedding E iota chi x * d.val) ∧
  (MulAction.stabilizer A (Quotient.mk'' V : CharacterWeight.IsoClass)).comap
      (inverseOpHom (ambientAction E iota chi)) =
    embeddedNormalizer (brauerEmbedding E iota chi) V.subgroup ∧
  (∀ d : embeddedNormalizer (brauerEmbedding E iota chi) V.subgroup,
    OrdinaryIrreducibleCharacter.twist K _ V.localCharacter
      (localAut V.subgroup (ambientAction E iota chi d.val)
        (normalizer_stable E iota chi V.subgroup d)) = V.localCharacter) ∧
  ∀ (d : embeddedNormalizer (brauerEmbedding E iota chi) V.subgroup)
    (n : Subgroup.normalizer (V.subgroup : Set G)),
    localAut V.subgroup (ambientAction E iota chi d.val)
      (normalizer_stable E iota chi V.subgroup d) (localMk V.subgroup n) =
    localMk V.subgroup ((normalizerBaseEquiv (brauerEmbedding E iota chi)
      (brauerEmbedding_injective E iota chi) V.subgroup).symm
        (MulAut.conjNormal d (normalizerBaseEquiv (brauerEmbedding E iota chi)
          (brauerEmbedding_injective E iota chi) V.subgroup n)))

theorem central_two_action_output (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (hAut : Function.Surjective E.conjAct) :
    CentralTwoActionOutput iota E phi.val V := by
  refine ⟨brauerEmbedding_injective E iota phi.val, inferInstance,
    embedded_center_central E iota hinj blocks R E1 phi,
    ambient_brauer_fixed E iota phi.val,
    normalizerAction_mem_range_iff E iota hinj blocks R E1 phi hAut V.subgroup,
    base_first_factorization iota hinj blocks R E1 E e hFamily.1 phi V hmatch,
    rawIsoClass_stabilizer_comap_eq iota hinj blocks R E1 E e hFamily phi V hmatch,
    ordinary_fixed iota hinj blocks R E1 E e hFamily phi V hmatch,
    ordinary_quotient_conjugation E iota phi.val V.subgroup⟩

variable (hC : Nat.card C = 2)
variable (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
variable (hAut : Function.Surjective E.conjAct)
variable (hZ : Nat.card (Subgroup.center G) = 2)

/-- One ordinary family, with action and full comparison at each actual row. -/
def CentralTwoOrdinaryOutput
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
        CentralTwoActionOutput iota E phi.val.val
          (characterWeightAt iota.prime Q (Omega nu Q phi).val) ∧
        CentralTwoMatchedPair iota hinj blocks R E1 E hC hOuter hAut hZ e he phi.val
          (characterWeightAt iota.prime Q (Omega nu Q phi).val) (hclass nu Q phi) source

theorem central_two_ordinary_output_of_availability (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    CentralTwoOrdinaryOutput iota hinj blocks R E1 E hC hOuter hAut hZ e hFamily.1 := by
  obtain ⟨Omega, hclass, hcovariance, hfixed⟩ :=
    ordinary_output_of_availability iota hinj blocks R E1 e hFamily compatibility availability
  refine ⟨Omega, hclass, hcovariance, hfixed, ?_⟩
  intro nu Q phi
  let V := characterWeightAt iota.prime Q (Omega nu Q phi).val
  let source : CanonicalRawReduction iota V :=
    Classical.choice (availability Q (Omega nu Q phi).val)
  refine ⟨source, ?_, ?_⟩
  · exact central_two_action_output iota hinj blocks R E1 E e hFamily phi.val V
      (hclass nu Q phi) hAut
  · exact central_two_same_family_pair iota hinj blocks R E1 E hC hOuter hAut hZ
      compatibility e hFamily phi.val V (hclass nu Q phi) source principle

theorem central_two_family_ordinary_assembly
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (nu0 : S) (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      StableMatchedOrdinaryFixed iota hinj blocks R E1 e ∧
      CentralTwoOrdinaryOutput iota hinj blocks R E1 E hC hOuter hAut hZ e hFamily.1 := by
  obtain ⟨e, hFamily, hIndependent, hfixed, _⟩ :=
    family_ordinary_deduction iota hinj blocks R E1 nu0
      (Or.inr (Or.inl hZ)) e0 he0
  exact ⟨e, hFamily, hIndependent, hfixed,
    central_two_ordinary_output_of_availability iota hinj blocks R E1 E hC hOuter hAut hZ
      e hFamily compatibility availability principle⟩

/-- The specified centre-two AD(3a) construction on the original extension.
Centre invertibility remains explicit; finite ambient, scalar bindings,
root injectivity, catalogue and routine are internally derived. -/
theorem central_two_manuscript_ordinary_assembly
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
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
        StableMatchedOrdinaryFixed iota inj bs R routine e ∧
        CentralTwoOrdinaryOutput iota inj bs R routine E hC hOuter hAut hZ e hFamily.1 := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact central_two_family_ordinary_assembly iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ E hC hOuter hAut hZ compatibility availability nu0 principle


end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoOrdinaryAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
