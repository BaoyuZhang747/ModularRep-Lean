import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction

/-! Faithful-centre AD(3a) on original G with identity embedding,
joined to the complete original gamma/model comparison on the SAME family. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryAssembly

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

/-- Ordinary invariance under the actual inner quotient action needs no match. -/
theorem ordinary_fixed (V : CharacterWeight p K G)
    (d : Subgroup.normalizer (V.subgroup : Set G)) :
    OrdinaryIrreducibleCharacter.twist K _ V.localCharacter
      (localAut V.subgroup (MulAut.conj d.val) (normalizer_stable V.subgroup d)) =
        V.localCharacter := by
  rw [localAut_conj]
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  change V.localCharacter (localMk V.subgroup d * x * (localMk V.subgroup d)⁻¹) =
    V.localCharacter x
  exact ordinaryCharacter_conj V.localCharacter (localMk V.subgroup d) x

/-- Inside original G, raw inertia is its normalizer for every original weight. -/
theorem rawIsoClass_stabilizer_comap_eq (V : CharacterWeight p K G) :
    (MulAction.stabilizer A (Quotient.mk'' V : CharacterWeight.IsoClass)).comap
      (inverseOpHom (MulAut.conj : G →* MulAut G)) =
        Subgroup.normalizer (V.subgroup : Set G) := by
  apply Subgroup.ext
  intro g
  change inverseOpHom (MulAut.conj : G →* MulAut G) g ∈
      MulAction.stabilizer A (Quotient.mk'' V : CharacterWeight.IsoClass) ↔
    g ∈ Subgroup.normalizer (V.subgroup : Set G)
  have hop : inverseOpHom (MulAut.conj : G →* MulAut G) g =
      (MulOpposite.op (MulAut.conj g))⁻¹ := by
    change MulOpposite.op (MulAut.conj g⁻¹) = MulOpposite.op ((MulAut.conj g)⁻¹)
    exact congrArg MulOpposite.op (map_inv (MulAut.conj : G →* MulAut G) g)
  rw [hop, Subgroup.inv_mem_iff]
  change (MulOpposite.op (MulAut.conj g) • (Quotient.mk'' V : CharacterWeight.IsoClass) =
    Quotient.mk'' V) ↔ _
  rw [rawIsoClass_fixed_iff]
  constructor
  · intro hraw
    exact (mem_normalizer_iff_stable V.subgroup g).mpr
      (congrArg CharacterWeight.subgroup hraw)
  · intro hg
    let d : Subgroup.normalizer (V.subgroup : Set G) := ⟨g, hg⟩
    exact (rightTwist_eq_iff_local_fixed V (MulAut.conj g)
      (normalizer_stable V.subgroup d)).mpr (ordinary_fixed V d)

/-- Concrete action output uses original G and its identity embedding. -/
def FaithfulActionOutput (chi : IBr iota) (V : CharacterWeight p K G) : Prop :=
  Function.Injective (MonoidHom.id G) ∧
  (⊤ : Subgroup G).Normal ∧
  (Subgroup.center G).map (MonoidHom.id G) ≤ Subgroup.center G ∧
  (∀ g : G, MulOpposite.op (MulAut.conj g) • chi = chi) ∧
  (∀ alpha : MulAut G, alpha ∈ (normalizerAction V.subgroup).range ↔
    (∀ z : Subgroup.center G, alpha z.val = z.val) ∧
    V.subgroup.comap alpha.toMonoidHom = V.subgroup ∧ MulOpposite.op alpha • chi = chi) ∧
  (∀ g : G, ∃ x : G, ∃ d : Subgroup.normalizer (V.subgroup : Set G),
    g = MonoidHom.id G x * d.val) ∧
  (MulAction.stabilizer A (Quotient.mk'' V : CharacterWeight.IsoClass)).comap
      (inverseOpHom (MulAut.conj : G →* MulAut G)) =
    Subgroup.normalizer (V.subgroup : Set G) ∧
  (∀ d : Subgroup.normalizer (V.subgroup : Set G),
    OrdinaryIrreducibleCharacter.twist K _ V.localCharacter
      (localAut V.subgroup (MulAut.conj d.val) (normalizer_stable V.subgroup d)) =
        V.localCharacter) ∧
  ∀ d : Subgroup.normalizer (V.subgroup : Set G),
    localAut V.subgroup (MulAut.conj d.val) (normalizer_stable V.subgroup d) =
      MulAut.conj (localMk V.subgroup d)

variable (hOuter : Nat.card (LiteralOuterQuotient G) = 2) (tau : MulAut G)
variable (hcard : Nat.card (Subgroup.center G) = 3 ∨
  Nat.card (Subgroup.center G) = 4 ∨ Nat.card (Subgroup.center G) = 6)
variable (hinverts : ∀ z : Subgroup.center G, tau z.val = z.val⁻¹)

include hOuter tau hcard hinverts in
theorem faithful_action_output (phi : FB) (V : CharacterWeight p K G) :
    FaithfulActionOutput iota phi.val V := by
  refine ⟨(fun _ _ h => h), inferInstance, ?_, inner_brauer_fixed iota phi.val,
    normalizerAction_mem_range_iff iota hinj blocks R E1 phi hOuter tau hcard hinverts V.subgroup,
    ?_, rawIsoClass_stabilizer_comap_eq V, ordinary_fixed V, localAut_conj V.subgroup⟩
  · rw [Subgroup.map_id]
  · intro g
    exact ⟨g, 1, by simp⟩

include hOuter tau hcard hinverts in
theorem faithful_same_family_pair
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (source : CanonicalRawReduction iota V) :
    PhysicalPairComparison iota hinj blocks phi.val V source := by
  have hsector : weightSector (R := R)
      (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) =
        brauerSector iota hinj blocks phi.val := by
    rw [hmatch]
    exact congrArg Subtype.val (hFamily.2.1 phi)
  exact faithful_pair_comparison iota _ (scalarBrauer iota hinj blocks phi.val) V source
    phi.faithful hOuter tau hcard hinverts
    (rawWeightSector_scalar iota R V source compatibility _ hsector)

/-- One ordinary family, with action and full comparison at each actual row. -/
def FaithfulOrdinaryOutput
    (e : FB ≃ FW) (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi) : Prop :=
  ∃ (Omega : ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q)
    (_hclass : ∀ nu Q phi, classAt iota.prime Q (Omega nu Q phi).val = (e phi.val).val),
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
        FaithfulActionOutput iota phi.val.val
          (characterWeightAt iota.prime Q (Omega nu Q phi).val) ∧
        PhysicalPairComparison iota hinj blocks phi.val.val
          (characterWeightAt iota.prime Q (Omega nu Q phi).val) source

include hOuter tau hcard hinverts in
theorem faithful_ordinary_output_of_availability (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota) :
    FaithfulOrdinaryOutput iota hinj blocks R E1 e hFamily.1 := by
  obtain ⟨Omega, hclass, hcovariance, hfixed⟩ :=
    ordinary_output_of_availability iota hinj blocks R E1 e hFamily compatibility availability
  refine ⟨Omega, hclass, hcovariance, hfixed, ?_⟩
  intro nu Q phi
  let V := characterWeightAt iota.prime Q (Omega nu Q phi).val
  let source : CanonicalRawReduction iota V :=
    Classical.choice (availability Q (Omega nu Q phi).val)
  refine ⟨source, ?_, ?_⟩
  · exact faithful_action_output iota hinj blocks R E1 hOuter tau hcard hinverts phi.val V
  · exact faithful_same_family_pair iota hinj blocks R E1 hOuter tau hcard hinverts
      compatibility e hFamily phi.val V (hclass nu Q phi) source

include hOuter tau hcard hinverts in
theorem faithful_family_ordinary_assembly
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota) (nu0 : S)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ (e : FB ≃ FW) (hFamily : FamilyProperties iota hinj blocks R E1 e),
      (∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) ∧
      StableMatchedOrdinaryFixed iota hinj blocks R E1 e ∧
      FaithfulOrdinaryOutput iota hinj blocks R E1 e hFamily.1 := by
  obtain ⟨e, hFamily, hIndependent, hfixed, _⟩ :=
    family_ordinary_deduction iota hinj blocks R E1 nu0
      (Or.inr (Or.inr ⟨hcard, tau, hinverts⟩)) e0 he0
  exact ⟨e, hFamily, hIndependent, hfixed,
    faithful_ordinary_output_of_availability iota hinj blocks R E1 hOuter tau hcard hinverts
      e hFamily compatibility availability⟩

include hOuter tau hcard hinverts in
/-- Specified faithful-centres3/4/6 AD(3a) on original G. The identity
embedding, original top models and same ordinary family are retained;
no extension group or cyclic-extension principle is supplied. -/
theorem faithful_manuscript_ordinary_assembly
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
        FaithfulOrdinaryOutput iota inj bs R routine e hFamily.1 := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact faithful_family_ordinary_assembly iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ hOuter tau hcard hinverts
    compatibility availability nu0

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
