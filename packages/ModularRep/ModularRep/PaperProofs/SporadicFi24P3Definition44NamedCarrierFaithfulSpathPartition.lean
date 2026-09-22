import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulRadicalPartition

/-! Spath's faithful-sector disjoint partition and exact local support,
using the same transported e and the same ordinary local equivalences.
This does not assert the printed AD equality-iff for two empty parts. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSpathPartition

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

open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulRadicalPartition

local notation "RC" => RadicalClass (p := p) (X := G)

/-- Explicit all-index conclusions, only used as output. -/
def PartitionLaws (e : FB ≃ FW) : Prop :=
  (⋃ j, part iota hinj blocks R E1 e j) = Set.univ ∧
  (∀ nu : S, (⋃ q, part iota hinj blocks R E1 e (nu, q)) =
    {phi | pX phi = nu}) ∧
  Pairwise (fun i j => Disjoint
    (part iota hinj blocks R E1 e i) (part iota hinj blocks R E1 e j)) ∧
  (∀ (a : A) (j : S × RC),
    (fun phi : FB => a • phi) '' part iota hinj blocks R E1 e j =
      part iota hinj blocks R E1 e (a • j)) ∧
  (∀ i j : S × RC,
    part iota hinj blocks R E1 e i = part iota hinj blocks R E1 e j ↔
      i = j ∨ (part iota hinj blocks R E1 e i = ∅ ∧
        part iota hinj blocks R E1 e j = ∅)) ∧
  Function.Injective (fun j : supportedIndices iota hinj blocks R E1 e =>
    part iota hinj blocks R E1 e j.val) ∧
  (⋃ j : supportedIndices iota hinj blocks R E1 e,
    part iota hinj blocks R E1 e j.val) = Set.univ ∧
  ∀ (a : A) (j : S × RC),
    (part iota hinj blocks R E1 e (a • j)).Nonempty ↔
      (part iota hinj blocks R E1 e j).Nonempty

theorem partition_laws (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e) :
    PartitionLaws iota hinj blocks R E1 e :=
  ⟨part_cover iota hinj blocks R E1 e,
    part_sector_union iota hinj blocks R E1 e,
    part_pairwise_disjoint iota hinj blocks R E1 e,
    part_covariance iota hinj blocks R E1 e hFamily,
    part_eq_iff iota hinj blocks R E1 e,
    supported_part_injective iota hinj blocks R E1 e,
    supported_part_cover iota hinj blocks R E1 e,
    supported_iff_twist iota hinj blocks R E1 e hFamily⟩

/-- Support is measured by the actual local ordinary row of the retained map. -/
theorem support_iff_nonempty_local (e : FB ≃ FW)
    (Omega : ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) :
    (part iota hinj blocks R E1 e (nu, (Quotient.mk'' Q : RC))).Nonempty ↔
      Nonempty (RootSectorLocal iota nu.val Q) := by
  constructor
  · rintro ⟨phi, hphi⟩
    exact ⟨Omega nu Q ⟨phi, (mem_part_iff iota hinj blocks R E1 e nu _ phi).mp hphi⟩⟩
  · rintro ⟨theta⟩
    let phi := (Omega nu Q).symm theta
    exact ⟨phi.val, (mem_part_iff iota hinj blocks R E1 e nu _ phi.val).mpr phi.property⟩

theorem part_empty_iff_local_empty (e : FB ≃ FW)
    (Omega : ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) :
    part iota hinj blocks R E1 e (nu, (Quotient.mk'' Q : RC)) = ∅ ↔
      IsEmpty (RootSectorLocal iota nu.val Q) := by
  rw [← Set.not_nonempty_iff_eq_empty,
    support_iff_nonempty_local iota hinj blocks R E1 e Omega nu Q]
  exact not_nonempty_iff

def OrdinaryPartitionOutput (e : FB ≃ FW)
    (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi) : Prop :=
  ∃ Omega : ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q,
    ((∀ nu Q phi, classAt iota.prime Q (Omega nu Q phi).val = (e phi.val).val) ∧
    (∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) (a : A)
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q),
      (Omega (a • nu) (Q.rightTwist a.unop)
        (brauerTransport iota hinj blocks R E1 e he nu Q a phi)).val =
        SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localCharacterTwist
          iota.prime Q a (Omega nu Q phi).val) ∧
    ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q)
      (alpha : MulAut G) (stable : Q.val.comap alpha.toMonoidHom = Q.val),
      MulOpposite.op alpha • phi.val.val = phi.val.val ↔
        OrdinaryIrreducibleCharacter.twist K _ (Omega nu Q phi).val.val
          (localAut Q.val alpha stable) = (Omega nu Q phi).val.val) ∧
    PartitionLaws iota hinj blocks R E1 e ∧
    (∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      (part iota hinj blocks R E1 e (nu, (Quotient.mk'' Q : RC))).Nonempty ↔
        Nonempty (RootSectorLocal iota nu.val Q)) ∧
    ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      part iota hinj blocks R E1 e (nu, (Quotient.mk'' Q : RC)) = ∅ ↔
        IsEmpty (RootSectorLocal iota nu.val Q)

/-- Consume the already derived ordinary output once, retaining its exact maps. -/
theorem partition_output_of_ordinary_output (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e)
    (hOrdinary : OrdinaryLocalOutput iota hinj blocks R E1 e hFamily.1) :
    OrdinaryPartitionOutput iota hinj blocks R E1 e hFamily.1 := by
  obtain ⟨Omega, hclass, hcov, hfixed⟩ := hOrdinary
  exact ⟨Omega, ⟨hclass, hcov, hfixed⟩,
    partition_laws iota hinj blocks R E1 e hFamily,
    support_iff_nonempty_local iota hinj blocks R E1 e Omega,
    part_empty_iff_local_empty iota hinj blocks R E1 e Omega⟩

/-- The manuscript faithful-sector partition/local-map deduction on specified
carriers. All radical classes and the original transported correspondence remain. -/
theorem faithful_spath_partition_deduction
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (nu0 : FaithfulSector (k := k) (X := G)) (hcase : FaithfulSectorOrbitCases (G := G)) :
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
        OrdinaryPartitionOutput iota inj bs R routine e hFamily.1 := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro e0 he0
  obtain ⟨e, hFamily, hIndependent, hFixed, hOrdinary⟩ :=
    faithful_family_ordinary_bijections iota R compatibility availability nu0 hcase e0 he0
  exact ⟨e, hFamily, hIndependent, hFixed,
    partition_output_of_ordinary_output iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks R ⟨⟩ e hFamily hOrdinary⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSpathPartition


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
